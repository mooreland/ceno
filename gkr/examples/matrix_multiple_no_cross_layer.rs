use frontend::structs::{CellType, CircuitBuilder, ConstantType};
use gkr::structs::{Circuit, CircuitWitness, IOPProverState, IOPVerifierState};
use gkr::utils::MultilinearExtensionFromVectors;
use goldilocks::{Goldilocks, SmallField};
use itertools::Itertools;
use transcript::Transcript;


#[derive(Debug)]
struct AllInputIndex {
    target_vec_idx:usize,
    init_vec_idx:usize,
    matrix_row_idx: Vec<usize>,
}

fn construct_circuit<F: SmallField>(vec_size: usize,row_count:usize) -> (Circuit<F>, AllInputIndex) {
    let mut circuit_builder = CircuitBuilder::<F>::new();
    let one = ConstantType::Field(F::ONE);


    let (target_vec_idx, target_vec_cells) = circuit_builder.create_wire_in(vec_size);
    let (init_vec_idx, init_vec_cells) = circuit_builder.create_wire_in(vec_size);

    let zero_cell = circuit_builder.create_constant_in(1,0)[0];

    let mut matrix_rows = vec![];
    for _ in 0..row_count{
        matrix_rows.push(circuit_builder.create_wire_in(vec_size));
    }
    let (matrix_row_idx,matrix_row_cells):(Vec<_>,Vec<_>) = matrix_rows.into_iter().unzip();

    let mut product_fn = |circuit_builder:&mut CircuitBuilder<F>,in_left:&[usize], in_right:&[usize]|{
        let product_cells = circuit_builder.create_cells(vec_size);
        for i in 0..vec_size {
            circuit_builder.mul2(product_cells[i], in_left[i], in_right[i], one);
        }
        product_cells
    };


    let mut acc_fn = |circuit_builder:&mut CircuitBuilder<F>,inputs :&[usize],zero_cell_stack:&[usize],acc:&[usize]|{
        let mut pad_cells:Vec<_> = inputs.into();
        for j in 0..zero_cell_stack.len(){
            let acc_cells = circuit_builder.create_cells(vec_size);
            for i in 0..vec_size {
                circuit_builder.add(acc_cells[i],pad_cells[i],one);
                circuit_builder.add(acc_cells[i],zero_cell_stack[j],one);
            }
            pad_cells =acc_cells;
        }
        let acc_cells = circuit_builder.create_cells(vec_size);
        for i in 0..vec_size {
            circuit_builder.add(acc_cells[i],pad_cells[i],one);
            circuit_builder.add(acc_cells[i],acc[i],one);
        }
        acc_cells


    };

    let mut acc = init_vec_cells;
    let mut zero_cells_stack = vec![];
    for (i,row_cells) in matrix_row_cells.iter().enumerate() {
        //pad init input to higher layer
        if i==0{
            let acc_cells = circuit_builder.create_cells(vec_size);
            for i in 0..vec_size {
                circuit_builder.add(acc_cells[i],acc[i],one);
                circuit_builder.add(acc_cells[i],zero_cell,one);
            }
            acc =acc_cells;
        }

        //pass through the zero cell to zero stack in each layer
        if i>0{
            let new_zero_cell = circuit_builder.create_cell();
            let last_zero_cell = if zero_cells_stack.len()>0{
                zero_cells_stack[zero_cells_stack.len()-1]
            }else { zero_cell };
            //add one is ok
            circuit_builder.add(new_zero_cell,last_zero_cell,one);
            zero_cells_stack.push(new_zero_cell);
        }
        //product row and target column vector
        let product = product_fn(&mut circuit_builder,&target_vec_cells, row_cells);
        //fold model, acc the result
        acc = acc_fn(&mut circuit_builder,&product, &zero_cells_stack,&acc);

    }

    circuit_builder.configure();
    circuit_builder.print_info();
    (
        Circuit::<F>::new(&circuit_builder),
        AllInputIndex {
            target_vec_idx,
            init_vec_idx,
            matrix_row_idx
        },
    )
}

fn main() {
    let vec_size = 2;
    let row_count = 3;
    let (circuit, input_idxs) = construct_circuit::<Goldilocks>(vec_size,row_count);
    let mut wires_in = vec![vec![Goldilocks::from(0u64);vec_size]; circuit.n_wires_in];

    for i in 0..vec_size{
        wires_in[input_idxs.target_vec_idx][i]=Goldilocks::from(1u64+i as u64);
        wires_in[input_idxs.init_vec_idx][i]=Goldilocks::from(0u64);
    }
    for v in input_idxs.matrix_row_idx{
        for i in 0..vec_size{
            wires_in[v][i]=Goldilocks::from(1u64+v as u64+i as u64);
        }
    }


    let circuit_witness = {
        let challenge = Goldilocks::from(9);
        let mut circuit_witness = CircuitWitness::new(&circuit, vec![challenge]);
        for _ in 0..1 {
            circuit_witness.add_instance(&circuit, &wires_in);
        }
        circuit_witness
    };
    print!("circuit: {:?}", circuit);
    print!("witness: {:?}", circuit_witness);
    #[cfg(feature = "debug")]
    circuit_witness.check_correctness(&circuit);

    let instance_num_vars = circuit_witness.instance_num_vars();

    let (proof, output_num_vars, output_eval) = {
        let mut prover_transcript = Transcript::new(b"example");
        let output_num_vars = instance_num_vars + circuit.last_layer_ref().num_vars();

        let output_point = (0..output_num_vars)
            .map(|_| {
                prover_transcript
                    .get_and_append_challenge(b"output point")
                    .elements[0]
            })
            .collect_vec();

        let output_eval = circuit_witness
            .layer_poly(0, circuit.last_layer_ref().num_vars())
            .evaluate(&output_point);
        (
            IOPProverState::prove_parallel(
                &circuit,
                &circuit_witness,
                &[(output_point, output_eval)],
                &[],
                &mut prover_transcript,
            ),
            output_num_vars,
            output_eval,
        )
    };

    let gkr_input_claims = {
        let mut verifier_transcript = &mut Transcript::new(b"example");
        let output_point = (0..output_num_vars)
            .map(|_| {
                verifier_transcript
                    .get_and_append_challenge(b"output point")
                    .elements[0]
            })
            .collect_vec();
        IOPVerifierState::verify_parallel(
            &circuit,
            circuit_witness.challenges(),
            &[(output_point, output_eval)],
            &[],
            &proof,
            instance_num_vars,
            &mut verifier_transcript,
        )
        .expect("verification failed")
    };

    let expected_values = circuit_witness
        .wires_in_ref()
        .iter()
        .map(|witness| {
            witness
                .as_slice()
                .mle(circuit.max_wires_in_num_vars, instance_num_vars)
                .evaluate(&gkr_input_claims.point)
        })
        .collect_vec();
    for i in 0..gkr_input_claims.values.len() {
        assert_eq!(expected_values[i], gkr_input_claims.values[i]);
    }

    println!("verification succeeded");
}
