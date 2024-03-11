def check_subsetsum(input_set, t):
    n = len(input_set)
    vars = z3.IntVector('x', n)

    solver = z3.Solver()
    
    for var in vars:
        solver.add(z3.Or(var == 0, var == 1))

    subset_sum = z3.Sum([vars[i] * input_set[i] for i in range(n)])
    solver.add(subset_sum == t)
    
    folder_name = f'subsetsum_{n}'
    os.makedirs(folder_name, exist_ok=True)

    smt2_representation = solver.to_smt2()
    file_name = f'{folder_name}/subsetsum_{n}_{t}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        subset = [input_set[i] for i in range(n) if model[vars[i]] == 1]
        print(t, subset)
    else:
        print(t, result)
        model = None

    return result, model
