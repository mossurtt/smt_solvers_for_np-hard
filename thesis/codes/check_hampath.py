def check_hampath(graph: dict[int, list[int]]):

    n = len(graph)
    vertices = z3.IntVector("v", n)

    solver = z3.Solver()

    solver.add(proper_numbers(vertices))

    solver.add(distinct_vs(vertices))

    edges = []
    for i in range(n - 1):
        edges.append(dir_edge(graph, vertices[i], vertices[i + 1]))
    solver.add(z3.And(edges))

    smt2_representation = solver.to_smt2()
    file_name = f'hampath_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        vertex_values = [(idx, model[v].as_long()) for idx, v in enumerate(vertices)]
        sorted_verticess = sorted(vertex_values)
        print("Hamiltonian Path:")
        for idx, value in sorted_verticess[:-1]:
            print(f"v__{value}", end=' -> ')
        print(f"v__{sorted_verticess[-1][1]}")
    else:
        print(result)
