def check_maxindset(graph: dict[int, list[int]], k):
    n = len(graph)

    vertices = z3.IntVector("v", n)
    solver = z3.Solver()

    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))
        
    no_edges = []
    for i in range(k):
        for j in range(i + 1, k):
                no_edges.append(z3.Not(edge(graph, vertices[i], vertices[j])))
    solver.add(z3.And(no_edges))

    result = solver.check() 
    if result == z3.sat:
        model = solver.model()
        maxindset = [model[vertices[i]].as_long() for i in range(k)]
        print(maxindset)
    else:
        print(result)
        model = None

    smt2_representation = solver.to_smt2()
    file_name = f'maxindset_{n}_{k}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    return result, model
