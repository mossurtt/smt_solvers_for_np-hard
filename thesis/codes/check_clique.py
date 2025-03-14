def check_clique(graph: dict[int, list[int]], k):
    n = len(graph)

    vertices = z3.IntVector("v", k)
    solver = z3.Solver()

    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))
        
    edges = []
    for i in range(k):
        for j in range(i + 1, k):
            edges.append(edge(graph, vertices[i], vertices[j]))
    solver.add(z3.And(edges))

    result = solver.check() 
    if result == z3.sat:
        print('Znaleziono klike o rozmiarze', k)
        model = solver.model()
        clique = [model[vertices[i]].as_long() for i in range(k)]
        print(clique)
    else:
        print('Nie znaleziono kliki o rozmiarze', k)
        model = None

    smt2_representation = solver.to_smt2()
    file_name = f'maxclique-{n}-{k}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    return (result, model)
