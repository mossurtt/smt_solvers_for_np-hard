def check_vertexcover(graph: dict[int, list[int]], k):
    n = len(graph)
    vertices = z3.IntVector('v', k)
    solver = z3.Solver()

    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices))

    for source in graph:
        for target in graph[source]:
            vertex_in_cover = False
            for j in range(k):
                vertex_in_cover = z3.Or(vertex_in_cover, z3.Or(vertices[j] == source, vertices[j] == target))
            solver.add(vertex_in_cover)


    smt2_representation = solver.to_smt2()
    file_name = f'vertexcover_{n}_{k}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check() 
    if result == z3.sat:
        print('Znaleziono pokrycie o rozmiarze', k)
        model = solver.model()
        vertex_cover = [model[v].as_long() for v in vertices]
        print(vertex_cover) 
    else:
        print('Nie znaleziono pokrycia o rozmiarze', k)
        model = None
