import z3 

def main():

    filename = "unsatgraph.txt"
    digraph = read_graph_from_file(filename)
    

    # digraph = {
    #     0: [1, 4, 5],
    #     1: [0, 7, 2],
    #     2: [1, 9, 3],
    #     3: [2, 11, 4],
    #     4: [3, 13, 0],
    #     5: [0, 14, 6],
    #     6: [5, 16, 7],
    #     7: [6, 8, 1],
    #     8: [7, 17, 9],
    #     9: [8, 10, 2],
    #     10: [9, 18, 11],
    #     11: [10, 3, 12],
    #     12: [11, 19, 13],
    #     13: [12, 14, 4],
    #     14: [13, 15, 5],
    #     15: [14, 16, 19],
    #     16: [6, 17, 15],
    #     17: [16, 8, 18],
    #     18: [10, 19, 17],
    #     19: [18, 12, 15]
    # }

#     unsatgraph = {
#     0: [1, 2],
#     1: [0, 2, 3],
#     2: [0, 1],
#     3: [1],
#     4: [1]
# }
    
    hamiltonian_path(digraph)

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors

    return graph

def hamiltonian_path(graph: dict[int, list[int]]):

    n = len(graph)
    vertice = z3.IntVector("v", n)

    solver = z3.Solver()

    solver.add(proper_numbers(vertice))

    solver.add(distinct_vs(vertice))

    edges = []
    for i in range(n - 1):
        edges.append(edge(graph, vertice[i], vertice[i + 1]))
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
        vertex_values = [(idx, model[v].as_long()) for idx, v in enumerate(vertice)]
        sorted_vertices = sorted(vertex_values)
        print("Hamiltonian Path:")
        for idx, value in sorted_vertices[:-1]:
            print(f"v__{value}", end=' -> ')
        print(f"v__{sorted_vertices[-1][1]}")
    else:
        print(result)
    
def proper_numbers(vertice):
    n = len(vertice)
    atoms = []
    for i in range(n - 1):
        atoms.append(z3.And(vertice[i] >= 0, vertice[i] < n))
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf

def distinct_vs(vertice):
    n = len(vertice)
    atoms = []
    for i in range(n - 1):
        for j in range(i + 1, n):
            atoms.append(vertice[i] != vertice[j])
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf

def edge(graph: dict[int, list[int]], s, t):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.And([s == source, t == target]))
    bf = z3.Or(atoms)
    z3.simplify(bf)
    return bf


if __name__ == "__main__":
    main()
