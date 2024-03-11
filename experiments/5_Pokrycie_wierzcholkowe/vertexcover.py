import sys
import z3 
from utils.constraints import proper_numbers
from utils.read_input import read_graph_from_file

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxindset.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)

    for k in range(n, 0, -1):
        result, model = check_vertexcover(graph, k)
        if result != z3.sat:
            break

def check_vertexcover(graph: dict[int, list[int]], k):
    n = len(graph)
    vertices = z3.IntVector("v", n)
    solver = z3.Solver()
    
    solver.add(proper_numbers(vertices))
    solver.add(distinct_vs(vertices, k))

    vertex_in_cover = []
    for i in range(k):
        for j in range(i + 1, k):
            vertex_in_cover.append(edge_covered(graph, vertices[i]))
    solver.add(z3.Or(vertex_in_cover))

    smt2_representation = solver.to_smt2()
    file_name = f'vertexcover_{n}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check() 
    if result == z3.sat:
        print('Znaleziono pokrycie o rozmiarze', k)
        model = solver.model()
        vertex_cover = [model[vertices[i]].as_long() for i in range(k)]
        print(model, vertex_cover) 
    else:
        print('Nie znaleziono pokrycia')
        model = None

    return result, model

def distinct_vs(vertices, k):
    atoms = []
    for i in range(k):
        for j in range(i + 1, k):
            atoms.append(vertices[i] != vertices[j])
    bf = z3.And(atoms)
    return bf

def edge_covered(graph: dict[int, list[int]], v):
    atoms = []
    for source in graph:
        for target in graph[source]:
            atoms.append(z3.Or([v == source, v == target]))  
    bf = z3.And(atoms)
    z3.simplify(bf)
    return bf

if __name__ == "__main__":
    main()