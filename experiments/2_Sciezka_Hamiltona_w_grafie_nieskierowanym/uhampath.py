import sys
import z3 
from utils.constraints import proper_numbers, distinct_vs, edge
from utils.read_input import read_graph_from_file

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 uhampath.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)

    hamiltonian_path(graph)

def hamiltonian_path(graph: dict[int, list[int]]):

    n = len(graph)
    vertices = z3.IntVector("v", n)

    solver = z3.Solver()

    solver.add(proper_numbers(vertices))

    solver.add(distinct_vs(vertices))

    edges = []
    for i in range(n - 1):
        edges.append(edge(graph, vertices[i], vertices[i + 1]))
    solver.add(z3.And(edges))

    smt2_representation = solver.to_smt2()
    file_name = f'uhampath_{n}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        vertex_values = [(idx, model[v].as_long()) for idx, v in enumerate(vertices)]
        sorted_vertices = sorted(vertex_values)
        print("Hamiltonian Path:")
        for idx, value in sorted_vertices[:-1]:
            print(f"v__{value}", end=' -> ')
        print(f"v__{sorted_vertices[-1][1]}")
    else:
        print(result)


if __name__ == "__main__":
    main()
