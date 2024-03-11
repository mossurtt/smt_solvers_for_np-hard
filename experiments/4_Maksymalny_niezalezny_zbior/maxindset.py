import sys
import z3 
from utils.constraints import proper_numbers, distinct_vs, edge
from utils.read_input import read_graph_from_file

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 maxindset.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)
    n = len(graph)

    for k in range(2, n + 1):
        result, model = check_maxindset(graph, k)
        if result != z3.sat:
            break

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

    folder_name = f'maxindset_{n}'
    os.makedirs(folder_name, exist_ok=True)

    smt2_representation = solver.to_smt2()
    file_name = f'{folder_name}/maxindset_{n}_{k}.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    return result, model


if __name__ == "__main__":
    main()

    
    
