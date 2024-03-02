import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 vertexcover.py <filename>")
        return

    filename = sys.argv[1]
    graph = read_graph_from_file(filename)

    print(check_vertexcover(graph))

def read_graph_from_file(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    graph = {}
    for i, line in enumerate(lines):
        neighbors = [int(x) for x in line.strip().split(',')]
        graph[i] = neighbors
    return graph


def check_vertexcover(graph):
    n = len(graph)
    vertices = z3.BoolVector('v', n)

    solver = z3.Solver()

    min_size = float('inf')
    left = 0
    right = n
    
    while left <= right:
        mid = (left + right) // 2
        solver.reset()
        solver.add(z3.Sum([z3.If(vertices[v], 1, 0) for v in range(n)]) <= mid)
        
        for u in range(n):
            for v in graph[u]:
                solver.add(z3.Or(vertices[u], vertices[v]))
        
        if solver.check() == z3.sat:
            min_size = mid
            right = mid - 1
        else:
            left = mid + 1
    
    smt2_representation = solver.to_smt2()
    file_name = f'vertexcover_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    if solver.check() == z3.sat:
        model = solver.model()
        cover = [v for v in range(n) if model.eval(vertices[v])]
        return cover
    else:
        return None

if __name__ == "__main__":
    main()