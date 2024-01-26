import z3

graph_count = 0

def hamiltonian_path(graph):
    global graph_count
    n = len(graph)
    v = [z3.Int(f"v{i}") for i in range(n)]
    print(v)
    solver = z3.Solver()
    solver.add(v[0] == 0)
    
    for i in range(n):
        solver.add(z3.Or([v[j] == (v[i] + 1) % n for j in graph[i]]))

    smt2_representation = solver.to_smt2()

    graph_count += 1
    file_name = f'hampath_state_{graph_count}.smt2'
    with open(file_name, 'w') as file:
        file.write(smt2_representation)

    return solver


def get_input():
    print("Enter the number of vertices:")
    n = int(input())

    graph = {}
    for i in range(n):
        print(f"Enter the neighbors of vertex {i}: (comma-separated, e.g. 1,2,3)")
        neighbors_input = input().strip()

        if neighbors_input:        
            neighbors = list(map(int, neighbors_input.split(',')))
        else:
            neighbors = []
            
        graph[i] = neighbors
    print(graph)
    return graph


def examples():
    graph = get_input()
    solution = hamiltonian_path(graph)
    print(solution.check())
    
    if (solution.check() == z3.sat): 
        path = solution.model()
        print(" -> ".join(f"{i}" for i in path))
        print(path)
    else:
        print("No Hamiltonian path found.")
        return None


if __name__ == "__main__":
    examples()
    
