import z3


def hamiltonian_path(graph):
    
    n = len(graph)
    vertice = [z3.Int(f"v{i}") for i in range(n)]

    bf = z3.Solver()
    
    for i in range(n):
        for j in range(n):
            bf.add(z3.And(vertice[i] != vertice[j]))
    
    for i in range(n):
        bf.add(z3.And([vertice[j] == (vertice[i] + 1) for j in range(n)]))

    
    smt2_representation = bf.to_smt2()

    
    file_name = f'uhamcycle_state.smt2'
    with open(file_name, 'w') as file:
        file.write(smt2_representation)

    return bf
        


def examples():
    graph = {
    0: [1, 2, 3, 4, 5],
    1: [6, 7],
    2: [8, 9],
    3: [10, 11],
    4: [12, 13],
    5: [14, 15],
    6: [16, 17],
    7: [18, 19],
    8: [0],
    9: [1],
    10: [2],
    11: [3],
    12: [4],
    13: [5],
    14: [6],
    15: [7],
    16: [8],
    17: [9],
    18: [10],
    19: [11],
}

    solution = hamiltonian_path(graph)
    print(solution.check())
    
    if (solution.check() == z3.sat): 
        path = solution.model()
        # print(" -> ".join(f"{i}" for i in path))
        print(path)
    else:
        print("No Hamiltonian path found.")
        return None


if __name__ == "__main__":
    examples()
    

    
