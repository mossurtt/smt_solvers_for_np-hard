from z3 import *

def hamiltonian_path(graph):

    n = len(graph)
    
    v = [Int(f"v{i}") for i in range(n)]

    s = Solver()
    s.add(v[0] == 0)
    
    for i in range(n):
        s.add(Or([v[j] == (v[i] + 1) % n for j in graph[i]]))
    return s

def examples():
    # Dodecahedron
    grdodec = { 0: [1, 4, 5],
                1: [0, 7, 2],
                2: [1, 9, 3],
                3: [2, 11, 4],
                4: [3, 13, 0],
                5: [0, 14, 6],
                6: [5, 16, 7],
                7: [6, 8, 1],
                8: [7, 17, 9],
                9: [8, 10, 2],
                10: [9, 18, 11],
                11: [10, 3, 12],
                12: [11, 19, 13],
                13: [12, 14, 4],
                14: [13, 15, 5],
                15: [14, 16, 19],
                16: [6, 17, 15],
                17: [16, 8, 18],
                18: [10, 19, 17],
                19: [18, 12, 15] }

    import pprint
    pp = pprint.PrettyPrinter(indent=4)
    pp.pprint(grdodec)

    sdodec = hamiltonian_path(grdodec)
    print(sdodec.check())
    path = sdodec.model()
    if (sdodec.check() == sat): print(" -> ".join(f"{i}" for i in path))
    else: return None

    # The Herschel graph is the smallest possible polyhedral graph that does not have a Hamiltonian cycle.
    grherschel = { 0: [1, 9, 10, 7],
                   1: [0, 8, 2],
                   2: [1, 9, 3],
                   3: [2, 8, 4],
                   4: [3, 9, 10, 5],
                   5: [4, 8, 6],
                   6: [5, 10, 7],
                   7: [6, 8, 0],
                   8: [1, 3, 5, 7],
                   9: [2, 0, 4],
                   10: [6, 4, 0] }

    pp.pprint(grherschel)
    sherschel = hamiltonian_path(grherschel)
    print(sherschel.check())
    if (sherschel.check() == sat): print(sherschel.model())
    else: return None

if __name__ == "__main__":
    examples()
