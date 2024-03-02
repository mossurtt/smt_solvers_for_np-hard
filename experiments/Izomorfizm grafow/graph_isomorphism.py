import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 hampath.py <filename>")
        return

    filename = sys.argv[1]
    graph1, graph2 = read_input_from_file(filename)
    # graph1 = [
    #     [1, 2],
    #     [0, 3],
    #     [0, 3],
    #     [1, 2]
    # ]

    # graph2 = [
    #     [1, 2],
    #     [0, 3],
    #     [0, 3],
    #     [1, 2]
    # ] 

    check_isomorphism(graph1, graph2)

def check_isomorphism(graph1, graph2):
    n = len(graph1)

    mapping = [z3.Int(f'mapping_{i}') for i in range(n)]

    solver = z3.Solver()

    solver.add([z3.And(0 <= mapping[i], mapping[i] < n) for i in range(n)])

    solver.add([z3.Distinct(mapping)])

    for i in range(n):
        for n in graph1[i]:
            mapped_n = mapping[n]
            solver.add(z3.Or([z3.And(mapping[i] == j, mapped_n in graph2[j]) for j in range(n)]))

    print(solver.check())

if __name__ == '__main__':
    main()
