import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 setcover.py <filename>")
        return

    filename = sys.argv[1]
    universe, subsets = read_input_from_file(filename)
    
    print(check_setcover(universe, subsets))

def read_input_from_file(filename):
    with open(filename, 'r') as file:
        universe = set()
        subsets = []

        for line in file:
            elements = list(map(int, line.strip().split(',')))
            if len(universe) == 0:
                universe.update(elements)
            else:
                subsets.append(set(elements))

    return universe, subsets

def check_setcover(universe, subsets):
    n = len(universe)
    m = len(subsets)

    selected = [z3.Bool(f's_{i}') for i in range(m)]

    universe_list = list(universe)

    solver = z3.Solver()

    for i in range(n):
        solver.add(z3.Or([selected[j] for j in range(m) if universe_list[i] in subsets[j]]))

    k = 0
    min_cover = None
    while k <= m:
        k += 1
        solver.push()
        solver.add(z3.Sum(selected) <= k)
        if solver.check() == z3.sat:
            model = solver.model()
            min_cover = [subsets[i] for i in range(m) if model[selected[i]] == z3.BoolVal(True)]
            solver.pop()
            break
        solver.pop()

    smt2_representation = solver.to_smt2()
    file_name = f'setcover_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        return min_cover 
    else:
        return result

if __name__ == '__main__':
    main()
