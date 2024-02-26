import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 subsetsum.py <filename>")
        return

    filename = sys.argv[1]
    input_set = read_set_from_file(filename)
    
    check_subsetsum(input_set)

def read_set_from_file(filename):
    with open(filename, 'r') as file:
        data = file.read().strip()
        input_set = list(map(int, data.split(',')))
    return input_set

def check_subsetsum(input_set):
    set_len = len(input_set)

    vars = [z3.Int(f'vars_{i}') for i in range(set_len)]

    solver = z3.Solver()
    terms = []

    for i in range(set_len):
        terms.append(vars[i] * input_set[i])
        solver.add(z3.Or(vars[i] == 0, vars[i] == 1))

    solver.add(sum(terms) == 0)
    solver.add(sum(vars) > 1)

    smt2_representation = solver.to_smt2()
    file_name = f'subsetsum_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        solution = [input_set[i] for i in range(set_len) if model[vars[i]] == 1]
        print(solution)
    else:
        print(result)

if __name__ == "__main__": 
    main()