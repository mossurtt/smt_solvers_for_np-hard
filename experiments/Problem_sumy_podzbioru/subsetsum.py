import sys
import z3 
from utils.read_input import read_set_from_file

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 subsetsum.py <filename>")
        return

    filename = sys.argv[1]
    input_set = read_set_from_file(filename)
    n = len(input_set)
    
    for k in range(1, n + 1):
        result, model = check_subsetsum(input_set, k)
        
def check_subsetsum(input_set, k):
    n = len(input_set)
    vars = z3.IntVector('x', n)

    solver = z3.Solver()
    solver.add(set_vars(vars, input_set))

    target_sum = z3.IntVal(0)
    subset = []

    for i in range(k):
        subset.append(vars[i]) 

    solver.add(z3.Sum(subset) == target_sum)

    smt2_representation = solver.to_smt2()
    file_name = f'subsetsum_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        solution = [model[vars[i]].as_long() for i in range(k)]
        print(solution)
        # print(model)
    else:
        print(result)
        model = None

    return result, model

def set_vars(vars, input_set):
    n = len(input_set)
    atoms = []
    for i in range(n):
        atoms.append(vars[i] == input_set[i])
    bf = z3.Or(atoms)
    return bf

if __name__ == "__main__": 
    main()