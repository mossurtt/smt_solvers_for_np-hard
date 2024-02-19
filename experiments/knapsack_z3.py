import z3

def main():
    filename = 'input_knapsack.txt'
    values, weights, capacity = read_input_from_file(filename)

    print(check_knapsack(values, weights, capacity))

def read_input_from_file(filename):
    with open(filename, 'r') as file:
        contents = file.read()
    
    lines = contents.strip().split('\n')

    values = list(map(int, lines[0].split(',')))
    weights = list(map(int, lines[1].split(',')))
    capacity = int(lines[2])

    return values, weights, capacity

def check_knapsack(values, weights, capacity):
    n = len(values)

    solver = z3.Solver()

    x = [z3.Bool(f'x_{i}') for i in range(n)]

    max_value = -1
    left = 0
    right = sum(values)
    
    while left <= right:
        mid = (left + right) // 2
        solver.reset()
        solver.add(z3.Sum([z3.If(x[i], weights[i], 0) for i in range(n)]) <= capacity)

        solver.add(z3.Sum([z3.If(x[i], values[i], 0) for i in range(n)]) >= mid)        

        if solver.check() == z3.sat:
            max_value = mid
            left = mid + 1
        else:
            right = mid - 1

    solver.reset()
    solver.add(z3.Sum([z3.If(x[i], weights[i], 0) for i in range(n)]) <= capacity)
    solver.add(z3.Sum([z3.If(x[i], values[i], 0) for i in range(n)]) == max_value)

    smt2_representation = solver.to_smt2()
    file_name = f'knapsack_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    solver.check()
    model = solver.model()
    selected_items = [i for i in range(n) if model[x[i]]]

    return max_value, selected_items


if __name__ == '__main__':
    main()