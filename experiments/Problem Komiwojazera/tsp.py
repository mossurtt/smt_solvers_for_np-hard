import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 tsp.py <filename>")
        return

    filename = sys.argv[1]
    distances = read_input_from_file(filename)

    print(check_tsp(distances))

def read_input_from_file(filename):
    distances = []
    with open(filename, 'r') as file:
        for line in file:
            distances.append([int(x) for x in line.strip().split(',')])

    return distances

def check_tsp(distances):
    n = len(distances)
    
    x = {}
    for i in range(n):
        for j in range(i + 1, n):
            x[i, j] = z3.Int(f'x_{i}_{j}')
    
    solver = z3.Solver()
 
    for i in range(n):
        solver.add(z3.Sum([z3.If(x[i, j] == 1, 1, 0) for j in range(i + 1, n)]) == 1)

    for j in range(1, n):
        solver.add(z3.Sum([z3.If(x[i, j] == 1, 1, 0) for i in range(j)]) == 1)

    for i in range(n):
        for j in range(i + 1, n):
            solver.add(x.get((i, j), 0) == x.get((j, i), 0))

    objective = z3.Sum([distances[i][j] * x[i, j] for i in range(n) for j in range(i + 1, n)])

    solver.add(objective <= 100000)


    smt2_representation = solver.to_smt2()
    file_name = f'tsp_state.smt2'
    with open(file_name, 'w') as file:
        file.write("(set-logic ALL)\n")
        file.write(smt2_representation)  
    file.close()

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        tour = [0]
        current_city = 0
        while len(tour) < n:
            for j in range(1, n):
                if model[x[current_city, j]] == 1:
                    tour.append(j)
                    current_city = j
                    break
        tour.append(0)
        return tour
    else:
        return result
   
if __name__ == '__main__':
    main()



