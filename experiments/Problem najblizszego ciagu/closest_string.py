import sys
import z3 

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 closest_string.py <filename>")
        return

    filename = sys.argv[1]
    check_closest_string(strings)

def check_closest_string(strings):
    
    solver = z3.Solver()


if __name__ == '__main__':
    main()