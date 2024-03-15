import os
import random
import sys

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 generate_wgraph.py <folder_path>")
        return

    folder_path = sys.argv[1]
    append_weights(folder_path)

def append_weights(folder_path):
    for filename in os.listdir(folder_path):
        if filename.endswith('.txt'):
            filepath = os.path.join(folder_path, filename)
            with open(filepath, 'r') as f:
                lines = f.readlines()
            with open(filepath, 'w') as f:
                for line in lines:
                    s, t = map(int, line.strip().split())
                    w = random.randint(10, 20)
                    f.write(f'{s} {t} {w}\n')


if __name__ == '__main__':
    main()
