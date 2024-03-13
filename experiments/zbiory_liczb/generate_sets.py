import random

def main():
    generate_sets()

def generate_sets():
    for n in range(5, 56, 5):
        int_set = set(random.sample(range(1, n * 10), n))

        filename = f'{n}.txt'
        with open(filename, 'w') as file:
            file.write(' '.join(map(str, int_set)))

if __name__ == "__main__":
    main()