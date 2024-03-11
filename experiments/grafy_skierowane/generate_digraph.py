import igraph as ig
import random

def main():
    for i in range(5, 105, 5):
            g = ig.Graph.Barabasi(i, random.randint(1, 10), directed=True)
            g.write_edgelist(f'barabasi/barabasi_{i}.txt')


if __name__ == '__main__':
    main()
