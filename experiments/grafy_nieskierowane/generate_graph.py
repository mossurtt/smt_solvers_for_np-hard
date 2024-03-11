import igraph as ig
import random

def main():
    for i in range(5, 100, 5):
            g = ig.Graph.Barabasi(i, random.randint(1, 10))
            g.write_edgelist(f'barabasi_{i}.txt')

    for i in range(100, 1050, 50):
        g = ig.Graph.Barabasi(i, random.randint(10, 50))
        g.write_edgelist(f'barabasi_{i}.txt')
        

if __name__ == '__main__':
    main()
