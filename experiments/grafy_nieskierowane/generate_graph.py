import igraph as ig
import random

def main():
    for i in range(5, 100, 5):
        g1 = ig.Graph.Barabasi(i, random.randint(1, 10))
        g1.write_edgelist(f'barabasi/barabasi_{i}.txt')
    
        g2 = ig.Graph.Erdos_Renyi(n=i, m=i)
        g2.write_edgelist(f'erdos_renyi/erdos_renyi_{i}.txt')
        

if __name__ == '__main__':
    main()
