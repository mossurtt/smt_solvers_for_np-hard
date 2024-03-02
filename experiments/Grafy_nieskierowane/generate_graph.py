import igraph as ig

def main():
    for i in range(5, 100, 5):
        for j in range(3, 30, 2):
            g = ig.Graph.Barabasi(i,j)
            g.write_edgelist(f'barabasi_{i}.txt')

    for i in range(100, 1050, 50):
        for j in range(3, 30, 2):
            g = ig.Graph.Barabasi(i, j)
            g.write_edgelist(f'barabasi_{i}.txt')

if __name__ == '__main__':
    main()
