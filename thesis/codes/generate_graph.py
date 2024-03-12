def generate_graph():
    for i in range(5, 105, 5):
        g1 = ig.Graph.Barabasi(i, random.randint(1, 10))
        g1.write_edgelist(f'barabasi/barabasi_{i}.txt')
    
        g2 = ig.Graph.Erdos_Renyi(n = i, m = 2 * i - random.randint(1, (i // 2))
        g2.write_edgelist(f'erdos_renyi/erdos_renyi_{i}.txt')
