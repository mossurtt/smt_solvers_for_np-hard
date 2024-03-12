def append_weights(folder_path):
    for filename in os.listdir(folder_path):
        if filename.endswith('.txt'):
            filepath = os.path.join(folder_path, filename)
            with open(filepath, 'r') as f:
                lines = f.readlines()
            with open(filepath, 'w') as f:
                for line in lines:
                    s, t = map(int, line.strip().split())
                    w = random.randint(1, 100)
                    f.write(f'{s} {t} {w}\n')

