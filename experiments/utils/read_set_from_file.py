def read_set_from_file(filename):
	with open(filename, 'r') as file:
		data = file.read().strip()
		input_set = list(map(int, data.split()))
	return input_set
