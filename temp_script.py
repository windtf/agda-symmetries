import re
import json

agda_content = open('types25pp.agda').read()

files_to_process = [
    'papers/types25pp/universal-algebra.tex',
    'papers/types25pp/free-monoids.tex',
    'papers/types25pp/free-commutative-monoids.tex',
    'papers/types25pp/combinatorics.tex',
    'papers/types25pp/sorting.tex',
]

def find_next(alink_type, start_index):
    for i in range(start_index+1, 100):
        if f"{alink_type}-{i} :" in agda_content:
            return i
    raise ValueError(f"No available id for alink type '{alink_type}' starting from {start_index}")

i = 0
for file_path in files_to_process:
    content = open(file_path).read()
    # Revised regex to capture all three arguments as groups
    matches = re.findall(r'\\alink{([^}]+)}.+{([^}]+)}', content)
    for alink_type, alink_label in matches:
        i = find_next(alink_type, i)
        print(f"Found alink in {file_path}: type='{alink_type}', label='{alink_label}', assigned id={i}")