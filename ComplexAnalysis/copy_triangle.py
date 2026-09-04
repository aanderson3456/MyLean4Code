with open('/Users/austinanderson/AnalysTSP/WeierstrassLimitR2.lean', 'r') as f:
    lines = f.readlines()

out = []
for i in range(150, 310):
    out.append(lines[i])

with open('scratch_triangle.lean', 'w') as f:
    f.writelines(out)
