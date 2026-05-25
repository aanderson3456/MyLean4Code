with open('VTlean/NumOsNumIs.lean', 'r') as f:
    content = f.read()

vector_part = content[content.find('namespace Vector'):]

header = """import VTlean.B
import VTlean.InsDel
import VTlean.NumOsNumIs

"""

with open('scratch_vector.lean', 'w') as f:
    f.write(header + vector_part)
