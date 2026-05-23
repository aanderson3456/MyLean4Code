with open('InfiniteTwos.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
for line in lines:
    if len(line) > 100:
        # We need to wrap it if it's a comment
        if line.lstrip().startswith('-- '):
            # very simple hack: just split at 90 characters
            words = line.split(' ')
            cur = ""
            for w in words:
                if len(cur) + len(w) > 90:
                    new_lines.append(cur + '\n')
                    cur = "-- " + w + " "
                else:
                    cur += w + " "
            if cur:
                new_lines.append(cur.strip() + '\n')
            continue
    new_lines.append(line)

final_lines = []
for i, line in enumerate(new_lines):
    if line.strip() == '' and i > 0 and new_lines[i-1].strip() != '' and i < len(new_lines)-1 and new_lines[i+1].strip() != '':
        # maybe an empty line in a proof
        # Check if the surrounding lines are inside a proof (indented by spaces)
        if new_lines[i-1].startswith('  ') and new_lines[i+1].startswith('  '):
            # Just remove it or comment it
            final_lines.append('  --\n')
            continue
    final_lines.append(line)

with open('InfiniteTwos.lean', 'w') as f:
    f.writelines(final_lines)
