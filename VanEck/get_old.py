import subprocess
out = subprocess.check_output(['git', 'show', 'HEAD:MirskyNewman.lean']).decode('utf-8')
print(out)
