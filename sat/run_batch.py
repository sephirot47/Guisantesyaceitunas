import subprocess
import time
import os

def run(cmd,file):
    f = open('inputs/' + file)
    p = subprocess.Popen(cmd, stdin=f, stdout=subprocess.PIPE)
    start = time.time()
    output = p.communicate()[0]
    end = time.time()
    elapsed = end-start;
    for line in output.splitlines():
	print(line)
    return elapsed

for file in sorted(os.listdir('inputs/')):
    if file.startswith('vars-'):
	oscarSAT_time = run(['./sat'],file)
	picosat_time = run(['picosat','-n'],file)
	
	print "mine: " + str(round(oscarSAT_time,3)) + ", pico: " + str(round(picosat_time,3))
