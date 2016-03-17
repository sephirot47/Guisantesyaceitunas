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
    if file.startswith('vars-250'):
	print file
<<<<<<< HEAD
	print '========================'
	
	print 'Running SAT...'
	oscarSAT_time = run(['./sat'],file)
	print '***'
	print 'Running picosat...'
	picosat_time = run(['picosat','-n'],file)
	print '***'
	
	print 'SAT time: ' + str(round(oscarSAT_time,3))
	print 'picosat time: ' + str(round(picosat_time,3))
	print 'Comparison: ' + str(round(oscarSAT_time/picosat_time,2)) + '\n'
=======
#	print '========================'
	
	print 'Running SAT...'
	oscarSAT_time = run(['./sat'],file)
#	print '***'
	print 'Running picosat...'
	picosat_time = run(['picosat','-n'],file)
#	print '***'
	
	#print 'SAT time: ' + str(round(oscarSAT_time,3))
	#print 'picosat time: ' + str(round(picosat_time,3))
	print ': ' + str(round(oscarSAT_time/picosat_time,2)) + '\n'
>>>>>>> new_branch_name
