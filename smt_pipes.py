import subprocess
import sys

smt_cmd = "/home/william/Documents/garbled/mathsat-5.2.1-linux-x86/bin/mathsat"

python_proc = subprocess.Popen(["python","translate_smt.py",sys.argv[1]], 
                               stdout=subprocess.PIPE,
                               stdin=subprocess.PIPE)

smt_proc = subprocess.Popen([smt_cmd], stdin=python_proc.stdout, stdout=python_proc.stdin)

smt_proc.wait()
python_proc.wait()
