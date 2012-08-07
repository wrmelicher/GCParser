import sys
import re

if sys.argv[1] == "-":
    file = sys.stdin
else:
    file = open( sys.argv[1], 'r' )

valid = set()

int_re = re.compile("^[0-9]")

for line in file.xreadlines():
    args = line.split()
    if args[0] == ".input" or args[0] == ".include" or args[0] == ".startparty" or args[0] == ".endparty":
        print line.strip()
        continue
    if args[0] == ".output":
        print line.strip()
        valid.add( args[1] )
        continue
    if args[0] in valid:
        valid.remove( args[0] )
        for arg in args[2:]:
            if re.match( int_re, arg ) == None:
                if not arg in valid:
                    print ".remove "+arg
                valid.add( arg )
        print line.strip()
