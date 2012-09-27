import sys
import re

if sys.argv[1] == "-":
    file = sys.stdin
else:
    file = open( sys.argv[1], 'r' )

valid = set()

int_re = re.compile("^-?[0-9]")

for line in file.xreadlines():
    args = line.split()
    if len(args) == 0:
        continue
    if args[0] == ".output":
        valid.add( args[1] )
    if args[0][0] == ".":
        print line.strip()
        continue
    if args[0] in valid:
        valid.remove( args[0] )
        for arg in args[2:]:
            if re.match( int_re, arg ) == None:
                if not arg in valid:
                    print ".remove "+arg
                valid.add( arg )
        print line.strip()
