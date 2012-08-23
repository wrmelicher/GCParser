import sys
import re

if sys.argv[1] == "-":
    file = sys.stdin
else:
    file = open( sys.argv[1], 'r' )

int_re = re.compile("^[0-9]")

var_map = {}
party_mode = 0

could_be_local = {}
local_lines = { 1 : "", 2: "" }

neutral = {}

linenum = 0

for line in file.xreadlines():
    args = line.split()
    linenum += 1
    if len( args ) == 0:
        continue
    if args[0] == ".input":
        var_map[ args[1] ] = int( args[2] )
    elif args[0] == ".remove":
        del var_map[ args[1] ]
    elif args[0][0] == ".":
        continue
    else:
        party_arg = []
        for arg in args[2:]:
            arg_party = 0
            if re.match(int_re, arg) != None: 
                arg_party = 0
            elif not arg in var_map:
                raise Exception("cannot identify "+arg+" on line "+str(linenum) )
            elif var_map[arg] == 0:
                neutral[arg] = line
            
            party_arg.append( arg_party )
        if party_arg > 0 and party_arg != party_mode:
            local_lines[party_arg] += line
            could_be_local[ args[0] ] = party_arg
        var_map[ args[0] ] = party_arg


in_party = False
printed_locals = False
file.seek(0)
for line in file.xreadlines():
    args = line.split()
    if args[0] == ".startparty":
        in_party = True
    elif args[0] == ".endparty":
        in_party = False
    elif args[0] == ".remove" and args[1] in could_be_local:
        continue
    elif not printed_locals and not in_party and args[0][0] != ".":
        print ".startparty 1"
        print local_lines[1],
        print ".endparty 1"
        print ".startparty 2"
        print local_lines[2],
        print ".endparty 2"
        printed_locals = True
    if not args[0] in could_be_local:
        print line.strip()
