import sys
import re

if sys.argv[1] == "-":
    file = sys.stdin
else:
    file = open( sys.argv[1], 'r' )

int_re = re.compile("^[0-9]")
spec_re = re.compile("^\\.")

vars = {}
party_mode = 0

could_be_local = {}
local_lines = { 1 : "", 2: "" }

linenum = 0

for line in file.xreadlines():
    args = line.split()
    linenum += 1
    if args[0] == ".input":
        vars[ args[1] ] = int( args[2] )
    elif args[0] == ".remove":
        del vars[ args[1] ]
    elif args[0] == ".startparty":
        party_mode = int( args[1] )
    elif args[0] == ".endparty":
        party_mode = 0
    elif args[0] == ".remove" and args[1] in could_be_local:
        local_lines[ could_be_local[args[1] ] ] += line
    elif args[0][0] == ".":
        continue
    else:
        party_arg = 0
        for arg in args[2:]:
            if re.match(int_re, arg) != None: 
                continue
            if not arg in vars:
                raise Exception("cannot identify "+arg+" on line "+str(linenum) )
            if vars[arg] != party_mode and party_mode != 0:
                raise Exception("cannot calculate "+args[0]+" when it depends on "+arg+" on line "+str(linenum) )
            if party_arg == 0:
                party_arg = vars[arg]
            if party_arg != vars[arg]:
                party_arg = -1;
        if party_arg > 0 and party_arg != party_mode:
            local_lines[party_arg] += line
            could_be_local[ args[0] ] = party_arg
        vars[ args[0] ] = party_arg


in_party = False
printed_locals = False
file.seek(0)
for line in file.xreadlines():
    args = line.split()
    if args[0] == ".startparty":
        in_party = True
    elif args[0] == ".endparty":
        in_party = False
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
