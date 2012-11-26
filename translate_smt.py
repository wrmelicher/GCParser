import sys
import re

if sys.argv[1] == "-":
    file = sys.stdin
else:
    file = open( sys.argv[1], 'r' )

vars = set()
int_re = re.compile("^-?([0-9])+:([0-9])+$")

def introduce_var(name):
    global vars
    vars.add(name)
    return "(declare-fun "+name+" () Int)"

def arg_to_smt(arg):
    match = int_re.match(arg)
    if match == None:
        if arg not in vars:
            print introduce_var(arg)
        return arg
    return int(match.group(1))

def assert_smt(statement):
    return "(assert "+statement+")"

def assign_smt(statement,out):
    return "(= "+out+" "+statement+")"

# still need bitwise operations
ops_map = {
    "add" : "+",   "sub" : "-",   "ltes" : "<=", "lteu" : "<=",
    "gtes" : ">=", "gteu" : ">=", "lts" : "<",   "ltu" : "<",
    "gts" : ">",   "gtu" : ">",   "negate" : "-" }

def map_ops(op, args):
    retval = "("+ops_map[op]
    for i in args:
        retval += " "+arg_to_smt(i)
    return retval + ")"

def sp_chose(out,cond,arg1,arg2):
    return "(if "+cond+" "+arg_to_smt(arg1)+" "+arg_to_smt(arg2)+")"

def sp_shiftl(args):
    arg1val = arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftl must shift by constant amount")
    return "(* "+arg_to_smt(args[0])+" "+str(2**arg1val)+")"

def sp_shiftr(args):
    arg1val = const_to_int(args[1])
    if arg1val == None:
        raise Error("shiftr must shift by constant amount")
    return "(div "+arg_to_smt(args[0])+" "+str(2**arg1val)+")"

# bits_special = {
#             "concat" : sp_concat, 
#             "concatls" : sp_concatls, 
#             "select" : sp_select, 
#             "sextend" : sp_sextend,
#             "trunc" : sp_trunc,
#             "decode" : sp_decode, 
#             "zextend" : sp_zextend }

special = { "shiftl" : sp_shiftl,
            "shiftr" : sp_shiftr }

def map_il_to_smt(op,args,out):
    print introduce_var(out)
    if op == "chose":
        op_clause = sp_chose(out,args[0],args[1],args[2])
        print assert_clause(op_clause)
        return
    if op in ops_map:
        op_clause = map_ops(op,args)
    elif op in special:
        op_clause = special[op](args)
    assign_clause = assign_smt(op_clause,out)
    assert_clause = assert_smt(assign_clause)
    print assert_clause

def assert_between(name, lower, upper):
    return assert_smt( "(and (>= "+name+" "+lower+") (< "+name+" "+upper+"))" )

def map_dot_to_smt(dot_op, args):
    if dot_op == ".input":
        print introduce_var(args[0])
        bit_width = int(args[2])
        print assert_between(args[0],str(0),str(2**bit_width))
    return ""

def header():
    return """(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(define-fun if ((cond Bool) (a Int) (b Int) (ans Int)) Bool
 (and (or (not cond) (= ans a)) (or cond (= ans b))))"""

def footer():
    return """(check-sat)
(exit)"""

print header()
for line in file.xreadlines():
    args = line.split()
    if len(args) == 0:
        continue
    if args[0][0] == ".":
        print map_dot_to_smt( args[0], args[1:] )
    else:
        print map_il_to_smt( args[1], args[2:], args[0] )
print footer()
