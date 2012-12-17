import sys
import re
import subprocess

file = open( sys.argv[1], 'r' )
log_file = open( "translate_smt.log", 'w' )

smt_cmd = "/home/william/Documents/garbled/mathsat-5.2.1-linux-x86/bin/mathsat"
smt_proc = subprocess.Popen([smt_cmd], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

vars = {}
int_re = re.compile("^-?([0-9])+(:([0-9])+)?$")
find_ranges = {}

def smt_proc_write( val ):
    log_file.write(val)
    smt_proc.stdin.write(val)

def introduce_var(name,rng):
    global vars
    vars[name] = rng
    smt_proc_write("(declare-fun "+name+" () Int)\n")

def arg_to_smt(arg):
    match = int_re.match(arg)
    if match == None:
        return (arg,vars[arg])
    return ( int(match.group(1)), int(match.group(2)) )

def assert_smt(statement):
    return "(assert "+statement+")\n"

def assign_smt(statement,out):
    return "(= "+out+" "+statement+")"

# still need bitwise operations
same_len_ops = {
   "add" : "+",    "sub" : "-", 
   "negate" : "-", "chose" : "ite" }
one_bit_ops = {
     "ltes" : "<=", "lteu" : "<=",
    "gtes" : ">=", "gteu" : ">=", "lts" : "<",   "ltu" : "<",
    "gts" : ">",   "gtu" : ">" }
ops_set = same_len_ops.viewkeys() | one_bit_ops.viewkeys()

def map_ops(op, args):
    retval = "("
    arg_size = 0
    if op in same_len_ops:
        retval += same_len_ops[op]
    else:
        retval += one_bit_ops[op]
        arg_size = 1
    for i in xrange(len(args)):
        vals = arg_to_smt(args[i])
        if i == 0 and op == "chose":
            retval += " (= "+vals[0]+" 1)"
        else:
            retval += " "+vals[0]
        if op in same_len_ops:
            arg_size = vals[1]
    return ( retval + ")", arg_size )

def sp_shiftl(args):
    arg1val = arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftl must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    state = "(* "+arg2val[0]+" "+str(2**arg1val[0])+")"
    return (state, arg1val[0] + arg2val[1] )

def sp_shiftr(args):
    arg1val = const_to_int(args[1])
    if arg1val == None:
        raise Error("shiftr must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    state = "(div "+arg2val[0]+" "+str(2**arg1val[0])+")"
    return (state, arg2val[1] - arg1val[0] )

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
    if op in same_len_ops:
        op_clause = map_ops(op,args)
    elif op in one_bit_ops:
        op_clause = map_ops(op,args)
    elif op in special:
        op_clause = special[op](args)
    introduce_var(out, op_clause[1] )
    if op == "chose":
        find_ranges[out] = op_clause[1]
    assign_clause = op_clause[0]
    if op in one_bit_ops:
        assign_clause = "(ite "+assign_clause+" 1 0)"
    assign_clause = assign_smt(assign_clause,out)
    assert_clause = assert_smt(assign_clause)
    smt_proc_write( assert_clause ) 

def assert_between(name, lower, upper):
    return assert_smt( "(and (>= "+name+" "+lower+") (< "+name+" "+upper+"))" )

def map_dot_to_smt(dot_op, args):
    global vars
    if dot_op == ".input":
        bit_width = int(args[2])
        introduce_var(args[0], 2**bit_width )
        smt_proc_write( assert_between(args[0],str(0),str(2**bit_width)) )
    if dot_op == ".remove":
        vars.pop( args[1] )

def header():
    return """(set-option :global-decls true)
(set-info :smt-lib-version 2.0)
"""

smt_proc_write( header() )
for line in file.xreadlines():
    args = line.split()
    if len(args) == 0:
        continue
    if args[0][0] == ".":
        map_dot_to_smt( args[0], args[1:] )
    else:
        map_il_to_smt( args[1], args[2:], args[0] )

def make_guess(arg,lessthan):
    smt_proc_write( "(push 1)" )
    smt_proc_write( assert_smt("(>= "+arg+" "+str(lessthan)+")") )
    smt_proc_write("(check-sat)\n")
    line = smt_proc.stdout.readline().strip()
    log_file.write( "-> "+line+"\n" )
    if line == "sat":
        smt_proc_write( "(pop 1)\n" ) 
        return False
    elif line == "" or line == "unsat":
        return True
    else:
        raise Exception("SMT lib exception: "+line)

def search_range(var,end):
    start = 0
    max_val = end
    while max_val > start and not make_guess(var,2**start):
        start = start + 1
    return start

for i in find_ranges:
    rng = search_range( i, find_ranges[i] )
    log_file.write( i +" "+str( rng )+"\n" )

smt_proc_write( "(exit)\n" )

smt_proc.wait()

log_file.close()
