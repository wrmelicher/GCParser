import sys
import re
import subprocess


log_file = open( "translate_smt.log", 'w' )

smt_cmd = "/home/william/Documents/garbled/mathsat-5.2.1-linux-x86/bin/mathsat"
smt_proc = subprocess.Popen([smt_cmd], stdin=subprocess.PIPE, stdout=subprocess.PIPE)

vars = {}
int_re = re.compile("^-?([0-9])+(:([0-9]+))?$")
find_ranges = {}

def smt_proc_write( val ):
    log_file.write(val)
    smt_proc.stdin.write(val)

def introduce_var(name,rng):
    global vars
    vars[name] = rng
    smt_proc_write("(declare-fun "+name+" () (_ BitVec "+str(rng)+"))\n")

def arg_to_smt(arg):
    match = int_re.match(arg)
    if match == None:
        return (arg,vars[arg])
    size = int(match.group(3))
    return ( "(nat2bv["+str(size)+"] "+match.group(1)+")", size )

def const_bv_literal( num, size ):
    raw = bin(num)[2:]
    raw = "0"*(size-len(raw))
    return "#b"+raw

def const_arg_to_smt( arg ):
    match = int_re.match(arg)
    size = int(match.group(3))
    return ( match.group(1), size )

def assert_smt(statement):
    return "(assert "+statement+")\n"

def assign_smt(statement,out):
    return "(= "+out+" "+statement+")"

# still need bitwise operations
same_len_ops = {
   "add" : "bvadd",    
   "sub" : "bvadd", 
   "negate" : "bvneg", 
   "chose" : "ite",
   "and" : "bvand",
   "or" : "bvor",
   "xor" : "bvxor" }

one_bit_ops = {
    "ltes" : (True, True, True),
    "lteu" : (False, True, True),
    "gtes" : (True, False, True), 
    "gteu" : (False, False, True), 
    "lts" : (True, True, False),
    "ltu" : (False, True, False),
    "gts" : (True, False, False),   
    "gtu" : (False, False, False) }

ops_set = same_len_ops.viewkeys() | one_bit_ops.viewkeys()

def comparison(a, b, is_signed, is_lt, is_eq):
    ret = "(bvult "
    arga = arg_to_smt(a)
    argb = arg_to_smt(b)
    if is_lt:
        if is_eq:
            ret += argb[0] + " " + arga[0] + ")"
            ret = "(not "+ret+")"
        else:
            ret += arga[0] + " " + argb[0] + ")"
    else:
        if is_eq:
            ret += argb[0] + " " + arga[0] + ")"
        else:
            ret += arga[0] + " " + argb[0] + ")"
            ret = "(not "+ret+")"
    return ret

def map_ops(op, args):
    retval = "("
    arg_size = 0
    if op in same_len_ops:
        retval += same_len_ops[op]
    else:
        compvals = one_bit_ops[op]
        retval = comparison( args[0], args[1],
                             compvals[0],
                             compvals[1],
                             compvals[2] )
        arg_size = 1
        return ( retval, arg_size )
    for i in xrange(len(args)):
        vals = arg_to_smt(args[i])
        vals_bv_form = vals[0]
        if i == 0 and op == "chose":
            retval += " (= "+vals_bv_form+" #b1)"
        else:
            retval += " "+vals_bv_form
        if op in same_len_ops:
            arg_size = vals[1]
    return ( retval + ")", arg_size )

def sp_shiftl(args):
    arg1val = const_arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftl must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    state = "(bvshl "+arg2val[0]+" "+const_bv_literal(arg1val[0],arg1val[1])+")"
    return (state, arg1val[0] + arg2val[1] )

def sp_shiftr(args):
    arg1val = const_arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftr must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    state = "(bvshr "+arg2val[0]+" "+const_bv_literal(arg1val[0],arg1val[1])+")"
    return (state, arg2val[1] - arg1val[0] )

# bits_special = {
#             "concatls" : sp_concatls, 
#             "decode" : sp_decode, 

def sp_concat(args):
    ret = ""
    bit_size_accum = 0
    num_close = 0
    for i in xrange( len(args) ):
        val = arg_to_smt( args[i] )
        if i != len(args)-1:
            ret += "(concat "+val[0]+" "
            num_close += 1
        else:
            ret += val[0]
        bit_size_accum += val[1]
    ret += ")"*num_close
    return ( ret, bit_size_accum )

def sp_select(args):
    ret = "((_ extract "
    from_arg = const_arg_to_smt(args[1])
    to_arg = const_arg_to_smt( args[2] )
    base_arg = arg_to_smt( args[0] )
    ret += str(from_arg[0]) + " " + str(to_arg[0]) + ") "
    ret += base_arg[0] + ")"
    return ( ret, to_arg[0] - from_arg[0] )

def sp_sextend( args ):
    # TODO: handle signed arguments
    to_arg = const_arg_to_smt( args[1] )
    base_arg = arg_to_smt( args[0] )
    ret = "(concat "+base_arg[0]+" #b"+("0"*(to_arg[0]-base_arg[1]))+")"
    return ( ret, to_arg[0] )

def sp_trunc( args ):
    return sp_sextend( [ args[0], "0:1" ] )

special = { "shiftl" : sp_shiftl,
            "shiftr" : sp_shiftr,
            "concat" : sp_concat,
            "select" : sp_select,
            "sextend" : sp_sextend,
            "trunc" : sp_trunc,
            "zextend" : sp_sextend }

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
        assign_clause = "(ite "+assign_clause+" #b1 #b0)"
    assign_clause = assign_smt(assign_clause,out)
    assert_clause = assert_smt(assign_clause)
    smt_proc_write( assert_clause ) 

def assert_less(name, upper):
    return assert_smt( "(ult "+name+" "+const_bv_literal(upper,vars[name])+")" )

def map_dot_to_smt(dot_op, args):
    global vars
    if dot_op == ".input":
        bit_width = int(args[2])
        introduce_var(args[0], bit_width )
        # smt_proc_write( assert_less(args[0],2**bit_width) )
    if dot_op == ".remove":
        vars.pop( args[1] )

def header():
    return """(set-option :global-decls true)
(set-info :smt-lib-version 2.0)
(set-logic QF_BV)
"""


def make_guess(arg,lessthan):
    smt_proc_write( "(push 1)\n" )
    smt_proc_write( assert_smt("(bvult "+str(lessthan)+" "+arg+")") )
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

if __name__=="__main__":
    smt_proc_write( header() )
    file = open( sys.argv[1], 'r' )
    for line in file.xreadlines():
        args = line.split()
        if len(args) == 0:
            continue
        if args[0][0] == ".":
            map_dot_to_smt( args[0], args[1:] )
        else:
            map_il_to_smt( args[1], args[2:], args[0] )
    for i in find_ranges:
        rng = search_range( i, find_ranges[i] )
        log_file.write( i +" "+str( rng )+"\n" )
        
    smt_proc_write( "(exit)\n" )
    smt_proc.wait()
    log_file.close()

