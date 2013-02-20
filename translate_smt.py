import sys
import re
import subprocess
import os
import os.path

smt_cmd = os.getenv( "SMT_LOCATION" ) # find external smt solver

# variable information
vars = {}
new_vars = {}
# reg exp for constant arguments
int_re = re.compile("^-?([0-9]+)(:([0-9]+))?$")

# operations whose results are the same size
# as their operands
same_len_ops = {
   "add" : "bvadd",    
   "sub" : "bvadd",
   "negate" : "bvneg",
   "chose" : "ite", # exception to above rule
   "ite" : "ite", # exception to above rule
   "and" : "bvand",
   "or" : "bvor",
   "xor" : "bvxor",
   "not" : "bvnot" }

# operations whose operands are the same size
# but the result is always one bit wide
# ( is_signed, is_lt, is_eq_comp, is_equ_fun )
one_bit_ops = {
    "ltes" : (True, True, True, False),
    "lteu" : (False, True, True, False),
    "gtes" : (True, False, True, False),
    "gteu" : (False, False, True, False),
    "lts" :  (True, True, False, False),
    "ltu" :  (False, True, False, False),
    "gts" :  (True, False, False, False),
    "gtu" :  (False, False, False, False),
    "equ" :  (False, False, False, True), 
    "nequ" : (False, False, True, True) }

############# utility methods
def smt_proc_write( val ):
    log_file.write(val)
    smt_proc.stdin.write(val)

def introduce_var(name,rng):
    global vars
    vars[name] = rng
    smt_proc_write("(declare-fun "+name+" () (_ BitVec "+str(rng)+"))\n")

def const_to_bv( match ):
    mag = int(match.group(1))
    size = match.group(3)
    if size == None:
        size = len(bin(mag))-2
    return ( const_bv_literal(mag,int(size)), int(size) )

def arg_to_smt(arg):
    match = int_re.match(arg)
    if match == None:
        return (arg,vars[arg])
    return const_to_bv( match )

def const_bv_literal( num, size = -1 ):
    raw = bin(num)[2:]
    if size == -1:
        size = len(raw)
    raw = ( "0"*(size-len(raw) ) ) + raw
    return "#b"+raw

def const_arg_to_smt( arg ):
    match = int_re.match(arg)
    mag = int( match.group(1) )
    return mag

def assert_smt(statement):
    return "(assert "+statement+")\n"

def assign_smt(statement,out):
    return "(= "+out+" "+statement+")"

########### end utility methods

def comparison(a, b, params):
    ( is_signed, is_lt, is_eq_comp, is_equ_fun ) = params
    ret = "(bvult "
    arga = arg_to_smt(a)
    argb = arg_to_smt(b)
    if is_equ_fun:
        ret = "(= "+arga[0]+" "+argb[0]+")"
        if not is_eq_comp:
            ret = "(not "+ret+")"
        return ret
    if is_lt:
        if is_eq_comp:
            ret += argb[0] + " " + arga[0] + ")"
            ret = "(not "+ret+")"
        else:
            ret += arga[0] + " " + argb[0] + ")"
    else:
        if is_eq_comp:
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
    elif op in one_bit_ops:
        compvals = one_bit_ops[op]
        retval = comparison( args[0], args[1], compvals )
        arg_size = 1
        return ( retval, arg_size )
    for i in xrange(len(args)):
        vals = arg_to_smt(args[i])
        vals_bv_form = vals[0]
        if i == 0 and (op == "chose" or op == "ite"):
            retval += " (= "+vals_bv_form+" #b0)"
        elif i == 1 and op == "sub":
            retval += " (bvneg "+vals_bv_form+")"
        else:
            retval += " "+vals_bv_form
        if op in same_len_ops:
            arg_size = max(vals[1],arg_size)
    return ( retval + ")", arg_size )

def sp_shiftl(args):
    arg1val = const_arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftl must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    zeros = "0"*arg1val
    state = "(bvshl (concat #b"+zeros+" "+str(arg2val[0])+") "+const_bv_literal(arg1val,arg2val[1]+arg1val)+")"
    return (state, arg1val + arg2val[1])

def sp_shiftr(args):
    arg1val = const_arg_to_smt(args[1])
    if arg1val == None:
        raise Error("shiftr must shift by constant amount")
    arg2val = arg_to_smt(args[0])
    state = "((_ extract "+str(arg2val[1]-arg1val-1)+" 0) (bvlshr "+str(arg2val[0])+" "+const_bv_literal(arg1val,arg2val[1])+"))"
    return (state, arg2val[1] - arg1val)

def sp_concatls(args):
    first = arg_to_smt(args[0])
    ret = first[0]
    bit_size_accum = first[1]
    for i in xrange(1, len(args) ):
        val = arg_to_smt( args[i] )
        ret = "(concat "+ret+" "+val[0]+")"
        bit_size_accum += val[1]
    return ( ret, bit_size_accum )

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
    ret += str(to_arg-1) + " " + str(from_arg) + ") "
    ret += base_arg[0] + ")"
    return ( ret, to_arg - from_arg )

def sp_sextend( args ):
    to_arg = const_arg_to_smt( args[1] )
    base_arg = arg_to_smt( args[0] )
    ret = "(concat (ite (= ((_ extract " + str(base_arg[1]-1) + " "+str(base_arg[1]-1)+") "+base_arg[0]+") #b0) #b"+("0"*(to_arg-base_arg[1]))+" #b"+("1"*(to_arg-base_arg[1]))+") "+base_arg[0]+")"
    return ( ret, to_arg )

def sp_zextend( args ):
    # TODO: handle signed arguments
    to_arg = const_arg_to_smt( args[1] )
    base_arg = arg_to_smt( args[0] )
    ret = "(concat #b"+("0"*(to_arg-base_arg[1]))+" "+base_arg[0]+")"
    return ( ret, to_arg )

def sp_select_out(args, out):
    size = prev_arg_size(args[0])
    from_arg = const_arg_to_smt(args[1])
    to_arg = const_arg_to_smt(args[2])
    write = out + " select "
    if size <= from_arg:
        out_file.write( out + " set 0:1\n")
        return 1
    elif size < to_arg:
        write += " ".join( args[:2] + [ str(size) ] )
        out_file.write(write+"\n")
        return size - from_arg
    else:
        write += " ".join( args )
        out_file.write(write+"\n")
        return to_arg - from_arg

# operations which require special consideration
# "operation" : ( smt_translation_fun, output_translation_fun )
# TODO: must support decode operation
special = { "shiftl" : (sp_shiftl, None),
            "shiftr" : (sp_shiftr, None),
            "concat" : (sp_concat, None),
            "select" : (sp_select, sp_select_out),
            "sextend" : (sp_sextend, None),
            "trunc" : (lambda arg:
                           sp_select( [ arg[0], "0:1", arg[1] ] ),
                       lambda arg, out:
                           sp_select_out( [arg[0], "0:1", arg[1] ], out)),
            "zextend" : (sp_zextend, None),
            "concatls" : (sp_concatls, None) }

def prev_arg_size(arg):
    if arg in new_vars:
        return new_vars[arg]
    else:
        return arg_to_smt(arg)[1]

counter = 0
    
def temp_var(arg):
    global counter
    counter += 1
    if int_re.match(arg) == None:
        return arg+"_t"+str(counter)
    else:
        return "t_t_"+str(counter)

def out_file_name(arg):
    if prev_arg_size(arg) == 0:
        return "0:1"
    else:
        return arg

def out_file_bit_align(arg,size):
    prev_size = prev_arg_size(arg)
    temp_name = temp_var(arg)
    if prev_size == 0:
        out_file.write(temp_name+" zextend 0:1 "+str(size)+"\n")
        return temp_name
    elif prev_size < size:
        out_file.write(temp_name+" zextend "+arg+" "+str(size)+"\n")
        return temp_name
    elif prev_size > size:
        out_file.write(temp_name+" trunc "+arg+" "+str(size)+"\n")
        return temp_name
    return arg

def out_file_operation(op, args, out):
    if op in special:
        if special[op][1] == None:
            out_file.write(" ".join( [out,op] +
                                     map(lambda x:
                                             out_file_name(x), args) )+"\n")
            new_vars[out] = special[op][0](args)[1]
        else:
            new_vars[out] = special[op][1](args,out)
    else:
        if op in same_len_ops:
            size = vars[out]
        elif op in one_bit_ops:
            size = max( map( prev_arg_size, args) )
        if op == "ite" or op == "chose":
            args_actual = [out_file_name(args[0])] + map( lambda x: out_file_bit_align(x,size), args[1:] )
        else:
            args_actual = map( lambda x: out_file_bit_align(x,size), args )
        out_file.write( " ".join( [out,op] + args_actual ) +"\n" )
        new_vars[out] = size

def map_il_to_smt(op,args,out):
    # prepare smt assertions
    if op in same_len_ops:
        op_clause = map_ops(op,args)
    elif op in one_bit_ops:
        op_clause = map_ops(op,args)
    elif op in special:
        op_clause = special[op][0](args)
    else:
        log_file.write("Error: unknown function "+op+"\n")
        raise Exception("unknown function "+op)
    introduce_var(out, op_clause[1] )
    assign_clause = op_clause[0]
    if op in one_bit_ops:
        assign_clause = "(ite "+assign_clause+" #b1 #b0)"
    # send assertion to smt solver
    assign_clause = assign_smt(assign_clause,out)
    assert_clause = assert_smt(assign_clause)
    smt_proc_write( assert_clause )
    # query smt solver for size of variable
    rng = search_range( out, op_clause[1] )
    # write answer to log
    if rng < op_clause[1]:
        log_file.write( out + " " + str(rng) + "\n" )
    new_vars[out] = rng
    if rng != 0:
        # write new variable to output file
        out_file_operation(op, args, out)

def map_dot_to_smt(dot_op, args):
    if dot_op == ".input":
        bit_width = int(args[2])
        introduce_var(args[0], bit_width )
    if dot_op == ".output":
        args[0] = out_file_name(args[0])
    out_file.write( dot_op + " " + ( " ".join(args) ) + "\n" )
    # if dot_op == ".remove":
    #     del vars[args[0]]


# (set-logic QF_BV)
def header():
    return """(set-info :smt-lib-version 2.0)
"""

def make_guess(arg,lessthan):
    smt_proc_write( "(push 1)\n" )
    smt_proc_write( assert_smt("(not (bvult "+arg+" "+const_bv_literal(2**lessthan,vars[arg])+"))") )
    smt_proc_write("(check-sat)\n")
    line = smt_proc.stdout.readline().strip()
    log_file.write( "-> "+line+"\n" )
    if line == "sat":
        smt_proc_write( "(pop 1)\n" )
        return False
    elif line == "" or line == "unsat":
        smt_proc_write( "(pop 1)\n" )
        return True
    else:
        raise Exception("SMT lib exception: "+line)

def search_range(var,end):
    imin = 0
    imax = end
    while imin < imax:
        imid = (imax+imin)/2
        if not make_guess( var, imid ):
            imin = imid + 1
        else:
            imax = imid
    return imin

if __name__=="__main__":
    # open sub process to smt solver
    smt_proc = subprocess.Popen([smt_cmd], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    if len(sys.argv) < 2:
        print "Error"
        print "Usage: "
        print "translate_smt.py [Input File]"
    out_file = open( os.path.splitext( sys.argv[1] )[0]+".smt", 'w' )
    log_file = open( "translate_smt.log", 'w' )
    smt_proc_write( header() )
    file = open( sys.argv[1], 'r' )
    counter = 0
    for line in file.xreadlines():
        counter += 1
        args = line.split()
        try:
            if len(args) == 0:
                continue
            if args[0][0] == ".":
                map_dot_to_smt( args[0], args[1:] )
            else:
                map_il_to_smt( args[1], args[2:], args[0] )
        except:
            print "Error on line "+str(counter)
            raise
    smt_proc_write( "(exit)\n" )
    smt_proc.wait()
    log_file.close()
