// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import YaoGC.*;
import GCParser.*;
import java.util.*;

public abstract class OpCircuitUser extends OpDirections {
  private static Map<String, OpCircuitUser> circuit_ops = new HashMap<String,OpCircuitUser>();
  protected Map<Integer,Circuit> cached_circuits;

  private static long[] cir_executed = {0, 0, 0};
  
  public static final int AND = 0;
  public static final int OR  = 1;
  public static final int XOR = 2;
  
  public OpCircuitUser( String name ){
    super(name);
    circuit_ops.put( name, this );
    cached_circuits = new HashMap<Integer,Circuit>();
  }
  public static void clear_circuit_cache(){
    for( String s : circuit_ops.keySet() ){
      circuit_ops.get(s).cached_circuits.clear();
    }
    cir_executed = new long[3];
  }
  public State execute(State[] operands) throws Exception {
    int id = circuit_id( operands );
    Circuit res = cached_circuits.get( id );
    if( res == null ){
      res = create_circuit( operands );
      res.build();
      cached_circuits.put( id, res );
    }
    long[] start = new long[3];
    long[] end = new long[3];
    get_cir_num( start );
    
    State ans = execute( operands, res );
 
    get_cir_num( end );
    for( int i = 0; i < 3; i++ ){
      cir_executed[i] += end[i] - start[i];
    }
    return ans;
  }
  public abstract Circuit create_circuit( State[] operands ) throws Exception ;
  public abstract int circuit_id( State[] operands );

  public abstract State execute( State[] operands, Circuit c ) throws Exception;
  
  public static long get_executed_num( int cir ){
    return cir_executed[cir];
  }

  private void get_cir_num( long[] ans ){
    for( int i = 0; i < 3; i++ ){
      long c;
      switch(i){
      case AND:
	c = AND_2_1.get_num_executed();
	break;
      case OR:
	c = OR_2_1.get_num_executed();
	break;
      case XOR:
	c = XOR_2_1.get_num_executed();
	break;
      default:
	c = 0;
      }
      ans[i] = c;
    }
  }
}