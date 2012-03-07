// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import YaoGC.*;
import GCParser.*;
import java.util.*;

public abstract class OpCircuitUser extends OpDirections {
  private static Map<String, OpCircuitUser> circuit_ops = new HashMap<String,OpCircuitUser>();
  protected Map<Integer,Circuit> cached_circuits;
  
  public OpCircuitUser( String name ){
    super(name);
    circuit_ops.put( name, this );
    cached_circuits = new HashMap<Integer,Circuit>();
  }
  public static void clear_circuit_cache(){
    for( String s : circuit_ops.keySet() ){
      circuit_ops.get(s).cached_circuits.clear();
    }
  }
  public State execute(State[] operands) throws Exception {
    int id = circuit_id( operands );
    Circuit res = cached_circuits.get( id );
    if( res == null ){
      res = create_circuit( operands );
      res.build();
      cached_circuits.put( id, res );
    }
    return execute( operands, res );
  }
  public abstract Circuit create_circuit( State[] operands ) throws Exception ;
  public abstract int circuit_id( State[] operands );

  public abstract State execute( State[] operands, Circuit c ) throws Exception;
  
}