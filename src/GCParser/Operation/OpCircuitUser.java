// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import YaoGC.*;
import GCParser.*;
import java.util.*;

public abstract class OpCircuitUser extends OpDirections {
  private static Map<String, OpCircuitUser> circuit_ops = new HashMap<String,OpCircuitUser>();
  protected Map<Integer,Circuit> cached_circuits;

  private static long[] cir_executed = {0, 0, 0};
  private static long[] local_cir_executed = {0, 0, 0};

  private static Stack< ArrayList<Long> > active_counter = new Stack< ArrayList<Long> >();
  private static Map<String, ArrayList<Long> > profile_map =
    new HashMap<String, ArrayList<Long> >();

  private static boolean local_eval = true;
  public static void doneWithLocalComp(){
    local_eval = false;
  }
  public static void setActiveCounter( String name ){
    if( name.equals("") ){
      active_counter.pop();
      return;
    }
    if( profile_map.containsKey(name) ){
      active_counter.push( profile_map.get(name) );
    } else {
      ArrayList<Long> toadd = new ArrayList<Long>(3);
      active_counter.push(toadd);
      toadd.add(0L);
      toadd.add(0L);
      toadd.add(0L);
      profile_map.put(name,toadd);
    }
  }
  
  public static final int AND = 0;
  public static final int OR  = 1;
  public static final int XOR = 2;
  
  private static boolean profile_count = SimpleCircuit_2_1.profile_count;
  
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
    if( res == null || SimpleCircuit_2_1.printer != null ){
      res = create_circuit( operands );
      res.build();
      cached_circuits.put( id, res );
    }
    long[] start = new long[3];
    long[] end = new long[3];
    
    if( profile_count ){
      get_cir_num( start );
    }
    
    State ans = execute( operands, res );

    if( profile_count ){
      get_cir_num( end );
      long[] counter = local_eval ? local_cir_executed : cir_executed;
      if( active_counter != null ){
	for( ArrayList<Long> active : active_counter ){
	  for( int i = 0; i < 3 ; i++ ){
	    active.set( i, active.get(i) + (end[i] - start[i]) );
	  }
	}
      }
      for( int i = 0; i < 3; i++ ){
	counter[i] += end[i] - start[i];
      }
    }
    return ans;
  }
  public abstract Circuit create_circuit( State[] operands ) throws Exception ;
  public abstract int circuit_id( State[] operands );

  public abstract State execute( State[] operands, Circuit c ) throws Exception;
  
  public static long get_executed_num( int cir, boolean local ){
    return local ? local_cir_executed[cir] : cir_executed[cir];
  }
  public static Map<String, ArrayList<Long> > getProfileInfo(){
    return profile_map;
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
