// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import java.util.*;
import java.math.BigInteger;
import GCParser.Input_Variable;
import YaoGC.State;

public class PrivateInputsStore implements PrivateInputProvider {
  private Map<String,BigInteger> store;
  public PrivateInputsStore(Map<String,BigInteger> s){
    store = s;
  }
  public static PrivateInputsStore FromStateMap( Map<String,State> in ){
    Map<String,BigInteger> arg = new HashMap<String,BigInteger>();
    for( String s : in.keySet() ){
      arg.put( s, State.toBigInteger( in.get(s) ) );
    }
    return new PrivateInputsStore( arg );
  }
  public Map<String, BigInteger> privateInputs( Map<String, Input_Variable> requested ){
    return store;
  }
}