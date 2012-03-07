// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import java.util.*;
import java.math.BigInteger;
import GCParser.Input_Variable;

public class PrivateInputsRandom implements PrivateInputProvider {
  Random rnd;
  public PrivateInputsRandom(){
    this( new Random() );
  }
  public PrivateInputsRandom( Random RND ){
    rnd = RND;
  }
  public Map<String, BigInteger> privateInputs( Map<String, Input_Variable> requested ){
    Iterator<String> it = requested.keySet().iterator();
    Map<String, BigInteger> ans = new HashMap<String, BigInteger>();
    while( it.hasNext() ){
      Input_Variable var = requested.get( it.next() );
      ans.put( var.getId(), new BigInteger( var.bitcount, rnd ) );
    }
    return ans;
  }
  
}