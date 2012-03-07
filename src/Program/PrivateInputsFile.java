// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import java.io.*;
import java.math.BigInteger;
import java.util.*;
import GCParser.Input_Variable;

public class PrivateInputsFile implements PrivateInputProvider {
  private InputStream in;
  private Map<String,BigInteger> ans = null;
  public PrivateInputsFile( InputStream inarg ){
    in = inarg;
  }
  public Map<String, BigInteger> privateInputs( Map<String, Input_Variable> requested ){
    if( ans != null )
      return ans;
    ans = new HashMap<String, BigInteger>();
    Scanner sc = new Scanner( in );
    String id;
    BigInteger val; 
    while( sc.hasNext() ){
      id = sc.next();
      if( sc.hasNextBigInteger() )
	val = sc.nextBigInteger();
      else {
	System.out.println( "Variable \""+id+"\" has no value...Exiting" );
	System.exit(1);
	val = null;
      }
      Input_Variable var = requested.get( id );
      if( var != null ){
	if( val.bitCount() > var.bitcount )
	  System.out.println( "Value of "+val+" may be too large for variable \""+id+"\" with required bit length of "+var.bitcount+". Calculations may be incorrect." );
	ans.put( id, val );
      }
    }
    sc.close();
    try {
      in.close();
    } catch ( IOException e ){
      System.out.println(e.getMessage());
    }
    return ans;
  }
}