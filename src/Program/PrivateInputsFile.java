// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import java.io.*;
import java.math.BigInteger;
import java.util.*;
import GCParser.Input_Variable;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

public class PrivateInputsFile implements PrivateInputProvider {
  private InputStream in;
  private Map<String,BigInteger> ans = null;
  private static Pattern formatPat = Pattern.compile("format=(\\w+)");
  private static BigIntFormat NORMAL;
  private static final Map<String,BigIntFormat> formatDirectives =
    new HashMap<String, BigIntFormat>();

  private static abstract class BigIntFormat {
    public BigIntFormat(String name){
      formatDirectives.put( name, this );
    }
    public abstract BigInteger getFrom( String val );
  }

  private static class NormalFmt extends BigIntFormat {
    public NormalFmt(){
      super("dec");
    }
    public BigInteger getFrom(String val){
      return new BigInteger(val,10);
    }
  }

  private static class HexFmt extends BigIntFormat {
    public HexFmt(){
      super("hex");
    }
    public BigInteger getFrom( String val ){
      return new BigInteger( val, 16 );
    }
  }

  public PrivateInputsFile( InputStream inarg ){
    in = inarg;
    new HexFmt();
    NORMAL = new NormalFmt();
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
      BigIntFormat fmt = NORMAL;
      if( sc.hasNext(formatPat) ){
	String pattern = sc.next( formatPat );
	Matcher m = formatPat.matcher( pattern );
	m.matches();
	String formatString = m.group(1);
	fmt = formatDirectives.get(formatString);
	if( fmt == null ){
	  System.out.println("Cannot recognize format: "+formatString);
	  System.exit(1);
	}
      }
      if( sc.hasNext() )
	val = fmt.getFrom( sc.next() );
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
