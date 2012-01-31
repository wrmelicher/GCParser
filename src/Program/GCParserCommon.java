package Program;

import GCParser.*;
import GCParser.Operation.CircuitDescriptionException;
import Utils.*;
import YaoGC.*;

import java.math.*;
import java.io.*;
import java.util.*;

public class GCParserCommon extends ProgCommon{

  private Variable_Context context;
  private File desc;
  private PrivateInputProvider pip;

  public GCParserCommon( File DESC, PrivateInputProvider PIP ){
    desc = DESC;
    pip = PIP;
  }
  public void parseCircuit( int party ) throws Exception {
    try {
      context = CircuitParser.read(desc);
    } catch (CircuitDescriptionException e) {
      System.out.println(e.getMessage()+"...Exiting");
      System.exit(1);
    } catch( Exception e ){
      System.out.println(e.getMessage()+"...Exiting");
      e.printStackTrace();
      System.exit(1);
    }
    Map<String,BigInteger> privIns = getPrivateInputs(party);
    context.collapseLocalVars( privIns, party );
  }
  public Variable_Context context(){
    return context;
  }
  public void reset(){
    context.resetCircuit();
  }
  public void setPIP( PrivateInputProvider PIP ){
    pip = PIP;
    reset();
  }
  public Boolean isSignedHint( String name ){
    return context.isSigned(name);
  }
  public Map<String,BigInteger> getPrivateInputs(int party) throws Exception {
    Iterator<Input_Variable> it = context().getInVarsOfParty(party).iterator();
    Map<String, Input_Variable> requested = new HashMap<String, Input_Variable>();
    while( it.hasNext() ) {
      Input_Variable var = it.next();
      requested.put( var.getId(), var );
    }

    Map<String, BigInteger> provided = pip.privateInputs( requested );
    if( ! provided.keySet().containsAll( requested.keySet() ) ){
      Set<String> undefined = requested.keySet();
      undefined.removeAll( provided.keySet() );
      String error = "The following private variables are undefined: ";
      Iterator<String> errIt = undefined.iterator();
      while( errIt.hasNext() ){
	error += "\""+errIt.next()+"\", ";
      }
      error += "...Exiting";
      throw new Exception( error );
    }
    return provided;
  }

  public static BigInteger interpretUnsigned( State s, BigInteger[] lbs ) throws Exception {
    return interpretUnsigned( s, lbs, lbs.length );
  }
  private static BigInteger interpretUnsigned( State s, BigInteger[] lbs, int width ) throws Exception {
    BigInteger ans = BigInteger.ZERO;
    for (int i = 0; i < width; i++) {
      if( interpretBit( s, lbs, i ) )
	ans = ans.setBit(i);
    }
    return ans;
  }
  public static BigInteger interpretSigned( State s, BigInteger[] lbs ) throws Exception {
    BigInteger magnitude = interpretUnsigned( s, lbs ,lbs.length-1 );
    if ( interpretBit( s, lbs, lbs.length-1 ) ) {
      for( int i = 0; i < s.getWidth()-1; i++ ){
	magnitude = magnitude.flipBit(i);
      }
      magnitude = magnitude.add( BigInteger.ONE );
      magnitude = magnitude.negate();
    }
    return magnitude;
  }
  private static boolean interpretBit( State s, BigInteger[] lbs, int bit ) throws Exception {
    if (s.wires[bit].value != Wire.UNKNOWN_SIG) {
      if (s.wires[bit].value == 1)
	return true;
    } else if (lbs[bit].equals(s.wires[bit].invd ? 
			       s.wires[bit].lbl :
			       s.wires[bit].lbl.xor(Wire.R.shiftLeft(1).setBit(0)))) {
      return true;
    } else if (!lbs[bit].equals(s.wires[bit].invd ? 
				s.wires[bit].lbl.xor(Wire.R.shiftLeft(1).setBit(0)) :
				s.wires[bit].lbl)) 
      throw new Exception("Bad label encountered: i = " + bit + "\t" +
			  Color.red + lbs[bit] + " != (" + 
			  s.wires[bit].lbl + ", " +
			  s.wires[bit].lbl.xor(Wire.R.shiftLeft(1).setBit(0)) + ")" + Color.black);
    return false;
  }
}