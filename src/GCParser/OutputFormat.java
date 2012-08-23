package GCParser;

import YaoGC.*;
import Utils.*;
import java.math.BigInteger;

public class OutputFormat {
  public boolean signed;

  public OutputFormat( boolean isSigned ){
    signed = isSigned;
  }

  public String printFormat(BigInteger val){
    return val.toString();
  }

  public String printIdentifier(){
    return signed ? "signed" : "unsigned";
  }

  public BigInteger interpret( State s, BigInteger[] lbs ) throws Exception {
    return signed ? interpretSigned( s, lbs ) : interpretUnsigned( s, lbs );
  }
  
  private static BigInteger interpretUnsigned( State s, BigInteger[] lbs ) throws Exception {
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
  private static BigInteger interpretSigned( State s, BigInteger[] lbs ) throws Exception {
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
