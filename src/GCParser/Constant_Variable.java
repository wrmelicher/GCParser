// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser;

import YaoGC.*;
import java.math.*;
import GCParser.Operation.CircuitDescriptionException;

public class Constant_Variable extends Variable { //oxymoron
  private BigInteger value;
  private int numBits;
  public Constant_Variable( String idarg, BigInteger valuearg ){
    this( idarg, -1, valuearg );
  }
  public Constant_Variable( String idarg, int lineNumArg, BigInteger valuearg ){
    this( idarg, lineNumArg, valuearg, valuearg.bitLength() + 1 );
  }
  public Constant_Variable( String idarg, BigInteger valuearg, int bitsarg ){
    this( idarg, -1, valuearg, bitsarg );
  }
  public Constant_Variable( String idarg, int lineNumArg, BigInteger valuearg, int bitsarg ){
    super( idarg, Input_Variable.NEUTRAL ,lineNumArg );
    value = valuearg;
    numBits = bitsarg;
  }
  public State execute() {
    BigInteger unsigned = value;
    if( value.signum() == -1 ){
      unsigned = unsigned.negate();
      for( int i = 0; i < numBits; i++ ){
	unsigned = unsigned.flipBit(i);
      }
      unsigned = unsigned.add( BigInteger.ONE );
    }
    return new State(unsigned,numBits);
  }
  public int validate() throws CircuitDescriptionException{
    if( value.bitCount() > numBits ){
      throw createException("Value of "+value+" is too large for "+numBits);
    }
    return numBits;
  }
  public BigInteger getValue(){
    return value;
  }
  public void localEval( int party, Variable_Context con ){}
  public String toString(){
    return super.toString()+"(Constant:"+getValue()+")";
  }
}