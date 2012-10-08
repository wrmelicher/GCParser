// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;
import YaoGC.State;
import java.math.BigInteger;
import GCParser.*;
public class SelectOperation extends OpDirections {
  public final static String NAME = "select";
  public SelectOperation(){
    super(NAME);
  }
  // select a 1 4 returns bits 1 2 and 3 of variable a
  public State execute(State[] inputs) throws Exception {
    BigInteger startB = State.toBigInteger( inputs[1] );
    BigInteger endB = State.toBigInteger( inputs[2] );
    int start = startB.intValue();
    int end = endB.intValue();
    State out = State.extractState( inputs[0], start, end );
    reusedWires(out);
    return out;
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 3 )
      throw createException( getOp_name()+" not given three operands" );
    if( !(operands[1] instanceof Constant_Variable && operands[2] instanceof Constant_Variable) )
      throw createException( getOp_name()+" operands 2 and 3 must be literal values" );
    int var = operands[0].validate();
    
    int end = ( (Constant_Variable)operands[2] ).getValue().intValue();
    int start = ( (Constant_Variable)operands[1] ).getValue().intValue();
    if( start >= end )
      throw createException
	( getOp_name()+": start bit cannot be greater than or equal to end bit" );
    if( var < end )
      throw createException
	( getOp_name()+": end bit cannot be greater than bit width of "+var);
    return end-start;
  }
}
