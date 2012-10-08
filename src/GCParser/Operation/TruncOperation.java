// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;
import YaoGC.State;
import java.math.BigInteger;
import GCParser.*;
public class TruncOperation extends OpDirections {
  public final static String NAME = "trunc";
  public TruncOperation(){
    super(NAME);
  }
  public State execute(State[] inputs) throws Exception {
    BigInteger endB = State.toBigInteger( inputs[1] );
    int end = endB.intValue();
    State out = State.extractState( inputs[0], 0, end );
    reusedWires(out);
    return out;
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 2 )
      throw createException( getOp_name()+" not given two operands" );
    if( ! (operands[1] instanceof Constant_Variable ) )
      throw createException( getOp_name()+" operand 2 must be a constant operand" );
    int var = operands[0].validate();
    
    int end = ( (Constant_Variable)operands[1] ).getValue().intValue();
    if( var < end )
      throw createException
	( getOp_name()+": must truncate to a smaller width");
    return end;
  }
}
