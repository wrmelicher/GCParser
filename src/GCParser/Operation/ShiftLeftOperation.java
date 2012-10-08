package GCParser.Operation;

import GCParser.*;
import YaoGC.*;
import java.math.BigInteger;

public class ShiftLeftOperation extends OpDirections {
  public static final String NAME = "shiftl";
  public ShiftLeftOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    State zero = new State
      (BigInteger.ZERO,
       State.toBigInteger(inputs[1]).intValue() );
    reusedWires( inputs[0] );
    return State.concatenate( inputs[0], zero );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if(operands.length != 2){
      throw createException(NAME+" must have 2 arguments");
    }
    if( !(operands[1] instanceof Constant_Variable ) ){
      throw createException(NAME+" argument 2 must be literal constant");
    }
    int end = ( (Constant_Variable)operands[1] ).getValue().intValue();
    return operands[0].validate()+end;
  }
}
