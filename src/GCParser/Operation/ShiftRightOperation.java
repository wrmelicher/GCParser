package GCParser.Operation;

import GCParser.*;
import YaoGC.*;
import java.math.BigInteger;

public class ShiftRightOperation extends OpDirections {
  public static final String NAME = "shiftr";
  public ShiftRightOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    State out = State.extractState
      ( inputs[0],
	State.toBigInteger(inputs[1]).intValue(),
	inputs[0].getWidth() );
    reusedWires(out);
    return out;
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if(operands.length != 2){
      throw createException(NAME+" must have 2 argument");
    }
    if( !(operands[1] instanceof Constant_Variable ) ){
      throw createException(NAME+" argument 2 must be literal constant");
    }
    int end = ( (Constant_Variable)operands[1] ).getValue().intValue();
    int v = operands[0].validate();
    if( v - end < 0 )
      throw createException(NAME+" cannot create state of negative width");
    return operands[0].validate()-1;
  }
}
