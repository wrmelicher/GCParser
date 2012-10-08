package GCParser.Operation;
import YaoGC.State;
import java.math.BigInteger;
import GCParser.*;
public class SetOperation extends OpDirections {
  public final static String NAME = "set";
  public SetOperation(){
    super(NAME);
  }

  public State execute(State[] inputs) throws Exception {
    reusedWires(inputs[0]);
    return inputs[0];
  }

  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 1 ){
      throw createException( getOp_name() + " must have 1 operand" );
    }
    return operands[0].validate();
  }
}
