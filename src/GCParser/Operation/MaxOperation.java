package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class MaxOperation extends OpDirections {
  public final static String NAME = "max";
  public MaxOperation(){
    super(NAME);
  }
  public State execute(State[] inputs) throws Exception {
    return binaryOperation( new MAX_2L_L( inputs[0].getWidth() ),inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}