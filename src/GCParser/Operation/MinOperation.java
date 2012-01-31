package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class MinOperation extends OpDirections {
  public final static String NAME = "min";
  public MinOperation(){
    super(NAME);
  }
  public State execute(State[] inputs) throws Exception {
    return binaryOperation( new MIN_2L_L( inputs[0].getWidth() ),inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}