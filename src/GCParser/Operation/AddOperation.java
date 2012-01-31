package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class AddOperation extends OpDirections {
  public static final String NAME = "add";
  public AddOperation(){
    super( NAME );
  }
  public State execute( State[] inputs ) throws Exception {
    return binaryOperation( new ADD_2N_N( inputs[0].getWidth() ),inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}
