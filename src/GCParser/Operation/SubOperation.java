package GCParser.Operation;

import YaoGC.State;
import YaoGC.SUB_2N_N;
import GCParser.*;

public class SubOperation extends OpDirections {
  public final static String NAME = "sub";
  public SubOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    return binaryOperation( new SUB_2N_N( inputs[0].getWidth() ),inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}
