package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GteuOperation extends OpDirections {
  public final static String NAME = "gteu";
  // greater than equal to unsigned
  public GteuOperation(){
    super(NAME);
  }
  // gteu a b returns 1 if a is greater or equal to b
  public State execute( State[] inputs ) throws Exception {
    return binaryOperation( new GTE_2L_1( inputs[0].getWidth() ), inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}