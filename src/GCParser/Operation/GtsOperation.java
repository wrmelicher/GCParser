package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GtsOperation extends OpDirections {
  public final static String NAME = "gts";
  // greater than signed
  public GtsOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    return binaryOperation( new GTS_2L_1( inputs[0].getWidth() ), inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}