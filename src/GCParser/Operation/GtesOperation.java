package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GtesOperation extends OpDirections {
  public final static String NAME = "gtes";
  // greater than or equal to signed
  public GtesOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    return binaryOperation( new GTES_2L_1( inputs[0].getWidth() ), inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}