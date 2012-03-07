// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GtsOperation extends OpCircuitUser {
  public final static String NAME = "gts";
  // greater than signed
  public GtsOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ){
    return new GTS_2L_1( operands[0].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[0].getWidth();
  }
  public State execute( State[] inputs, Circuit c ) throws Exception {
    return binaryOperation( c, inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}