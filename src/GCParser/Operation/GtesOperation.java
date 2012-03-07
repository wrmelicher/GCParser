// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GtesOperation extends OpCircuitUser {
  public final static String NAME = "gtes";
  // greater than or equal to signed
  public GtesOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ){
    return new GTES_2L_1( operands[0].getWidth() );
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