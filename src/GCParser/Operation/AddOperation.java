// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class AddOperation extends OpCircuitUser {
  public static final String NAME = "add";
  public AddOperation(){
    super( NAME );
  }
  public Circuit create_circuit( State[] operands ){
    return new ADD_2N_N( operands[0].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[0].getWidth();
  }
  public State execute( State[] inputs, Circuit cir ) throws Exception {
    return binaryOperation( cir, inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}
