// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class MaxsOperation extends OpCircuitUser {
  public final static String NAME = "maxs";
  // max signed operation
  public MaxsOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ){
    return new MAXS_2L_L( operands[0].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[0].getWidth();
  }
  public State execute(State[] inputs, Circuit c) throws Exception {
    return binaryOperation( c, inputs );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return operands[0].validate();
  }
}