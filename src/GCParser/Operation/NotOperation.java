// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import YaoGC.*;
import GCParser.*;

public class NotOperation extends OpCircuitUser {
  public final static String NAME = "not";
  public NotOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ){
    return new NOT_N_N( operands[0].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[0].getWidth();
  }
  public State execute( State[] inputs, Circuit not ) throws Exception{
    return not.startExecuting( inputs[0] );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 1 )
      throw createException(getOp_name()+" must have one operands" );
    return operands[0].validate();
  }
}