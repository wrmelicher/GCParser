// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class XorOperation extends OpCircuitUser {
  public final static String NAME = "xor";
  public XorOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ){
    if( operands.length == 1 ){
      return new XOR_L_1( operands[0].getWidth() );
    } else {
      return new XOR_2L_L( operands[0].getWidth() );
    }
  }
  public int circuit_id( State[] operands ){
    int id = operands[0].getWidth();
    if( operands.length == 1 )
      return -id;
    else 
      return id;
  }
  public State execute(State[] inputs, Circuit xor) throws Exception {
    if( inputs.length == 1 ){
      return xor.startExecuting( inputs[0] );
    } else {
      return binaryOperation( xor, inputs );
    }
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length == 1 ){
      return 1;
    } else {
      binaryOperation( operands );
      return operands[0].validate();
    }
  }
}