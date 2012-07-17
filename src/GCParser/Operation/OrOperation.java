// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class OrOperation extends OpCircuitUser {
  public final static String NAME = "or";
  public OrOperation(){
    super(NAME);
  }
  public Circuit create_circuit( State[] operands ) throws Exception {
    if( operands.length == 1 ){
      return new OR_L_1( operands[0].getWidth() );
    } else {
      return new OR_2L_L( operands[0].getWidth() );
    }
  }
  public int circuit_id( State[] operands ){
    int id = operands[0].getWidth();
    if( operands.length == 1 )
      return -id;
    else 
      return id;
  }
  public State execute(State[] inputs, Circuit or) throws Exception {
    if( inputs.length == 1 ){
      return or.startExecuting( inputs[0] );
    } else {
      return binaryOperation( or, inputs );
    }
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length == 1 ){
      int o = operands[0].validate();
      if( o < 2 ){
	throw createException("Unary or operation requires at least two bits");
      }
      return 1;
    } else {
      binaryOperation( operands );
      return operands[0].validate();
    }
  }
}
