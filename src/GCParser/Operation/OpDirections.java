// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import YaoGC.*;
import GCParser.OperationNameResolver;
import GCParser.*;

public abstract class OpDirections {

  private String op_name;
  protected Variable currentVar;
  public OpDirections(String name){
    op_name = name;
    OperationNameResolver.registerOp(op_name,this);
  }
  public String getOp_name(){
    return op_name;
  }

  public abstract State execute(State[] operands) throws Exception;

  // returns the number of bits this operation will output, or throws an exception
  public abstract int validate( Variable[] operands ) throws CircuitDescriptionException;
  public int validate( Variable[] operands, Variable caller ) throws CircuitDescriptionException {
    currentVar = caller;
    return validate( operands );
  }
  public void reusedWires( State s ){
    for( int i = 0; i < s.wires.length; i++ ){
      s.wires[i].num_pointers++;
    }
  }
  public CircuitDescriptionException createException(String mess){
    return new CircuitDescriptionException( mess, currentVar.getLineNum() );
  }
  public State executeOther( String other, State[] operands ) throws Exception {
    OpDirections op_other = OperationNameResolver.get( other );
    op_other.currentVar = currentVar;
    return op_other.execute( operands );
  }

  // convenience methods
  protected void binaryOperation( Variable[] operands ) throws CircuitDescriptionException{
    if( operands.length != 2 )
      throw createException( getOp_name()+" operation not given 2 operands");
    if( operands[0].validate() != operands[1].validate() )
      throw createException( getOp_name()+" operands must have the same bit length" );
  }
  protected State binaryOperation( Circuit c, State[] operands ) throws Exception {
    State in = State.fromConcatenation(operands[0], operands[1]);
    return c.startExecuting( in );
  }
  protected static State fromMapping( State total, int[] mapping ) throws Exception {
    assert mapping.length == total.getWidth() : "Mapping length not equal to state length";
    State res = State.extractState( total, mapping[0], mapping[0]+1 );
    for( int i = 1; i < mapping.length; i++ ){
      State bit = State.extractState( total, mapping[i], mapping[i]+1 );
      res = State.fromConcatenation( res, bit );
    }
    return res;
  }
}
