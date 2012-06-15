package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

/*

  out chose control x y

  out = x if control == 0
  out = y otherwise

 */


public class ChoseOperation extends OpCircuitUser {
  public static final String NAME = "chose";
  public ChoseOperation() {
    super( NAME );
  }
  public Circuit create_circuit( State[] operands ){
    return new MUX_2Lplus1_L( operands[1].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[1].getWidth();
  }
  public State execute( State[] inputs, Circuit cir ) throws Exception {
    State total = State.fromConcatenation( inputs[1], inputs[2] );
    int[] mapping = new int[ inputs[1].getWidth()*2 ];
    for( int i = 0; i < inputs[1].getWidth(); i++ ){
      mapping[ MUX_2Lplus1_L.X(i) ] = i;
      mapping[ MUX_2Lplus1_L.Y(i) ] = i + inputs[1].getWidth();
    }
    State in = OpDirections.fromMapping( total, mapping );
    State with_c = State.fromConcatenation( in, inputs[0] );

    return cir.startExecuting( with_c );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 3 ){
      throw createException( NAME+" operation must have 3 variables" );
    }
    if( operands[0].validate() != 1 ){
      throw createException( "First operand of "+NAME+" operation must have length 1" );
    }

    int lenFirst = operands[1].validate();
    int lenSecond = operands[2].validate();

    if( lenFirst != lenSecond ){
      throw createException( "Operands 2 and 3 of "+NAME+" operation must have the same length" );
    }
    return lenFirst;
  }
}