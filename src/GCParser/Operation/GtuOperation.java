package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class GtuOperation extends OpDirections {
  public final static String NAME = "gtu";
  // greater than unsigned
  public GtuOperation(){
    super(NAME);
  }
  // gt a b returns 1 if a is greater than b
  public State execute( State[] inputs ) throws Exception {
    GT_2L_1 gtu = new GT_2L_1( inputs[0].getWidth() );
    gtu.build();
    State total = State.fromConcatenation( inputs[0], inputs[1] );
    int[] mapping = new int[ inputs[0].getWidth()*2 ];
    for( int i = 0; i < inputs[0].getWidth(); i++ ){
      mapping[ GT_2L_1.X(i) ] = i;
      mapping[ GT_2L_1.Y(i) ] = i + inputs[0].getWidth();
    }
    State in = OpDirections.fromMapping( total, mapping );
    return gtu.startExecuting( in );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}