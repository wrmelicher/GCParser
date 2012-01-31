package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class LtuOperation extends OpDirections {
  public final static String NAME = "ltu";
  // less than unsigned
  public LtuOperation(){
    super(NAME);
  }
  // ltu a b returns 1 if a is less than b
  public State execute( State[] inputs ) throws Exception {
    GT_2L_1 gtu = new GT_2L_1( inputs[0].getWidth() );
    gtu.build();
    State total = State.fromConcatenation( inputs[0], inputs[1] );
    int[] mapping = new int[ inputs[0].getWidth()*2 ];
    for( int i = 0; i < inputs[0].getWidth(); i++ ){
      mapping[ GT_2L_1.X(i) ] = i + inputs[0].getWidth();
      mapping[ GT_2L_1.Y(i) ] = i;
    }
    State in = OpDirections.fromMapping( total, mapping );
    return gtu.startExecuting( in );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}