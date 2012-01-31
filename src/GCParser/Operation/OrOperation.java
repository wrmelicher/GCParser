package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class OrOperation extends OpDirections {
  public final static String NAME = "or";
  public OrOperation(){
    super(NAME);
  }
  public State execute(State[] inputs) throws Exception {
    if( inputs.length == 1 ){
      OR_L_1 or = new OR_L_1( inputs[0].getWidth() );
      or.build();
      return or.startExecuting( inputs[0] );
    } else {
      return binaryOperation( new OR_2L_L( inputs[0].getWidth() ),inputs );
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