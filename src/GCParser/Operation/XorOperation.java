package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class XorOperation extends OpDirections {
  public final static String NAME = "xor";
  public XorOperation(){
    super(NAME);
  }
  public State execute(State[] inputs) throws Exception {
    if( inputs.length == 1 ){
      XOR_L_1 xor = new XOR_L_1( inputs[0].getWidth() );
      xor.build();
      return xor.startExecuting( inputs[0] );
    } else {
      return binaryOperation( new XOR_2L_L( inputs[0].getWidth() ),inputs );
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