package GCParser.Operation;

import YaoGC.*;
import GCParser.OperationNameResolver;
import GCParser.*;
public class NequOperation extends OpDirections {
  public final static String NAME = "nequ";
  public NequOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    State[] xor = new State[1];
    xor[0] = OperationNameResolver.executeFromName(XorOperation.NAME, inputs );
    return OperationNameResolver.executeFromName(OrOperation.NAME, xor);
  }	
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}
