package GCParser.Operation;

import YaoGC.*;
import GCParser.*;

public class NotOperation extends OpDirections {
  public final static String NAME = "not";
  public NotOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception{
    NOT_N_N not = new NOT_N_N( inputs[0].getWidth() );
    not.build();
    return not.startExecuting( inputs[0] );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    if( operands.length != 1 )
      throw createException(getOp_name()+" must have one operands" );
    return operands[0].validate();
  }
}