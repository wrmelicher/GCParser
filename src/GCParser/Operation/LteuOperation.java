// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class LteuOperation extends OpDirections {
  public final static String NAME = "lteu";
  // less than equal to unsigned
  public LteuOperation(){
    super(NAME);
  }
  // lteu a b returns 1 if a is less than or equal to b
  public State execute( State[] inputs ) throws Exception {
    State[] switched = new State[2];
    switched[0] = inputs[1];
    switched[1] = inputs[0];
    return executeOther( GteuOperation.NAME, switched );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}