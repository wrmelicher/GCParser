// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
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
    State[] switched = { inputs[1], inputs[0] };
    return executeOther( GtuOperation.NAME, switched );
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}