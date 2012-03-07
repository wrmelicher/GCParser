// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;
import GCParser.OperationNameResolver;
public class EquOperation extends OpDirections {
  public final static String NAME = "equ";
  public EquOperation(){
    super(NAME);
  }
  public State execute( State[] inputs ) throws Exception {
    State[] nequ = new State[1];
    nequ[0] = executeOther(NequOperation.NAME, inputs);
    return executeOther(NotOperation.NAME, nequ);
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    binaryOperation( operands );
    return 1;
  }
}
