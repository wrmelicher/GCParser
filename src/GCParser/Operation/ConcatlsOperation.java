// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser.Operation;

import GCParser.*;
import YaoGC.*;

public class ConcatlsOperation extends OpDirections {
  public final static String NAME = "concatls";
  public ConcatlsOperation(){
    super(NAME);
  }

  // concatenates operands with most significant bits first
  public State execute( State[] inputs ) throws Exception {
    State ans = inputs[0];
    for( int i = 1; i < inputs.length; i++ ){
      ans = State.concatenate( inputs[i], ans );
    }
    reusedWires(ans);
    return ans;
  }
  public int validate( Variable[] operands ) throws CircuitDescriptionException {
    int sum = 0;
    for( Variable v : operands ){
      sum += v.validate();
    }
    return sum;
  }
}
