// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import java.math.BigInteger;
import java.util.Map;
import GCParser.Input_Variable;
public interface PrivateInputProvider {
  // returns private input values for a circuit
  public Map<String, BigInteger> privateInputs( Map<String, Input_Variable> requested );
}