// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser;

import YaoGC.*;
import java.math.BigInteger;
import java.util.Map;
import GCParser.Operation.CircuitDescriptionException;

public class Input_Variable extends Variable {
  public int bitcount;
  protected State value;
  public static final int CLIENT = 1;
  public static final int SERVER = 2;
  public static final int NEUTRAL = 0;
  public static final int ALL = -1;
  public Input_Variable( String idarg, int partyarg , int bitarg ){
    this(idarg, partyarg, -1, bitarg);
  }
  public Input_Variable( String idarg, int partyarg , int lineNumArg, int bitarg ){
    super(idarg, partyarg, lineNumArg);
    bitcount = bitarg;
    value = null;
  }
  public State execute() throws Exception {
    assert value != null : "Variable \""+getId()+"\" not initialized";
    return value;
  }
  public void setState(BigInteger in){
    setState( new State( in, bitcount ));
  }
  public void setState(State in){
    assert in.getWidth() == bitcount : "Recieved input for variable \""+getId()+"\" with "+in.getWidth()+" bits, expected "+bitcount+" bits.";
    value = in;
  }
  public int validate() throws CircuitDescriptionException {
    return bitcount;
  }
  public String toString(){
    String s = super.toString();
    return s+"(Input)";
  }
}
