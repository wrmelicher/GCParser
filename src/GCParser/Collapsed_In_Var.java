// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser;
import YaoGC.State;
class Collapsed_In_Var extends Input_Variable {
  private Variable other;
  private int computingParty;
  public Collapsed_In_Var( Variable v ) {
    super( "_"+v.getId(), v.getParty(), v.bitCount() );
    other = v;
  }
  public void localEval( int p, Variable_Context con ) throws Exception {
    computingParty = p;
  }
  public State execute() throws Exception {
    if( getParty() == computingParty )
      return other.execute();
    else
      return value;
  }
  public void setState( State v ){
    super.setState(v);
    computingParty = -1;
  }
  /*
  public void reset(){
    other.reset();
    }*/
}
