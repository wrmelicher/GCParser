// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser;
import YaoGC.State;
import GCParser.Operation.CircuitDescriptionException;

public class Dummy_Variable extends Computed_Variable {
  private Dummy_Variable( String name, int line, Variable[] v ){
    super( name, v[0].getParty(), line, v, null );
  }
  public static Dummy_Variable newInstance( String name, int line, Variable v ){
    Variable[] varg = new Variable[1];
    varg[0] = v;
    return new Dummy_Variable( name, line, varg );
  }
  public State execute() throws Exception {
    return getChildren()[0].execute();
  }
  public int validate() throws CircuitDescriptionException {
    return getChildren()[0].validate();
  }
  public String toString(){
    return super.toString()+"(Dummy)";
  }
}