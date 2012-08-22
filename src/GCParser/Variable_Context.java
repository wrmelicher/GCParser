// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package GCParser;
import java.util.*;
import YaoGC.State;
import GCParser.Operation.CircuitDescriptionException;
import java.math.BigInteger;
public class Variable_Context {

  private Map<String, Input_Variable> inVar;
  private Map<String, OutPair> outVar;
  private Map<String, Input_Variable> collapsedVars;
  private Set<Variable> computedParty;
  private boolean isReset;
  private boolean local;

  private static class OutPair {
    private Variable var;
    private OutputFormat fmt;
    public OutPair( Variable v, OutputFormat f ){
      var = v;
      fmt = f;
    }
  }
  
  public Variable_Context(){
    isReset = true;
    local = false;
    outVar = new HashMap<String,OutPair>();
    inVar = new HashMap<String,Input_Variable>();
    collapsedVars = new HashMap<String, Input_Variable>();
    computedParty = new HashSet<Variable>();
  }
  public void putVar( Variable v ) throws CircuitDescriptionException {
    v.validate();
    if( v instanceof Input_Variable ){
      Input_Variable inv = (Input_Variable) v;
      inVar.put( inv.getId(), inv );
    } else if( ( v.getParty() == Input_Variable.SERVER || v.getParty() == Input_Variable.CLIENT ) && !local) {
      computedParty.add( v );
    }
  }
  public Set<String> getInputs() {
    return inVar.keySet();
  }
  public Set<String> getOutputs() {
    return outVar.keySet();
  }
  public OutputFormat getOutputFormat( String name ){
    return outVar.get(name).fmt;
  }
  public void addOutput( Variable v, OutputFormat fmt ){
    outVar.put( v.getId(), new OutPair( v, fmt ) );
  }
  public void addOutput( Variable v, boolean b ){
    addOutput(v, new OutputFormat(b) );
  }

  public Variable getOutVar( String name ){
    return outVar.get( name ).var;
  }

  public Input_Variable getInVar( String name ){
    return inVar.get( name );
  }
  
  public void collapseLocalVars( Map<String,BigInteger> in, int party ) throws Exception {
    for( String s : in.keySet() ){
      Input_Variable v = getInVar(s);
      v.setState(new State( in.get(s), v.bitcount ));
    }
    local = true;
    for( Variable com : computedParty ){
      com.localEval( party, this );
    }
    local = false;
  }
  public void remove( Variable v ){
    inVar.remove(v.getId());
    if( v instanceof Input_Variable )
      collapsedVars.put( v.getId(),(Input_Variable) v );
  }
  public void validate() throws CircuitDescriptionException {
    if( getOutputs().isEmpty() ){
      throw new CircuitDescriptionException( "No outputs are defined" );
    }
  }
  /*
  public void resetCircuit(){
    Iterator<String> outit = getOutputs().iterator();
    while( outit.hasNext() ){
      String id = outit.next();
      Variable out = getOutVar(id);
      if( out == null ){
	System.out.println("Output variable \""+id+"\" not defined...Exiting");
	System.exit(1);
      }
      out.reset();
    }
    isReset = true;
    }*/
  public Map<String,State> execCircuit(){
    Iterator<String> outit = getOutputs().iterator();
    Map<String, State> ans = new HashMap<String, State>();
    while( outit.hasNext() ){
      String id = outit.next();
      Variable out = getOutVar( id );
      if( out == null ){
	System.out.println("Output variable \""+id+"\" not defined...Exiting");
	System.exit(1);
      }
      ans.put( id, out.executeDebug() );
    }
    return ans;
  }
  public void setInVals( Map<String, State> in ){
    Iterator<String> it = in.keySet().iterator();
    while( it.hasNext() ){
      String id = it.next();
      Input_Variable var = getInVar( id );
      var.setState( in.get( id ) );
    }
    inVar = null;
    collapsedVars = null;
    computedParty = null;
  }
  public Map<String,State> execCircuit( Map<String, State> inputVals ){
    /*if( !isReset )
      resetCircuit();*/
    setInVals( inputVals );
    return execCircuit();
  }
  public Collection<Input_Variable> getInVarsOfParty( int party ){
    List<Input_Variable> ans = new LinkedList<Input_Variable>();
    for( String s : getInputs() ){
      if( getInVar(s).getParty() == party ){
	ans.add( getInVar(s) );
      }
    }
    return ans;
  }
  public Collection<Input_Variable> getPrivInOfParty( int party ){
    // get private inputs to supply
    Set<Input_Variable> ans = new HashSet<Input_Variable>();
    for( Input_Variable i : getInVarsOfParty(party) ){
      if( !(i instanceof Collapsed_In_Var ) ){
	ans.add(i);
      }
    }
    for( String v : collapsedVars.keySet() ){
      ans.add( collapsedVars.get(v) );
    }
    return ans;
  }
  public int getBitsOfParty( int party ){
    Collection<Input_Variable> list = getInVarsOfParty( party );
    int accum = 0;
    for( Input_Variable v : list ){
      accum += v.bitcount;
    }
    return accum;
  }
  public int getNumVarsOfParty( int party ){
    return getInVarsOfParty( party ).size();
  }
  public void debugPrint(){
    for( String s: getOutputs() ){
      getOutVar(s).debugPrint();
    }
  }
}
