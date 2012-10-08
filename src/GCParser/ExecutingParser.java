package GCParser;

import GCParser.Operation.*;
import java.io.*;
import java.util.*;
import java.math.BigInteger;

public class ExecutingParser extends CircuitParser<Variable> {
  
  protected boolean execute_streaming = false;
  private Variable_Context context = new Variable_Context();
  
  protected ExecutingParser( File f, InputStream s ){
    super( f, s );
  }
  protected ExecutingParser( File f, InputStream s, ExecutingParser p ) throws IOException {
    super( f, s, p );
  }

  public static ExecutingParser fromFile( File f ) throws FileNotFoundException {
    ExecutingParser p = new ExecutingParser( f, new FileInputStream(f) );
    return p;
  }

  public Variable_Context context(){
    return context;
  }

  public void readInputs() throws CircuitDescriptionException {
    super.readInputs();
    for( String id : curVars() ){
      Variable v = getVar(id);
      v.setFeedsLocally( false );
    }
  }

  public void read() throws CircuitDescriptionException {
    execute_streaming = true;
    super.read();
    context.validate();
  }

  @Override
    protected void putVar( String name, Variable v ) throws CircuitDescriptionException {
    super.putVar( name, v );
    context().putVar( v );
    if( execute_streaming ){
      v.executeDebug();
    }
  }

  protected Variable computedVariable( String name, OpDirections op, List<Variable> args ) throws CircuitDescriptionException{
    Variable ans = new Computed_Variable( name, partyComp(), lineNumber(), args.toArray( new Variable[0] ), op );
    return ans;
  }
  
  protected Variable inputVariable( String name, int party, int bits ) throws CircuitDescriptionException {
    Variable ans = new Input_Variable( name, party, lineNumber(), bits );
    return ans;
  }
  
  protected void addOutput( Variable val, OutputFormat signed ) throws CircuitDescriptionException {
    context().addOutput( val, signed );
  }
  
  protected Variable constantVariable( BigInteger value, int bits ) throws CircuitDescriptionException {
    Variable ans = new Constant_Variable( value.toString(), lineNumber(), value, bits );
    return ans;
  }

  public void addInputMapping( Variable_Context other, Map<String, Variable> inMap ){
    for( Iterator<String> it = other.getInputs().iterator(); it.hasNext(); ){
      String otherInId = it.next();
      Variable arg = inMap.get(otherInId);
      Input_Variable join = (other.getInVar(otherInId));
      join.replaceWith(arg);
    }
  }
  
  public void addOutputMapping( Variable_Context other, Map<String,String> outMap ) throws CircuitDescriptionException {
    for( Iterator<String> it = other.getOutputs().iterator(); it.hasNext(); ){
      String otherOutId = it.next();
      String newVarName = outMap.get( otherOutId );
      Variable newVar = other.getOutVar( otherOutId );
      Variable dummyVar = Dummy_Variable.newInstance( newVarName, lineNumber(), newVar );
      context().putVar( dummyVar );
    }
  }

  protected ExecutingParser child( File f ) throws FileNotFoundException, IOException {
    FileInputStream io = new FileInputStream(f);    
    return new ExecutingParser( f, io, this );
  }
  
  protected void include( File fname, Map<String,Variable> inMap, Map<String,String> outMap )
    throws CircuitDescriptionException, FileNotFoundException, IOException{

    ExecutingParser p = child( fname );
    p.read();
    Variable_Context includeCon = p.context();
    
    if( !inMap.keySet().containsAll( includeCon.getInputs() ) ){
      String error = "The following input variables were not defined in the included file "+fname+": ";
      includeCon.getInputs().removeAll( inMap.keySet() );
      for( Iterator<String> it = includeCon.getInputs().iterator(); it.hasNext(); ){
	error += "\""+it.next()+"\"";
	if( it.hasNext() )
	  error += ", ";
      }
      throw new CircuitDescriptionException( error, lineNumber() );
    }
    addInputMapping( includeCon, inMap );
    
    if( ! includeCon.getOutputs().containsAll( outMap.keySet() ) ){
      String error = "The following output variables were not found in the included file "+fname+
	": ";
      outMap.keySet().removeAll( includeCon.getOutputs() );
      for( Iterator<String> it = outMap.keySet().iterator(); it.hasNext(); ){
	error += "\""+it.next()+"\"";
	if( it.hasNext() )
	  error += ", ";
      }
      throw new CircuitDescriptionException( error, lineNumber() );
    }
    addOutputMapping( includeCon, outMap );
    
  }

}
