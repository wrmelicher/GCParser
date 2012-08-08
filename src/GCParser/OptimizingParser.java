package GCParser;

import java.util.*;
import java.io.*;
import java.math.BigInteger;
import GCParser.Operation.OpDirections;
import GCParser.Operation.CircuitDescriptionException;

public class OptimizingParser extends CircuitParser<VariableInfo> {

  private PrintStream ps;
  private Set<VariableInfo> inputs = new HashSet<VariableInfo>();
  private Map<VariableInfo,Boolean> outputs = new HashMap<VariableInfo,Boolean>();
  
  private OptimizingParser( File f, InputStream i, OutputStream os ){
    super( f, i );
    ps = new PrintStream( os );
  }

  public static OptimizingParser fromFile( File f ) throws FileNotFoundException {
    return new OptimizingParser( f, new FileInputStream(f), new FileOutputStream( new File( f.getPath()+".opt") ) );
  }

  public void print() throws IOException {
    VariableInfo.parser = this;
    for( VariableInfo v : inputs ){
      v.printSafe();
    }
    for( VariableInfo v: outputs.keySet() ){
      v.printSafe();
      ps.println(".output "+v.getName() + (outputs.get(v) ? " signed" : "") );
    }
    ps.close();
  }

  public PrintStream out(){
    return ps;
  }
  
  protected VariableInfo computedVariable( String name, OpDirections op, List<VariableInfo> args ) throws CircuitDescriptionException{
    return new ComputedInfo( name, op, args.toArray( new VariableInfo[0] ) );
  }
  protected VariableInfo inputVariable( String name, int party, int bits ) throws CircuitDescriptionException {
    VariableInfo i = new InputInfo( name, party, bits );
    inputs.add(i);
    return i;
  }
  
  protected void addOutput( VariableInfo val, boolean signed ) throws CircuitDescriptionException{
    outputs.put( val, signed );
  }
  protected VariableInfo constantVariable( BigInteger value, int bits ) throws CircuitDescriptionException {
    return new ConstantInfo( value, bits );
  }
  protected void include( File fname, Map<String,VariableInfo> inMap, Map<String,String> outMap )
    throws CircuitDescriptionException, FileNotFoundException, IOException{
    
  }

}
