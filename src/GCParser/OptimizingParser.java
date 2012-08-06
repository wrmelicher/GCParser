package GCParser;

import java.util.*;
import java.io.*;
import java.math.BigInteger;
import GCParser.Operation.OpDirections;
import GCParser.Operation.CircuitDescriptionException;

public class OptimizingParser extends CircuitParser<VariableInfo> {

  private OptimizingParser( File f, InputStream i ){
    super( f, i );
  }

  public static OptimizingParser fromFile( File f ) throws FileNotFoundException {
    return new OptimizingParser( f, new FileInputStream(f) );
  }

  private Set<VariableInfo> inputs = new HashSet<VariableInfo>();
  private Map<VariableInfo,Boolean> outputs = new HashMap<VariableInfo,Boolean>();

  public void print( OutputStream f ) throws IOException {
    PrintStream out = new PrintStream( f );
    for( VariableInfo v : inputs ){
      v.printSafe( out );
    }
    for( VariableInfo v: outputs.keySet() ){
      v.printSafe( out );
      out.println(".output "+v.getName() + (outputs.get(v) ? " signed" : "") );
    }
    out.close();
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
