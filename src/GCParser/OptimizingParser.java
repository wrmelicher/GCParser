package GCParser;

import java.util.*;
import java.io.*;
import java.math.BigInteger;
import GCParser.Operation.OpDirections;
import GCParser.Operation.CircuitDescriptionException;

public class OptimizingParser extends CircuitParser<VariableInfo> {

  private PrintStream otherComp;
  private PrintStream inputs;
  private List<PrintStream> localComp;
  private List<File> streams = new LinkedList<File>();
  private List<PrintStream> all = new LinkedList<PrintStream>();
  
  private OptimizingParser( File f, InputStream i ){
    super( f, i );
    otherComp = makeNew(f);
    inputs = makeNew(f);
    localComp = new LinkedList<PrintStream>();
    localComp.add( makeNew(f) );
    localComp.add( makeNew(f) );
  }

  private PrintStream makeNew( File f ){
    File tempFile = null;
    try{
      tempFile = File.createTempFile(f.getName(), "temp", f.getParentFile() );
    } catch( IOException e ){
      System.out.println(e.getMessage());
      System.exit(1);
    }
    streams.add(tempFile);
    PrintStream ans = null;
    try{
      ans = new PrintStream( new FileOutputStream(tempFile) );
    } catch( FileNotFoundException e ){
      System.out.println(e.getMessage());
      System.exit(1);
    }
    all.add(ans);
    return ans;
  }

  public static OptimizingParser fromFile( File f ) throws FileNotFoundException {
    return new OptimizingParser( f, new FileInputStream(f) );
  }

  public void print() throws CircuitDescriptionException {
    parse();
    for( PrintStream ps : all ){
      ps.close();
    }
  }

  private void print( VariableInfo v ){
    PrintStream choose;
    if( v.getParty() == Input_Variable.ALL ){
      choose = otherComp;      
    } else if( v.getParty() == Input_Variable.NEUTRAL ){
      return;
    } else {
      choose = localComp.get(v.getParty()-1);
      v.printNeutralChildren(choose);
    }
    v.printOn(choose);
  }
  
  protected VariableInfo computedVariable( String name, OpDirections op, List<VariableInfo> args ) throws CircuitDescriptionException{
    VariableInfo ans = VariableInfo.computedVariable( name, op, args );
    print(ans);
    return ans;
  }
  
  protected VariableInfo inputVariable( String name, int party, int bits ) throws CircuitDescriptionException {
    VariableInfo in = new VariableInfo( name, party, ".input "+name+" "+party+" "+bits );
    in.printOn(inputs);
    return in;
  }

  public void removeVar( String key ) {
    PrintStream choose = otherComp;
    choose.println(".remove "+key);
    try {
      VariableInfo inf = getVar(key);
      inf.remove();
    } catch( CircuitDescriptionException e ){
      // do nothing
    }
    super.removeVar( key );
  }
  
  protected void addOutput( VariableInfo val, OutputFormat fmt ) throws CircuitDescriptionException{
    otherComp.println(".output "+val.getName()+" "+fmt.printIdentifier() );
  }
  
  protected VariableInfo constantVariable( BigInteger value, int bits ) throws CircuitDescriptionException {
    return new VariableInfo( value.toString()+":"+bits, Input_Variable.NEUTRAL, "" );
  }
  
  protected void include( File fname, Map<String,VariableInfo> inMap, Map<String,String> outMap )
    throws CircuitDescriptionException, FileNotFoundException, IOException{
    
  }

}
