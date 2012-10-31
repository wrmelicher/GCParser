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
  private List<PrintStream> all = new LinkedList<PrintStream>();
  private List<ByteArrayOutputStream> all_out = new LinkedList<ByteArrayOutputStream>();

  private OptimizingParser( File f, InputStream i ){
    super( f, i );

    inputs = makeNew(f);
    localComp = new LinkedList<PrintStream>();
    localComp.add( makeNew(f) );
    localComp.add( makeNew(f) );
    otherComp = makeNew(f);
    localComp.get(0).println(".startparty 1");
    localComp.get(1).println(".startparty 2");
  }

  private PrintStream makeNew( File f ){
    ByteArrayOutputStream bs = new ByteArrayOutputStream();
    all_out.add(bs);
    PrintStream ans = new PrintStream( bs );
    all.add(ans);
    return ans;
  }

  public static OptimizingParser fromFile( File f ) throws FileNotFoundException {
    return new OptimizingParser( f, new FileInputStream(f) );
  }

  public void print() throws CircuitDescriptionException, FileNotFoundException, IOException {
    parse();
    localComp.get(0).println(".endparty 1");
    localComp.get(1).println(".endparty 2");
    for( PrintStream ps : all ){
      ps.close();
    }
    OutputStream out = System.out;
    for( ByteArrayOutputStream bs : all_out ){
      out.write( bs.toByteArray() );
    }
    out.close();
  }

  public void optimizeVar( VariableInfo v ){
    //GateTranslator gt = new GateTranslator();
  }

  private void print( VariableInfo v ){
    PrintStream choose;
    if( v.getParty() == Input_Variable.ALL ){
      choose = otherComp;
      v.printNeutralChildren(choose);
    } else if( v.getParty() == Input_Variable.NEUTRAL ){
      return;
    } else {
      choose = localComp.get(v.getParty()-1);
      v.printNeutralChildren(choose);
    }
  }
  
  protected VariableInfo computedVariable( String name, OpDirections op, List<VariableInfo> args ) throws CircuitDescriptionException{
    VariableInfo ans;
    if( op instanceof GCParser.Operation.SetOperation ){
      ans = args.get(0);
      ans.inc_references();
    } else {
      ans = VariableInfo.computedVariable( name, op, args );
      print(ans);
    }
    return ans;
  }
  
  protected VariableInfo inputVariable( String name, int party, int bits ) throws CircuitDescriptionException {
    VariableInfo in = new VariableInfo( name, party, ".input "+name+" "+party+" "+bits );
    in.printOn(inputs);
    return in;
  }

  public void removeVar( String key ) {
    PrintStream choose = otherComp;
    try {
      VariableInfo inf = getVar(key);
      if(inf.remove())
	choose.println(".remove "+inf.getName());	
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
