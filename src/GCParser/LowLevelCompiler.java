package GCParser;

import java.io.*;
import java.util.*;
import GCParser.Operation.OpDirections;
import GCParser.Operation.CircuitDescriptionException;
import YaoGC.*;

public class LowLevelCompiler extends ExecutingParser {
  private PrintStream out;
  private long wires_num = 0;
  private long high = newWire();
  private long low = newWire();
  
  public LowLevelCompiler( File f, InputStream i ) throws FileNotFoundException {
    super(f,i);
    out = new PrintStream( new FileOutputStream( new File(f.getName()+".gate") ) );
  }

  protected LowLevelCompiler( File f, InputStream s, LowLevelCompiler p ) throws IOException {
    super( f, s, p );
    out = p.out;
  }

  public long newWire(){
    return ++wires_num;
  }

  public long high(){
    return high;
  }

  public long low(){
    return low;
  }

  public static void fromFileComp( File f ) throws FileNotFoundException, CircuitDescriptionException, IOException {
    FileInputStream fis = new FileInputStream(f);
    LowLevelCompiler low = new LowLevelCompiler( f, fis );
    low.execute_streaming = true;
    SimpleCircuit_2_1.printer = low;
    Circuit.isForGarbling = true;
    low.readInputs();

    low.printConsts();

    low.read();
    fis.close();
  }

  public enum Gate {
    AND, OR, XOR
  }

  private static Map<String, Gate> nameMap =
    new TreeMap<String, Gate>();

  static{
    nameMap.put("OR_2_1",Gate.OR);
    nameMap.put("OR_2_1",Gate.OR);
    nameMap.put("G_AND_2_1",Gate.AND);
    nameMap.put("E_AND_2_1",Gate.AND);
    nameMap.put("XOR_2_1",Gate.XOR);
  }

  public static Gate fromName( String name ){
    return nameMap.get(name);
  }
  
  protected void setPartyComp( int i ) {
    super.setPartyComp(i);
    try{
      printLocal( partyComp() );
    } catch (IOException e ){
      System.err.println(e.getMessage());
      System.exit(1);
    }
  }

  private void printLabel( long lab ) throws IOException {
    out.print("t"+lab);
  }

  private enum Mode {
    CONSTANT,
    COMP,
    INPUT,
    LOCALSTART,
    LOCALEND,
    OUTPUT,
    REMOVE;
    
  }

  public void printMode( Mode m ) throws IOException {
    switch( m ){
    case LOCALSTART:
      out.print(".startparty ");
      break;
    case LOCALEND:
      out.print(".endparty");
      break;
    case INPUT:
      out.print(".input ");
      break;
    case REMOVE:
      out.print(".remove ");
      break;
    case OUTPUT:
      out.print(".output ");
      break;
    default:
      break;
    }
  }


  private void printValue( int i ) throws IOException {
    out.print(" set ");
    out.print(i+":1");
  }

  private void endCmd() throws IOException {
    out.println();
  }

  private void printConsts() throws IOException {
    printMode( Mode.CONSTANT );
    printLabel( high() );
    printValue( 1 );
    endCmd();

    printMode( Mode.CONSTANT );
    printLabel( low() );
    printValue( 0 );
    endCmd();
  }
  
  public void printInput( long label, int party ) throws IOException {
    printMode( Mode.INPUT );
    printLabel( label );
    out.print( " " + party + " 1" );
    endCmd();
  }

  public void printLocal( int party ) throws IOException {
    if( party == Input_Variable.ALL ){
      printMode( Mode.LOCALEND );
      endCmd();
    } else {
      printMode( Mode.LOCALSTART );
      out.println(party);
    }
  }

  protected Variable inputVariable( String name, int party, int bits ) throws CircuitDescriptionException {
    Variable ans = super.inputVariable( name, party, bits );
    State.StaticWire[] ws = new State.StaticWire[bits];
    for( int i = 0; i < bits; i++ ){
      ws[i] = new State.StaticWire(Wire.UNKNOWN_SIG);
      try{
	printInput( ws[i].printLabel, ans.getParty() );
      } catch( IOException e ){
	System.err.println(e.getMessage());
	System.exit(1);
      }
    }
    State st = new State( ws );
    ((Input_Variable)ans).setState( st );
    return ans;
  }

  protected void addOutput( Variable val, OutputFormat signed ) throws CircuitDescriptionException {
    super.addOutput( val, signed );
    try{
      State st = val.execute();
      for( State.StaticWire w : st.wires ){
	printMode( Mode.OUTPUT );
	printLabel( w.printLabel );
	endCmd();
      }
    } catch( Exception e ){
      
    }
  }

  public void removeVar( String key ){
    try {
      Variable inf = getVar(key);
      State s = inf.execute();
      for( State.StaticWire w : s.wires ){
	w.num_pointers--;
	if( w.num_pointers == 0 ){
	  printMode( Mode.REMOVE );
	  printLabel( w.printLabel );
	  endCmd();
	}
      }
    } catch( Exception e ){

    }
    super.removeVar( key );
  }

  private void printGate( Gate g ){
    out.print(" ");
    switch( g ){
    case AND:
      out.print("and");
      break;
    case OR:
      out.print("or");
      break;
    case XOR:
      out.print("xor");
      break;
    }
    out.print(" ");
  }

  public void printComp( long label, String gate, long one, long two ) {
    Gate g = fromName(gate);
    try{
      printMode( Mode.COMP );
      printLabel( label );
      printGate( g );
      printLabel( one );
      out.print(" ");
      printLabel( two );
      endCmd();
    } catch(IOException e){
      System.err.println(e.getMessage());
      System.exit(1);
    }
  }

  protected ExecutingParser child( File f ) throws FileNotFoundException, IOException {
    FileInputStream io = new FileInputStream(f);
    return new LowLevelCompiler( f, io, this );
  }
}
