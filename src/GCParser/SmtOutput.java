package GCParser;

import java.io.*;
import java.util.*;
import GCParser.Operation.OpDirections;
import GCParser.Operation.CircuitDescriptionException;
import YaoGC.*;

public class SmtOutput extends CircuitParser<Variable> {
  private PrintStream out;

  public SmtOutput( File f, InputStream i ) throws FileNotFoundException {
    super(f,i);
    out = new PrintStream( new FileOutputStream( new File(f.getName()+".smt2") ) );
  }

  protected SmtOutput( File f, InputStream s, SmtOutput p ) throws IOException {
    super( f, s, p );
    out = p.out;
  }

  public static void fromFileComp( File f ) throws FileNotFoundException, CircuitDescriptionException, IOException {
    FileInputStream fis = new FileInputStream(f);
    SmtOutput out = new LowLevelCompiler( f, fis );
    low.execute_streaming = true;
    low.readInputs();
    low.printConsts();
    low.read();
    fis.close();
  }
  
  protected void header(){
    out.println("(set-option :produce-models true)\
(set-info :smt-lib-version 2.0)					\
(define-fun if ((cond Bool) (a Int) (b Int) (ans Int)) Bool\
 (and (or (not cond) (= ans a)) (or cond (= ans b))))");
  }

  protected void footer(){
    out.println("(check-sat)\
(exit)");
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

    protected abstract void include( File fname, Map<String,T> inMap, Map<String,String> outMap )
      throws CircuitDescriptionException, FileNotFoundException, IOException ;


  protected ExecutingParser child( File f ) throws FileNotFoundException, IOException {
    FileInputStream io = new FileInputStream(f);
    return new LowLevelCompiler( f, io, this );
  }
}
