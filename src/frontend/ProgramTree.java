package frontend;

import java.util.List;
import java.util.ArrayList;
import java.io.PrintStream;

public class ProgramTree {

  private List<Statement> statements;
  private List<DeclareInputStatement> inputs;
  private List<DeclareOutput> outputs;

  public static PrintStream output = System.out;
  public static PrintStream error = System.err;

  // 1 means function identification debuging
  public static int DEBUG = 1;
  
  public ProgramTree(){
    statements = new ArrayList<Statement>();
    inputs = new ArrayList<DeclareInputStatement>();
    outputs = new ArrayList<DeclareOutput>();
  }
  
  public void compile() throws CompileException{
    // inputs and stuff
    compile_list( inputs );
    compile_list( statements );
    compile_list( outputs );
  }
  
  private void compile_list( List<? extends Statement> l ) throws CompileException{
    for( Statement s : l ){
      s.compile();
    }
  }
  
  public void addStatement( Statement s ){
    if( s instanceof DeclareOutput )
      outputs.add( (DeclareOutput)s );
    else if( s instanceof DeclareInputStatement )
      inputs.add( (DeclareInputStatement)s );
    else 
      statements.add( s );
  }

  public List<DeclareInputStatement> inputs(){
    return inputs;
  }
  
  public List<DeclareOutput> outputs() {
    return outputs;
  }
}