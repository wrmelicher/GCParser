package frontend;
import java.io.PrintStream;
import java.io.File;
import java.util.Scanner;
import java.util.List;
import java.io.FileNotFoundException;

public abstract class CompilerTest {
  private static ProgramTree t;
  private static String base_name;

  public interface Compiler {
    public ProgramTree tree() throws CompileException;
  }
  
  public static void main( String[] args, Compiler c ) {
    if( args.length < 1 ){
	System.out.println("usage: java CompilerTest outname" );
      System.exit(1);
    }
    try{
      t = c.tree();
    } catch ( CompileException e ){
      System.err.println( e.getMessage() );
      System.exit(1);
    }
    base_name = args[0];
    inputs();
    try {
    ProgramTree.output = new PrintStream( new File( base_name+".cir" ) );
    } catch ( FileNotFoundException e ){
      System.err.println( e.getMessage() );
      System.exit(1);
    }
    try {
    t.compile();
    } catch ( CompileException e ){
      System.err.println( e.getMessage() );
      System.exit(1);
    }
  }

  public static void inputs() {
    try {
    List<DeclareInputStatement> ls = t.inputs();
    PrintStream client_inputs = new PrintStream( new File( base_name+"_client.priv" ) );
    PrintStream server_inputs = new PrintStream( new File( base_name+"_server.priv" ) );
    Scanner in = new Scanner( System.in );
    for( DeclareInputStatement d : ls ){
      d.request_val( d.party() == 1 ? client_inputs : server_inputs, in );
    }
    client_inputs.close();
    server_inputs.close();
    } catch (FileNotFoundException e ){
      System.err.println( e.getMessage() );
      System.exit(1);
    }
  }
}