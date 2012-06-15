package frontend;
import java.io.PrintStream;
public class DeclareOutput extends Statement {
  private Variable out;
  public DeclareOutput( int line, Variable var ){
    super( line );
    out = var;
  }

  public void compile() throws CompileException {
    PrintStream os = ProgramTree.output;
    os.println( out.debug_name()+"_output set " + out.cur_name() );
    os.print(".output "+out.debug_name()+"_output" );
    if( out.getType() == Type.IntType ){
      if( ((IntTypeData) out.getData()).signed() )
	os.print(" signed");
      else
	os.print(" unsigned");
    }
    os.println();
  }
}