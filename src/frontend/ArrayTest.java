package frontend;

public class ArrayTest implements CompilerTest.Compiler {

  public static void main( String[] args ){
    CompilerTest.main( args, new ArrayTest() );
  }

  public ProgramTree tree() throws CompileException {
    ProgramTree tree = new ProgramTree();

    return tree;
  }
}