package frontend;

public class MinSumTest implements CompilerTest.Compiler {

  public static void main( String[] args ){
    CompilerTest.main( args, new MinSumTest() );
  }

  
  public ProgramTree tree() throws CompileException {
    ProgramTree tree = new ProgramTree();

    int size = 4;
    int int_size = 31;
    int linenum = 0;
    
    ArrayVariable arr1 = new ArrayVariable
      ("arr1", new ArrayData( new IntTypeData( 127, false ), size ) );
    ArrayVariable arr2 = new ArrayVariable
      ("arr2", new ArrayData( new IntTypeData( int_size, false ),size ) );

    Variable<IntTypeData> minsum = new Variable<IntTypeData>("minsum",new IntTypeData( 0 ) );

    tree.addStatement( new DeclareInputStatement( linenum++, arr1, 1 ) );
    tree.addStatement( new DeclareInputStatement( linenum++, arr2, 2 ) );
    
    ForStatement for_s = new ForStatement( linenum++, 0, size, "i" );

    FunctionExp lessthanExp = 
      new FunctionExp( linenum++, "<", new Expression[] {
	  new ArrayAccessExp( linenum++, arr1, for_s.getLoopVar() ),
	  new ArrayAccessExp( linenum++, arr2, for_s.getLoopVar() )
	} );

    FunctionExp condition = 
      new FunctionExp( linenum++, "if", new Expression[] {
	  lessthanExp,
	  new ArrayAccessExp( linenum++, arr1, for_s.getLoopVar() ),
	  new ArrayAccessExp( linenum++, arr2, for_s.getLoopVar() )
	} );
        
    AssignmentExp in_loop = new AssignmentExp
      ( linenum++, minsum, new FunctionExp( linenum++, "+", new Expression[] {
	  condition,
	  new VariableExp( linenum++, minsum )
	} ) );

    for_s.addStatement( in_loop );
    tree.addStatement( for_s );
    
    tree.addStatement( new DeclareOutput( linenum++, minsum ) );
    
    return tree;
  }
}