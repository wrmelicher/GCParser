package frontend;

public class ASTTest implements CompilerTest.Compiler {
  
  public static void main( String[] args ){
    CompilerTest.main( args, new ASTTest() );
  }

  public ProgramTree tree() throws CompileException{
    ProgramTree tree = new ProgramTree();

    int size = 4;
    int int_size = 255;
    int linenum = 0;
    Variable<IntTypeData> ind = new Variable<IntTypeData>
      ("ind", new IntTypeData( size-1, false ) );
    
    ArrayVariable arr2 = new ArrayVariable
      ( "arr2", new ArrayData
	(new IntTypeData( int_size, false ), size) );
    
    tree.addStatement( new DeclareInputStatement( linenum++, ind, 1 ) );
    tree.addStatement( new DeclareInputStatement( linenum++, arr2, 2 ) );

    tree.addStatement( new AssignmentExp
		       ( linenum++,
			 arr2.at( ind ),
			 new VariableExp
			 ( linenum++,
			   new Variable<IntTypeData>( new IntTypeData(0) ) ) ) );
    
    tree.addStatement( new DeclareOutput( linenum++, arr2 ) );
    
    return tree;
  }
}