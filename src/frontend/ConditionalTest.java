package frontend;

public class ConditionalTest implements CompilerTest.Compiler {
  
  public static void main( String[] args ) {
    CompilerTest.main( args, new ConditionalTest() );
  }
  public ProgramTree tree() throws CompileException {
    ProgramTree tree = new ProgramTree();

    int linenum = 0;
    
    Variable<IntTypeData> a = new Variable<IntTypeData>
      ("a", new IntTypeData(63,true) );

    Variable<IntTypeData> b = new Variable<IntTypeData>
      ("b", new IntTypeData(63,true) );

    tree.addStatement( new DeclareInputStatement( linenum++, a, 1 ) );
    tree.addStatement( new DeclareInputStatement( linenum++, b, 2 ) );
    
    Variable<IntTypeData> ans = new Variable<IntTypeData>
      ( "ans", new IntTypeData( 0 ) );

    FunctionExp cond = new FunctionExp
      (linenum++, "<", new Expression[] {
	new VariableExp( linenum++, a ),
	new VariableExp( linenum++, b )
      } );

    FunctionExp sub_if = new FunctionExp
      (linenum++, "-", new Expression[] {
	new VariableExp( linenum++, a ),
	new VariableExp( linenum++, b )
      } );

    FunctionExp sub_else = new FunctionExp
      (linenum++, "-", new Expression[] {
	new VariableExp( linenum++, b ),
	new VariableExp( linenum++, a )
      } );

    IfExpression if_exp = new IfExpression
      (linenum++, cond,
       new AssignmentExp(linenum++, ans, sub_if),
       new AssignmentExp(linenum++, ans, sub_else) );

    tree.addStatement( if_exp );
    
    tree.addStatement( new DeclareOutput( linenum++, ans ) );
    
    return tree;
  }
}