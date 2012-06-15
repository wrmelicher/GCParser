package frontend;

import java.util.List;
import java.io.PrintStream;

class ForStatement extends ExpressionContainer {
  private Variable<IntTypeData> loop_var;
  private int from;
  private int to;
  private Expression incExp;
  private Variable out;
  public ForStatement( int line, int lower, int upper, String loop_name ){
    super( line );
    from = lower;
    to = upper;
    loop_var = new Variable<IntTypeData>( loop_name, new IntTypeData( from ) );
    
    FunctionExp incFuncExp = new FunctionExp
      ( getLine(), "++", new Expression[] { new VariableExp( getLine(), loop_var ) } );

    incExp = new AssignmentExp( getLine(), loop_var, incFuncExp );
  }
  public Variable<IntTypeData> getLoopVar(){
    return loop_var;
  }
  private void compile_one_iteration() throws CompileException {
    for( Expression s : statements() ){
      s.compile();
      out = s.returnVar();
      incExp.compile();
    }
  }
  public Variable returnVar(){
    return out;
  }
  public void compile() throws CompileException {
    for( int i = from; i < to; i++ ){
      compile_one_iteration();
    }
  }

  
}