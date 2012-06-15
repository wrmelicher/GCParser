package frontend;

import java.io.PrintStream;

public abstract class Expression extends Statement {

  protected static IfExpression cond_scope = null;
  
  public Expression( int line ){
    super( line );
  }
  
  public abstract void compile() throws CompileException;
  public abstract Variable returnVar();
}