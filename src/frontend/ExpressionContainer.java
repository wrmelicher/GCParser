package frontend;

import java.util.List;
import java.util.LinkedList;

public abstract class ExpressionContainer extends Expression {
  private List<Expression> statements;
  public ExpressionContainer( int line ){
    super( line );
    statements = new LinkedList<Expression>();
  }
  public void addStatement( Expression s ){
    statements.add( s );
  }
  public List<Expression> statements(){
    return statements;
  }
  public abstract void compile() throws CompileException;
  public abstract Variable returnVar();
}