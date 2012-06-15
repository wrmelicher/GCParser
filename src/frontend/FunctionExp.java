package frontend;
import java.io.PrintStream;

import java.util.List;
import java.util.LinkedList;

public class FunctionExp extends ExpressionContainer {
  private String name;
  private Variable outvar;
  public FunctionExp( int line, String afunc ){
    super( line );
    name = afunc;
  }
  public FunctionExp( int line, String afunc, Expression[] args ){
    this( line, afunc );
    for( Expression e : args ){
      addStatement( e );
    }
  }
  public Variable returnVar(){
    return outvar;
  }
  public void compile() throws CompileException {
    Variable[] vargs = new Variable[ statements().size() ];
    int i = 0;
    for( Expression e : statements() ){
      e.compile();
      vargs[i++] = e.returnVar();
    }
    outvar = Function.call( name, vargs, this );
  }

}