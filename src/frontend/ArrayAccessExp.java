package frontend;

import java.io.PrintStream;

public class ArrayAccessExp extends Expression {
  private Variable<IntTypeData> index;
  private ArrayVariable arr;
  private ArrayPosition out;
  public ArrayAccessExp( int linenum, ArrayVariable a, int i ){
    this( linenum, a, new Variable<IntTypeData>( new IntTypeData( i ) ) );
  }
  public ArrayAccessExp( int linenum, ArrayVariable a, Variable<IntTypeData> i ){
    super( linenum );
    index = i;
    arr = a;
  }
  
  public Variable returnVar(){
    return out;
  }
  
  public void compile() throws CompileException {
    out = arr.at( index );
  }
  
}