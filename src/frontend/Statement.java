package frontend;



abstract class Statement {
  private int linenum;
  public Statement( int line ){
    linenum = line;
  }
  public abstract void compile() throws CompileException;

  public CompileException error( String mess ){
    return new CompileException( mess, linenum );
  }

  public int getLine(){
    return linenum;
  }
}