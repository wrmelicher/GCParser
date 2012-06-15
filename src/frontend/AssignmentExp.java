package frontend;

public class AssignmentExp extends ExpressionContainer {
  private Variable dest;
  private String outputName;
  public AssignmentExp( int linenum, Variable adest, Expression asource ){
    super( linenum );
    dest = adest;
    addStatement( asource );
  }
  public Variable returnVar(){
    return dest;
  }
  public void compile() throws CompileException{
    
    Expression source = statements().get(0);
    source.compile();
    Variable sourceVar = source.returnVar();
    if( !dest.getType().equals( sourceVar.getType() ) ){
      throw error( "Variable \""+dest.debug_name()+"\" is not of type "+sourceVar.getType().name());
    }

    dest.compile_assignment( sourceVar, this );

  }
}