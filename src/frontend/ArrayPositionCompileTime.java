package frontend;
import java.io.PrintStream;

public class ArrayPositionCompileTime extends ArrayPosition {
  private int pos;
  private boolean changed = false;
  public ArrayPositionCompileTime( ArrayVariable par, int place ){
    super( par );
    pos = place;
  }
  public void read_value(){
    changed = false;
    getParent().state_index( pos, new_name() );
    setData( getParent().getData().getElementData() );
  }
  public boolean is_changed(){
    return changed;
  }
  
  @Override
  public void compile_assignment( Variable other, Statement owner ) throws CompileException {
    changed = true;
    validate();
    ArrayData parentData = getParent().getData();
    if( pos >= parentData.getSize() ){
      throw owner.error( "Index "+pos+" is greater than array length" );
    }
    if( pos < 0 ){
      throw owner.error( "Cannot access a negative array index" );
    }
    if( other.getType() != parentData.getType() ){
      throw owner.error( "Cannot assign type "+other.getType()+" to array of type "+parentData.getType() );
    }
    super.compile_assignment( other, owner );
    // assume that all size adjustments have already been made
  }
}