package frontend;

import java.io.PrintStream;

public abstract class ArrayPosition extends Variable {
  private ArrayVariable parent;
  private boolean is_valid;
  public ArrayPosition( ArrayVariable par ){
    super( par.debug_name()+"_access", par.getData().getElementData() );
    parent = par;
  }

  public String cur_name(){
    if( !is_valid ){
      read_value();
    }
    return super.cur_name();

  }
  public boolean is_valid(){
    return is_valid;
  }
  
  public void invalidate(){
    is_valid = false;
  }
  public void validate(){
    is_valid = true;
  }
  
  public abstract void read_value();
  public ArrayVariable getParent() {
    return parent;
  }

  /*  public void compile_assignment( Variable other, AssignmentExp owner ) throws CompileException {
    ArrayData parentData = parent.getData();

    String other_name;
    // expand size
    if( other.getData().bit_count() > parentData.getElementData().bit_count() ){
      // must resize elements
      extend_size( other.getData().bit_count() );
      other_name = other.cur_name();
    } else if( other.getData().bit_count() < parentData.getElementData().bit_count() ){
      other_name = other.padTo( parentData.getElementData().bit_count() );
    } else {
      other_name = other.cur_name();
    }
    compile_assignment( other_name, owner );
    }*/
    
  
  /*  private void extend_size( int to ){
    // TODO adjust typedata when expanding
    
    PrintStream ps = ProgramTree.output;
    ArrayData parentData = parent.getData();
    String[] before_extends = new String[ parentData.getSize() ];
    
    for( int i = 0; i < parentData.getSize(); i++){
      
      String select_name = parent.state_index( i );
      before_extends[i] = Variable.temp_var_name();
      ps.println( before_extends[i] + " " + getData().extend_operation() + " " + select_name + " " + to );
    }
    
    ps.print( parent.new_name() + " concat" );
    for( int i = 0; i < parentData.getSize(); i++ ){
      ps.print( " " + before_extends[i] );
    }
    ps.println();

    parent.invalidate_indices();
    }*/
}