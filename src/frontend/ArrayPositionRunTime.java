package frontend;
import java.io.PrintStream;

import java.lang.Math;
public class ArrayPositionRunTime extends ArrayPosition {
  private Variable<IntTypeData> index;
  public ArrayPositionRunTime( ArrayVariable par, Variable<IntTypeData> ind ){
    super( par );
    index = ind;
  }
  public void read_value() {
    getParent().join_indices();
    validate();
    String input = getParent().cur_name();
    int num_elements = getParent().getData().getSize();
    int element_size = getParent().getData().getElementData().bit_count();

    PrintStream ps = ProgramTree.output;
    
    if( !is_power_of_2( num_elements ) ){
      String old = input;
      input = Variable.temp_var_name();

      ps.println( input + " zextend " + old + " " + (next_power_of_2(num_elements)*element_size ) );
      num_elements = next_power_of_2( num_elements );
    }
    int required_control_bits = (int)Math.round( Math.log( num_elements ) / Math.log( 2.0 ) );

    String control = index.cur_name();
    if( required_control_bits > index.getData().bit_count() ){
      control = Variable.temp_var_name();
      ps.println( control + " sextend " + index.cur_name() +" "+required_control_bits);
    } else if( required_control_bits < index.getData().bit_count() ){
      control = Variable.temp_var_name();
      ps.println( control + " trunc " + index.cur_name() + " " + required_control_bits );
    }
    read_helper( input, control, required_control_bits - 1, num_elements );
  }

  private static int next_power_of_2( int i ){
    int k = 1;
    while( k < i ){
      k = k << 1;
    }
    return k;
  }

  private static boolean is_power_of_2( int i ){
    return 2*i == ( i ^ (i-1) + 1 );
  }
  
  private void read_helper( String cur_in, String cur_control, int control_bit_position, int num_elements ){
    PrintStream ps = ProgramTree.output;
    int element_size = getParent().getData().getElementData().bit_count();
    String control_bit = Variable.temp_var_name();
    ps.println( control_bit + " select "+ cur_control +" "+control_bit_position+" "+(control_bit_position + 1 ) );

    String lower = Variable.temp_var_name();
    ps.println( lower + " select " + cur_in + " 0 " + (element_size*(num_elements/2)) );
    String higher = Variable.temp_var_name();
    ps.println( higher + " select "+cur_in +" " + (element_size*num_elements/2) + " "+num_elements*element_size);
    String out_name = num_elements == 2 ? new_name() : Variable.temp_var_name();
    ps.println( out_name + " chose " + control_bit + " " + lower + " " + higher );

    if( num_elements != 2 ){
      read_helper( out_name, cur_control, control_bit_position - 1, num_elements / 2 );
    }
  }

  @Override
  public void compile_assignment( Variable other, Statement owner ) throws CompileException {
    getParent().join_indices();
    if( Expression.cond_scope != null ){
      Expression.cond_scope.register_assignment( getParent() );
    }

    PrintStream ps = ProgramTree.output;

    // assume that all size adjustments have already been made
    ArrayData parentData = getParent().getData();
    String[] mux_out_names = new String[ parentData.getSize() ];
    Variable[] args = new Variable[2];
    args[0] = index;
    String other_name = other.padTo( getParent().element_size() );
    for( int i = 0; i < parentData.getSize(); i++){
      String select_name = getParent().state_index( i );

      args[1] = new Variable( new IntTypeData( i ) ); 
      Variable mux_choice = Function.call( "==", args, owner );
      
      mux_out_names[i] = Variable.temp_var_name();
      ps.println( mux_out_names[i]+" chose "+mux_choice.cur_name()+" "+select_name+" " + other_name );
    }
    ps.print( getParent().new_name() + " concat");
    for( int i = 0; i < parentData.getSize(); i++){
      ps.print( " "+mux_out_names[i] );
    }
    ps.println();

  }
}