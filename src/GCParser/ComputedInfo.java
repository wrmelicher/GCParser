package GCParser;

import GCParser.Operation.OpDirections;
import java.io.PrintStream;

class ComputedInfo extends VariableInfo {
  private OpDirections op;
  private VariableInfo[] children;
  public ComputedInfo( String name, OpDirections o, VariableInfo[] c ){
    super( name );
    op = o;
    children = c;
    int temp_party = c[0].getParty();
    for( VariableInfo child : children ){
      child.addParent();
      if( child.getParty() != temp_party && child.getParty() != Input_Variable.NEUTRAL ){
	temp_party = Input_Variable.ALL;
      }
    }
    setParty( temp_party );
  }
  public void print(PrintStream ps){

    for( VariableInfo v : children ){
      v.printSafe();
    }
    String ans = getName()+" "+op.getOp_name();
    for( VariableInfo v : children ){
      ans += " "+v.getName();
    }
    parser.out().println( ans );
    for( int i = 0; i < children.length; i++ ){
      children[i].subParent( ps );
      children[i] = null;
    }
  }
}
