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
    for( VariableInfo child : children ){
      child.addParent();
    }
  }
  public void print(PrintStream ps){

    for( VariableInfo v : children ){
      v.printSafe(ps);
    }
    String ans = getName()+" "+op.getOp_name();
    for( VariableInfo v : children ){
      ans += " "+v.getName();
    }
    ps.println( ans );
    for( int i = 0; i < children.length; i++ ){
      children[i].subParent( ps );
      children[i] = null;
    }
  }
}
