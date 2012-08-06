package GCParser;

import java.io.PrintStream;

public class InputInfo extends VariableInfo {
  private int bits;
  private int party;
  public InputInfo( String n, int aparty, int bitcount ){
    super(n);
    party = aparty;
    bits = bitcount;
  }
  public void print(PrintStream ps){
    ps.println( ".input "+getName()+" "+party+" "+bits);
  }
}
