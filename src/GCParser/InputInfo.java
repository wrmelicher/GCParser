package GCParser;

import java.io.PrintStream;

public class InputInfo extends VariableInfo {
  private int bits;
  public InputInfo( String n, int aparty, int bitcount ){
    super(n);
    setParty( aparty );
    bits = bitcount;
  }
  public void print(){
    parser.out().println( ".input "+getName()+" "+getParty()+" "+bits);
  }
}
