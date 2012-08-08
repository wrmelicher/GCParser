package GCParser;
import java.io.PrintStream;
public abstract class VariableInfo {
  private boolean alreadyPrint = false;
  private String name;
  private int parents = 0;
  private int party;
  protected static OptimizingParser parser;
  public VariableInfo( String n ){
    name = n;
  }

  public void addParent(){
    parents += 1;
  }

  public void setParty( int i ){
    party = i;
  }
  
  public int getParty(){
    return party;
  }

  public void subParent( PrintStream ps ){
    parents -= 1;
    if( parents == 0 && ( this instanceof ComputedInfo ) ){
      ps.println(".remove "+getName());
    }
  }
  
  public String getName(){
    return name;
  }

  public void printSafe(){
    if( !alreadyPrint ){
      print();
      alreadyPrint = true;
    }
  }
  public int hashCode(){
    return getName().hashCode();
  }
  
  public void print(){}
}
