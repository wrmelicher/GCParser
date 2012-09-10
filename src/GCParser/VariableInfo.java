package GCParser;

import java.util.LinkedList;
import java.util.List;
import java.util.HashSet;
import java.util.Set;
import java.io.PrintStream;
import GCParser.Operation.OpDirections;

public class VariableInfo {
  private String name;
  private int party;
  private Set<PrintStream> beenPrinted = new HashSet<PrintStream>();
  private String printOut;
  private List<VariableInfo> parents = new LinkedList<VariableInfo>();
  private List<VariableInfo> children;
  private int references = 1;
  public VariableInfo( String aName, int aParty, String print ){
    name = aName;
    party = aParty;
    printOut = print;
    children = new LinkedList<VariableInfo>();
  }
  public static VariableInfo computedVariable( String name, OpDirections op, List<VariableInfo> args ){
    int party = Input_Variable.NEUTRAL;
    String line = name+" "+op.getOp_name();
    for( VariableInfo inf : args ){
      if( inf.getParty() != Input_Variable.NEUTRAL ){
	if( party == Input_Variable.NEUTRAL ){
	  party = inf.getParty(); 
	} else if( party != inf.getParty() ){
	  party = Input_Variable.ALL;
	}
      }
      line += " "+inf.getName();
    }
    VariableInfo ans = new VariableInfo( name, party, line );
    for( VariableInfo inf : args ){
      inf.addParent(ans);
    }
    return ans;
  }

  private String definition(){
    return printOut;
  }

  public void inc_references(){
    references += 1;
  }

  public void printOn( PrintStream ps ){
    if( !definition().equals("") ){
      ps.println(definition());
      beenPrinted.add(ps);
    }
  }

  public void addParent( VariableInfo i ){
    parents.add(i);
    i.children.add(this);
  }

  public String getName(){
    return name;
  }

  public int getParty(){
    return party;
  }

  public void printNeutralChildren(PrintStream ps){
    if( beenPrinted.contains(ps) )
      return;
    if( children != null ){
      for( VariableInfo child : children ){
	if( child.getParty() == Input_Variable.NEUTRAL ){
	  child.printNeutralChildren(ps);
	}
      }
    }
    printOn(ps);
  }

  public boolean remove(){
    references--;
    if( references > 0 )
      return false;
    
    children = null;
    for( VariableInfo parent : parents ){
      if( getParty() != Input_Variable.NEUTRAL && parent.children != null )
	parent.children.remove(this);
    }
    parents = null;
    return true;
  }
}
