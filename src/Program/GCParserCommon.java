// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import GCParser.*;
import GCParser.Operation.*;
import Utils.*;
import YaoGC.*;

import java.math.*;
import java.io.*;
import java.util.*;

public class GCParserCommon extends ProgCommon{
  
  private static boolean profile_count = SimpleCircuit_2_1.profile_count;

  private ExecutingParser parser;
  private File desc;
  private PrivateInputProvider pip;

  public GCParserCommon( File DESC, PrivateInputProvider PIP ){
    desc = DESC;
    pip = PIP;
  }
  public void parseInputs( int party ) throws Exception {
    try {
      parser = ExecutingParser.fromFile( desc );
      parser.readInputs();
    } catch (CircuitDescriptionException e) {
      System.out.println(e.getMessage()+"...Exiting");
      System.exit(1);
    } catch( Exception e ){
      System.out.println(e.getMessage()+"...Exiting");
      e.printStackTrace();
      System.exit(1);
    }
    Map<String,BigInteger> privIns = getPrivateInputs(party);
    context().collapseLocalVars( privIns, party );

  }
  public void parseCircuit() throws Exception {
    try {
      OpCircuitUser.doneWithLocalComp();
      parser.read();
    } catch (CircuitDescriptionException e) {
      System.out.println(e.getMessage()+"...Exiting");
      System.exit(1);
    }
  }

    
  public Variable_Context context(){
    return parser.context();
  }

  // public void reset(){
  //   context().resetCircuit();
  // }
  public void setPIP( PrivateInputProvider PIP ){
    pip = PIP;
  }
  public Map<String,BigInteger> getPrivateInputs(int party) throws Exception {
    Iterator<Input_Variable> it = context().getPrivInOfParty(party).iterator();
    Map<String, Input_Variable> requested = new HashMap<String, Input_Variable>();
    while( it.hasNext() ) {
      Input_Variable var = it.next();
      requested.put( var.getId(), var );
    }

    Map<String, BigInteger> provided = pip.privateInputs( requested );
    if( ! provided.keySet().containsAll( requested.keySet() ) ){
      Set<String> undefined = requested.keySet();
      undefined.removeAll( provided.keySet() );
      String error = "The following private variables are undefined: ";
      Iterator<String> errIt = undefined.iterator();
      while( errIt.hasNext() ){
	error += "\""+errIt.next()+"\", ";
      }
      error += "...Exiting";
      throw new Exception( error );
    }
    return provided;
  }


  private static String intToCircuitName( int i ){
    String name;
    switch(i){
    case OpCircuitUser.AND:
      name = "AND";
      break;
    case OpCircuitUser.OR:
      name = "OR";
      break;
    case OpCircuitUser.XOR:
      name = "XOR";
      break;
    default:
      name = "OTHER";
    }
    return name;
  }

  private static void printCircuitUsage( boolean local ){
    System.out.println("Elementary circuits computed"+ ( local ? " locally" : "") + ":");
    for( int i = 0; i < 3; i++ ){
      String name = intToCircuitName( i );
      System.out.println( name+": "+OpCircuitUser.get_executed_num(i, local) );
    }
  }
  private static void printCircuitUsage( ArrayList<Long> data ){
    for( int i = 0; i < 3; i++ ){
      String gateName = intToCircuitName( i );
      System.out.println( gateName + ": " + data.get(i) );
    }
  }
  
  public static void printCircuitUsage(){
    if( !profile_count )
      return;
    printCircuitUsage( true );
    printCircuitUsage( false );
    Map<String, ArrayList<Long> > profileInfo = OpCircuitUser.getProfileInfo();
    for( String key : profileInfo.keySet() ){
      System.out.println("Circuits for "+key);
      printCircuitUsage( profileInfo.get(key) );
    }
  }
}
