// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import GCParser.*;
import GCParser.Operation.OpCircuitUser;
import YaoGC.*;
import Utils.*;

import java.math.*;
import java.util.*;

public class GCParserClient extends ProgClient {
  private Map<String, State> outputState, inputState;
  private Map<String,BigInteger> outValues;
  private GCParserCommon gccom;

  public GCParserClient( GCParserCommon GCCOM ){
    gccom = GCCOM;
    outValues = null;
    inputState = new HashMap<String,State>();
  }
  protected void init() throws Exception {
    gccom.parseInputs( Input_Variable.CLIENT );
    otNumOfPairs = gccom.context().getBitsOfParty(Input_Variable.CLIENT);
    super.init();
  }
  /*
  public void reset(){
    gccom.reset();
    outValues = null;
    }*/
  // public void reset( PrivateInputProvider p ){
  //   gccom.setPIP(p);
  //   reset();
  // }

  protected void execTransfer() throws Exception {
    int bytelength = (Wire.labelBitLength-1)/8 + 1;

    Input_Variable[] order = new Input_Variable
      [ gccom.context().getNumVarsOfParty( Input_Variable.CLIENT ) ];
    BigInteger clientValues = BigInteger.ZERO;
    int bit = 0;
    int clientIndex = 0;
    // exchange labels
    for( int i = 0; i < gccom.context().getInputs().size(); i++ ){
      String varid = (String) GCParserCommon.ois.readObject();
      Input_Variable var = gccom.context().getInVar(varid);

      if( var.getParty() == Input_Variable.CLIENT ){ 
	// client private input
	BigInteger val = State.toBigInteger(var.execute());
	if( val == null ){
	  throw new Exception("Variable \""+varid+"\" not defined in private input file");
	}
	for( int offset = 0; offset < var.bitcount ; offset++ ){
	  if( val.testBit( offset ) )
	    clientValues = clientValues.setBit( bit+offset );
	}
	order[clientIndex++] = var;
	bit += var.bitcount;
      } else { 
	// server private input
	BigInteger[] lbs = new BigInteger[var.bitcount];
	for( int servBit = 0; servBit < lbs.length ; servBit++ ){
	  lbs[servBit] = Utils.readBigInteger(bytelength, GCParserCommon.ois);
	}
	// initialize variable
	inputState.put( varid, State.fromLabels(lbs) );
      }
    }
    
    // transfer client input labels
    rcver.execProtocol( clientValues );
    BigInteger[] clientLps = rcver.getData();
    State clientState = State.fromLabels( clientLps );
    
    // initialize client variables
    bit = 0;
    for( int i = 0; i < order.length; i++ ){
      Input_Variable var = order[i];
      inputState.put( order[i].getId(), State.extractState( clientState, bit, bit+var.bitcount ) );
      bit += var.bitcount;
    }
  }

  protected void execCircuit() throws Exception {
    int serverk = GCParserCommon.ois.readInt();
    GCParserCommon.oos.writeInt( Wire.K );
    GCParserCommon.oos.flush();
    Wire.K = Math.max( Wire.K, serverk );
    OpCircuitUser.clear_circuit_cache();
    StopWatch.taskTimeStamp("transfer inputs");
    gccom.context().setInVals( inputState );
    gccom.parseCircuit();
    outputState = gccom.context().execCircuit();
    StopWatch.taskTimeStamp("execution of circuit");
  }
  public Map<String,BigInteger> getOutputValues() throws Exception {
    if( outValues != null )
      return outValues;
    Iterator<String> it = outputState.keySet().iterator();
    while( it.hasNext() ){
      String id = it.next();
      GCParserCommon.oos.writeObject( id );
      State valState = outputState.get(id);
      BigInteger[] labels = valState.toLabels();
      GCParserCommon.oos.writeObject( labels );
    }
    GCParserCommon.oos.flush();
    outValues = (Map<String,BigInteger>) GCParserCommon.ois.readObject();
    return outValues;
    
  }

  protected void interpretResult() throws Exception {
    System.out.println("output: ");
    Map<String,BigInteger> values = getOutputValues();
    for( String id : values.keySet() ){
      OutputFormat fmt = gccom.context().getOutputFormat( id );
      System.out.println(id+" = "+fmt.printFormat(values.get(id)));
    }
    GCParserCommon.printCircuitUsage();
  }

  protected void verify_result(){}
}
