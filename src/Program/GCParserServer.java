// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Program;

import YaoGC.*;
import Utils.*;
import GCParser.Input_Variable;
import GCParser.Operation.OpCircuitUser;
import GCParser.OutputFormat;

import java.math.*;
import java.util.*;

public class GCParserServer extends ProgServer {
  
  private Map<String,State> outputState, inputState;
  private Map<String,BigInteger> outValues;
  private GCParserCommon gccom;
  public GCParserServer( GCParserCommon GCCOM ){
    gccom = GCCOM;
    inputState = new HashMap<String,State>();
    outValues = null;
  }
  protected void init() throws Exception {
    gccom.parseInputs( Input_Variable.SERVER );
    super.init();
  }

  protected BigInteger[][] generateNLabelPairs( int bits ){
    BigInteger[][] lbs = new BigInteger[ bits ][2];
    for( int i = 0; i < bits; i++ ){
      lbs[i] = Wire.newLabelPair();
    }
    return lbs;
  }
  /*
  public void reset(){
    outValues = null;
    gccom.reset();
    }
  public void reset( PrivateInputProvider p ){
    gccom.setPIP(p);
    reset();
    }*/

  protected void execTransfer() throws Exception {
    int bytelength = (Wire.labelBitLength-1)/8 + 1;

    BigInteger[][] clientLps = new BigInteger
      [gccom.context().getBitsOfParty(Input_Variable.CLIENT)][2];
    int bits = 0;
    // exchange labels
    Iterator<String> it = gccom.context().getInputs().iterator();
    while( it.hasNext() ){
      String varid = it.next();
      Input_Variable var = gccom.context().getInVar(varid);
      GCParserCommon.oos.writeObject(varid);
      BigInteger[][] lps = generateNLabelPairs(var.bitcount);

      if( var.getParty() == Input_Variable.CLIENT ){ 
	// client private inputs
	for(int i = 0; i < var.bitcount; i++ ){
	  clientLps[bits+i] = lps[i];
	}
	bits += var.bitcount;
      } else { 
	// server private inputs
	BigInteger val = State.toBigInteger(var.execute());
	if( val == null ){
	  throw new Exception("Variable \""+varid+"\" not defined in private input file");
	}
	for( int bit = 0; bit < var.bitcount; bit++ ){
	  int index = val.testBit(bit) ? 1 : 0;
	  Utils.writeBigInteger( lps[bit][index], bytelength, GCParserCommon.oos);
	}
      }
      // initialize variable
      BigInteger[] lbs = new BigInteger[ lps.length ];
      for( int i = 0; i < lps.length; i++ ){
	lbs[i] = lps[i][0];
      }
      State put = State.fromLabels(lbs);
      inputState.put( varid, put );
    }
    GCParserCommon.oos.flush();
    snder.execProtocol( clientLps );
  }

  protected void execCircuit() throws Exception {
    GCParserCommon.oos.writeInt( Wire.K );
    GCParserCommon.oos.flush();
    int clientk = GCParserCommon.ois.readInt();
    Wire.K = Math.max( Wire.K, clientk );

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
    outValues = new HashMap<String,BigInteger>();
    for( int i = 0; i < outputState.size(); i++ ){
      String id = (String) GCParserCommon.ois.readObject();
      BigInteger[] lbs = (BigInteger[]) GCParserCommon.ois.readObject();
      BigInteger val = gccom.context().getOutputFormat( id ).interpret( outputState.get(id), lbs );
      outValues.put( id, val );
    }
    GCParserCommon.oos.writeObject( outValues );
    GCParserCommon.oos.flush();
    return outValues;
  }
  protected void interpretResult() throws Exception {System.out.println("output: ");
    Map<String,BigInteger> values = getOutputValues();
    for( String id : values.keySet() ){
      OutputFormat fmt = gccom.context().getOutputFormat( id );
      System.out.println(id+" = "+fmt.printFormat(values.get(id)));
    }
    GCParserCommon.printCircuitUsage();
  }
  protected void verify_result(){}
}
