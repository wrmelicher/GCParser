package Program;

import java.math.*;
import java.io.*;
import java.util.*;

import YaoGC.*;
import OT.*;
import Utils.*;

public class MultiTMClient extends ProgClient{
    static BigInteger Y; 
	
    private BigInteger[] Xlbs, Ylbs;
    private State outputState;

    public MultiTMClient() {}

    protected void init() throws Exception {
	Y = (BigInteger) MultiTMCommon.ois.readObject();
	
	otNumOfPairs = 2;

	super.init();
	MultiTMCommon.initCircuits();
    }

    protected void execTransfer() throws Exception {
	int bytelength = (Wire.labelBitLength-1)/8 + 1;

	Xlbs = new BigInteger[2];
    	for (int i = 0; i < 2; i++) {
		Xlbs[i] = Utils.readBigInteger(bytelength, 
						   MultiTMCommon.ois);
	    }
   
	StopWatch.taskTimeStamp("receiving labels for peer's inputs");

	BigInteger temp = BigInteger.ZERO;
	for (int i = 0; i < 2; i++)
		if (Y.testBit(i))
		    temp = temp.setBit(i);

	rcver.execProtocol(temp);
	Ylbs = rcver.getData();
	StopWatch.taskTimeStamp("receiving labels for self's inputs");
    }

    protected void execCircuit() throws Exception {
	outputState = MultiTMCommon.execCircuit(Xlbs, Ylbs);
    }

    protected void interpretResult() throws Exception {
	    MultiTMCommon.oos.writeObject(outputState.toLabels());
	MultiTMCommon.oos.flush();

    }

    protected void verify_result() throws Exception {

	}
}