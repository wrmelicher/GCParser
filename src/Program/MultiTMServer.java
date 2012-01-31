package Program;

import java.math.*;
import java.util.*;

import YaoGC.*;
import Utils.*;

public class MultiTMServer extends ProgServer {
    static BigInteger X, Y; 

    private BigInteger[][] Xlps, Ylps;

    private State outputState;

    private static final Random rnd = new Random();

    public MultiTMServer(BigInteger x, BigInteger y) {
	X = x; Y = y;
    }

    protected void init() throws Exception {
	MultiTMCommon.oos.writeObject(Y);
	MultiTMCommon.oos.flush();

	super.init();
	MultiTMCommon.initCircuits();

	generateLabelPairs();
    }

    private void generateLabelPairs() {
	Xlps = new BigInteger[2][2];
	Ylps = new BigInteger[2][2];
	for (int i=0;i<2;i++){
	Xlps[i] = Wire.newLabelPair();
	}
	for (int i=0;i<2;i++){
	Ylps[i] = Wire.newLabelPair();
    }
	}
    protected void execTransfer() throws Exception {
    	int bytelength = (Wire.labelBitLength-1)/8 + 1;

    	for (int i = 0; i < 2; i++) {

		int idx = X.testBit(i) ? 1 : 0;
		Utils.writeBigInteger(Xlps[i][idx], bytelength, 
				      MultiTMCommon.oos);
    	}
		MultiTMCommon.oos.flush();
    	StopWatch.taskTimeStamp("sending labels for selfs inputs");

    	snder.execProtocol(Ylps);
    	StopWatch.taskTimeStamp("sending labels for peers inputs");
    }

    protected void execCircuit() throws Exception {
    	BigInteger[] Xlbs = new BigInteger[2];
    	BigInteger[] Ylbs = new BigInteger[2];

    	for (int i = 0; i < Xlbs.length; i++)
    	    Xlbs[i] = Xlps[i][0];

    	for (int i = 0; i < Ylbs.length; i++)
    	    Ylbs[i] = Ylps[i][0];
    	outputState = MultiTMCommon.execCircuit(Xlbs, Ylbs);
    }
	BigInteger output = BigInteger.ZERO;

    protected void interpretResult() throws Exception {
		System.out.println("Interpreting Results");

	BigInteger[] outLabels = (BigInteger[]) MultiTMCommon.ois.readObject();
	    for (int i = 0; i < outLabels.length; i++) {
		if (outputState.wires[i].value != Wire.UNKNOWN_SIG) {
		    if (outputState.wires[i].value == 1)
			output = output.setBit(i);
		    continue;
		}else if (outLabels[i].equals(outputState.wires[i].invd ? 
					     outputState.wires[i].lbl :
					     outputState.wires[i].lbl.xor(Wire.R.shiftLeft(1).setBit(0)))) {
		    output = output.setBit(i);
	    }
		else if (!outLabels[i].equals(outputState.wires[i].invd ? 
					      outputState.wires[i].lbl.xor(Wire.R.shiftLeft(1).setBit(0)) :
					      outputState.wires[i].lbl)) 
		    throw new Exception("Bad label encountered: i = " + i + "\t" +
					Color.red + outLabels[i] + " != (" + 
					outputState.wires[i].lbl + ", " +
					outputState.wires[i].lbl.xor(Wire.R.shiftLeft(1).setBit(0)) + ")" + Color.black);
	    }
		
		System.out.println(output);

	StopWatch.taskTimeStamp("output labels received and interpreted");
    }

    protected void verify_result() throws Exception {	System.out.println("Verifying results:");

	System.out.println("output (verify): ");
	System.out.println(X.multiply(Y)+"");
	System.out.println("output (pp):\t ");	System.out.println(output);

    }
}