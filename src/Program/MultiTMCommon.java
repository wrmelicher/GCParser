package Program;

import java.math.*;
import java.util.*;
import java.io.*;

import Utils.*;
import YaoGC.*;

public class MultiTMCommon extends ProgCommon {

    static void initCircuits() {
	ccs = new Circuit[1];
	ccs[0] = new Multiply_22_4();
	try{
	    ccs[0].build();
	}
	catch(Exception e){
	    e.printStackTrace();
	    System.exit(1);
	}
    }

    public static State execCircuit(BigInteger[] Xlbs, BigInteger[] Ylbs) throws Exception {
	State in = State.fromConcatenation(State.fromLabels(Xlbs),State.fromLabels(Ylbs));
	State output = ccs[0].startExecuting(in);

	StopWatch.taskTimeStamp("circuit executing");
	return output;
    }
}