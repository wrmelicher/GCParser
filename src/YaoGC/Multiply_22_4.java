package YaoGC;

import java.util.*;
import Cipher.*;

public class Multiply_22_4 extends CompositeCircuit{
//    private final int L;
    public final static int XOR0 = 0;
    public final static int XOR1 = 1;
    public final static int AND0 = 2;
    public final static int AND1 = 3;
    public final static int AND2 = 4;
    public final static int AND3 = 5;
    public final static int AND4 = 6;
    public final static int AND5 = 7;
    
    public final static int A0 = 0;
    public final static int A1 = 1;
    public final static int B0 = 2;
    public final static int B1 = 3;

    public final static int S0 = 0;
    public final static int S1 = 1;
    public final static int S2 = 2;
    public final static int S3 = 3;

    
    public Multiply_22_4(){
	super(4,4,8,"Multiply2");
    }
    
    protected void createSubCircuits() throws Exception{

	subCircuits[XOR0] = new XOR_2_1();
	subCircuits[XOR1] = new XOR_2_1();

	subCircuits[AND0] = AND_2_1.newInstance();
	subCircuits[AND1] = AND_2_1.newInstance();
	subCircuits[AND2] = AND_2_1.newInstance();
	subCircuits[AND3] = AND_2_1.newInstance();
	subCircuits[AND4] = AND_2_1.newInstance();
	subCircuits[AND5] = AND_2_1.newInstance();
	super.createSubCircuits();
    }
    
    protected void connectWires(){
	inputWires[A0].connectTo(subCircuits[AND0].inputWires,0);
	inputWires[B0].connectTo(subCircuits[AND0].inputWires,1);
	inputWires[A1].connectTo(subCircuits[AND1].inputWires,0);
	inputWires[B0].connectTo(subCircuits[AND1].inputWires,1);
	inputWires[A0].connectTo(subCircuits[AND2].inputWires,0);
	inputWires[B1].connectTo(subCircuits[AND2].inputWires,1);
	inputWires[A1].connectTo(subCircuits[AND3].inputWires,0);
	inputWires[B1].connectTo(subCircuits[AND3].inputWires,1);	
	subCircuits[AND1].outputWires[0].connectTo(subCircuits[XOR0].inputWires,0);
	subCircuits[AND2].outputWires[0].connectTo(subCircuits[XOR0].inputWires,1);
	subCircuits[AND1].outputWires[0].connectTo(subCircuits[AND4].inputWires,0);
	subCircuits[AND2].outputWires[0].connectTo(subCircuits[AND4].inputWires,1);
	subCircuits[AND3].outputWires[0].connectTo(subCircuits[XOR1].inputWires,0);
	subCircuits[AND4].outputWires[0].connectTo(subCircuits[XOR1].inputWires,1);
	subCircuits[AND3].outputWires[0].connectTo(subCircuits[AND5].inputWires,0);
	subCircuits[AND4].outputWires[0].connectTo(subCircuits[AND5].inputWires,1);
    }

    protected void defineOutputWires(){
	outputWires[S0] = subCircuits[AND0].outputWires[0];
	outputWires[S1] = subCircuits[XOR0].outputWires[0];
	outputWires[S2] = subCircuits[XOR1].outputWires[0];
	outputWires[S3] = subCircuits[AND5].outputWires[0];
    }
}