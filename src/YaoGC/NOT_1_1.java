package YaoGC;

import java.math.*;

import Cipher.*;
import Utils.*;

public class NOT_1_1 extends CompositeCircuit {
    private final static int XOR = 0;
    
    public final static int X = 0;

    public NOT_1_1() {
	super(1,1,1,"NOT");
    }

    protected void createSubCircuits() throws Exception {
	subCircuits[XOR] = new XOR_2_1();
	
	super.createSubCircuits();
    }

    protected void connectWires(){
	inputWires[XOR].connectTo(subCircuits[0].inputWires,0);
    }
    protected void defineOutputWires(){
	outputWires[0] = subCircuits[XOR].outputWires[0];
    }
    protected void fixInternalWires(){
	Wire internalWire = subCircuits[0].inputWires[1];
	internalWire.fixWire(1);
    }
}
