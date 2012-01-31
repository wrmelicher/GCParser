package YaoGC;

public class GTE_2L_1 extends CompositeCircuit {
    private final int L;

    public GTE_2L_1(int l) {
	super(2*l, 1, l, "GTE_" + (2*l) + "_1");
	L = l;
    }

    protected void createSubCircuits() throws Exception {
	for (int i = 0; i < L; i++) {
	    subCircuits[i] = new GT_3_1();
	}
	super.createSubCircuits();
    }

    protected void connectWires() {
	inputWires[X(0)].connectTo(subCircuits[0].inputWires, GT_3_1.X);
	inputWires[Y(0)].connectTo(subCircuits[0].inputWires, GT_3_1.Y);

	for (int i = 1; i < L; i++) {
	    inputWires[X(i)].connectTo(subCircuits[i].inputWires, GT_3_1.X);
	    inputWires[Y(i)].connectTo(subCircuits[i].inputWires, GT_3_1.Y);
	    subCircuits[i-1].outputWires[0].connectTo(subCircuits[i].inputWires, GT_3_1.C);
	}
	
    }

    protected void defineOutputWires() {
	outputWires[0] = subCircuits[L-1].outputWires[0];
    }

    protected void fixInternalWires() {
    	Wire internalWire = subCircuits[0].inputWires[GT_3_1.C];
    	internalWire.fixWire(1);
    }

    int X(int i) {
	return i;
    }

    int Y(int i) {
	return i+L;
    }
}
