package YaoGC;

public class OR_2L_L extends CompositeCircuit {

    public OR_2L_L(int l) {
	super(2*l, l, l, "OR_"+(2*l)+"_"+l);
    }

    protected void createSubCircuits() throws Exception {
	for (int i = 0; i < outDegree; i++) 
	    subCircuits[i] = OR_2_1.newInstance();

	super.createSubCircuits();
    }

    protected void connectWires() {
	for (int i = 0; i < outDegree; i++) {
	    inputWires[X(i)].connectTo(subCircuits[i].inputWires, 0);
	    inputWires[Y(i)].connectTo(subCircuits[i].inputWires, 1);
	}
    }

    protected void defineOutputWires() {
	for (int i = 0; i < outDegree; i++)
	    outputWires[i] = subCircuits[i].outputWires[0];
    }

    public int X(int i) {
	return i + outDegree;
    }

    public int Y(int i) {
	return i;
    }
}