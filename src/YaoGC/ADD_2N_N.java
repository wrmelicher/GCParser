package YaoGC;
public class ADD_2N_N extends CompositeCircuit{
    private final int L;
    public ADD_2N_N(int n){
	super(2*n,n,n,"ADDN");
	L=n;
    }

    protected void createSubCircuits() throws Exception{
	for (int i = 0;i<L;i++){
	    subCircuits[i] = new ADD_3_2();
	}
	super.createSubCircuits();
    }

    protected void connectWires(){
	for (int i=0;i<L;i++){
	    inputWires[i].connectTo(subCircuits[i].inputWires,ADD_3_2.X);
	    inputWires[i+L].connectTo(subCircuits[i].inputWires,ADD_3_2.Y);
	    if( i+1 < L)
	      subCircuits[i].outputWires[ADD_3_2.COUT].connectTo(subCircuits[i+1].inputWires,ADD_3_2.CIN);
	}
    }
    protected void defineOutputWires(){
	for (int i=0;i<L;i++){
	    outputWires[i] = subCircuits[i].outputWires[ADD_3_2.S];
	}
    }
    protected void fixInternalWires(){
	Wire internalWire = subCircuits[0].inputWires[ADD_3_2.CIN];
	internalWire.fixWire(0);
    }
}