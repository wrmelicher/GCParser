package YaoGC;

// [KSS Fig .04] - I believe figure 4 is wrong. Slightly different below
public class SUB_2N_N extends CompositeCircuit{
    private final int L;
    public SUB_2N_N(int n){
	super(2*n,n,2*n,"SUBN");
	L=n;
    }

    protected void createSubCircuits() throws Exception{
	for (int i = 0;i<L;i++){
	    subCircuits[i] = new ADD_3_2();
	    subCircuits[i+L] = new NOT_1_1();
	}
	super.createSubCircuits();
    }

    protected void connectWires(){
	for (int i=0;i<L;i++){
	    inputWires[i].connectTo(subCircuits[i].inputWires,ADD_3_2.X);
	    inputWires[i+L].connectTo(subCircuits[i+L].inputWires,0);
	    if( i+1 < L )
	      subCircuits[i].outputWires[ADD_3_2.COUT].connectTo(subCircuits[i+1].inputWires,ADD_3_2.CIN);
	    subCircuits[i+L].outputWires[0].connectTo( subCircuits[i].inputWires, ADD_3_2.Y );
	}
    }
    protected void defineOutputWires(){
	for (int i=0;i<L;i++){
	    outputWires[i] = subCircuits[i].outputWires[0];
	}

    }
    protected void fixInternalWires(){
	Wire internalWire = subCircuits[0].inputWires[ADD_3_2.CIN];
	internalWire.fixWire(1);
    }
}