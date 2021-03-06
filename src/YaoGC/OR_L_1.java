// Copyright (C) 2011 by Yan Huang <yhuang@virginia.edu>

package YaoGC;

public class OR_L_1 extends CompositeCircuit {
    private final int L;

    public OR_L_1(int l) throws Exception {
	super(l, 1, l-1, "OR_" + l + "_1");
	/*	if (l < 2)
		throw new Exception("OR_L_1: input length cannot be less than 2.");*/
	L = l;
    }

    protected void createSubCircuits() throws Exception {
      if( L != 1 ){
	for (int i = 0; i < L-1; i++) {
	    subCircuits[i] = OR_2_1.newInstance();
	}
      }
      super.createSubCircuits();
    }

    protected void connectWires() {
      if( L != 1 ){
	inputWires[0].connectTo(subCircuits[0].inputWires, 0);
	inputWires[1].connectTo(subCircuits[0].inputWires, 1);

	// subCircuits[0].inputWires[0].connectFrom(inputWires[0]);
	// subCircuits[0].inputWires[1].connectFrom(inputWires[1]);

	for (int i = 1; i < L-1; i++) {
	    subCircuits[i-1].outputWires[0].connectTo(subCircuits[i].inputWires, 0);
	    inputWires[i+1].connectTo(subCircuits[i].inputWires, 1);

	    // subCircuits[i].inputWires[0].connectFrom(subCircuits[i-1].outputWires[0]);
	    // subCircuits[i].inputWires[1].connectFrom(inputWires[i+1]);
	}
      }
      
    }

    protected void defineOutputWires() {
      if( L != 1 )
	outputWires[0] = subCircuits[L-2].outputWires[0];
      else
	outputWires[0] = inputWires[0];
    }
}
