package YaoGC;

public class NOT_N_N extends CompositeCircuit {
  private final int L;
  public NOT_N_N( int l ){
    super(l,l,l,"NOT_"+l+"_"+l);
    L = l;
  }
  protected void createSubCircuits() throws Exception {
    for( int i = 0; i < L; i++ ){
      subCircuits[i] = new NOT_1_1();
    }
    super.createSubCircuits();
  }
  protected void connectWires() {
    for( int i = 0; i < L; i++ ){
      inputWires[i].connectTo( subCircuits[i].inputWires, 0 );
    }
  }
  protected void defineOutputWires() {
    for( int i = 0; i < L; i++ ){
      outputWires[i] = subCircuits[i].outputWires[0];
    }
  }

}