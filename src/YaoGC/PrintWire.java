package YaoGC;

public class PrintWire extends Wire {
  private long label;
  public PrintWire(){
    label = SimpleCircuit_2_1.printer.newWire();
  }
  public long label(){
    return label;
  }
  public void setPrintLabel( long l ){
    label = l;
  }
}
