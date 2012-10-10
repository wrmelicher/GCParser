package YaoGC;

import java.lang.Math;

public class Decoder_Nplus1_2powN extends CompositeCircuit {
  private final int N;

  public static final int NOT1 = 0;
  public static final int AND = 1;
  public static final int XOR = 2;
  public static final int UPPER_DECODE = 3;
  public static final int LOWER_DECODE = 4;

  public Decoder_Nplus1_2powN( int n ){
    super( n+1, (int)Math.pow( 2, n ), 
	   n == 1 ?
	   3 : 5, 
	   "Decoder"+n);
    N = n;
  }

  protected void createSubCircuits() throws Exception{
    subCircuits[NOT1] = new NOT_1_1();
    subCircuits[AND] = AND_2_1.newInstance();
    subCircuits[XOR] = new XOR_2_1();
    if( N != 1 ){
      subCircuits[UPPER_DECODE] = new Decoder_Nplus1_2powN( N - 1 );
      subCircuits[LOWER_DECODE] = new Decoder_Nplus1_2powN( N - 1 );
    }
    super.createSubCircuits();
  }

  protected void connectWires(){
    inputWires[ N - 1 ].connectTo(subCircuits[NOT1].inputWires, NOT_1_1.X);
    inputWires[ N - 1 ].connectTo(subCircuits[AND].inputWires, 0);
    inputWires[ N ].connectTo(subCircuits[AND].inputWires, 1);
    
    subCircuits[AND].outputWires[0].connectTo
      ( subCircuits[XOR].inputWires, 0);
    inputWires[ N ].connectTo
      ( subCircuits[XOR].inputWires, 1);
    if( N != 1 ){
      subCircuits[AND].outputWires[0].connectTo
	( subCircuits[UPPER_DECODE].inputWires, N - 1 );
      subCircuits[XOR].outputWires[0].connectTo
	( subCircuits[LOWER_DECODE].inputWires, N - 1 );
      for( int i = 0; i < N - 1; i++ ) {
	inputWires[i].connectTo( subCircuits[UPPER_DECODE].inputWires, i );
	inputWires[i].connectTo( subCircuits[LOWER_DECODE].inputWires, i );
      }
    }
  }

  protected void defineOutputWires(){
    if( N != 1 ){
      for( int i = 0; i < Math.pow( 2, N - 1 ); i++ ){
	outputWires[i] = subCircuits[LOWER_DECODE].outputWires[i];
      }
      for( int i = 0; i < Math.pow( 2, N - 1 ); i++ ){
	outputWires[i+(int)Math.pow(2,N-1)] = subCircuits[UPPER_DECODE].outputWires[i];
      }
    } else {
      outputWires[1] = subCircuits[AND].outputWires[0];
      outputWires[0] = subCircuits[XOR].outputWires[0];
    }
  }

  protected void fixInternalWires(){
    
  }

}
