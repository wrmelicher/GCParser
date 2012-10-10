package GCParser.Operation;
import YaoGC.*;
import GCParser.*;
public class DecodeOperation extends OpCircuitUser {
  public final static String NAME = "decode";
  public DecodeOperation(){
    super( NAME );
  }
  public Circuit create_circuit( State[] operands ){
    return new Decoder_Nplus1_2powN( operands[0].getWidth() );
  }
  public int circuit_id( State[] operands ){
    return operands[0].getWidth();
  }
  public State execute( State[] inputs, Circuit cir ) throws Exception {
    State input = State.fromConcatenation( inputs[0], inputs[1] );
    return cir.startExecuting( input );
  }
  public int validate( Variable[] inputs ) throws CircuitDescriptionException {
    if( inputs.length != 2 ){
      throw createException("decode operation must have 2 inputs: number, and enable");
    }
    int n = inputs[0].validate();
    int enable = inputs[1].validate();
    if( enable != 1 ){
      throw createException("Decode's enable input must be 1 bit wide");
    }
    return (int) java.lang.Math.pow( 2, n );
  }
}
