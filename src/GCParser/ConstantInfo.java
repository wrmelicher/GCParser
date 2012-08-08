package GCParser;
import java.math.BigInteger;

public class ConstantInfo extends VariableInfo {
  public ConstantInfo( BigInteger b, int bits ){
    super( b.toString()+ ":" +bits );
    setParty(Input_Variable.NEUTRAL);
  }
  public ConstantInfo( BigInteger b ){
    super( b.toString() );
    setParty(Input_Variable.NEUTRAL);
  }
}
