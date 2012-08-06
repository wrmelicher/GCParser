package GCParser;
import java.math.BigInteger;

public class ConstantInfo extends VariableInfo {
  public ConstantInfo( BigInteger b, int bits ){
    super( b.toString()+ ":" +bits );
  }
  public ConstantInfo( BigInteger b ){
    super( b.toString() );
  }
}
