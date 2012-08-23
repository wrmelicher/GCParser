package GCParser;
import java.math.BigInteger;
public class HexFormat extends OutputFormat {
  public HexFormat(){
    super(false);
  }
  public String printFormat(BigInteger val){
    return val.toString(16);
  }
  public String printIdentifier(){
    return "hex";
  }
}
