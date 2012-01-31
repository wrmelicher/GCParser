package Test;
import java.io.File;
import GCParser.CircuitParser;
public class TestParserFile {
  public static void main( String[] args ){
    for( String s : args ){
      try {
	CircuitParser.read( new File(s) );
	System.out.println(s+": ok");
      } catch (Exception e){
	System.out.println(s+": not ok -"+e.getMessage());
      }
    }
  }
}