// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Test;
import java.io.*;
import GCParser.*;
import GCParser.Operation.CircuitDescriptionException;
import jargs.gnu.CmdLineParser;
import java.util.TreeMap;
import java.math.BigInteger;
public class TestParserFile {
  public static boolean DEBUG = false;
  public static boolean DEBUG_LOCAL = false;
  public static boolean OPTIMIZE = false;
  public static boolean GENERATE = false;
  public static String[] parse_args(String[] args){
    CmdLineParser parser = new CmdLineParser();
    CmdLineParser.Option debug = parser.addBooleanOption('d',"debug");
    CmdLineParser.Option help = parser.addBooleanOption('h',"help");
    CmdLineParser.Option debug_local = parser.addBooleanOption('l',"debug-local");
    CmdLineParser.Option output_opt = parser.addBooleanOption('o',"optimize");
    CmdLineParser.Option gen_cir = parser.addBooleanOption('g',"generate-circuit");

    try{
      parser.parse(args);
    } catch( CmdLineParser.OptionException e ){
      printHelp(1);
    }
    if( (Boolean) parser.getOptionValue(help,false) ){
      printHelp(0);
    }
    DEBUG = (Boolean) parser.getOptionValue(debug,false);
    DEBUG_LOCAL = (Boolean) parser.getOptionValue(debug_local,false);
    OPTIMIZE = (Boolean) parser.getOptionValue(output_opt,false);
    GENERATE = (Boolean) parser.getOptionValue(gen_cir,false);
    return parser.getRemainingArgs();
  }
  public static void main( String[] args ){
    String[] files = parse_args(args);
    for( String s : files ){
      try {
	File f = new File(s);
	OptimizingParser v = OptimizingParser.fromFile( f );
	/*if( DEBUG_LOCAL ){
	  v.context().collapseLocalVars( new TreeMap<String,BigInteger>(), 1 );
	  }
	if( DEBUG || DEBUG_LOCAL ){
	  v.context().debugPrint();
	  }*/
	if(OPTIMIZE){
	  v.print();
	} else if(!GENERATE) {
	  v.parse();
	}
	if( GENERATE ){
	  LowLevelCompiler.fromFileComp(f);
	}
	System.out.println(s+": ok");
      } catch (CircuitDescriptionException e){
	System.out.println(s+": not ok -"+e.getMessage());
      } catch (FileNotFoundException e ){
	System.out.println(s+": not ok -"+e.getMessage());
      } catch (IOException e ){
	System.out.println(s+": not ok -"+e.getMessage());
      }
      

      
      
    }
  }
  public static void printHelp(int exit){
    System.out.println("TestParserFile [-h --help] [-d --debug] [-l --debug-local] FILES...");
    System.exit(exit);
  }
}
