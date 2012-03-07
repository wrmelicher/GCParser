// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Test;

import jargs.gnu.CmdLineParser;

import java.io.*;
import Program.*;
import Utils.*;
import YaoGC.*;
import GCParser.CircuitParser;
import java.util.Map;
import java.math.BigInteger;
public class TestGCParserFeedServer {

  private static void printUsage() {
    System.out.println("Usage: java TestGCParserFeedServer [{-w, --wire-bitlength} w]");
  }

  private static void process_cmdline_args(String[] args) {
    CmdLineParser parser = new CmdLineParser();
    CmdLineParser.Option optionWireBL = parser.addIntegerOption('w', "wire-bitlength");

    try {
	parser.parse(args);
    }
    catch (CmdLineParser.OptionException e) {
	System.err.println(e.getMessage());
	printUsage();
	System.exit(2);
    }
    Wire.labelBitLength = ((Integer) parser.getOptionValue(optionWireBL, new Integer(80))).intValue();
  }

  public static void main(String[] args) throws Exception {
    StopWatch.pointTimeStamp("Starting program");
    process_cmdline_args(args);

    File addSub = new File( "./CircuitFiles/addSub.cir" );
    File addTest = new File( "./CircuitFiles/addTest.cir" );

    PrivateInputProvider pip = new PrivateInputsRandom();
    
    GCParserServer gc = new GCParserServer( new GCParserCommon(addSub,pip) );
    gc.run();
    Map<String,BigInteger> out = gc.getOutputValues();

    pip = new PrivateInputsStore( out );
    gc = new GCParserServer( new GCParserCommon(addTest,pip) );
    gc.run();
  }
}