// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Test;

import jargs.gnu.CmdLineParser;

import java.io.*;
import Program.*;
import Utils.*;
import GCParser.CircuitParser;
import java.util.Map;
import YaoGC.State;
import java.math.BigInteger;

public class TestGCParserFeedClient {

  private static void printUsage() {
    System.out.println("Usage: java TestGCParserClient [{-s, --server} servername] [{-r, --iteration} r] ");
  }

  private static void process_cmdline_args(String[] args) {
      CmdLineParser parser = new CmdLineParser();
      CmdLineParser.Option optionServerIPname = parser.addStringOption('s', "server");
      CmdLineParser.Option optionIterCount = parser.addIntegerOption('r', "iteration");

      try {
	  parser.parse(args);
      }
      catch (CmdLineParser.OptionException e) {
	  System.err.println(e.getMessage());
	  printUsage();
	  System.exit(2);
      }

      ProgClient.serverIPname = (String) parser.getOptionValue(optionServerIPname, new String("localhost"));
      Program.iterCount = ((Integer) parser.getOptionValue(optionIterCount, new Integer(1))).intValue();
  }

  public static void main(String[] args) throws Exception {
    StopWatch.pointTimeStamp("Starting program");
    process_cmdline_args(args);

    File addSub = new File( "./CircuitFiles/addSub.cir" );
    File addTest = new File( "./CircuitFiles/addTest.cir" );

    PrivateInputProvider pip = new PrivateInputsRandom();
    
    GCParserClient gc = new GCParserClient( new GCParserCommon(addSub,pip) );
    gc.run();
    Map<String,BigInteger> out = gc.getOutputValues();

    pip = new PrivateInputsStore( out );
    gc = new GCParserClient( new GCParserCommon(addTest,pip) );
    gc.run();
  }
}