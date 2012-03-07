// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Test;

import jargs.gnu.CmdLineParser;

import java.io.*;
import Program.*;
import Utils.*;
import YaoGC.*;
public class TestGCParserServer {
  private static String circuitDesc;
  private static String privateFileName;
  private static void printUsage() {
    System.out.println("Usage: java TestGCParserServer [{-f, --file-name} f] [{-p --private-file-name} p] [{-w, --wire-bitlength} w]");
  }

  private static void process_cmdline_args(String[] args) {
    CmdLineParser parser = new CmdLineParser();
    CmdLineParser.Option optionFilename = parser.addStringOption('f', "file-name");
    CmdLineParser.Option optionWireBL = parser.addIntegerOption('w', "wire-bitlength");
    CmdLineParser.Option optionPrivateFilename = parser.addStringOption('p',"private-file-name");

    try {
	parser.parse(args);
    }
    catch (CmdLineParser.OptionException e) {
	System.err.println(e.getMessage());
	printUsage();
	System.exit(2);
    }
    privateFileName = (String) parser.getOptionValue(optionPrivateFilename, new String(""));
    circuitDesc = (String) parser.getOptionValue(optionFilename, new String(""));
    Wire.labelBitLength = ((Integer) parser.getOptionValue(optionWireBL, new Integer(80))).intValue();
  }

  public static void main(String[] args) throws Exception {
    StopWatch.pointTimeStamp("Starting program");
    process_cmdline_args(args);

    File cirFile = new File( circuitDesc );
    PrivateInputProvider pip;
    if( privateFileName.equals("") ){
      pip = new PrivateInputsRandom();
    } else {
      pip = new PrivateInputsFile( new FileInputStream( new File(privateFileName) ) );
    }
    GCParserCommon com = new GCParserCommon(cirFile,pip);
    GCParserServer server = new GCParserServer( com );
    server.run();
  }
}