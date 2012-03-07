// Copyright (C) Billy Melicher 2012 wrm2ja@virginia.edu
package Test;

import jargs.gnu.CmdLineParser;

import java.io.*;
import Program.*;
import Utils.*;

public class TestGCParserClient {
  private static String privateFileName;
  private static String circuitDesc;

  private static void printUsage() {
    System.out.println("Usage: java TestGCParserClient [{-f, --file-name}] [{-p --private-file-name} p] [{-s, --server} servername] [{-r, --iteration} r] ");
  }

  private static void process_cmdline_args(String[] args) {
      CmdLineParser parser = new CmdLineParser();
      CmdLineParser.Option optionServerIPname = parser.addStringOption('s', "server");
      CmdLineParser.Option optionIterCount = parser.addIntegerOption('r', "iteration");
      CmdLineParser.Option optionFilename = parser.addStringOption('f', "file-name");
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
      ProgClient.serverIPname = (String) parser.getOptionValue(optionServerIPname, new String("localhost"));
      Program.iterCount = ((Integer) parser.getOptionValue(optionIterCount, new Integer(1))).intValue();
      circuitDesc = (String) parser.getOptionValue(optionFilename, new String(""));
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
    GCParserClient gcclient = new GCParserClient( com );
    gcclient.run();
  }
}