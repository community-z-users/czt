package ant;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import java_cup.*;
import org.apache.tools.ant.Task;
import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.taskdefs.PumpStreamHandler;

/**
 * The implements a simple java cup ant task. The only options that are
 * supported at the moment is -debug, -parser and -symbol
 *
 * @author Tim Miller
 */
public class JavaCupTask extends Task
{
  //the file from which to read the grammar
  private String inputFile_;

  //the file in which to put the parser
  private String parserFile_;

  //the file to which to put the symbols
  private String symbolFile_;

  //the directory of the file
  private String srcDir_;

  //the destination directory
  private String destDir_;  

  //the -debug flag
  private boolean debug_ = false;

  //direct all err and output from subprocess
  PumpStreamHandler handler = new PumpStreamHandler();

  public void execute () throws BuildException
  {
    try {
      /*
      if (inputFile_ == null) {
        throw new BuildException("An input file must be specified");
	}*/
      //if a src dir is specified, append it to the full file name
      String inputFileFull = new String();
      if (srcDir_ != null) {
        inputFileFull += srcDir_ + File.separator;
      }
      inputFileFull += inputFile_;

      String parserFileFull = new String();
      String symbolFileFull = new String();
      if (destDir_ != null) {
        parserFileFull += destDir_ + File.separator;
        symbolFileFull += destDir_ + File.separator;
      }

      if (parserFile_ == null) {
        parserFile_ += java_cup.emit.parser_class_name;
      }
      parserFileFull += parserFile_;

      if (symbolFile_ == null) {
        symbolFile_ += java_cup.emit.symbol_const_class_name;
      }
      symbolFileFull += symbolFile_;

      //construct the file objects
      File fInputFile = new File(inputFileFull);
      File fParserFile = new File(parserFileFull + ".java");
      File fSymbolFile = new File(symbolFileFull + ".java");
      
      //only regenerate the parser is the CUP file has changed
      if (fInputFile.lastModified() > fParserFile.lastModified()) {

        //first, set the options that will always be set
	List cmdarray = new ArrayList();
	cmdarray.add("java");
	cmdarray.add("java_cup.Main");
	cmdarray.add("-parser");
	cmdarray.add(parserFile_);
	cmdarray.add("-symbols");
	cmdarray.add(symbolFile_);

        //now, set the other options
	if (debug_) {
	  cmdarray.add("-debug");
	}

	//call CUP, redirecting the stdin, stderr, stdout of the 
	//subprocess to this process
	Process p = Runtime.getRuntime().exec(toStringArray(cmdarray));
	handler.setProcessInputStream(p.getOutputStream());
	handler.setProcessOutputStream(p.getInputStream());
	handler.setProcessErrorStream(p.getErrorStream());

	InputStream is = new FileInputStream(inputFileFull);

	StreamWriter sw = new StreamWriter(p.getOutputStream(), is);

	//write to the process and read back the output
	handler.start();
	sw.start();

	//wait for the process to finish executing
	p.waitFor();

	//move the files
	String intermediateParserFile = new String();
	String intermediateSymbolFile = new String();
	intermediateParserFile += parserFile_ + ".java";
	intermediateSymbolFile += symbolFile_ + ".java";
	
	boolean pMoved = 
	  new File(intermediateParserFile).renameTo(fParserFile);
	boolean sMoved =
	  new File(intermediateSymbolFile).renameTo(fSymbolFile);
	
	if (!pMoved) {
	  String error = "Parser could not be written to " +
	    fParserFile.getAbsolutePath();
	    throw new Exception(error);
	}
	else {
	  System.out.println("Parser written to " +
			     fParserFile.getAbsolutePath());
	}

	if (!sMoved) {
	  String error = "Symbols could not be written to " +
	    fSymbolFile.getAbsolutePath();
	    throw new Exception(error);
	}
	else {
	  System.out.println("Symbols written to " +
			     fSymbolFile.getAbsolutePath());
	}
      }
    }
    catch (Exception e) {
      e.printStackTrace();
      throw new BuildException("Java cup failed!", e);      
    }
  }

  public void setDestdir(String destDir)
  {
    destDir_ = destDir;
  }

  public void setSrcDir(String srcDir)
  {
    srcDir_ = srcDir;
  }

  public void setInputFile(String inputFile)
  {
    inputFile_ = inputFile;
  }

  public void setParserFile(String parserFile)
  {
    parserFile_ = parserFile;
  }

  public void setSymbolFile(String symbolFile)
  {
    symbolFile_ = symbolFile;
  }

  public void setDebug(boolean debug)
  {
    debug_ = debug;
  }

  private String [] toStringArray(List list)
  {
    String [] result = new String [list.size()];
    for (int i = 0; i < list.size(); i++) {
      String next = (String) list.get(i);
      result[i] = next;
    }
    return result;
  }
}

class StreamReader extends Thread
{
  //the output stream of the process
  private InputStream pOut_;

  //the stream to which to send any output
  private OutputStream write_;

  StreamReader(InputStream out, OutputStream write)
  {
    pOut_ = out;
    write_ = write;
  }


  public void run()
  {
    read();
  }

  public void read()
  {
    try
    {
      if (pOut_.available() > 0) {
	Debug.debug("Start reading");
	while (pOut_.available() > 0) {
	  int c = pOut_.read();
	  write_.write(c);
	  write_.flush();
	}
      }
      Debug.debug("Finish reading");
      write_.flush();
      write_.close();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

class StreamWriter extends Thread
{
  //the input stream of the process
  //declared as an OutputStream because we write to it
  private OutputStream pIn_;

  //the stream from which to read data and send to the process's 
  //input stream
  private InputStream read_;

  StreamWriter(OutputStream in, InputStream read)
  {
    pIn_ = in;
    read_ = read;
  }

  public void run()
  {
    write();
  }

  public synchronized void write()
  {
    try
    {
      Debug.debug("Start writing");
      int c = read_.read();
      Debug.debug("one char read from input file");
      while (c >= 0) {
        pIn_.write(c);
	c = read_.read();
      }
      pIn_.flush();
      pIn_.close();
    }
    catch (Exception e) {
      e.printStackTrace();  
    }
  }
}

class Debug {

  final static private boolean DEBUG = false;

  static void debug(String message)
  {
    if (DEBUG) {
      System.err.println(message);
    }
  }
}
