package ant;

import java.io.*;

import java_cup.*;

/**
 * The implements a simple java cup ant task. The only options that are
 * supported at the moment is -parser and -symbol
 *
 * @author Tim Miller
 */
public class JavaCupTask
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

  public void execute() throws Exception
  {
    try {
      if (inputFile_ == null) {
        throw new Exception("An input file must be specified");
      }

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
	String [] cmdarray =
	  new String [] {
	    "java", "java_cup.Main",
	    "-parser", parserFile_,
	    "-symbols", symbolFile_,
	  };
	
	//call CUP
	Process p = Runtime.getRuntime().exec(cmdarray);
	
	InputStream is = new FileInputStream(inputFileFull);
	
	StreamWriter sw = new StreamWriter(p.getOutputStream(), is, this);
	StreamReader sr = new StreamReader(p.getErrorStream(), System.err, this);
	StreamReader so = new StreamReader(p.getInputStream(), System.out, this);

	//write to the process and read back the output
	sw.write();
	sr.read();
	so.read();

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
      throw new Exception("Java cup failed!", e);      
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
}

class StreamReader
{
  //the output stream of the process
  private InputStream pOut_;

  //the stream to which to send any output
  private OutputStream write_;

  //the calling JavaCupTask object
  private JavaCupTask caller_;

  StreamReader(InputStream out, OutputStream write, JavaCupTask caller)
  {
    pOut_ = out;
    write_ = write;
    caller_ = caller;
  }

  public void read()
  {
    try
    {
      if (pOut_.available() > 0) {
	int c = pOut_.read();
	while (pOut_.available() > 0) {
	  write_.write(c);
	  c = pOut_.read();
	}
      }
      write_.flush();
      write_.close();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

class StreamWriter
{
  //the input stream of the process
  //declared as an OutputStream because we write to it
  private OutputStream pIn_;

  //the stream from which to read data and send to the process's 
  //input stream
  private InputStream read_;

  //the calling JavaCupTask object
  private JavaCupTask caller_; 

  StreamWriter(OutputStream in, InputStream read, JavaCupTask caller)
  {
    pIn_ = in;
    read_ = read;
    caller_ = caller;
  }
  
  public synchronized void write()
  {
    try
    {
      //wait for the input stream to be assigned
      int c = read_.read();
      while (c >= 0) {
        pIn_.write(c);
	pIn_.flush();
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
