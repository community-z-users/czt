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
        String [] args =
	  new String [] {"-parser", parserFile_,
                         "-symbols", symbolFile_,
			 inputFileFull};

        //call CUP. This is dodgy...
	java_cup.Main.main(args);

        //move the files
        String intermediateParserFile = new String();
        String intermediateSymbolFile = new String();
        intermediateParserFile += parserFile_ + ".java";
        intermediateSymbolFile += symbolFile_ + ".java";

        boolean pMoved = 
	  new File(intermediateParserFile).renameTo(fParserFile);
        boolean sMoved =
	  new File(intermediateSymbolFile).renameTo(fSymbolFile);
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

