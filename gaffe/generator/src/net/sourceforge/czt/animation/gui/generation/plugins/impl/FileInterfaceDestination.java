package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;

import java.net.URL;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;

import net.sourceforge.czt.animation.gui.generation.plugins.InterfaceDestination;

public final class FileInterfaceDestination implements InterfaceDestination {
  public Option[] getOptions() {
    return new Option[]{
      new Option("destination", Option.MUST, "filename", "File to write the interface to.",
		 destHandler),
      new Option("destination-stdout", Option.MUSTNOT, null, "The interface will be written to System.out.",
		 destStdOutHandler)
	};
  };
  public String getHelp() {return "Selects a location to write the interface to.";};
    
  private OptionHandler destHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	file=new File(argument);
	if(!file.canWrite())
	  throw new Error("The argument to -dest must be a file location that can be written to.");
      };
    };
  private OptionHandler destStdOutHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	os=System.out;
      };
    };
  

  private File file=null;
  private OutputStream os=null;

  public OutputStream obtainOutputStream(URL inputURL) throws IllegalStateException {
    if(os!=null) return os;
    if(file==null && inputURL!=null && inputURL.getProtocol().equals("file")) {
      File inputFile=new File(inputURL.getPath());
      if(inputFile.getName().endsWith(".zml"))
	file=new File(inputFile.getName().substring(0,inputFile.getName().lastIndexOf("."))+".gaffe");
    }
    if(file!=null) try {
      return new FileOutputStream(file);
    } catch (FileNotFoundException ex) {
      throw new IllegalStateException("The FileInterfaceDestination couldn't write to the file given to "
				      +"it ("+file+").");
    } else
      throw new IllegalStateException("The FileInterfaceDestination needs an argument giving a location to "
				      +"write to.");
  };
};
