package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.io.InputStream;
import java.io.IOException;

import java.net.MalformedURLException;
import java.net.URL;

import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SpecSource;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

public final class SpecReaderSource implements SpecSource {
  public Option[] getOptions() {
    return new Option[]{
      new Option("spec", Option.MUST, "filename or URL", "File name or URL of the specification to use.",
		 specHandler),
      new Option("spec-file", Option.MUST, "filename", "File name of the specification to use.",
		 specFileHandler),
      new Option("spec-url", Option.MUST, "url", "URL of the specification to use.",
		 specURLHandler),
      new Option("spec-stdin", Option.MUSTNOT, null, "The specification to use will come from System.in.",
		 specStdInHandler)
	};
  };
  public String getHelp() {return "Obtains a Z specification from a file, URL, or standard input.";};  

  private OptionHandler specHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	try {
	  url=new URL(argument);
	} catch (MalformedURLException ex) {
	  file=new File(argument);
	  if(!file.canRead()) 
	    throw new Error("The argument to -spec must be an existing readable file or a valid URL.");
	}
      };
    };
  private OptionHandler specFileHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	file=new File(argument);
	if(!file.canRead()) 
	  throw new Error("The argument to -spec-file must be an existing readable file.");
      };
    };
  private OptionHandler specURLHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	try {
	  url=new URL(argument);
	} catch(MalformedURLException ex) {
	  throw new Error("The argument to -spec-url must be a valid URL.");
	}
      };
    };
  private OptionHandler specStdInHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	is=System.in;
      };
    };
  
  private JaxbXmlReader reader=new JaxbXmlReader();
  private File file=null;
  private URL url=null;
  private InputStream is=null;
  
  public Term obtainSpec() throws IllegalStateException {
    if(file!=null) return reader.read(file);
    else if(url!=null) try {
      return reader.read(url.openStream());
    } catch(IOException ex) {
      throw new IllegalStateException("The SpecReaderSource could not read from the URL that was given.");
    } else if(is!=null) return reader.read(is);
    else 
      throw new IllegalStateException("The SpecReaderSource needs an argument giving a URL or a "
				      +"filename.");
  };
};
  
