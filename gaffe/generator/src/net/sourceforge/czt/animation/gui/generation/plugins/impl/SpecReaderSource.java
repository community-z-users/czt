package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.io.InputStream;
import java.io.IOException;

import java.net.MalformedURLException;
import java.net.URL;

import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SpecSource;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

public final class SpecReaderSource implements SpecSource {
  private JaxbXmlReader reader=new JaxbXmlReader();
  private File file=null;
  private URL url=null;
  private InputStream is=null;
  public String getArgsDocumentation() {
    return "-spec <filename or url>          File name or URL of the specification to use.\n"
          +"-spec-file <filename>            File name of the specification to use.\n"
          +"-spec-url <url>                  URL of the specification to use.\n"
          +"-spec-stdin                      The specification to use will come from System.in.\n";
  };    
  public void handleArgs(ListIterator/*<String>*/ args) throws BadArgumentsException {
    for(;args.hasNext();) {
      String arg=(String)args.next();
      if(arg.equals("-spec")) {
	if(!args.hasNext())
	  throw new BadArgumentsException("-spec requires an argument giving a file name or URL.");
	String fileOrUrl=(String)args.next();
	try {
	  url=new URL(fileOrUrl);
	} catch (MalformedURLException ex) {
	  file=new File((String)args.next());
	  if(!file.canRead()) 
	    throw new BadArgumentsException("The argument to -spec must be an existing readable file or a "
					    +"valid URL.");
	}
      } else if (arg.equals("-spec-file")) {
	if(!args.hasNext()) 
	  throw new BadArgumentsException("-spec-file requires an argument giving a file name.");
	file=new File((String)args.next());
	if(!file.canRead()) 
	  throw new BadArgumentsException("The argument to -spec-file must be an existing readable file.");
      } else if (arg.equals("-spec-url")) {
	if(!args.hasNext()) 
	  throw new BadArgumentsException("-spec-url requires an argument giving a URL.");
	try {
	  url=new URL((String)args.next());
	} catch(MalformedURLException ex) {
	  throw new BadArgumentsException("The argument to -spec-url must be a valid URL.");
	};
      } else if(arg.equals("-spec-stdin")) {
	is=System.in;
      } else {
	args.previous();
	return;
      }
    }
  };
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
  
