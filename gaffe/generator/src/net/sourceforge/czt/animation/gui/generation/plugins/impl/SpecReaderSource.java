/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.io.InputStream;
import java.io.IOException;

import java.net.MalformedURLException;
import java.net.URL;

import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;

import net.sourceforge.czt.animation.gui.generation.plugins.SpecSource;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

/**
 * A plugin implementation for obtaining Z the specifications from a file, URL, or System.in.
 * @author Nicholas Daley
 */
public final class SpecReaderSource implements SpecSource {
  /**
   * {@inheritDoc}
   * Options for specifying where the specification is loaded from:
   * <ul>
   *   <li>-spec &lt;filename or URL&gt;</li>
   *   <li>-spec-file &lt;filename&gt;</li>
   *   <li>-spec-url &lt;URL&gt;</li>
   *   <li>-spec-stdin</li>
   * </ul>
   */
  public Option[] getOptions() {
    return new Option[]{
      new Option("spec", Option.MUST, "filename or URL", "File name or URL of the specification to use.",
		 specHandler),
      new Option("spec-file", Option.MUST, "filename", "File name of the specification to use.",
		 specFileHandler),
      new Option("spec-url", Option.MUST, "URL", "URL of the specification to use.",
		 specURLHandler),
      new Option("spec-stdin", Option.MUSTNOT, null, "The specification to use will come from System.in.",
		 specStdInHandler)
	};
  };
  /**
   * {@inheritDoc}
   */
  public String getHelp() {return "Obtains a Z specification from a file, URL, or standard input.";};  

  /**
   * Option handler for <tt>-spec</tt>.
   * Tries to turn it into a URL, then as a file, if both fail it throws an Error.
   */
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
  /**
   * Option handler for <tt>-spec-file</tt>.
   * Tries to turn it into a file, if this fails it throws an Error.
   */
  private OptionHandler specFileHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	file=new File(argument);
	if(!file.canRead()) 
	  throw new Error("The argument to -spec-file must be an existing readable file.");
      };
    };
  /**
   * Option handler for <tt>-spec-url</tt>.
   * Tries to turn it into a URL, if this fails it throws an Error.
   */
  private OptionHandler specURLHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	try {
	  url=new URL(argument);
	} catch(MalformedURLException ex) {
	  throw new Error("The argument to -spec-url must be a valid URL.");
	}
      };
    };
  /**
   * Option handler for <tt>-spec-stdin</tt>.
   * Sets the input stream to use to System.in.
   */
  private OptionHandler specStdInHandler=new OptionHandler() {
      public void handleOption(Option opt, String argument) {
	is=System.in;
      };
    };
  
  /**
   * The reader to use when reading the spec from the input stream.
   */
  private JaxbXmlReader reader=new JaxbXmlReader();
  /**
   * The file to read from or null.
   */
  private File file=null;
  /**
   * The URL to read from or null.
   */
  private URL url=null;
  /**
   * The input stream to read from or null.
   */
  private InputStream is=null;
  
  /**
   * {@inheritDoc}
   * Opens the file/URL/input stream, uses the reader to turn its contents into a Z specification, returns 
   * this specification.
   */
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
  /**
   * {@inheritDoc}
   * If it was loaded from a file, translates this into a URL.
   * If it was loaded from a URL, returns this.
   * Otherwise returns null.
   */
  public URL getURL() {
    if(file!=null) try {
      return file.toURL();
    } catch(MalformedURLException ex) {
      return null;
    } else if(url!=null)
      return url;
    else return null;
  };
};
