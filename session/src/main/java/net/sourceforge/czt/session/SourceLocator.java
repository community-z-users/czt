/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.session;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Properties;
import java.util.logging.Logger;

/**
 * A command to compute the URL for a Z section.
 * 
 * This first looks for /lib/<code>name</code>.tex in the CZT sources,
 * then searches for a variety of file extensions in the directory
 * specified by czt.path.
 */
public class SourceLocator
  implements Command
{
  protected final String [] suffix_ = {
    ".tex", ".zed", ".zed8", ".zed16", ".oz", ".oz8", ".oz16",
    ".circus", ".circus8", ".circus16", ".zedpatt", ".zedpatt8", ".zedpatt16",
    ".zml", ".error"};

  /**
   * Tries to locate the resource named for the given section manager.
   * The lookup algorithm for name as follows:
   * 
   * <ol>
   *   <li> checks if is a toolkit within czt.jar!/lib/name.tex
   *   <li> checks under current directory as ./name.suffixes, 
   *        where the sufixes include all possible values allowed
   *        (e.g., .tex, .zed, .oz, .zed8, .zml, .circus, etc)
   *   <li> checks for czt.path within <code>SectionManager</code> properties:
   *        <ol>
   *          <li> if availble, looks for czt.path/name.suffixes; 
   *          <li> otherwise, looks for czt.path within user.dir/czt.properties
   *        </ol>
   *   <li> checks if user.dir/czt.properties has czt.path within it,
   *        and if so, checks its value with name.suffixes.
   * </ol>
   * 
   * The first successful check in this order wins. If none work,
   * a <code>SourceLocatorException</code> is raised with the latest calculated
   * path and the name as additional information. Note that <code>czt.path</code>
   * can be a semicolon-separated list of paths looked in FIFO order. That means,
   * if a file is found at an earlier directory, that is the one used.
   * 
   * @param name the resource we are trying to locate.
   * @param manager the manager requesting the resource.
   * @return true if resource found, raises an exception otherwise.
   * @throws net.sourceforge.czt.session.CommandException if resource not found.
   */   
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    debug("SL-locate " + name);
    // see if "name" is a toolkit (i.e., czt.jar/lib/name.tex)
    String filename = "/lib/" + name + ".tex";
    URL url = getClass().getResource(filename);
    if (url != null) {
      debug("SL-TK-found="+filename);
      manager.put(new Key<Source>(name, Source.class), new UrlSource(url));
      return true;
    }
    debug("SL-non-toolkit ; try current directory.");
    // see if "name" is within the current directory 
    // with all possible sufixes (i.e., ./name.suffix)
    for (int i = 0; i < suffix_.length; i++) {
      filename = name + suffix_[i];
      File file = new File(filename);
      if (file.exists() && ! file.isDirectory()) {
        debug("SL-CURDIR-found="+filename);
        manager.put(new Key<Source>(name, Source.class), new FileSource(file));
        return true;
      }
    }
    debug("SL-non-current-dir ; try czt.path");
    // try to retrieve czt.path
    List<String> cztpaths = new ArrayList<String>();
    String path = manager.getProperty("czt.path");
    debug("SL-SM-czt.path   = " + path);    
    // if empty or null, try czt.properties
    if (path == null || path.isEmpty())
    {
      Properties cztprops = retrieveCZTProperties();
      if (cztprops != null)
      {
        // gets within czt.properties (if it exists) czt.path or "." by default
        path = cztprops.getProperty("czt.path", ".");
        debug("SL-CZTP-SM-setProperties");
        // sets the manager with all properties within cztprops
        // hence overriding any previous properties within it.
        manager.setProperties(cztprops);                              
        debug("SL-CZTP-czt.properties=" + cztprops);
      }
    }
    if (path != null && !path.isEmpty())
    {
      // split the paths nicely
      cztpaths = processCZTPaths(path);    
      for (String cztpath : cztpaths)
      {     
        debug("SL-CZTP-cztpath[i]=" + cztpath);
        // check czt.path/name with all possible sufixes as last resort
        for (int i = 0; i < suffix_.length; i++) {
          filename = cztpath + "/" + name + suffix_[i];
          File file = new File(filename);
          if (file.exists()) {
            debug("SL-CZTP-found="+filename);
            manager.put(new Key<Source>(name, Source.class), new FileSource(file));
            return true;
          }
        }
      }
    }
    debug("SL-CZTP-FAILED="+path);
    // raise an error that name could not be found.
    throw new SourceLocatorException(name, path);
  }
  
  
  /**
   * Retrieve the czt.properties file within user.dir or "."
   * @return the properties file containing information from czt.properties, or null if not found.
   * @throws CommandException if czt.properties cannot be processed
   */
  public static Properties retrieveCZTProperties() throws CommandException
  {
    debug("Trying czt.path as user.dir and look for czt.properties");
    // if not set, look for the user working directory, or "." by default      
    String path = System.getProperty("user.dir", ".");
    debug("SL-SYS-user.dir  = " + path);
    String filename = path + "/czt.properties";
    File cztpropsfile = new File(filename);
    debug("SL-CZTP-fileexists? = " + filename + " " + cztpropsfile.exists());
    Properties cztprops = null;
    if (cztpropsfile.exists())
    {
        // if czt.properties lives on the working directory (or ".")
        // retrieve its values
        cztprops = new Properties();
        debug("SL-CZTP-retrival");
        try 
        {          
          FileInputStream fis = new FileInputStream(cztpropsfile);
          //cztprops.loadFromXML(fis);          
          cztprops.load(fis);
        } catch (IOException e)
        {        
          throw new SourceLocatorException("czt.properties", path, e);
        }        
    }
    debug("SL-CZTP-czt.path = " + path);
    return cztprops;
  }
  
  /**
   * Very simple path splitting through <code>path.split(";")</code>.
   * Any more complicated behaviour can be defined differently elsewhere.
   * 
   * @param path the string to split, it expects the path to be non-null and non-empty
   * @return a list of paths to search for files
   */
  public static List<String> processCZTPaths(String path)
  {
    assert path != null && !path.isEmpty() : "invalid czt.path to process";
    return Arrays.asList(path.split(";"));
  }
  
  private static Logger getLogger()
  {
    return Logger.getLogger(SectionManager.class.getName());
  }
  
  private static void debug(String msg)
  {    
    // log the stuff done through searching
    //System.out.println(msg);
    getLogger().finest(msg);
  }

  /**
   * Exception thrown when source could not be found.
   */
  @SuppressWarnings("serial")
  public static class SourceLocatorException
    extends CommandException
  {
    private String name_;
    private String path_;

    public SourceLocatorException(String name, String path)
    {
      super("Cannot find source for section " + name
          + " with czt.path="+path);
      name_ = name;
      path_ = path;
    }
    
    public SourceLocatorException(String name, String path, Throwable cause)
    {
      super("Cannot find source for section " + name
          + " with czt.path="+path, cause);
      name_ = name;
      path_ = path;      
    }

    public String getName()
    {
      return name_;
    }

    public String getPath()
    {
      return path_;
    }
  }  
}
