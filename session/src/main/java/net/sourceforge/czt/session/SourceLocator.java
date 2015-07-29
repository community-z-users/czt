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
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * A command to compute the URL for a Z section.
 * 
 * This first looks for /lib/<code>name</code>.tex in the CZT sources,
 * then searches for a variety of file extensions in the directory
 * specified by czt.path.
 */
public class SourceLocator extends AbstractCommand
{
  private final static String[] suffix_ = Markup.KNOWN_FILENAME_SUFFIXES;

  public static final String PROP_CZT_PATH = "czt.path";


  /**
   * Locates the given name as a toolkit within CZT.jar /lib/name.tex
   * @param name
   * @return  URL for name
   */
  protected URL locateToolkit(String name)
  {
    /*
     * When CZT core is package in one JAR (czt.jar), the toolkits are all collected
     * together during the build. In a modular approach (separate JARs), this does
     * not work, because the toolkits need to be resolved for different classes.
     * 
     * Implemented a workaround at the moment, where all providers are registered
     * in /toolkit.loc file as classes from different packages. Then we use
     * Class.getResource() for each provider to resolve them. This allows to locate
     * toolkits in different JARs and still works for a single JAR build.
     * 
     * TODO: Investigate a better resource sharing/registry approach.
     */
    for (Class<?> toolkitProvider : ToolkitProviders.INSTANCE.providers) {
      URL toolkitUrl = locateToolkitForClass(toolkitProvider, name);
      if (toolkitUrl != null) {
        return toolkitUrl;
      }
    }
    
    return null;
  }
  
  protected URL locateToolkitForClass(Class<?> sourceClass, String name)
  {
    // see if "name" is a toolkit in JAR of the specified class (i.e., parser-zeves.jar/lib/name.tex).
    // This comes with assumptions that there can be several JARs containing toolkit files,
    // each under *.jar/lib/name.tex
    String filename = "/lib/" + name + ".tex";
    return sourceClass.getResource(filename);
  }
  
  /**
   * Tries to locate the resource named for the given section manager.
   * The lookup algorithm for name as follows :
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
  protected boolean doCompute(String name, SectionManager manager)
    throws CommandException
  {
    traceLog("SL-locate       = " + name);
    URL url = locateToolkit(name);
    if (url != null) {
      traceLog("SL-TK-found     = "+url.toString());
      // source locators have no key dependency
      manager.endTransaction(new Key<Source>(name, Source.class), new UrlSource(url));
      return true;
    }
    traceLog("SL-NO-TK        = try current directory.");
    // see if "name" is within the current directory 
    // with all possible sufixes (i.e., ./name.suffix)
    for (int i = 0; i < suffix_.length; i++) {
      final String filename = name + suffix_[i];
      File file = new File(filename);
      if (file.exists() && ! file.isDirectory()) {
        traceLog("SL-CURDIR-FOUND = "+filename);
        manager.endTransaction(new Key<Source>(name, Source.class), new FileSource(file));
        return true;
      }
    }
    traceLog("SL-NO-CURDIR    = try czt.path");
    String path = manager.getProperty(PROP_CZT_PATH);
    traceLog("SL-SM-czt.path  = " + path);
    // if empty or null, try czt.properties
    if (path == null || path.isEmpty())
    {
      Properties cztprops = retrieveCZTProperties(manager.getDialect());
      if (cztprops != null)
      {
        // gets within czt.properties (if it exists) czt.path or "." by default
        path = cztprops.getProperty(PROP_CZT_PATH, ".");
        // sets the manager with all properties within cztprops
        // hence overriding any previous properties within it.
        manager.setProperties(cztprops);
        traceLog("SL-SM-CZT-prop  = " + cztprops);
      }
    }
    if (path != null && !path.isEmpty())
    {
      // try to retrieve czt.path
      List<String> cztpaths = processCZTPaths(path);   
      // split the paths nicely
      for (String cztpath : cztpaths)
      {     
        traceLog("SL-SM-cztpath[i] = " + cztpath);
        // check czt.path/name with all possible sufixes as last resort
        for (int i = 0; i < suffix_.length; i++) {
          final String filename = cztpath + "/" + name + suffix_[i];
          File file = new File(filename);
          if (file.exists()) {
            traceLog("SL-CZTP-found   = "+filename);
            manager.endTransaction(new Key<Source>(name, Source.class), new FileSource(file));
            return true;
          }
        }
      }
    }
    traceLog("SL-CZTP-FAILED  = "+path);
    // raise an error that name could not be found.
    throw new SourceLocatorException(manager.getDialect(), name, path);
  }
  
  
  /**
   * Retrieve the czt.properties file within user.dir or "."
   * @return the properties file containing information from czt.properties, or null if not found.
   * @throws CommandException if czt.properties cannot be processed
   */
  public static Properties retrieveCZTProperties(Dialect d) throws CommandException
  {
    traceLog("Trying czt.path as user.dir and look for czt.properties");
    // if not set, look for the user working directory, or "." by default      
    String path = System.getProperty("user.dir", ".");
    traceLog("SL-SYS-user.dir  = " + path);
    String filename = path + "/czt.properties";
    File cztpropsfile = new File(filename);
    traceLog("SL-CZT-fileexists? = " + filename + " " + cztpropsfile.exists());
    Properties cztprops = null;
    if (cztpropsfile.exists())
    {
        // if czt.properties lives on the working directory (or ".")
        // retrieve its values
        cztprops = new Properties();
        traceLog("SL-CZT-retrival");
        try 
        {          
          FileInputStream fis = new FileInputStream(cztpropsfile);
          //cztprops.loadFromXML(fis);
          try {
            cztprops.load(fis);
          } finally {
            fis.close();
          }
        } catch (IOException e)
        {        
          throw new SourceLocatorException(d, "czt.properties", path, e);
        }        
    }
    traceLog("SL-CZT-czt.path = " + path);
    return cztprops;
  }
  
  /**
   * Very simple path splitting through <code>path.split(File.pathSeparator)</code>.
   * Any more complicated behaviour can be defined differently elsewhere.
   * 
   * @param path the string to split, it expects the path to be non-null and non-empty
   * @return a list of paths to search for files
   */
  public static List<String> processCZTPaths(String path)
  {
    assert path != null && !path.isEmpty() : "invalid czt.path to process";
    return Arrays.asList(path.split(File.pathSeparator));
  }
  
  private static void checkString(String s)
  {
    if (s == null || s.isEmpty())
    {
      throw new IllegalArgumentException("SL-STR-NULL-OR-EMPTY");
    }
  }

  /**
   * For a file "./dir/foo.ext" or ".\dir\foo.ext", removes
   * the path such that the result is "foo.ext". If "foo.ext"
   * is given, it is directly returned.
   * @param filename full file name to remove path
   * @return file name with path removed
   */
  public static String removePath(String filename)
  {
    checkString(filename);
    int barIdx = filename.lastIndexOf(File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('/');
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('\\');
    }
    return barIdx == -1 ? filename : filename.substring(barIdx + 1);
  }

  /**
   * For a file "./dir/foo.ext" or ".\dir\foo.ext", extracts
   * the path such that the result is "./dir/". If "foo.ext"
   * is given, "./" is returned.
   * @param filename full file name to remove path
   * @return path from file name
   */
  public static String extractPath(String filename)
  {
    checkString(filename);
    int barIdx = filename.lastIndexOf(File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('/');
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('\\');
    }
    return barIdx == -1 ? "./" : filename.substring(0, barIdx);
  }

  /**
   * For a file "./dir/foo.ext", returns "./dir/foo".
   * If no extension is present, the filename given is returned.
   * @param filename full file name to remove extension
   * @return filename without extension
   */
  public static String getFileNameNoExt(String filename)
  {
    checkString(filename);
    int dotIdx = filename.lastIndexOf('.');
    return dotIdx == -1 ? filename : filename.substring(0, dotIdx);
  }

  /**
   * Get the CZT Source name from a given file. It removes the
   * path for the file name without extension.
   *
   * @param filename
   * @return
   */
  public static String getSourceName(String filename)
  {
    // transforms c:\temp\myfile.tex into myfile
    String resource = removePath(getFileNameNoExt(filename));
    return resource;
  }

  public static String getCZTPathFor(File file, SectionManager manager)
  {
    assert file != null && manager != null;
    String localcztpath = manager.getProperty(PROP_CZT_PATH);
    if (localcztpath == null || localcztpath.isEmpty())
    {
      localcztpath = file.getParent();
    }
    else
    {
      localcztpath += File.pathSeparator + file.getParent();
    }
    return localcztpath;
  }

  public static void addCZTPathFor(File file, SectionManager manager)
  {
    String localcztpath = getCZTPathFor(file, manager);
    if (localcztpath == null || localcztpath.isEmpty())
      throw new IllegalArgumentException("Cannot add null path to czt.path for file " + file);
    manager.setProperty(PROP_CZT_PATH, localcztpath);
  }
  
  /**
   * Exception thrown when source could not be found.
   */
  public static class SourceLocatorException
    extends CommandException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 5010516393930955258L;
	
	private final String name_;
    private final String path_;

    public SourceLocatorException(Dialect d, String name, String path)
    {
      super(d, "Cannot find source for section " + name
          + " with czt.path="+path);
      name_ = name;
      path_ = path;
    }
    
    public SourceLocatorException(Dialect d, String name, String path, Throwable cause)
    {
      super(d, "Cannot find source for section " + name
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
  
  /** A singleton collection of Z toolkit provider classes */
  private enum ToolkitProviders
  {
    INSTANCE;

    // load toolkit providers into a singleton enum
    private List<Class<?>> providers = Collections.unmodifiableList(loadToolkitProviders());
  }
  
  /**
   * Loads a collection of classes that represent Z toolkit providers. The toolkit files
   * may be located in separate JARs, thus we read class names representing each JAR and
   * try to resolve toolkit files from them.
   */
  private static List<Class<?>> loadToolkitProviders()
  {
    URL providersListUrl = SourceLocator.class.getResource("/toolkit.loc");
    
    getLogger().log(Level.FINEST, "Load commands from URL ''{0}''", providersListUrl);
    final String errorMessage = "Error while loading toolkit locations " +
      "for the section manager: Cannot open " + providersListUrl.toString();
    try {
      Properties props = new Properties();
      InputStream is = providersListUrl.openStream();
      try {
        props.loadFromXML(is);
      } finally {
        is.close();
      }
        
      // get the keys (class names)
      Set<String> classNames = props.stringPropertyNames();
      List<Class<?>> toolkitProviders = new ArrayList<Class<?>>();
      
      // add current class as provider
      toolkitProviders.add(SourceLocator.class);
      
      // resolve the class for each class name
      for (String className : classNames) {
        Class<?> aClass = toClass(className);
        
        // only use classes that are available (e.g. we may have a subset of CZT core)
        if (aClass != null) {
          toolkitProviders.add(aClass);
        }
      }
      
      return toolkitProviders;
    }
    catch (IOException e) {
      getLogger().warning(errorMessage);
      throw new RuntimeException(errorMessage, e);
    }
  }
  
  private static final Logger getLogger()
  {
    return Logger.getLogger(SourceLocator.class.getName());
  }
  
  /**
   * Returns Class.forName(className) but does not throw exceptions.
   * 
   * Exception messages are sent to a logger, so will probably not
   * be visible to users.
   * @param name 
   * 
   * @return null if the requested class could not be loaded.
   */
  private static Class<?> toClass(String name)
  {
    try {
      return Class.forName(name);
    }
    catch (ExceptionInInitializerError e) {
      final String message = "Cannot get class " + name +
        "; exception in initialzier";
      getLogger().warning(message);
    }
    catch (LinkageError e) {
      final String message = "Cannot get class " + name +
        "; linkage error";
      getLogger().warning(message);
    }
    catch (ClassNotFoundException e) {
      final String message = "Cannot get class " + name +
        "; class cannot be found";
      getLogger().finest(message);
    }
    return null;
  }
}
