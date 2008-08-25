
package net.sourceforge.czt.modeljunit.gui;

import java.net.URL;
import java.net.URLClassLoader;

/*
 * ClassFileLoader.java
 * @author rong ID : 1005450 15th Aug 2007
 */
public class ClassFileLoader extends ClassLoader
{
  private static ClassFileLoader m_loader;

  private ClassFileLoader()
  {
  }

  public static ClassFileLoader getInstance()
  {
    if (m_loader == null)
      m_loader = new ClassFileLoader();
    return m_loader;
  }

  public static int runtime = 0;

  public Class<?> loadClass(String classname)
  {
    // http://forum.java.sun.com/thread.jspa?threadID=568853&messageID=2815072
    // that thread explained why i have to add file://C in front of strPL
    // java doc does not explain :(
    String strPL = Parameter.getPackageLocation();
    strPL = "file://" + strPL;
    String strPN = Parameter.getPackageName();
    if (strPN.charAt(strPN.length() - 1) != '.')
      strPN = strPN + ".";

    ClassLoader prevCL = Thread.currentThread().getContextClassLoader();
    // Create the class loader by using the given URL
    // Use prevCl as parent to maintain current visibility
    if (strPL != null && strPL.length() > 0) {
      try {
        ClassLoader cl = URLClassLoader.newInstance(new URL[]{new URL(strPL)},
            prevCL);

        // Set class loader to current thread
        Thread.currentThread().setContextClassLoader(cl);
        // Expect that environment properties are in
        // application resource file found at "url"

      }
      catch (Exception e) {
        e.printStackTrace();
      }
      finally {
        // Restore
        Thread.currentThread().setContextClassLoader(prevCL);
      }
    }

    try {
      Class<?> modelclass = Class.forName(strPN + classname);
      if (modelclass == null)
        System.out.println("NULL model class was returned!!!");
      return modelclass;
    }
    catch (Exception e) {
      e.printStackTrace();
    }

    System.out.println("NULL model class was returned!!!");
    return null;
  }
}
