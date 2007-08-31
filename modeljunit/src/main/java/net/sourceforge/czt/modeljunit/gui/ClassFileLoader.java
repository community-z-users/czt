
package net.sourceforge.czt.modeljunit.gui;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

/**
 * ClassFileLoader.java
 *
 * @author rong
 * ID : 1005450
 * 15th Aug 2007
 * */
public class ClassFileLoader extends ClassLoader
{
  private static ClassFileLoader m_loader;

  private ClassFileLoader()
  {
  }

  public static ClassFileLoader createLoader()
  {
    if (m_loader == null)
      m_loader = new ClassFileLoader();
    return m_loader;
  }
/*
  public Class<?> findClass(String name)
  {
    byte[] data = loadClassData(name);
    Class<?> theClass = defineClass(name, data, 0, data.length);
    return theClass;

  }
*/
  public static int runtime = 0;
  public Class<?> loadClass(String classname)
  {

    FileInputStream fis = null;
    byte[] data = null;
    // Bad coding style, just try
    try
    {
      Class<?> modelclass = Class.forName(classname);
      return modelclass;
    }
    catch (Exception exp)
    {
      try {
        fis = new FileInputStream(new File(Parameter.getModelLocation()));
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        int ch = 0;
        while ((ch = fis.read()) != -1) {
          baos.write(ch);
        }
        data = baos.toByteArray();
      }
      catch (IOException e) {
        e.printStackTrace();
      }
    }
    // System.out.println("ClassFileLoader.loadClass: "+classname+" load time: "+runtime);
    Class<?> theClass = defineClass(classname, data, 0, data.length);
    return theClass;
  }

}
