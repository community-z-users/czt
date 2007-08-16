package net.sourceforge.czt.modeljunit.gui;

import java.io.ByteArrayOutputStream;    
import java.io.File;    
import java.io.FileInputStream;    
import java.io.IOException;

public class ClassFileLoader extends ClassLoader
{
  private static ClassFileLoader m_loader;
  private ClassFileLoader()
  {}
  
  public static ClassFileLoader createLoader()
  {
    if( m_loader == null )
      m_loader = new ClassFileLoader();
    return m_loader;
  }
  public Class findClass(String name) {    
    byte[] data = loadClassData(name); 
    return defineClass(name, data, 0, data.length);    
  }
  private byte[] loadClassData(String name) {    
    FileInputStream fis = null;    
    byte[] data = null;    
    try {    
      fis = new FileInputStream(new File(Parameter.getModelLocation()));    
      ByteArrayOutputStream baos = new ByteArrayOutputStream();    
      int ch = 0;    
      while ((ch = fis.read()) != -1) {    
        baos.write(ch);    
      }    
      data = baos.toByteArray();    
    } catch (IOException e) {    
      e.printStackTrace();    
    }    
    return data;    
  }    

}
