/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.util;

/**
 *
 * @author leo
 */
public abstract class CztPrintString {
  
  private final String extension_;
  private final String string_;
  
    /**
   * @throws NullPointerException if value is <code>null</code>.
   */
  public CztPrintString(String value)
  {
    this(value, "z");
  }

  /**
   * @throws NullPointerException if value or extension is <code>null</code>.
   */
  public CztPrintString(String value, String extension)
  {
    if (value == null || extension == null) {
      throw new NullPointerException();
    }
    extension_ = extension;
    string_ = value;
  }

  public String getExtension()
  {
    return extension_;
  }

  public String toString()
  {
    return string_;
  }
}
