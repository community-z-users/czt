/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.util;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;

/**
 *
 * @author leo
 */
public abstract class CztPrintString {
  
  private final Dialect extension_;
  private final String string_;
  
    /**
   * @throws NullPointerException if value is <code>null</code>.
   */
  public CztPrintString(String value)
  {
    this(value, SectionManager.DEFAULT_EXTENSION);
  }

  /**
   * @throws NullPointerException if value or extension is <code>null</code>.
   */
  public CztPrintString(String value, Dialect extension)
  {
    if (value == null || extension == null) {
      throw new NullPointerException("Invalid Czt string or extension dialect");
    }
    extension_ = extension;
    string_ = value;
  }

  public Dialect getExtension()
  {
    return extension_;
  }

  public String toString()
  {
    return string_;
  }
}
