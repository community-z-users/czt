/*
 * PrintException.java
 *
 * Created on 23 June 2006, 15:09
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.util;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.util.CztException;

/**
 *
 * @author leo
 */
public class PrintException extends CztException {
  
  private final TreeMap<String, List<String>> warnings_ = new TreeMap<String, List<String>>();

  public PrintException()
  {
      super();
  }

  public PrintException(String message)
  {
    super(message);
  }

  public PrintException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public PrintException(Throwable cause)
  {
    super(cause);
  }
  
  public PrintException(String message, Map<String, List<String>> warnings) {
      super(message);
      warnings_.putAll(warnings);
  }
    
  public PrintException(String message, Throwable cause, Map<String, List<String>> warnings) {
      super(message, cause);
      warnings_.putAll(warnings);
  }

  public PrintException(Throwable cause, Map<String, List<String>> warnings) {
      super(cause);
      warnings_.putAll(warnings);
  }
  
  public Map<String, List<String>> getZSectWarnings() {
      return warnings_;
  }   
  
  public String toString() {
      StringBuffer str = new StringBuffer(super.toString());      
      str.append("\n");
      for(String sect : warnings_.keySet()) {          
          str.append("Warnings for " + sect + "\n");
          for(String warn : warnings_.get(sect)) {
              str.append(warn);
              str.append("\n");
          }
          str.append("\n");
      }      
      return str.toString();
  }
}
