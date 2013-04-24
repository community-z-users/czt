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
  
  /**
	 * 
	 */
	private static final long serialVersionUID = -7918297654639663505L;
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
  
  @Override
  public String toString() {
      StringBuilder str = new StringBuilder(super.toString());
      str.append("\n");
      for(String sect : warnings_.keySet()) {          
          str.append("Warnings for ").append(sect).append("\n");
          for(String warn : warnings_.get(sect)) {
              str.append(warn);
              str.append("\n");
          }
          str.append("\n");
      }      
      return str.toString();
  }
  

  public List<CztError> getErrorList()
  {
    return errorList_;
  }

  public List<CztError> getErrors()
  {
    return errorList_;
  }

  public void printErrorList()
  {
	System.err.println("PrintException errors for " + getDialect().toString());
    for (CztError parseError : errorList_) {
      System.err.println(parseError.toString());
    }
  }

  @Override
  public String getMessage()
  {
    StringBuilder result = new StringBuilder();
    result.append("PrintException errors for ").
    	append(getDialect().toString()).
    	append(" with message ").
    	append(String.valueOf(super.getMessage())).append("\n");
    for (CztError parseError : errorList_) {
      result.append("\n").append(parseError.toString());
    }
    return result.toString();
  }
}
