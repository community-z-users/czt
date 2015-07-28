/*
 * PrintException.java
 *
 * Created on 23 June 2006, 15:09
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;

/**
 *
 * @author leo
 */
public class PrintException	 	
	extends CommandException
implements CztErrorList {
  
  /**
	 * 
	 */
	private static final long serialVersionUID = -7918297654639663505L;
private final TreeMap<String, List<String>> warnings_ = new TreeMap<String, List<String>>();

  private final Dialect dialect_;
	private final List<CztError> errorList_;
  
  public PrintException(Dialect d)
  {
      super(d);
      if (d == null) throw new NullPointerException();
      dialect_ = d;
      errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }

  public PrintException(Dialect d, String message)
  {
    super(d, message);
    if (d == null) throw new NullPointerException();
    dialect_ = d;
    errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }
  

  public PrintException(Dialect d, List<CztError> errorList)
  {
	  this(d);
    if (errorList == null) throw new NullPointerException();
   	errorList_.addAll(errorList);
  }

  public PrintException(Dialect d, CztError error)
  {
	this(d);
	if (error == null) throw new NullPointerException();
    errorList_.add(error);
  }

  public PrintException(Dialect d, String message, Throwable cause)
  {
    super(d, message, cause);
    if (d == null) throw new NullPointerException();
    dialect_ = d;
    errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }

  public PrintException(Dialect d, Throwable cause)
  {
    super(d, cause);
    if (d == null) throw new NullPointerException();
    dialect_ = d;
    errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }
  
  public PrintException(Dialect d, String message, Map<String, List<String>> warnings) {
      super(d, message);
      if (d == null) throw new NullPointerException();
      dialect_ = d;
      warnings_.putAll(warnings);
      errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }
    
  public PrintException(Dialect d, String message, Throwable cause, Map<String, List<String>> warnings) {
      super(d, message, cause);
      if (d == null) throw new NullPointerException();
      dialect_ = d;
      warnings_.putAll(warnings);
      errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }

  public PrintException(Dialect d, Throwable cause, Map<String, List<String>> warnings) {
      super(d, cause);
      if (d == null) throw new NullPointerException();
      dialect_ = d;
      warnings_.putAll(warnings);
      errorList_ = new ArrayList<CztError>(PerformanceSettings.INITIAL_ARRAY_CAPACITY); 
  }
  
  public Map<String, List<String>> getZSectWarnings() {
      return warnings_;
  }   
  
  public Dialect getDialect()
  {
	  return dialect_;
  }
  
  @Override
  public String toString() {
      StringBuilder str = new StringBuilder(super.toString());
      str.append("\n");
      for(Map.Entry<String, List<String>> sect : warnings_.entrySet()) {          
          str.append("Warnings for ").append(sect.getKey()).append("\n");
          for(String warn : sect.getValue()) {
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
