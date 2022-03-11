/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.base.util;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.logging.Level;
import java.util.logging.Logger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.TermImpl;

/**
 *
 * @author Leo Freitas
 * @date Apr 12, 2012
 */
public class TermInstanceCountManager 
{
  public final static int DEFAULT_TARGET_INCREASE = 3;
  public final static int DEFAULT_CALL_DEPTH_LOWER_BOUND = 0;
  public final static int DEFAULT_CALL_DEPTH_UPPER_BOUND = 6;
  
  public static void log(Term term, String extra)
  {
    log(term, extra, DEFAULT_CALL_DEPTH_LOWER_BOUND, DEFAULT_CALL_DEPTH_UPPER_BOUND, DEFAULT_TARGET_INCREASE);
  }
  
  public static void log(Term term, String extra, int callDepthLowerBound, int callDepthUpperBound, int targetIncrease)
  {
    Long instanceCount = null;
    Long startLoggingFrom = null;
    try
    {
      Field fic;
      Field fslf;
      try 
      {
        // TODO: or should it always be getDeclaredField?
        fic = term.getClass().getField("instanceCount_");
        fslf = term.getClass().getField("startLoggingFrom_");
      }
      catch (NoSuchFieldException a)
      {
        fic = term.getClass().getDeclaredField("instanceCount_");
        fslf = term.getClass().getDeclaredField("startLoggingFrom_");
      }
      fic.setAccessible(true);
      fslf.setAccessible(true);
      instanceCount = fic.getLong(null);
      startLoggingFrom = fslf.getLong(null);
      fic.setAccessible(false);
      fslf.setAccessible(false);
    }
    catch (SecurityException e)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Security exception when trying to get instance field for {0}", term.getClass().getName());
    }
    catch (NoSuchFieldException f)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Couldn''t find instance counting fields of {0}", term.getClass().getName());
    }
    catch (IllegalAccessException g)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Security exception when trying to get instance field for {0}", term.getClass().getName());
    }
    catch (IllegalArgumentException h)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Could not retrieve instance field for {0}", term.getClass().getName());      
    }
    catch (ExceptionInInitializerError i)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Could not retrieve instance field for {0}", term.getClass().getName());            
    }
    catch (NullPointerException j)
    {
      // ignore exception
      Logger.getLogger(term.getClass().getName()).log(Level.WARNING, "Could not retrieve instance field for {0}", term.getClass().getName());      
    }  
    boolean shouldL = instanceCount != null && startLoggingFrom != null && instanceCount >= startLoggingFrom;
    if (shouldL)
    {
      final String caller = whoWasCalling(callDepthLowerBound, callDepthUpperBound, targetIncrease);
      log(instanceCount + "\t" + caller + 
                  (term instanceof TermImpl ? 
                      (((TermImpl)term).getFactory() != null ? 
                          " (" + ((TermImpl)term).getFactory().getClass().getSimpleName() + ")" 
                          : "(null factory)") : "") + "\n\t\t" + extra);
    }
  }
  
  private static void log(String msg)
  {
    System.out.println(msg);
  }

  protected static String whoWasCalling(int callDepthLowerBound, int callDepthUpperBound, int targetIncrease)
  {
    Throwable t = new Throwable();
    t.fillInStackTrace();
    StackTraceElement[] stes = t.getStackTrace();
    StringBuffer result = new StringBuffer();
    for(int i = callDepthUpperBound; i >= callDepthLowerBound; i--)
    {
      int targetDepth = targetIncrease + i;
      if (targetDepth >= 0 && targetDepth < stes.length)
      {
        StackTraceElement el = stes[targetDepth];
        final String msg = el.getClassName() + "." + el.getMethodName() + ", " + el.getLineNumber();
        result.append(msg);
        if (i > callDepthLowerBound) result.append("\n\t");
      }
    }
    return result.toString();
  }
  
  public static long instancesCount(Term term, boolean live)
  {
    return instancesCount(term.getClass(), live);
  }
  
  public static long instancesCount(Class<? extends Term> termCls, boolean live)
  {
    try
    {
      Method mic = termCls.getDeclaredMethod("instanceCount", (Class<?>[]) null);
      long instancesCount = (Long)mic.invoke(null, (Object[]) null);

      long instancesFinalised = 0;
      if (live)
      {
        Method mcf = termCls.getDeclaredMethod("countingFinaliser", (Class<?>[]) null);
        boolean countingFinaliser = (Boolean)mcf.invoke(null, (Object[]) null);

        if (countingFinaliser)
        {
          Method mif = termCls.getDeclaredMethod("instancesFinalised", (Class<?>[]) null);
          instancesFinalised = (Long)mif.invoke(null, (Object[]) null);
        }
        else
        {
           Logger.getLogger(termCls.getName()).log(Level.WARNING, "Could not count finalised objects for {0}. It does not have a finalize method", termCls.getName());
        }
      }
      return instancesCount - instancesFinalised;
    }
    catch (IllegalAccessException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "Security exception when trying to get instance field for {0}", termCls.getName());
    }
    catch (IllegalArgumentException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "Illegal argument exception when trying to get instance field for {0}", termCls.getName());
    }
    catch (InvocationTargetException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "Invocation target argument exception when trying to get instance field for {0}", termCls.getName());
    }
    catch (NoSuchMethodException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "No such method exception when trying to get instance field for {0}", termCls.getName());
    }
    catch (SecurityException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "Security exception when trying to get instance field for {0}", termCls.getName());
    }
    catch (ClassCastException ex)
    {
       Logger.getLogger(termCls.getName()).log(Level.WARNING, "Class cast exception when trying to get instance field for {0}", termCls.getName());
    }
    throw new IllegalArgumentException("Could not retrieve instances count for " + termCls.getName());
  }

  private TermInstanceCountManager()
  {
  }
  
  //protected static void log(long instanceCount, long logFrom, int callDepthUpperBound, int targetIncrease)
  //{
  //  final String caller = whoWasCalling(instanceCount >= logFrom, 0, callDepthUpperBound, targetIncrease);
  //  log(instanceCount >= logFrom, instanceCount + "\t" + caller);// + (factory_ != null ? " (" + factory_.getClass().getSimpleName() + ")" : "(null)"));
  //}
  
  //protected static String whoWasCalling(boolean shouldLog, int callDepthUpperBound)
  //{
  //  return whoWasCalling(shouldLog, 0, callDepthUpperBound, DEFAULT_TARGET_INCREASE);
  //}

  //protected static String whoWasCalling(boolean shouldLog, int callDepthLowerBound, int callDepthUpperBound)
  //{
  //  return whoWasCalling(shouldLog, callDepthLowerBound, callDepthUpperBound, DEFAULT_TARGET_INCREASE);
  //}
}
