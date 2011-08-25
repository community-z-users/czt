/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the czt project.
 * 
 * The czt project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The czt project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with czt; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.util;

import java.net.URL;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.VCGPropertyKeys;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author Leo Freitas
 * @date Dec 26, 2010
 */
public abstract class VCGTest extends CztManagedTest
  implements VCGPropertyKeys {

  /**
   * Creates a new test case with a fresh section manager and given extension
   * @param extension usually "z" or "circus"
   * @param debug true or false
   */
  protected VCGTest(String extension, boolean debug)
  {
    super(extension, debug);
  }
  
  /**
   * Creates a test case with given (shared) section manager and debug flag. 
   * @param manager given
   * @param debug 
   */
  protected VCGTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }

  @Override
  protected TestCase createPositiveTest(URL url)
  {
    throw new UnsupportedOperationException("override for your own test class");
  }

  @Override
  protected TestCase createNegativeTest(URL url, String exception, Class<?> expCls)
  {
    throw new UnsupportedOperationException("override for your own test class");
  }

  @Override
  protected final boolean includeTest(String name, boolean positive)
  {
    if (positive)
      return super.includeTest(name, positive) && includeVCGTest(name, positive);
    else
      return super.includeTest(name, positive);
  }

  protected abstract boolean includeVCGTest(String name, boolean positive);

  /**
   * Positive test case
   * @param <R>
   */
  protected class NormalVCGTest<R> extends CztManagedTest.TestNormal
  {
    private final VCGUtils<R> vcgu_;

    public NormalVCGTest(URL url, VCGUtils<R> vcgu)
    {
      super(url);
      assert vcgu != null;
      vcgu_ = vcgu;
    }

    protected void config() throws VCGException
    {
      if (isDebugging())
      {
        System.out.println("Config SM for " + getSourceName());
      }
      vcgu_.getVCG().config();
    }

    /**
     * The default positive test case does nothing beyond parsing.
     * @param term
     * @throws Exception
     */
    @Override
    protected void doTest(Spec term) throws Exception
    {
      config();
      int vcEnvCnt = 0;
      if (isDebugging())
      {
        System.out.println("Creating VCs for " + getSourceName() + " at " + getTestsPath());
      }
      for (Sect sect : term.getSect())
      {
        if (sect instanceof ZSect)
        {
          ZSect zSect = (ZSect)sect;
          VCEnvAnn<R> zSectVCEnvAnn = vcgu_.calculateZSectVCEnv(zSect);
          vcgu_.printToFile(zSectVCEnvAnn, getTestsPath(), getMarkup());
          vcEnvCnt++;
        }
      }
      System.out.println("Created " + vcEnvCnt + " VCEnvAnn for " + getTestsPath() + "/" + getSourceName());
    }

    /**
     * Exceptions on positive tests are errors.
     * @param e
     * @param failureMsg
     * @return false
     */
    @Override
    protected boolean handledException(Throwable e, StringBuilder failureMsg)
    {
      boolean result = super.handledException(e, failureMsg);
      if (!result)
      {
        if (e instanceof DefinitionException)
        {
          failureMsg.append("DefinitionException = \n");
          failureMsg.append(((DefinitionException)e).getMessage(true));
          failureMsg.append("\n DC-TEST-DEF-TBL-EXCEPTION-IGNORE " + url_);
          result = true;//don't fail, but print out --- TODO: change to false when more examples are handled.
        }
        else if (e instanceof TypeErrorException)
        {
          TypeErrorException te = (TypeErrorException)e;
          VCGUtils.printTypeErrors(te);
          result = true;
        }
        else if (e instanceof VCGException && e.getCause() instanceof CommandException)
        {
          CommandException vcge = (CommandException)e.getCause();
          if (vcge.getCause() instanceof ParseException)
          {
            VCGUtils.printParseErrors((ParseException)vcge.getCause());
            result = true;
          }
          else if (vcge.getCause() instanceof TypeErrorException)
          {
            VCGUtils.printTypeErrors((TypeErrorException)vcge.getCause());
            result = true;
          }
          else if (/*e instanceof VCCollectionException &&*/ vcge instanceof VCGException &&
                  vcge.getCause() instanceof DefinitionException)
          {
            failureMsg.append("DefTbl errors = \n");
            failureMsg.append(((DefinitionException)vcge.getCause()).getMessage(true));
            result = true;
          }
          SectionManager.traceWarning("VCG-RESULT-HAS-ERRORS");
        }
      }
      if (!result || isDebugging())
      {
        printStackTraceWithCauses(e);
      }
      return result;
    }
  }
}
