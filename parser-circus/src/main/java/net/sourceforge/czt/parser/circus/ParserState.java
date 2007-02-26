/*
  Copyright (C) 2007 Leo Freitas
  Copyright (C) 2007 Petra Malik
  This file is part of the CZT project.

  The CZT project contains free software;
  you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.circus;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.util.Factory;

public class ParserState
  extends net.sourceforge.czt.parser.z.ParserState
{
  /**
   * Unique number seed for implicitly declared action names.
   */                         
  private static int implicitlyActUniqueNameSeed_ = 0;
    
  /**
   * Unique number seed for implicitly declared process names.
   */  
  private static int implicitlyProcUniqueNameSeed_ = 0;

  /**
   * <p>List of implicitly declared actions as action paragraphs,
   * where the action name is given according to
   * <code>implicitlyActUniqueNameSeed_</code> static field.</p>
   *
   * <p>This list is cleared at the <code>BasicProcess</code> related
   * productions so that they are always related to the current basic
   * process being parsed.</p>
   */
    private List<ActionPara> implicitlyDeclActPara_ =
      new ArrayList<ActionPara>();

  /**
   * <p>List of implicitly declared processes as process paragraphs,
   * where the process name is given according to
   * &lt;code&gt;implicitlyProcUniqueNameSeed_&lt;/code&gt; static
   * field.</p>
   *
   * <p>This list is cleared at the <code>ZSect</code> related
   * productions so that they are always related to the current Z
   * section being parsed.</p>
   */
  private List<ProcessPara> implicitlyDeclProcPara_ =
    new ArrayList<ProcessPara>();

  private Factory factory_ = new Factory();
           
  /**
   * Clears the implicitly declared actions cache for the current
   * <code>BasicProcess/code>.  It also resets the unique name seed to
   * zero.
   */
  public void clearBasicProcessOnTheFlyCache()
  {
    implicitlyActUniqueNameSeed_ = 0;
    implicitlyDeclActPara_.clear();      
  }
    
  /**
   * Clears the implicitly declared processes cache for the current
   * <code>ZSect</code>.  It also resets the unique name seed to zero.
   */
  public void clearSectProcessOnTheFlyCache()
  {
    implicitlyProcUniqueNameSeed_ = 0;
    implicitlyDeclProcPara_.clear();      
  }

  /**
   * Creates a unique string for implicitly declared actions.
   */
  public String createImplicitlyDeclActUniqueName()
  {
    String result = "$$implicitAct" + implicitlyActUniqueNameSeed_;
    implicitlyActUniqueNameSeed_++;
    return result;
  }

  /**
   * Creates a unique string for implicitly declared processes.
   */
  public String createImplicitlyDeclProcUniqueName()
  { 
    String result = "$$implicitProc" + implicitlyProcUniqueNameSeed_;
    implicitlyProcUniqueNameSeed_++;
    return result;
  }

  /**
   * Add an implicitly declared action to the current
   * <code>BasicProcess</code> cache.  It also includes an
   * <code>OnTheFlyDefAnn</code> for the action the paragraph defines.
   */
  public void addImplicitlyDeclActionPara(ActionPara ap)
  {
    assert ap.getCircusAction().getAnn(OnTheFlyDefAnn.class) == null :
      "Action already had an on-the-fly annotation";
    ap.getCircusAction().getAnns().add(factory_.createOnTheFlyDefAnn());
    implicitlyDeclActPara_.add(ap);
  }

  /**
   * Add an implicitly declared process to the current
   * <code>ZSect</code> cache.  It also includes an
   * <code>OnTheFlyDefAnn</code> for the process the paragraph
   * defines.
   */
  public void addImplicitlyDeclProcessPara(ProcessPara pp)
  {
    assert pp.getCircusProcess().getAnn(OnTheFlyDefAnn.class) == null :
      "Process already had an on-the-fly annotation";
    pp.getCircusProcess().getAnns().add(factory_.createOnTheFlyDefAnn());
    implicitlyDeclProcPara_.add(pp);
  }

  public List<ActionPara> getImplicitlyDeclActPara()
  {
    return implicitlyDeclActPara_;
  }
}
