/**
Copyright 2003 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
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
package net.sourceforge.czt.z2b;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.ZString;

import net.sourceforge.czt.z2b.*;


/**
 * This class scans a Z predicate/expression to see if it contains
 * various kinds of decorated variables.
 *
 * TODO: improve this to ignore bound variables (when we get a
 *       proper free-variable checking class).
 *
 * @author Mark Utting
 */
public class FreeVarChecker
  implements TermVisitor,
             ZDeclNameVisitor,
	     ZRefNameVisitor
{
  protected boolean foundPrime;
  protected boolean foundOutput;
  protected boolean foundInput;

  protected void reset()
  {
    foundPrime = false;
    foundOutput = false;
    foundInput = false;
  }

  public boolean containsPrimesOrOutputs(Term t)
  {
    reset();
    t.accept(this);
    return foundPrime || foundOutput;
  }

  public boolean containsInputs(Term t)
  {
    reset();
    t.accept(this);
    return foundInput;
  }

  /* =============================================
     The visitor methods (these set the found* flags to true).
     They do not change the AST they are visiting.
     =============================================
  */
  
  /** This generic visit method recurses into all Z terms. */
  public Object visitTerm(Term term) {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public void visitName(ZStrokeList strokes)
  {
    if (strokes.size() > 0) {
      Stroke str = strokes.get(strokes.size()-1);
      if (str instanceof OutStroke)
	foundOutput = true;
      else if (str instanceof NextStroke)
	foundPrime = true;
      else if (str instanceof InStroke)
	foundInput = true;
    }
  }

  public Object visitZDeclName(ZDeclName zDeclName)
  {
    visitName(zDeclName.getZStrokeList());
    return zDeclName;
  }

  public Object visitZRefName(ZRefName zRefName)
  {
    visitName(zRefName.getZStrokeList());
    return zRefName;
  }
}
