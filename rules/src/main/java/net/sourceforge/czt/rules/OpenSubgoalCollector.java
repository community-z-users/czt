/*
  Copyright (C) 2005, 2007 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.rules;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.unification.UnificationUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

public class OpenSubgoalCollector
  implements RuleApplVisitor,
             PredSequentVisitor,
             ProvisoVisitor,
             TermVisitor
{
  protected List<Sequent> subgoals_ = new ArrayList<Sequent>();

  public List<Sequent> getResult()
  {
    return subgoals_;
  }

  public Object visitRuleAppl(RuleAppl ruleAppl)
  {
    for (Sequent sequent : ruleAppl.getSequentList()) {
      sequent.accept(this);
    }
    return null;
  }

  public Object visitPredSequent(PredSequent predSequent)
  {
    if (predSequent.getDeduction() == null) {
      subgoals_.add(predSequent);
    }
    else {
      predSequent.getDeduction().accept(this);
    }
    return null;
  }

  public Object visitProviso(Proviso proviso)
  {
    if (proviso instanceof ProverProviso) {
      ProverProviso pp =(ProverProviso) proviso;
      if (ProverProviso.Status.PASS.equals(pp.getStatus())) {
        return null;
      }
    }
    subgoals_.add(proviso);
    return null;
  }

  public Object visitTerm(Term term)
  {
    VisitorUtils.visitTerm(this, term);
    return null;
  }
}
