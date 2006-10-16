/*
  Copyright (C) 2005 Petra Malik
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
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

public class Proof
{
  private PredSequent predSequent_;

  public Proof(Pred pred)
  {
    predSequent_ = ProverUtils.createPredSequent(pred, true);
  }

  public Proof(Expr expr)
  {
    predSequent_ = ProverUtils.createPredSequent(expr, true);
  }

  public Proof(ConjPara conjPara)
  {
    this(conjPara.getPred());
  }

  public Proof(PredSequent predSequent)
  {
    predSequent_ = predSequent;
  }

  public List<Sequent> getOpenSubgoals()
  {
    OpenSubgoalCollector collector = new OpenSubgoalCollector();
    predSequent_.accept(collector);
    return collector.getResult();
  }

  public List<Joker> getJokers()
  {
    JokerCollector collector = new JokerCollector();
    predSequent_.accept(collector);
    return collector.getResult();
  }

  public boolean done()
  {
    return getOpenSubgoals().isEmpty();
  }

  public boolean check(SectionManager manager, String section)
  {
    ProverProviso proviso = (ProverProviso) getOpenSubgoals().get(0);
    proviso.check(manager, section);
    return ProverProviso.Status.PASS.equals(proviso.getStatus());
  }

  public boolean apply(Rule rule)
    throws RuleApplicationException
  {
    PredSequent predSequent = (PredSequent) getOpenSubgoals().get(0);
    return SimpleProver.apply2(rule, predSequent);
  }

  public boolean apply(Rule[] rules, SectionManager manager, String section)
    throws RuleApplicationException
  {
    int ruleId = 0;
    while (! getOpenSubgoals().isEmpty()) {
      Object goal = getOpenSubgoals().get(0);
      if (goal instanceof ProverProviso) {
        if (! check(manager, section)) return false;
      }
      else {
	if (ruleId >= rules.length || ! apply(rules[ruleId])) return false;
	ruleId++;
      }
    }
    return true;
  }
}
