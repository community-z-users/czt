/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.zpatt.util;

import java.io.*;
import java.net.URL;
import java.util.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.jaxb.JaxbXmlReader;

public class SimpleProverTest
  extends TestCase
{
  public void testFindSimpleProve()
  {
    try {
      JaxbXmlReader reader = new JaxbXmlReader();
      URL url = getClass().getResource("/zpatt/rule.xml");
      List rules = collectRules(reader.read(url.openStream()));
      Factory factory = new Factory(new ProverFactory());
      ProverJokerExpr joker1 = (ProverJokerExpr) factory.createJokerExpr();
      ProverJokerExpr joker2 = (ProverJokerExpr) factory.createJokerExpr();
      Pred pred = factory.createEquality(joker1, joker2);
      PredSequent sequent = factory.createPredSequent();
      sequent.setPred(pred);
      SimpleProver prover = new SimpleProver(rules, factory);
      assertTrue(prover.prove(sequent));
    }
    catch (IOException exception) {
      fail("Should not throw exception " + exception);
    }
  }

  public void testFailSimpleProve()
  {
    try {
      JaxbXmlReader reader = new JaxbXmlReader();
      URL url = getClass().getResource("/zpatt/rule.xml");
      List rules = collectRules(reader.read(url.openStream()));
      Factory factory = new Factory(new ProverFactory());
      ProverJokerExpr joker = (ProverJokerExpr) factory.createJokerExpr();
      Pred pred = factory.createEquality(joker, joker);
      PredSequent sequent = factory.createPredSequent();
      sequent.setPred(pred);
      SimpleProver prover = new SimpleProver(rules, factory);
      assertFalse(prover.prove(sequent));
    }
    catch (IOException exception) {
      fail("Should not throw exception " + exception);
    }
  }

  public static List<Rule> collectRules(Term term)
  {
    List<Rule> result = new ArrayList();  
    if (term instanceof Spec) {
      for (Iterator i = ((Spec) term).getSect().iterator(); i.hasNext(); ) {
        Sect sect = (Sect) i.next();
        if (sect instanceof ZSect) {
          for (Iterator j = ((ZSect) sect).getPara().iterator();
               j.hasNext(); ) {
            Para para = (Para) j.next();
            if (para instanceof Rule) {
              result.add((Rule) para);
            }
          }
        }
      }
    }
    return result;
  }
}
