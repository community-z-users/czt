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

package net.sourceforge.czt.rules;

import java.io.*;
import java.net.URL;
import java.util.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.parser.zpatt.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.jaxb.JaxbXmlReader;

import static net.sourceforge.czt.rules.ProverUtils.*;

public class SimpleProverTest
  extends TestCase
{
  Factory factory_ = new Factory(new ProverFactory());
  SectionManager manager_ = new SectionManager();

  public void testSimple1()
  {
    prove("/simple1.tex");
  }

  public void testSimple2()
  {
    prove("/simple2.tex");
  }

  public void testSimple3()
  {
    prove("/simple3.tex");
  }

  public void testSimpleUnfold()
  {
    try {
      prove("/simpleUnfold.tex");
      fail("Should throw IllegalStateException");
    }
    catch (IllegalStateException e) {
      // ok
    }
  }

  private void prove(String resource)
  {
    try {
      URL url = getClass().getResource(resource);
      assertFalse(url == null);
      Term term = ParseUtils.parse(new UrlSource(url), manager_);
      TypeCheckUtils.typecheck(term, manager_);
      String sectname = term.accept(new GetZSectNameVisitor());
      Map<String,Rule> rules = collectRules(term);
      List<ConjPara> conjectures = collectConjectures(term);
      for (Iterator<ConjPara> i = conjectures.iterator(); i.hasNext(); ) {
        ConjPara conjPara = i.next();
        PredSequent sequent = factory_.createPredSequent();
	CopyVisitor visitor = new CopyVisitor(factory_);
        sequent.setPred((Pred) conjPara.getPred().accept(visitor));
        SimpleProver prover =
          new SimpleProver(rules, manager_, sectname);
        if (! prover.prove(sequent)) {
          StringWriter writer = new StringWriter();
          PrintUtils.print(conjPara.getPred(),
                           writer,
                           manager_,
                           "standard_toolkit",
                           Markup.LATEX);
          writer.close();
          fail("Failed to prove " + writer.toString());
        }
      }
    }
    catch (ParseException e) {
      fail("Should not throw exception " + e);
    }
    catch (IOException e) {
      fail("Should not throw exception " + e);
    }
  }
}
