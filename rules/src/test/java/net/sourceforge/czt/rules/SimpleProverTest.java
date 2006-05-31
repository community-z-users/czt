/*
  Copyright (C) 2005, 2006 Petra Malik
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

  public void testSimple1()
    throws Exception
  {
    prove("/simple1.tex");
  }

  public void testSimple2()
    throws Exception
  {
    prove("/simple2.tex");
  }

  public void testSimpleUnfold()
    throws Exception
  {
    prove("/simpleUnfold.tex");
  }

  /** Proves all the conjectures in the given file.
   *  The file should contain just one Z Section,
   *  which contains the conjectures to be proved.
   *  The ruletable of that section (which includes any
   *  inherited rules) will be used to do the proofs.
   *  appear in 
   * @param resource The name of the Z source. 
   * @throws Exception
   */
  private void prove(String resource)
    throws Exception
  {
    SectionManager manager = new SectionManager();
    manager.putCommands("zpatt");
    URL url = getClass().getResource(resource);
    assertFalse(url == null);
    manager.put(new Key(url.toString(), Source.class), new UrlSource(url));
    Term term = (Term) manager.get(new Key(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    manager.get(new Key(sectname, SectTypeEnvAnn.class));
    RuleTable rules =
      (RuleTable) manager.get(new Key(sectname, RuleTable.class));
    for (ConjPara conjPara : collectConjectures(term)) {
      PredSequent sequent = factory_.createPredSequent();
      CopyVisitor visitor = new CopyVisitor(factory_);
      sequent.setPred((Pred) conjPara.getPred().accept(visitor));
      SimpleProver prover =
        new SimpleProver(rules, manager, sectname);
      if (! prover.prove(sequent)) {
        StringWriter writer = new StringWriter();
        PrintUtils.print(conjPara.getPred(),
                         writer,
                         manager,
                         "standard_toolkit",
                         Markup.LATEX);
        writer.close();
        fail("Failed to prove " + writer.toString());
      }
    }
  }
}
