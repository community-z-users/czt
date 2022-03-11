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

package net.sourceforge.czt.rules.prover;

import static net.sourceforge.czt.rules.prover.ProverUtils.collectConjectures;

import java.io.StringWriter;
import java.net.URL;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

import junit.framework.TestCase;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.util.Factory;

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
    SectionManager manager = new SectionManager(Dialect.ZPATT);
    URL url = getClass().getResource(resource);
    assertFalse(url == null);
    manager.put(new Key<Source>(url.toString(), Source.class), new UrlSource(url));
    Term term =  manager.get(new Key<Spec>(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    manager.get(new Key<SectTypeEnvAnn>(sectname, SectTypeEnvAnn.class));
    RuleTable rules = manager.get(new Key<RuleTable>(sectname, RuleTable.class));
    
    // turn rules logging on
    Logger LOG = Logger.getLogger("net.sourceforge.czt.rules");
    LOG.setLevel(Level.FINEST);
    String logfile = resource.replaceAll("/", "").replaceAll(".tex", ".log");
    Handler handler = new FileHandler(logfile);
    handler.setLevel(Level.ALL);
    handler.setEncoding("utf8");
    LOG.addHandler(handler);
    
    for (ConjPara conjPara : collectConjectures(term)) {
      Sequent sequent = factory_.createSequent();
      CopyVisitor visitor = new CopyVisitor(factory_);
      sequent.setPred((Pred) conjPara.getPred().accept(visitor));
      SimpleProver prover =
        new SimpleProver(rules, manager, sectname);
      StringWriter writer = new StringWriter();
      PrintUtils.print(conjPara.getPred(),
                       writer,
                       manager,
                       "oracle_toolkit",
                       Markup.LATEX);
      writer.close();
      LOG.fine("Starting to prove conjecture: " + resource + ": " + writer.toString());
      if (! prover.prove(sequent)) {
        LOG.fine("FAILED conjecture: " + resource + ": " + writer.toString());
        fail("Failed to prove " + writer.toString());
      }
    }
  }
}
