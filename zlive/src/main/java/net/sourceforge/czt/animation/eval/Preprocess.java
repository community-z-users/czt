/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2005 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.io.IOException;
import java.net.URL;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.Rewrite;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zpatt.util.Factory;

/** Preprocesses a term to get it ready for evaluation.
 *  This unfolds some Z constructs into simpler ones,
 *  using sets of rewrite rules.
 *  
 * @author marku
 */
public class Preprocess
{
  private SectionManager sectman_;
  
  private RuleTable rules_;
  
  /** Create a term preprocessor that will apply a set
   *  of rules (see setRules) to a given term.
   * @param sectman  The section manager used to find rule tables.
   */
  public Preprocess(SectionManager sectman)
  {
    sectman_ = sectman;
  }

  /**
   * Collects the rules of the first ZSect in a given source file.
   * @param rulesFile  The name of the source file that contains the rules.
   */
  public void setRules(String rulesFile)
    throws IOException, ParseException, CommandException
  {
    URL url = getClass().getResource(rulesFile);
    if (url == null)
      throw new IOException("Cannot getResource("+rulesFile+")");
    sectman_.put(new Key(url.toString(), Source.class), new UrlSource(url));
    Term term = (Spec) sectman_.get(new Key(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    sectman_.get(new Key(sectname, SectTypeEnvAnn.class)); // typecheck sect
    rules_ = (RuleTable) sectman_.get(new Key(sectname, RuleTable.class));
    // for debugging only...
    for (String ruleName : rules_.getRules().keySet())
      System.out.println("loaded rule "+ruleName);
  }
  
  /** Rewrites the given term by firstly unfolding VarDecls
   *  with multiple variables (x,y:T), then appling all the rewrite 
   *  rules of this Preprocess object to that term.  This should be 
   *  called after type checking, so that VarDecls with multiple
   *  variables can be expanded correctly.  (Section C.7.3.1
   *  of the Z standard implies that x,y:T cannot be expanded
   *  until any generics in type T have been fully instantiated).
   *  
   * @param sectname Gives the context for the proofs of rewrite rules.
   * @param term     The input term to rewrite.
   * @return         The rewritten term.
   */
  public Term preprocess(String sectname, Term term)
  {
    if (rules_ == null)
      throw new RuntimeException("preprocessing error: no rules!");
    Factory factory = new Factory(new ProverFactory());
    Term term2 = term.accept(new CopyVisitor(factory));
    return Rewrite.rewrite(sectman_, sectname, term2, rules_);
  }
}
