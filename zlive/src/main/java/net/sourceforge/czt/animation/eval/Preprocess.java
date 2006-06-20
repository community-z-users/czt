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
import net.sourceforge.czt.rules.Rewrite;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;

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
  
  public Preprocess(SectionManager sectman)
  {
    sectman_ = sectman;
  }

  /**
   * Collects the rules of the first ZSect.
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
  
  public Term preprocess(String sectname, Term term)
  {
    if (rules_ == null)
      throw new RuntimeException("preprocessing error: no rules!");
    return Rewrite.rewrite(sectman_, sectname, term, rules_);
  }
}
