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

import static net.sourceforge.czt.rules.ProverUtils.collectConjectures;

import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.ast.PredSequent;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.Rewrite;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.session.*;

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
  
  private Factory factory_;
  
  private Rewrite rewrite_;
  
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
    // do we need to use a fresh factory each time?
    factory_ = new Factory(new ProverFactory());
    
    URL url = getClass().getResource(rulesFile);
    if (url == null)
      throw new IOException("Cannot getResource("+rulesFile+")");
    sectman_.put(new Key(url.toString(), Source.class), new UrlSource(url));
    Term term = (Spec) sectman_.get(new Key(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    sectman_.get(new Key(sectname, SectTypeEnvAnn.class)); // typecheck sect
    rules_ = (RuleTable) sectman_.get(new Key(sectname, RuleTable.class));
    for (String ruleName : rules_.getRules().keySet())
      System.out.println("loaded rule "+ruleName);
    rewrite_ = new Rewrite(sectman_, rules_);
  }
 
  public Expr preprocess(Expr expr)
  {
    if (rewrite_ == null)
      throw new RuntimeException("preprocessing error: no rules!");
    return (Expr) rewrite_.visitExpr(expr);
  }
}
