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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.parser.zpatt.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;

/**
 * Utility methods for proving and rewriting.
 *
 * @author Petra Malik
 */
public final class ProverUtils
{
  public static Factory FACTORY = new Factory(new ProverFactory());

  public static PredSequent createPredSequent(Pred pred)
  {
    PredSequent predSequent = FACTORY.createPredSequent();
    predSequent.setPred(pred);
    return predSequent;
  }

  public static PredSequent createPredSequent(Expr expr)
  {
    Pred pred = FACTORY.createExprPred(expr);
    return createPredSequent(pred);
  }

  public static PredSequent createRewritePredSequent(Expr expr)
  {
    ProverJokerExpr joker = (ProverJokerExpr) FACTORY.createJokerExpr("_");
    Pred pred = FACTORY.createEquality(expr, joker);
    return createPredSequent(pred);
  }

  public static List<Rule> collectRules(Term term)
  {
    List<Rule> result = new ArrayList<Rule>();  
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

  public static List<ConjPara> collectConjectures(Term term)
  {
    List<ConjPara> result = new ArrayList<ConjPara>();  
    if (term instanceof Spec) {
      for (Iterator i = ((Spec) term).getSect().iterator(); i.hasNext(); ) {
        Sect sect = (Sect) i.next();
        if (sect instanceof ZSect) {
          for (Iterator j = ((ZSect) sect).getPara().iterator();
               j.hasNext(); ) {
            Para para = (Para) j.next();
            if (para instanceof ConjPara) {
              result.add((ConjPara) para);
            }
          }
        }
      }
    }
    return result;
  }

  public static void prove(URL url)
    throws IOException, ParseException
  {
    Factory factory = new Factory(new ProverFactory());
    SectionManager manager = new SectionManager();
    Term term = ParseUtils.parse(new UrlSource(url), manager);
    TypeCheckUtils.typecheck(term, manager, Markup.LATEX);
    String sectname = term.accept(new GetZSectNameVisitor());
    List<Rule> rules = collectRules(term);
    List<ConjPara> conjectures = collectConjectures(term);
    for (Iterator<ConjPara> i = conjectures.iterator(); i.hasNext(); ) {
      ConjPara conjPara = i.next();
      PredSequent sequent = factory.createPredSequent();
      CopyVisitor visitor = new CopyVisitor(factory);
      sequent.setPred((Pred) conjPara.getPred().accept(visitor));
      SimpleProver prover =
        new SimpleProver(rules, manager, sectname);
      if (! prover.prove(sequent)) {
        StringWriter writer = new StringWriter();
        PrintUtils.print(conjPara.getPred(),
                         writer,
                         manager,
                         sectname,
                         Markup.LATEX);
        writer.close();
        System.err.println("Failed to prove " + writer.toString());
        throw new IllegalStateException();
      }
    }
  }

  public static void main(String[] args)
    throws IOException, ParseException
  {
    URL url = new URL(args[0]);
    prove(url);
  }


  public static class GetZSectNameVisitor
    implements SpecVisitor<String>,
               ZSectVisitor<String>
  {
    public String visitSpec(Spec spec)
    {
      for (Sect sect : spec.getSect()) {
        String name = sect.accept(this);
        if (name != null) return name;
      }
      return null;
    }

    public String visitZSect(ZSect zSect)
    {
      return zSect.getName();
    }
  }
}
