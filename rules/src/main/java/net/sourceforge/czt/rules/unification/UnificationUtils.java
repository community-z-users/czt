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

package net.sourceforge.czt.rules.unification;

import java.io.IOException;
import java.util.Set;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zpatt.ast.Binding;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.ast.Rule;

public final class UnificationUtils
{
  /**
   * Do not create instances of this class.
   */
  private UnificationUtils()
  {
  }

  /**
   * Returns null if unification failed.
   */
  public static Set<Binding> unify(Object o1, Object o2)
  {
    Unifier unifier = new Unifier();
    if (unifier.unify(o1, o2)) return unifier.getBindings();
    for (Binding binding : unifier.getBindings()) {
      binding.reset();
    }
    return null;
  }

  /**
   * Throws and exception if unification failed.
   */
  public static Set<Binding> unify2(Object o1, Object o2)
    throws UnificationException
  {
    Unifier unifier = new Unifier();
    if (unifier.unify(o1, o2)) return unifier.getBindings();
    for (Binding binding : unifier.getBindings()) {
      binding.reset();
    }
    throw unifier.getCause();
  }

  /** Similar to parsePred, but for ZPattern expressions. */
  public static Expr parseExpr(String expr, String section,
      SectionManager sectman)
  throws IOException, CommandException
  {
    Pred pred = parsePred(expr + " = 3", section, sectman);
    return ((MemPred)pred).getLeftExpr();
  }

  /** Parse a Source string/file as a ZPattern Predicate.
   *  This is similar to net.sourceforge.czt.z.ParseUtils.parsePred,
   *  but parses the predicate within the conclusion of a rule,
   *  so that jokers are handled correctly.
   *  This method is mostly used for testing purposes.
   *  The context of the predicate defines Expr jokers E1..E9,
   *  Pred jokers P1..P9, DeclList jokers D1..D9 and Name jokers v1..v9.
   *
   * @param src The String or File etc. to be parsed.  Must use Latex markup.
   * @param section The Z section to parse within (null=zpattern_toolkit).
   * @param sectman A section manager to use.  Must be non-null.
   *
   * @throws IOException if there are errors reading file/url inputs
   * @throws CommandException if the expression cannot be parsed.
   */
  public static Pred parsePred(String term, String section,
      SectionManager sectman)
  throws IOException, CommandException
  {
    String parent = section;
    String name = "CZT_zpattern_parse_tmp19580281975";
    if (parent == null)
      parent = "zpattern\\_toolkit";

    String contents =
      "\\begin{zsection}\\SECTION "+name+" \\parents zpattern\\_toolkit\n" +
      "\\end{zsection}\n" +
      "\\begin{zedjoker}{DeclList} D1, D2, D3, D4, D5, D6, D7, D8, D9 \\end{zedjoker}\n" +
      "\\begin{zedjoker}{Pred} P1, P2, P3, P4, P5, P6, P7, P8, P9 \\end{zedjoker}\n" +
      "\\begin{zedjoker}{Expr} E1, E2, E3, E4, E5, E6, E7, E8, E9 \\end{zedjoker}\n" +
      "\\begin{zedjoker}{Name} v1, v2, v3, v4, v5, v6, v7, v8, v9 \\end{zedjoker}\n" +
      "\\begin{zedrule}{rule1} "+term+" \\end{zedrule}\n";

    // we create a temporary sectman so that this temp section does not
    //  clutter up the original section manager.
    SectionManager tmpsectman = (SectionManager)sectman.clone();
    Source input = new StringSource(contents);
    input.setMarkup(Markup.LATEX);
    tmpsectman.put(new Key<Source>(name, Source.class), input);
    Spec spec =  tmpsectman.get(new Key<Spec>(name, Spec.class));
    Rule rule = firstRule(spec);
    assert rule != null;
    Sequent seq = rule.getSequent();
    return seq.getPred();
  }

  /** Finds the first zedrule in the specification. */
  public static Rule firstRule(Spec spec)
  {
    for (Sect sect : spec.getSect())
      if (sect instanceof ZSect)
        for (Para para : (ZParaList) ((ZSect)sect).getParaList())
          if (para instanceof Rule)
            return (Rule) para;
    throw new RuntimeException("No rules in zpattern specification.");
  }
}
