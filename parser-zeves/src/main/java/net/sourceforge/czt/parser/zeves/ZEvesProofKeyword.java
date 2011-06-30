/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.parser.zeves;

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

import net.sourceforge.czt.zeves.util.ZEvesString;

/**
 *
 * @author Leo Freitas
 * @date Jun 22, 2011
 */
public enum ZEvesProofKeyword implements Token {

/*
PROOFWORDBEGIN  = "apply" | "back" | "cases" | "conjunctive" | "disjunctive" | "equality" |
                  "instantiate" | "invoke" | "next" | "prenex" | "prove" | "rearrange" |
                  "reduce" | "rewrite" | "simplify" | "split" | "trivial" | "try" | "use" | "with"

PROOFWORDMIDDLE = "by" | "enabled" | "expression" | "disabled" | "lemma" | 
                  "normalization" | "predicate" | "substitute" | "to"

PROOFCMDBEGIN   = "check" | "declare" | "help" | "parent" | "print" | "quit" |
                  "read" | "reset" | "retry" | "theorems" | "undo" |
                  "zsection" | "ztags"

PROOFCMDMIDDLE  = "about" | "back" | "declaration" | "formula" | "history" | "proof" |
                  "script" | "status" | "summary" | "to" | "through"
*/

  APPLY(ZEvesString.APPLY, NewlineCategory.BOTH),
  BACK (ZEvesString.BACK, NewlineCategory.BOTH),
  CASES(ZEvesString.CASES, NewlineCategory.BOTH),
  CONJUNCTIVE(ZEvesString.CONJUNCTIVE, NewlineCategory.BOTH),
  DISJUNCTIVE(ZEvesString.DISJUNCTIVE , NewlineCategory.BOTH),
  EQUALITY(ZEvesString.EQUALITY , NewlineCategory.BOTH),
  INSTANTIATE(ZEvesString.INSTANTIATE , NewlineCategory.BOTH),
  INVOKE(ZEvesString.INVOKE , NewlineCategory.BOTH),
  NEXT(ZEvesString.NEXT , NewlineCategory.BOTH),
  PRENEX(ZEvesString.PRENEX , NewlineCategory.BOTH),
  PROVE(ZEvesString.PROVE , NewlineCategory.BOTH),
  REARRANGE(ZEvesString.REARRANGE , NewlineCategory.BOTH),
  REDUCE(ZEvesString.REDUCE , NewlineCategory.BOTH),
  REWRITE(ZEvesString.REWRITE , NewlineCategory.BOTH),
  SIMPLIFY(ZEvesString.SIMPLIFY , NewlineCategory.BOTH),
  SPLIT(ZEvesString.SPLIT , NewlineCategory.BOTH),
  TRIVIAL(ZEvesString.TRIVIAL , NewlineCategory.BOTH),
  TRY(ZEvesString.TRY , NewlineCategory.BOTH),
  USE(ZEvesString.USE , NewlineCategory.BOTH),
  WITH(ZEvesString.WITH , NewlineCategory.BOTH),

  BY(ZEvesString.BY, NewlineCategory.BOTH),
  ENABLED(ZEvesString.ENABLED, NewlineCategory.BOTH),
  EXPRESSION(ZEvesString.EXPRESSION, NewlineCategory.BOTH),
  DISABLED(ZEvesString.DISABLED, NewlineCategory.BOTH),
  LEMMA(ZEvesString.LEMMA, NewlineCategory.BOTH),
  NORMALIZATION(ZEvesString.NORMALIZATION, NewlineCategory.BOTH),
  PREDICATE(ZEvesString.PREDICATE, NewlineCategory.BOTH),
  SUBSTITUTE(ZEvesString.SUBSTITUTE, NewlineCategory.BOTH),
  TO(ZEvesString.TO, NewlineCategory.BOTH),
  
  CHECK(ZEvesString.CHECK, NewlineCategory.BOTH),
  DECLARE(ZEvesString.DECLARE , NewlineCategory.BOTH),
  HELP(ZEvesString.HELP , NewlineCategory.BOTH),
  PARENT(ZEvesString.PARENT , NewlineCategory.BOTH),
  PRINT(ZEvesString.PRINT , NewlineCategory.BOTH),
  QUIT(ZEvesString.QUIT , NewlineCategory.BOTH),
  READ(ZEvesString.READ , NewlineCategory.BOTH),
  RESET(ZEvesString.RESET , NewlineCategory.BOTH),
  RETRY(ZEvesString.RETRY , NewlineCategory.BOTH),
  THEOREMS(ZEvesString.THEOREMS , NewlineCategory.BOTH),
  UNDO(ZEvesString.UNDO , NewlineCategory.BOTH),
  ZSECTION(ZEvesString.ZSECTION , NewlineCategory.BOTH),
  ZTAGS(ZEvesString.ZTAGS , NewlineCategory.BOTH),

  ABOUT(ZEvesString.ABOUT, NewlineCategory.BOTH),
  DECLARATION(ZEvesString.DECLARATION , NewlineCategory.BOTH),
  FORMULA(ZEvesString.FORMULA , NewlineCategory.BOTH),
  HISTORY(ZEvesString.HISTORY , NewlineCategory.BOTH),
  PROOF(ZEvesString.PROOF , NewlineCategory.BOTH),
  SCRIPT(ZEvesString.SCRIPT , NewlineCategory.BOTH),
  STATUS(ZEvesString.STATUS , NewlineCategory.BOTH),
  SUMMARY(ZEvesString.SUMMARY , NewlineCategory.BOTH),
  THROUGH(ZEvesString.THROUGH , NewlineCategory.BOTH),
        ;


  private String spelling_ = null;
  private NewlineCategory NewlineCategory_;

  ZEvesProofKeyword(NewlineCategory NewlineCategory)
  {
    NewlineCategory_ = NewlineCategory;
  }

  ZEvesProofKeyword(String spelling, NewlineCategory NewlineCategory)
  {
    spelling_ = spelling;
    NewlineCategory_ = NewlineCategory;
  }

  public static ZEvesProofKeyword[] headProofWordsOnly()
  {
//    return new String[] {
//       APPLY.getName(),
//       BACK.getName(),
//       CASES.getName(),
//       CONJUNCTIVE.getName(),
//       DISJUNCTIVE.getName(),
//       EQUALITY.getName(),
//       INSTANTIATE.getName(),
//       INVOKE.getName(),
//       NEXT.getName(),
//       PRENEX.getName(),
//       PROVE.getName(),
//       REARRANGE.getName(),
//       REDUCE.getName(),
//       REWRITE.getName(),
//       SIMPLIFY.getName(),
//       TRIVIAL.getName(),
//       TRY.getName(),
//       SPLIT.getName(),
//       USE.getName(),
//       WITH.getName()
//    };
    return new ZEvesProofKeyword[] {
       APPLY,
       BACK,
       CASES,
       CONJUNCTIVE,
       DISJUNCTIVE,
       EQUALITY,
       INSTANTIATE,
       INVOKE,
       NEXT,
       PRENEX,
       PROVE,
       REARRANGE,
       REDUCE,
       REWRITE,
       SIMPLIFY,
       TRIVIAL,
       TRY,
       SPLIT,
       USE,
       WITH 
    };
  }

  public String getName()
  {
    return toString();
  }

  public Object getSpelling()
  {
    return spelling_;
  }

  public String spelling()
  {
    return spelling_;
  }

  public NewlineCategory getNewlineCategory()
  {
    return NewlineCategory_;
  }
}
