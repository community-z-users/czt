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

package net.sourceforge.czt.zeves.util;

/**
 *
 * @author Leo Freitas
 * @date Jul 8, 2011
 */
public enum ZEvesConcreteSyntaxSymbol
{
  /* Top-level paragraphs */
  ZPROOF_PARA("Z proof paragraph"),
  ZPROOF_CMD_LIST("Proof commands list"),

  /* Proof commands */
  APPLY_GLOBAL_CMD("Apply theorem globally to goal with pattern matching"),
  APPLY_EXPR_CMD("Apply theorem to goal subexpression with pattern matching"),
  APPLY_PRED_CMD("Apply theorem to goal subpredicate with pattern matching"),
  BACK_CMD ("Backtrack step(s)"),
  CASES_CMD("Start case analysis"),
  CONJUNCTIVE_CMD("Conjunctive normal form"),
  DISJUNCTIVE_CMD("Disjunctive normal form"),
  EQUALITY_LOCAL_CMD("L-R equality substitution for given expression"),
  EQUALITY_GLOBAL_CMD("L-R equality substitution globally"),
  INSTANTIATE_CMD("Quantifiers instantiation"),
  INVOKE_PRED_CMD("Involved predicate/schema definition expansion"),
  INVOKE_NAME_CMD("Given name expansion"),
  INVOKE_GLOBAL_CMD("Definition expansion globally"),
  NEXT_CMD("Case analysis step switching"),
  PRENEX_CMD("Quantifiers elimination"),
  PROVE_RW_CMD("Tactical powerful term rewriting"),
  PROVE_RD_CMD("Tactical powerful term reduction"),
  REARRANGE_CMD("Lexicographic term rearrangement"),
  REDUCE_CMD("Term simplification via invoke and rewriting"),
  REWRITE_CMD("Term simplification using rules, frules, and simplification"),
  SIMPLIFY_CMD("Propositional and non-linear arithmetic reasoning using grules"),
  SPLIT_CMD("Arbritary case analysis on a predicate"),
  TRIVIAL_SIMP_CMD("Tactical trivial term simplification (no prop. reasoning)"),
  TRIVIAL_RW_CMD("Tactical trivial term rewriting"),
  TRY_CMD("Start the proof of a new on-the-fly goal"),
  TRY_LEMMA_CMD("Start the proof of a known conjecture name"),
  USE_TRIVIAL_CMD("Use theorem on goal with inferred parameters"),
  USE_GENTHM_CMD("Use theorem on goal with generic types and inferred parameters"),
  USE_COMPLEX_CMD("Use theorem on goal with user-supplied parameters"),
  WITH_NORM_CMD("Tactical term normalization"),
  WITH_PRED_CMD("Tactical application to goal subpredicate"),
  WITH_EXPR_CMD("Tactical application to goal subexpression"),
  WITH_ENABLED_CMD("Tactical application to goal with selected terms to enable"),
  WITH_DISABLED_CMD("Tactical application to goal with selected terms to disable"),

  SORRY_COMMAND("Remove unfinished proof from context"),
  OOPS_COMMAND("Keep unfinished proof within context"),

  THMREPLACEMENT("Variable replacement in theorem usage"),
  INSTANTIATION("Quantified variable instantiation"),
  INSTANTIATION_LIST("List of instantiations or thm replacements"),

  ZEVESLABEL("ZEves predicate label"),
  ZEVESNOTE("ZEves comment within formal text")

  // TODO: proof commands for admin purposes


  ;

  private final String description_;
  private ZEvesConcreteSyntaxSymbol other_;

  ZEvesConcreteSyntaxSymbol(String description)
  {
    other_ = null;
    description_ = description;
  }

  public String getDescription()
  {
    return description_;
  }

  ZEvesConcreteSyntaxSymbol getOther()
  {
    return other_;
  }

  ZEvesConcreteSyntaxSymbol add(ZEvesConcreteSyntaxSymbol other)
  {
    this.other_ = other;
    return this;
  }
}

