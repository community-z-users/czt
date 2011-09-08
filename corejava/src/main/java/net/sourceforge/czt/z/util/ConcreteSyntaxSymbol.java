/*
  Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

/**
 * An enumeration of concrete syntax symbols.
 * These are based on the concrete syntax productions in
 * the Z standard, plus a few extra symbols for the
 * CZT extensions, such as unparsed paragraphs and various
 * lists and pairs etc.
 * <p>
 * The {@link ConcreteSyntaxSymbolVisitor} in this package can be
 * used to classify most kinds of AST nodes as one of these 
 * symbols.
 * </p>
 * @author Petra Malik
 */
public enum ConcreteSyntaxSymbol
{
  SPEC("Specification"),
  SECTIONED_SPEC("Sectioned specification"),
  ANONYMOUS_SPEC("Anonymous specification"),

  /* In ZML, there is no distinction between inheriting and base section. */
  SECT("Section"),

  PARA("Paragraph"),
  GIVEN_PARA("Given types paragraph"),
  AX_PARA("Axiomatic description paragraph"),
  SCH_PARA("Schema definition paragraph"),
  GENAX_PARA("Generic axiomatic description paragraph"),
  GENSCH_PARA("Generic schema definition paragraph"),
  DEF_PARA("Horizontal definition paragraph"),
  GENDEF_PARA("Generic horizontal definition paragraph"),
  OPDEF_PARA("Generic operator definition paragraph"),
  FREE_PARA("Free types paragraph"),
  CONJ_PARA("Conjecture paragraph"),
  GENCONJ_PARA("Generic conjecture paragraph"),
  OPTEMP_PARA("Operator template paragraph"),

  FREETYPE("Free type paragraph"),

  BRANCH("Element or injection"),

  PRED("Predicate"),
  NL_AND_PRED("Newline conjunction predicate"),
  SEMI_AND_PRED("Semicolon conjunction predicate"),
  ALL_PRED("Universal quantification predicate"),
  EXI_PRED("Existential quantification predicate"),
  EXIONE_PRED("Unique existential quantification predicate"),
  IFF_PRED("Equivalence predicate"),
  IMPL_PRED("Implication predicate"),
  OR_PRED("Disjunction predicate"),
  AND_PRED("Conjunction predicate"),
  NEG_PRED("Negation predicate"),
  REL_PRED("Relation operator application predicate"),
  EXPR_PRED("Schema predicate"),
  TRUE_PRED("Truth predicate"),
  FALSE_PRED("False predicate"),
  PAREN_PRED("Parenthesized predicate"),

  EXPR("Expression"),
  ALL_EXPR("Schema universal quantification expression"),
  EXI_EXPR("Schema existential quantification expression"),
  EXIONE_EXPR("Schema unique existential quantification expression"),
  LAMBDA_EXPR("Function construction expression"),
  MU_EXPR("Definite description expression"),
  LET_EXPR("Substitution expression"),
  IFF_EXPR("Schema equivalence expression"),
  IMPL_EXPR("Schema implication expression"),
  OR_EXPR("Schema discjunction expression"),
  AND_EXPR("Schema conjunction expression"),
  NEG_EXPR("Schema negation expression"),
  COND_EXPR("Conditional expression"),
  COMP_EXPR("Schema composition expression"),
  PIPE_EXPR("Schema piping expression"),
  HIDE_EXPR("Schema hiding expression"),
  PROJ_EXPR("Schema projection expression"),
  PRE_EXPR("Schema precondition expression"),
  PROD_EXPR("Cartesian product expression"),
  POWER_EXPR("Powerset expression"),
  FUN_APPL_EXPR("Function application expression"),
  GENOP_APPL_EXPR("Generic operator application expression"),
  APPL_EXPR("Application expression"),
  DECOR_EXPR("Schema decoration expression"),
  RENAME_EXPR("Schema renaming expression"),
  BIND_SEL_EXPR("Binding selection expression"),
  TUPLE_SEL_EXPR("Tuple selection expression"),
  THETA_EXPR("Binding construction expression"),
  REF_EXPR("Reference expression"),
  GENREF_EXPR("Generic instantiation expression"),
  NUM_EXPR("Number literal expression"),
  SET_EXPR("Set extension expression"),
  SET_COMP_EXPR("Set comprehension expression"),
  CHAR_SET_COMP_EXPR("Characteristic set comprehension expression"),
  SCH_EXPR("Schema construction expression"),
  BIND_EXPR("Binding extension expression"),
  TUPLE_EXPR("Tuple extension expression"),
  CHAR_DEF_EXPR("Characteristic definite description"),
  PAREN_EXPR("Parenthesized expression"),

  SCH_TEXT("Schema text"),

  DECL("Declaration"),
  CONST_DECL("Constant declaration"),
  VAR_DECL("Variable declaration"),
  INCL_DECL("Include declaration"),

  NAME("Name"),

  /* CZT specific symbols */
  UNPARSED_Z_SECT("Unparsed Z section"),
  NARR_SECT("Narrative before or after a Z section"),

  LATEX_MARKUP_PARA("Latex markup directive paragraph"),
  NARR_PARA("Narrative paragraph"),
  UNPARSED_PARA("Unparsed paragraph"),

  CHAIN_AND_PRED("Chained relation predicate"),

  PARENT("Parent"),
  DIRECTIVE("LaTeX markup directive"),
  NUMERAL("Numeral"),

  NAME_SECT_TYPE_TRIPLE("Triple of name, section, and type"),
  NAME_TYPE_PAIR("Pair of name and type"),
  NAME_NAME_PAIR("Pair of names"),

  LIST("List"),
  BRANCH_LIST("List of branches"),
  DECL_LIST("List of declarations"),
  NAME_LIST("List of names"),
  EXPR_LIST("List of expressions"),
  FREETYPE_LIST("List of freetypes"),
  PARA_LIST("List of paragraphs"),
  RENAME_LIST("List of pairs of names"),
  STROKE_LIST("List of strokes"),

  ZREFINES("Z refinment link"),
  ZSTATE("Z state information");


  private final String description_;

  ConcreteSyntaxSymbol(String description)
  {
    description_ = description;
  }

  String getDescription()
  {
    return description_;
  }
}
