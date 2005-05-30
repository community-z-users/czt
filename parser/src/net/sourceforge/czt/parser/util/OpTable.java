/*
  Copyright (C) 2004, 2005 Tim Miller, Mark Utting, Petra Malik
  This file is part of the czt project: http://czt.sourceforge.net

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

package net.sourceforge.czt.parser.util;

import java.util.*;

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;

/**
 * An operator table manages all the operator definitions of a section.
 * It provides search facilities for all the operators defined in this
 * section or inherited from  parent sections,
 * plus facilities for defining new operators.
 */
public class OpTable
{
  /**
   * The name of the section.
   */
  private String section_;

  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String, Name or DeclName?
   */
  private /*@non_null@*/ SortedMap/*<String,OpInfo>*/ ops_ = new TreeMap();

  /**
   * <p>A mapping from operator word to operator template.
   * This is used to compute meaningful error messages.</p>
   */
  private Map<String, OptempPara> optempPara_ = new HashMap();

  /**
   * <p>A mapping from operator word to operator token type.
   * For instance, the operator template for '_ + _' adds an entry
   * '+' -> 'I' to this map.</p>
   * <p>This map corresponds to the associations between WORDs
   * and operator tokens mentioned in the Z Standard chapter 7.4.4.
   * Since the set of active associations is always a function,
   * a map can be used here.</p>
   */
  private Map/*<String, OperatorTokenType>*/ opTokens_ = new HashMap();

  /**
   * A mapping from operator word to precedence.
   * For instance, '+' is mapped to '30'.
   */
  private Map/*<String, Integer>*/ precedence_ = new HashMap();

  /**
   * Maps precedence to associativity.
   */
  private Map/*<Integer, Assoc>*/ assoc_ = new HashMap();

  /**
   * Constructs an operator table for a new section.
   * It checks that the operators defined in the parents are
   * consistent, according to the 3 rules in the Z standard.
   *
   * @param parents Operator tables of all direct parents of the new section.
   * @czt.todo we could take a set/map of Sections here?
   *           Or the section manager plus a set of parent names?
   */
  public OpTable(String section, Collection/*<OpTable>*/ parents)
    throws OperatorException
  {
    section_ = section;
    if (parents != null) {
      for (Iterator iter = parents.iterator(); iter.hasNext();) {
        OpTable table = (OpTable) iter.next();
        addParentOpTable(table);
      }
    }
  }

  private void addParentOpTable(OpTable parentTable)
    throws OperatorException
  {
    ops_.putAll(parentTable.ops_);
    addOpTokens(parentTable);
    addPrecedences(parentTable);
    addAssociativities(parentTable);
    optempPara_.putAll(parentTable.optempPara_);
  }

  /**
   * Removes all decorations, that are strokes,
   * from a decorword and returns the word part.
   */
  public static String getWord(String decorword)
  {
    Decorword dw = new Decorword(decorword);
    return dw.getWord();
  }

  public static String getOpNameWithoutStrokes(List/*<Oper>*/ oper)
  {
    StringBuffer result = new StringBuffer();
    for (Iterator iter = oper.iterator(); iter.hasNext();) {
      Oper o = (Oper) iter.next();
      if (o instanceof Operand) {
        final Operand operand = (Operand) o;
        if (Boolean.TRUE.equals(operand.getList())) {
          result.append(ZString.LISTARG_TOK);
        }
        else {
          result.append(ZString.ARG_TOK);
        }
      }
      else if (o instanceof Operator)
      {
        final Operator operator = (Operator) o;
        final String name = operator.getWord();
        assert name.equals(getWord(name));
        result.append(name);
      }
      else {
        throw new CztException("Unexpected Oper");
      }
    }
    return result.toString();
  }

  public String getSection()
  {
    return section_;
  }

  /**
   * Looks up opname to see if it is defined as an operator
   * in this section or in any of the ancestor sections.
   * The resulting OpInfo structure contains all the details about
   * the operator, including the name of the section it was defined in.
   *
   * @param opname Operator name.  Example " _ + _ ".
   * @return       Returns <code>null</code> if <code>opname</code>
   *               is not an operator.
   * @czt.todo What about "\power_1"?
   */
  public OpInfo lookup(String /*@non_null@*/ opname)
  {
    throw new UnsupportedOperationException();
  }
  public OpInfo lookup(List list)
  {
    StringBuffer opname = new StringBuffer();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      String s = (String) iter.next();
      if (ZString.ARG_TOK.equals(s) || ZString.LISTARG_TOK.equals(s)) {
        opname.append(s);
      }
      else {
        opname.append(getWord(s));
      }
    }
    OpInfo result = (OpInfo) ops_.get(opname.toString());
    return result;
  }
  public OpInfo lookup(OperatorName operatorName)
  {
    return (OpInfo) ops_.get(operatorName.getWord());
  }

  public OperatorTokenType getTokenType(Decorword decorword)
  {
    return (OperatorTokenType) opTokens_.get(decorword.getWord());
  }

  public Integer getPrec(String opWord)
  {
    return (Integer) precedence_.get(getWord(opWord));
  }

  public Assoc getAssoc(String opWord)
  {
    Integer prec = (Integer) precedence_.get(getWord(opWord));
    if (prec == null) return null;
    return (Assoc) assoc_.get(prec);
  }

  public String toString()
  {
    return "OpTable for " + section_ + "\n" + opTokens_;
  }

  /**
   * Adds a new operator.
   *
   * @throws OperatorException if operator is incompatible
   *                           with existing operators.
   */
  public void add(OptempPara opPara)
    throws OperatorException
  {
    List oper = opPara.getOper();
    if (oper.size() < 2) {
      throw new CztException("Error: operator template with less " +
                             "than 2 arguments");
    }
    OpInfo info = new OpInfo(section_, opPara);
    String name = getOpNameWithoutStrokes(opPara.getOper());
    addOperator(name, info);
    Oper first = (Oper) oper.get(0);
    Oper last = (Oper) oper.get(oper.size() - 1);
    if (first instanceof Operand) {
      if (last instanceof Operand) {
        addInfix(opPara);
        return;
      }
      addPostfix(opPara);
      return;
    }
    if (last instanceof Operand) {
      addPrefix(opPara);
      return;
    }
    addNofix(opPara);
    return;
  }

  /**
   * Adds an operator with name <code>name</code> and operator info
   * <code>info</code> to the set of all operators that are defined
   * in this scope.
   *
   * @throws OperatorException if this operator is already defined.
   */
  private void addOperator(String name, OpInfo info)
    throws OperatorException
  {
    if (ops_.get(name) != null) {
      String message = "Operator " + name + " defined more than once";
      throw new OperatorException(message);
    }
    ops_.put(name, info);
  }

  /**
   *
   * @czt.todo reimplement this method exploiting the fact that table
   *           <code>ops_</code> is ordered.
   */
  private void addOperators(OpTable parentTable)
    throws OperatorException
  {
    final Map parentOps = parentTable.ops_;
    for (Iterator i = parentOps.keySet().iterator(); i.hasNext();) {
      String name = (String) i.next();
      OpInfo info = (OpInfo) parentOps.get(name);
      assert info != null;
      OpInfo existingInfo = (OpInfo) ops_.get(name);
      if (existingInfo != null && ! existingInfo.equals(info)) {
        String message = "Operator " + name + " defined more than once" +
          " in parents " + info.getSection() + " and " +
          existingInfo.getSection();
        throw new OperatorException(message);
      }
      ops_.put(name, info);
    }
  }

  private void addPrefix(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();

    final int start = 1;
    final int finish = words.size() - 4;
    if (words.size() == 2) {
      //"PRE _ | PREP _"
      addPreOrPrep(opPara);
    }
    else {
      //"L  { _ (ES | SS) } _ (ERE | SRE) _ | "
      //"LP { _ (ES | SS) } _ (EREP | SREP) _"
      addLOrLp(opPara);
      addEsOrSsList(opPara, start, finish);
      addEreOrSreOrErepOrSRep(opPara);
    }
  }

  private void addPostfix(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int start = 2;
    final int finish = words.size() - 3;
    if (words.size() == 2) {
      //"_ POST | _ POSTP"
      addPostOrPostp(opPara);
    }
    else {
      //"_ EL { _ (ES | SS) } _ (ER | SR) |"
      //"_ ELP { _ (ES | SS) } _ (ERP | SRP)"

      addElOrElp(opPara);
      addEsOrSsList(opPara, start, finish);
      addErOrSrOrErpOrSrp(opPara);
    }
  }

  private void addInfix(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int start = 2;
    final int finish = words.size() - 4;
    if (words.size() == 3) {
      addIOrIp(opPara);
    }
    else {
      addElOrElp(opPara);
      addEsOrSsList(opPara, start, finish);
      addEreOrSreOrErepOrSRep(opPara);
    }
  }

  private void addNofix(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int start = 1;
    final int finish = words.size() - 2;

    addLOrLp(opPara);
    addEsOrSsList(opPara, start, finish);
    addErOrSrOrErpOrSrp(opPara);
  }

  private void addPreOrPrep(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int namePosition = 0;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.PREP :
      OperatorTokenType.PRE;

    addOp(words, namePosition, type, opPara);
  }

  private void addLOrLp(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int namePosition = 0;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.LP :
      OperatorTokenType.L;

    addOp(words, namePosition, type, opPara);
  }

  private void addPostOrPostp(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int namePosition = 1;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.POSTP :
      OperatorTokenType.POST;

    addOp(words, namePosition, type, opPara);
  }

  private void addElOrElp(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int namePosition = 1;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.ELP :
      OperatorTokenType.EL;

    addOp(words, namePosition, type, opPara);
  }

  private void addEsOrSsList(OptempPara opPara, int start, int finish)
    throws OperatorException
  {
    List words = opPara.getOper();

    for (int i = start; i < finish; i += 2) {
      OperatorTokenType type =
        isSeq(words, i) ?
        OperatorTokenType.SS :
        OperatorTokenType.ES;

      int namePosition = i + 1;
      addOp(words, namePosition, type, opPara);
    }
  }

  private void addErOrSrOrErpOrSrp(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    OperatorTokenType type = null;
    final int opPosition = words.size() - 2;
    final int namePosition = words.size() - 1;

    if (opPara.getCat().equals(Cat.Relation)) {
      type = isSeq(words, opPosition) ?
        OperatorTokenType.SRP :
        OperatorTokenType.ERP;
    }
    else {
      type = isSeq(words, opPosition) ?
        OperatorTokenType.SR :
        OperatorTokenType.ER;
    }

    addOp(words, namePosition, type, opPara);
  }

  private void addEreOrSreOrErepOrSRep(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    OperatorTokenType type = null;
    final int opPosition = words.size() - 3;
    final int namePosition = words.size() - 2;

    if (opPara.getCat().equals(Cat.Relation)) {
      type = isSeq(words, opPosition) ?
        OperatorTokenType.SREP :
        OperatorTokenType.EREP;
    }
    else {
      type = isSeq(words, opPosition) ?
        OperatorTokenType.SRE :
        OperatorTokenType.ERE;
    }

    addOp(words, namePosition, type, opPara);
  }

  private void addIOrIp(OptempPara opPara)
    throws OperatorException
  {
    List words = opPara.getOper();
    final int namePosition = 1;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.IP :
      OperatorTokenType.I;

    addOp(words, namePosition, type, opPara);
  }

  private boolean isSeq(List words, int i)
  {
    return (((Operand) words.get(i)).getList()).booleanValue();
  }

  /**
   * Converts a DeclName to its string representation.
   */
  private String getName(Object o)
  {
    String result = null;

    if (o instanceof Operator) {
      Operator op = (Operator) o;
      assert op.getWord().equals(getWord(op.getWord()));
      result = op.getWord();
    }
    else {
      throw new CztException("Attempt to add non-operator " +
                             "into operator table");
    }
    return result;
  }

  private void addOp(String name, OperatorTokenType type, OptempPara opPara)
    throws OperatorException
  {
    final Integer precedence = opPara.getPrec();
    final Assoc associativity = opPara.getAssoc();
    addOptempPara(name, opPara);
    addOpToken(name, type, opPara);
    addPrecedence(name, precedence);
    addAssociativity(precedence, associativity);
  }

  private void addOp(List words, int namePosition, OperatorTokenType type,
                     OptempPara opPara)
    throws OperatorException
  {
    String name = getName(words.get(namePosition));
    addOp(name, type, opPara);
  }

  private void addOptempPara(String word, OptempPara optempPara)
  {
    optempPara_.put(word, optempPara);
  }

  /**
   * Adds a new association from a word to operator token.
   * This is explained in section 7.4.4 of the Z standard.
   *
   * throws OperatorException if an association of the same
   *        word to a different operator token already exists.
   */
  private void addOpToken(String word,
                          OperatorTokenType type,
                          OptempPara opPara)
    throws OperatorException
  {
    final OperatorTokenType existingType =
      (OperatorTokenType) opTokens_.get(word);
    if (existingType != null && ! type.equals(existingType)) {
      OptempPara optempPara = optempPara_.get(word);
      LocAnn locAnn1 = (LocAnn) optempPara.getAnn(LocAnn.class);
      LocAnn locAnn2 = (LocAnn) opPara.getAnn(LocAnn.class);
      String message =
        "Operator word " + word + " defined as operator token " + existingType;
      if (locAnn1 != null) {
        message += " at line " + locAnn1.getLine() +
          " column " + locAnn1.getCol() +
          " in " + locAnn1.getLoc();
      }
      message += " and as operator token " + type;
      if (locAnn2 != null) {
        message += " at line " + locAnn2.getLine() +
          " column " + locAnn2.getCol() +
          " in " + locAnn2.getLoc();
      }
      message += "; but the association of operator words " +
        "and operator tokens must be a function " +
        "(see ISO Z Standard section 7.4.4).";
      throw new OperatorException(message);
    }
    opTokens_.put(word, type);
  }

  /**
   * Adds all the associations from a word to operator token
   * provided by the parent operator table to the current scope.
   *
   * @throws OperatorException if an association of one of the
   *        words to a different operator token already exists.
   */
  private void addOpTokens(OpTable parentTable)
    throws OperatorException
  {
    final Map parentOpTokens = parentTable.opTokens_;
    for (Iterator i = parentOpTokens.keySet().iterator(); i.hasNext();) {
      String word = (String) i.next();
      OperatorTokenType type = (OperatorTokenType) parentOpTokens.get(word);
      assert type != null;
      addOpToken(word, type, parentTable.optempPara_.get(word));
    }
  }

  /**
   * Adds a new association from a word to precedence.
   * As explained in section 8.3 of the Z standard,
   * all templates in scope that use the same word shall
   * have the same precedence.
   *
   * throws OperatorException if an association of the same
   *        word to a different precedence already exists.
   */
  private void addPrecedence(String word, Integer precedence)
    throws OperatorException
  {
    if (precedence != null) {
      final Integer existingPrec = (Integer) precedence_.get(word);
      if (existingPrec != null && ! existingPrec.equals(precedence)) {
        String message =
          "Name " + word + " defined with precedence " + existingPrec +
          " and " + precedence;
        throw new OperatorException(message);
      }
      precedence_.put(word, precedence);
    }
  }

  /**
   * Adds all the associations from a word to operator token
   * provided by the parent operator table to the current scope.
   *
   * @throws OperatorException if an association of one of the
   *        words to a different operator token already exists.
   */
  private void addPrecedences(OpTable parentTable)
    throws OperatorException
  {
    final Map parentPrecs = parentTable.precedence_;
    for (Iterator i = parentPrecs.keySet().iterator(); i.hasNext();) {
      String word = (String) i.next();
      Integer prec = (Integer) parentPrecs.get(word);
      assert prec != null;
      addPrecedence(word, prec);
    }
  }

  /**
   * Adds an associativity to a precedence level.
   * As explained in section 8.3 of the Z standard,
   * different associativities shall not be used at the same precedence level.
   *
   * throws OperatorException if a different association is already
   *        defined for this precedence.
   */
  private void addAssociativity(Integer precedence, Assoc assoc)
    throws OperatorException
  {
    if (precedence != null) {
      assert assoc != null;
      final Assoc existingAssoc = (Assoc) assoc_.get(precedence);
      if (existingAssoc != null && ! existingAssoc.equals(assoc)) {
        String message =
          "Precedence " + precedence + " is associated with " + existingAssoc +
          " and " + assoc;
        throw new OperatorException(message);
      }
      assoc_.put(precedence, assoc);
    }
  }

  /**
   * Adds all the associations from precedence to associativity
   * provided by the parent operator table to the current scope.
   *
   * @throws OperatorException if a different association is already
   *         defined for one of the precedences.
   */
  private void addAssociativities(OpTable parentTable)
    throws OperatorException
  {
    final Map parentAssoc = parentTable.assoc_;
    for (Iterator i = parentAssoc.keySet().iterator(); i.hasNext();) {
      Integer precedence = (Integer) i.next();
      Assoc assoc = (Assoc) parentAssoc.get(precedence);
      assert assoc != null;
      addAssociativity(precedence, assoc);
    }
  }

  /**
   * An operator info.
   */
  public static class OpInfo
  {
    /**
     * The name of the section where this operator is defined.
     */
    private String section_;
    private Cat cat_;
    private Assoc assoc_;
    private Integer prec_;

    public OpInfo(String section, OptempPara opPara)
    {
      section_ = section;
      cat_ = opPara.getCat();
      assoc_ = opPara.getAssoc();
      prec_ = opPara.getPrec();
    }

    public String getSection()
    {
      return section_;
    }

    public Cat getCat()
    {
      return cat_;
    }

    public Assoc getAssoc()
    {
      return assoc_;
    }

    public Integer getPrec()
    {
      return prec_;
    }
  }

  /**
   * @czt.todo How should this class look like?
   */
  public static class OperatorException
    extends CommandException
  {
    public OperatorException(String message)
    {
      super(message);
    }
  }
}
