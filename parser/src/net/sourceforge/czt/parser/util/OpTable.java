/**
Copyright (C) 2004 Tim Miller, Mark Utting, Petra Malik
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

package net.sourceforge.czt.parser.util;

import java.util.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
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
   * <p>A mapping from operator token to operator token type.
   * For instance, the operator template for '_ + _' adds an entry
   * '+' -> 'I' to this map.</p>
   * <p>This map corresponds to the associations between WORDs
   * and operator tokens mentioned in the Z Standard chapter 7.4.4.
   * Since the set of active associations is always a function,
   * a map can be used here.</p>
   */
  private Map/*<String, OperatorTokenType>*/ opTokens_ = new HashMap();

  /**
   * A mapping from operator token to precedence.
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
  {
    section_ = section;
    if (parents != null) {
      for (Iterator iter = parents.iterator(); iter.hasNext();) {
        OpTable table = (OpTable) iter.next();
        ops_.putAll(table.ops_);
        opTokens_.putAll(table.opTokens_);
        precedence_.putAll(table.precedence_);
        assoc_.putAll(table.assoc_);
      }
    }
  }

  /**
   * Removes all decorations, i.e. strokes,
   * from a decorword and returns the word part.
   */
  public static String getWord(String decorword)
  {
    DeclName dn = Strokes.getWordAndStroke(decorword);
    return dn.getWord();
  }

  public static String getOpNameWithoutStrokes(List/*<Oper>*/ oper) {
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

  public OperatorTokenType getTokenType(String opWord)
  {
    return (OperatorTokenType) opTokens_.get(getWord(opWord));
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
    if (ops_.get(name) != null) {
      String message = "Operator " + name + " defined more than once";
      throw new OperatorException(message);
    }
    ops_.put(name, info);
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
    final OperatorTokenType existingType =
      (OperatorTokenType) opTokens_.get(name);
    if (existingType != null && ! type.equals(existingType)) {
      String message =
        "Name " + name + " defined as " + existingType + " and " + type;
      throw new OperatorException(message);
    }
    opTokens_.put(name, type);
    if (opPara.getPrec() != null) {
      final Integer existingPrec = (Integer) precedence_.get(name);
      final Integer newPrec = opPara.getPrec();
      if (existingPrec != null && ! existingPrec.equals(newPrec)) {
        String message =
          "Name " + name + " defined with precedence " + existingPrec +
          " and " + newPrec;
        throw new OperatorException(message);
      }
      precedence_.put(name, newPrec);
      final Assoc existingAssoc = (Assoc) assoc_.get(newPrec);
      final Assoc newAssoc = opPara.getAssoc();
      if (existingAssoc != null && ! existingAssoc.equals(newAssoc)) {
        String message =
          "Precedence " + newPrec + " is associated with " + existingAssoc +
          " and " + newAssoc;
        throw new OperatorException(message);
      }
      assoc_.put(newPrec, newAssoc);
    }
  }

  private void addOp(List words, int namePosition, OperatorTokenType type, 
                     OptempPara opPara)
    throws OperatorException
  {
    String name = getName(words.get(namePosition));
    addOp(name, type, opPara);
  }

  /**
   * An operator info.
   */
  public class OpInfo
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
  public class OperatorException
    extends Exception
  {
    public OperatorException(String message)
    {
      super(message);
    }
  }
}
