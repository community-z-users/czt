/*
  Copyright (C) 2004, 2005 Tim Miller, Mark Utting, Petra Malik
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Assoc;
import net.sourceforge.czt.z.ast.Cat;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Operand;
import net.sourceforge.czt.z.ast.Operator;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;

/**
 * An operator table manages all the operator definitions of a section.
 * It provides search facilities for all the operators defined in this
 * section or inherited from  parent sections,
 * plus facilities for defining new operators.
 */
public class OpTable extends InfoTable
{

  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String, Name or DeclName?
   */
  private SortedMap<String,OpInfo> ops_ = new TreeMap<String,OpInfo>();

  /**
   * <p>A mapping from operator word to operator template.
   * This is used to compute meaningful error messages.</p>
   */
  private Map<String,OptempPara> optempPara_ =
    new HashMap<String,OptempPara>();

  /**
   * <p>A mapping from operator word to operator token type.
   * For instance, the operator template for '_ + _' adds an entry
   * '+' -> 'I' to this map.</p>
   * <p>This map corresponds to the associations between WORDs
   * and operator tokens mentioned in the Z Standard chapter 7.4.4.
   * Since the set of active associations is always a function,
   * a map can be used here.</p>
   */
  private Map<String,OperatorTokenType> opTokens_ =
    new HashMap<String,OperatorTokenType>();

  /**
   * A mapping from operator word to precedence.
   * For instance, '+' is mapped to '30'.
   */
  private Map<String,BigInteger> precedence_ =
    new HashMap<String,BigInteger>();

  /**
   * Maps precedence to associativity.
   */
  private Map<BigInteger,Assoc> assoc_ =
    new HashMap<BigInteger,Assoc>();
  
  /**
   * Constructs an operator table for the given section. The table needs to be initialized using
   * {@link #addParents(Collection)} method, passing in operator tables of all direct parents. The
   * method checks that the operators defined in the parents are consistent, according to the 3
   * rules in the Z standard.
   * 
   * @param sectionName
   */
  public OpTable(Dialect d, String sectionName)
  {
    super(d, sectionName);
  }
  
  /**
   * 
   * @param <T>
   * @param table
   * @throws net.sourceforge.czt.parser.util.InfoTable.InfoTableException
   */ 
  @Override
  protected <T extends InfoTable> void addParentTable(T table) throws InfoTable.InfoTableException
  {
    addParentOpTable((OpTable)table);
  }

  private void addParentOpTable(OpTable parentTable)
    throws OperatorException
  {
    assert parentTable != null && ops_ != null;
    ops_.putAll(parentTable.ops_);
    addOpTokens(parentTable);
    addPrecedences(parentTable);
    addAssociativities(parentTable);
    optempPara_.putAll(parentTable.optempPara_);
  }

  public static String getOpNameWithoutStrokes(List<Oper> oper)
  {
    StringBuffer result = new StringBuffer();
    for (Oper o : oper) {
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

  @Override
  public String toString()
  {
    return "OpTable for " + getSectionName() + "\n" + opTokens_;
  }
  
  public OpInfo lookup(OperatorName operatorName)
  {
    return ops_.get(operatorName.getWord());
  }

  public OperatorTokenType getTokenType(Decorword decorword)
  {
    return getTokenType(decorword.getWord());
  }

  public OperatorTokenType getTokenType(String opNameNoArgs)
  {
    return opTokens_.get(opNameNoArgs);
  }

  public BigInteger getPrec(String opWord)
  {
    return precedence_.get(getWord(opWord));
  }

  public Assoc getAssoc(String opWord)
  {
    BigInteger prec = precedence_.get(getWord(opWord));
    if (prec == null) return null;
    return assoc_.get(prec);
  }

  /**
   * Adds a new operator.
   *
   * @param opPara
   * @throws OperatorException if operator is incompatible
   *                           with existing operators.
   */
  public void add(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> oper = opPara.getOper();
    if (oper.size() < 2) {
      throw new OperatorException(getDialect(), "Error: operator template with less " +
                                  "than 2 arguments");
    }
    OpInfo info = new OpInfo(getSectionName(), opPara);
    String name = getOpNameWithoutStrokes(opPara.getOper());
    addOperator(name, info);
    Oper first = oper.get(0);
    Oper last = oper.get(oper.size() - 1);
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
      throw new OperatorException(getDialect(), message);
    }
    ops_.put(name, info);
  }

  private void addPrefix(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
    final int start = 1;
    final int finish = words.size() - 2;

    addLOrLp(opPara);
    addEsOrSsList(opPara, start, finish);
    addErOrSrOrErpOrSrp(opPara);
  }

  private void addPreOrPrep(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
    final int namePosition = 0;
    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.PREP :
      OperatorTokenType.PRE;

    addOp(words, namePosition, type, opPara);
  }

  private void addLOrLp(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
    final int namePosition = 0;
    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.LP :
      OperatorTokenType.L;

    addOp(words, namePosition, type, opPara);
  }

  private void addPostOrPostp(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
    final int namePosition = 1;
    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.POSTP :
      OperatorTokenType.POST;

    addOp(words, namePosition, type, opPara);
  }

  private void addElOrElp(OptempPara opPara)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
    final int namePosition = 1;
    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.ELP :
      OperatorTokenType.EL;

    addOp(words, namePosition, type, opPara);
  }

  private void addEsOrSsList(OptempPara opPara, int start, int finish)
    throws OperatorException
  {
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
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
    List<Oper> words = opPara.getOper();
    final int namePosition = 1;

    final OperatorTokenType type = opPara.getCat().equals(Cat.Relation) ?
      OperatorTokenType.IP :
      OperatorTokenType.I;

    addOp(words, namePosition, type, opPara);
  }

  private boolean isSeq(List<Oper> words, int i)
  {
    return (((Operand) words.get(i)).getList()).booleanValue();
  }

  /**
   * Converts a DeclName to its string representation.
   */
  private String getName(Object o)
    throws OperatorException
  {
    String result = null;

    if (o instanceof Operator) {
      Operator op = (Operator) o;
      assert op.getWord().equals(getWord(op.getWord()));
      result = op.getWord();
    }
    else {
      throw new OperatorException(getDialect(), "Attempt to add non-operator " +
                                  "into operator table");
    }
    return result;
  }

  private void addOp(String name, OperatorTokenType type, OptempPara opPara)
    throws OperatorException
  {
    final BigInteger precedence = opPara.getPrec();
    final Assoc associativity = opPara.getAssoc();
    addOptempPara(name, opPara);
    addOpToken(name, type, opPara);
    addPrecedence(name, precedence);
    addAssociativity(precedence, associativity);
  }

  private void addOp(List<Oper> words, int namePosition, OperatorTokenType type,
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
      opTokens_.get(word);
    if (existingType != null && ! type.equals(existingType)) {
      OptempPara optempPara = optempPara_.get(word);
      LocAnn locAnn1 = optempPara.getAnn(LocAnn.class);
      LocAnn locAnn2 = opPara.getAnn(LocAnn.class);
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
      throw new OperatorException(getDialect(), message);
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
    final Map<String,OperatorTokenType> parentOpTokens =
      parentTable.opTokens_;
    for (Map.Entry<String,OperatorTokenType> word : parentOpTokens.entrySet()) {
      OperatorTokenType type = word.getValue();
      assert type != null;
      addOpToken(word.getKey(), type, parentTable.optempPara_.get(word.getKey()));
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
  private void addPrecedence(String word, BigInteger precedence)
    throws OperatorException
  {
    if (precedence != null) {
      final BigInteger existingPrec = precedence_.get(word);
      if (existingPrec != null && ! existingPrec.equals(precedence)) {
        String message =
          "Name " + word + " defined with precedence " + existingPrec +
          " and " + precedence;
        throw new OperatorException(getDialect(), message);
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
    final Map<String,BigInteger> parentPrecs = parentTable.precedence_;
    for (Map.Entry<String, BigInteger> word : parentPrecs.entrySet()) {
      BigInteger prec = word.getValue();
      assert prec != null;
      addPrecedence(word.getKey(), prec);
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
  private void addAssociativity(BigInteger precedence, Assoc assoc)
    throws OperatorException
  {
    if (precedence != null) {
      assert assoc != null;
      final Assoc existingAssoc = assoc_.get(precedence);
      if (existingAssoc != null && ! existingAssoc.equals(assoc)) {
        String message =
          "Precedence " + precedence + " is associated with " + existingAssoc +
          " and " + assoc;
        throw new OperatorException(getDialect(), message);
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
    final Map<BigInteger,Assoc> parentAssoc = parentTable.assoc_;
    for (Map.Entry<BigInteger,Assoc> precedence : parentAssoc.entrySet()) {
      Assoc assoc = precedence.getValue();//parentAssoc.get(precedence);
      assert assoc != null;
      addAssociativity(precedence.getKey(), assoc);
    }
  }

  public OpInfo lookup(List<String> list)
  {
    StringBuilder opname = new StringBuilder();
    for (String s : list)
    {
      if (ZString.ARG_TOK.equals(s) || ZString.LISTARG_TOK.equals(s))
      {
        opname.append(s);
      }
      else
      {
        opname.append(getWord(s));
      }
    }
    OpInfo result = lookup(opname.toString());
    return result;
  }

  /**
   * Looks up opname to see if it is defined as an operator
   * in this section or in any of the ancestor sections.
   * The resulting OpInfo structure contains all the details about
   * the operator, including the name of the section it was defined in.
   *
   * @param opname Operator name.  Example " _ + _ ".
   * @return       Returns <code>null</code> if <code>opname</code>
   * is not an operator.
   * @czt.todo What about "\power_1"?
   */
  public OpInfo lookup(String opname)
  {
    return ops_.get(opname);
  }
   
  /**
   * An operator info.
   */
  public static class OpInfo extends InfoTable.Info
  {
    private Cat cat_;
    private Assoc assoc_;
    private BigInteger prec_;

    public OpInfo(String section, OptempPara opPara)
    {
      super(section);
      cat_ = opPara.getCat();
      assoc_ = opPara.getAssoc();
      prec_ = opPara.getPrec();
    }

    public Cat getCat()
    {
      return cat_;
    }

    public Assoc getAssoc()
    {
      return assoc_;
    }

    public BigInteger getPrec()
    {
      return prec_;
    }
  }

  /**
   * @czt.todo How should this class look like?
   */
  public static class OperatorException
    extends InfoTable.InfoTableException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -5924881417952399985L;

	public OperatorException(Dialect d, String message)
    {
      super(d, message);
    }
  }
}
