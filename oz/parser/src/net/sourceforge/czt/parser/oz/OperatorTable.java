/**
Copyright 2003 Tim Miller
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.parser.oz;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.util.TypesafeList;

/**
 * An operator table records each operator and its integer value.
 */
public class OperatorTable
{
  /** The different types of templates. */
  public static final int PREFIX = 1;
  public static final int POSTFIX = PREFIX + 1;
  public static final int INFIX = POSTFIX + 1;
  public static final int NOFIX = INFIX + 1;

  /** The name of the prelude section */
  public static final String PRELUDE = "prelude";

  /** The function of all sections to their immediate parents */
  protected Map mParents_ = new HashMap();

  /** The current section's parents. */
  protected Set mCurrentParents_ = new HashSet();

  /** The current section. */
  protected String mSection_ = null;

  /** The operators. */
  protected Set mOperators_ = new HashSet();

  /** The operator names - allows hash lookup of names */
  protected Set mOperatorNames_ = new HashSet();

  /**
   * Construct a new operator table.
   */
  public OperatorTable()
  {
  }

  /**
   * Add an operatior with a specified prefix. Other information is
   * retrieved from the OptempPara
   * @param fix the "fix" e.g. OperatorTable.PREFIX
   * @param otp the operator template paragraph containing the info
   */
  public void add(int fix, OptempPara otp)
  {
    switch (fix)
    {
        case PREFIX:
          addPrefix(otp);
          break;
        case POSTFIX:
          addPostfix(otp);
          break;
        case INFIX:
          addInfix(otp);
          break;
        case NOFIX:
          addNofix(otp);
          break;
        default:
          //do nothing
    }
  }

  /**
   * Set the current section.
   * @param section the section
   */
  public void setSection(String section)
  {
    endSection();
    mSection_ = new String(section);
  }

  /**
   * @return the current section
   */
  public String getSection()
  {
    return mSection_;
  }

  /**
   * Add a parent to the current section.
   * @param parent the parent to be added
   */
  public void addParent(String parent)
  {
    //add the parent as a current parents
    mCurrentParents_.add(parent);

    //get the current section's list of parents
    Set parents = (Set) mParents_.get(mSection_);

    //add the parents to the list of the current section's parents
    if (parents == null) {
      parents = new HashSet();
    }
    parents.add(parent);
    mParents_.put(mSection_, parents);

    //add the transitive parents
    mCurrentParents_.addAll(getTransitiveParents(parent));
  }

  /**
   * End the current section.
   */
  public void endSection()
  {
    mCurrentParents_ = new HashSet();
    mSection_ = null;
  }

  /**
   * Lookup the int token value of a symbol, e.g. LatexSym.PRE
   * @param symbol the string value of the symbol
   * @return the int token value of symbol
   * Assumes that symbols are never given the value -1
   */
  public int lookup(String symbol)
  {
    int result = -1;
    String section = null;

    for (Iterator iter = mOperators_.iterator(); iter.hasNext(); ) {
      Operator op = (Operator) iter.next();
      if (op.getName().equals(symbol)) {
        result = op.getType();
        section = op.getSection();
        break;
      }
    }

    //true if and only if the symbol was defined in this section,
    //or this section's parents (the prelude will always be a section)
    //or the specification is anonymous (i.e. all operators are available)
    return (mCurrentParents_.contains(section) ||
            (mSection_ != null && mSection_.equals(section)) ||
            (section != null && section.equals(PRELUDE)) ||
            mSection_ == null) ?
      result :
      -1;
  }

  //get the transitive parents of a section
  private Set getTransitiveParents(String section) {
    Set result = new HashSet();

    //get the set of direct parents
    Set parents = (Set) mParents_.get(section);

    if (parents != null) {
      result.addAll(parents);

      //for each direct parent, get the transitive parents
      for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
        String parent = (String) iter.next();
        Set transitiveParents = getTransitiveParents(parent);
        result.addAll(transitiveParents);
      }
    }
    return result;
  }

  /**
   * Dump the entire contents of the table (for debugging purposes).
   */
  public void dump()
  {
    for (Iterator iter = mOperators_.iterator(); iter.hasNext(); ) {
      Operator op = (Operator) iter.next();
      System.err.println(op.getName() + ": " + getType(op.getType()));
    }
  }

  /**
   * Returns the type as a string (for debugging purposes).
   */
  public static String getType(int type)
  {
    String result = null;
    switch (type) {
        case LatexSym.PREP:
          result = "PREP";
          break;
        case LatexSym.PRE:
          result = "PRE";
          break;
        case LatexSym.POSTP:
          result = "POSTP";
          break;
        case LatexSym.POST:
          result = "POST";
          break;
        case LatexSym.IP:
          result = "IP";
          break;
        case LatexSym.I:
          result = "I";
          break;
        case LatexSym.LP:
          result = "LP";
          break;
        case LatexSym.L:
          result = "L";
          break;
        case LatexSym.ELP:
          result = "ELP";
          break;
        case LatexSym.EL:
          result = "EL";
          break;
        case LatexSym.ERP:
          result = "ERP";
          break;
        case LatexSym.ER:
          result = "ER";
          break;
        case LatexSym.SRP:
          result = "SRP";
          break;
        case LatexSym.SR:
          result = "SR";
          break;
        case LatexSym.EREP:
          result = "EREP";
          break;
        case LatexSym.ERE:
          result = "ERE";
          break;
        case LatexSym.SREP:
          result = "SREP";
          break;
        case LatexSym.SRE:
          result = "SRE";
          break;
        case LatexSym.ES:
          result = "ES";
          break;
        case LatexSym.SS:
          result = "SS";
          break;
        default:
          result = "NOT_FOUND";
    }
    return result;
  }

  private void addPrefix(OptempPara otp)
  {
    List words = otp.getWordOrOperand();

    int start = 1;
    int finish = words.size() - 4;

    if (words.size() == 2) {
      //"PRE _ | PREP _"
      addPreOrPrep(otp);
    }
    else {
      //"L  { _ (ES | SS) } _ (ERE | SRE) _ | "
      //"LP { _ (ES | SS) } _ (EREP | SREP) _"
      addLOrLp(otp);
      addEsOrSsList(otp, start, finish);
      addEreOrSreOrErepOrSRep(otp);
    }
  }

  private void addPostfix(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int start = 2;
    int finish = words.size() - 3;

    if (words.size() == 2) {
      //"_ POST | _ POSTP"
      addPostOrPostp(otp);
    }
    else {
      //"_ EL { _ (ES | SS) } _ (ER | SR) |"
      //"_ ELP { _ (ES | SS) } _ (ERP | SRP)"

      addElOrElp(otp);
      addEsOrSsList(otp, start, finish);
      addErOrSrOrErpOrSrp(otp);
    }
  }

  private void addInfix(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int start = 2;
    int finish = words.size() - 4;

    if (words.size() == 3) {
      addIOrIp(otp);
    }
    else {
      addElOrElp(otp);
      addEsOrSsList(otp, start, finish);
      addEreOrSreOrErepOrSRep(otp);
    }
  }

  private void addNofix(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int start = 1;
    int finish = words.size() - 2;

    addLOrLp(otp);
    addEsOrSsList(otp, start, finish);
    addErOrSrOrErpOrSrp(otp);
  }

  private void addPreOrPrep(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int namePosition = 0;

    int type = otp.getCat().equals(Cat.Relation) ?
      LatexSym.PREP :
      LatexSym.PRE;

    addOp(words, namePosition, type);
  }

  private void addLOrLp(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int namePosition = 0;

    int type = otp.getCat().equals(Cat.Relation) ?
      LatexSym.LP :
      LatexSym.L;

    addOp(words, namePosition, type);
  }

  private void addPostOrPostp(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int namePosition = 1;

    int type = otp.getCat().equals(Cat.Relation) ?
      LatexSym.POSTP :
      LatexSym.POST;

    addOp(words, namePosition, type);
  }

  private void addElOrElp(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int namePosition = 1;

    int type = otp.getCat().equals(Cat.Relation) ?
      LatexSym.ELP :
      LatexSym.EL;

    addOp(words, namePosition, type);
  }

  private void addEsOrSsList(OptempPara otp, int start, int finish)
  {
    List words = otp.getWordOrOperand();

    for (int i = start; i < finish; i += 2) {
      int type =
        isSeq(words, i) ?
        LatexSym.SS :
        LatexSym.ES;

      int namePosition = i + 1;
      addOp(words, namePosition, type);
    }
  }

  private void addErOrSrOrErpOrSrp(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int type = -1;
    int opPosition = words.size() - 2;
    int namePosition = words.size() - 1;

    if (otp.getCat().equals(Cat.Relation)) {
      type = isSeq(words, opPosition) ?
        LatexSym.SRP :
        LatexSym.ERP;
    }
    else {
      type = isSeq(words, opPosition) ?
        LatexSym.SR :
        LatexSym.ER;
    }

    addOp(words, namePosition, type);
  }

  private void addEreOrSreOrErepOrSRep(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int type = -1;
    int opPosition = words.size() - 3;
    int namePosition = words.size() - 2;

    if (otp.getCat().equals(Cat.Relation)) {
      type = isSeq(words, opPosition) ?
        LatexSym.SREP :
        LatexSym.EREP;
    }
    else {
      type = isSeq(words, opPosition) ?
        LatexSym.SRE :
        LatexSym.ERE;
    }

    addOp(words, namePosition, type);
  }

  private void addIOrIp(OptempPara otp)
  {
    List words = otp.getWordOrOperand();
    int namePosition = 1;

    int type = otp.getCat().equals(Cat.Relation) ?
      LatexSym.IP :
      LatexSym.I;

    addOp(words, namePosition, type);
  }

  private void addOp(String name, int type)
  {
    if (mOperatorNames_.contains(name)) {
      //TODO: throw an exception
    }
    Operator op = new Operator(name, mSection_, type);
    mOperators_.add(op);
  }

  private void addOp(List words, int namePosition, int type)
  {
    String name = getName(words.get(namePosition));
    addOp(name, type);
  }

  //convert a DeclName to its string representation
  private String getName(Object o)
  {
    //TODO: remove this
    if (o instanceof String) {
      return (String) o;
    }

    String result = null;
    DeclName dn = (DeclName) o;

    result = new String(dn.getWord());

    for (int i = 0; i < dn.getStroke().size(); i++) {
      if (dn.getStroke().get(i) instanceof InStroke) {
        result += LatexScanner.INSTROKE;
      }
      else if (dn.getStroke().get(i) instanceof OutStroke) {
        result += LatexScanner.OUTSTROKE;
      }
      else if (dn.getStroke().get(i) instanceof NextStroke) {
        result += LatexScanner.NEXTSTROKE;
      }
      else if (dn.getStroke().get(i) instanceof NumStroke) {
        NumStroke ns = (NumStroke) dn.getStroke().get(i);
        result += Character.toString(LatexScanner.STROKE_USCORE) +
	  Character.toString(LatexScanner.STARTGLUE) +
	  ns.getNumber().toString() + 
	  Character.toString(LatexScanner.ENDGLUE);
      }
    }
    return result;
  }

  private boolean isSeq(List words, int i)
  {
    return (((Operand) words.get(i)).getList()).booleanValue();
  }

  /**
   * An operator
   */
  private class Operator
  {
    /** The "name" of the token. */
    protected String mName_;

    /** the section in which the operator is declared. */
    protected String mSection_;

    /** the type of the token (e.g. LatexSym.IP). */
    protected int mType_;

    /**
     * Construct a new operator.
     */
    public Operator()
    {
      mName_ = new String();
      mSection_ = new String();
      mType_ = -1;
    }

    /**
     * Construct a new operator from the given info.
     */
    public Operator(String name, String section, int type)
    {
      mName_ = new String(name);
      mSection_ = (section == null) ? null : new String(section);
      mType_ = type;
    }

    /**
     * Return the name of this operator.
     */
    public String getName()
    {
      return mName_;
    }

    /**
     * Return the section in which this operator was declared.
     */
    public String getSection()
    {
      return mSection_;
    }

    /**
     * Return the type of this operator.
     */
    public int getType()
    {
      return mType_;
    }
  }
}
