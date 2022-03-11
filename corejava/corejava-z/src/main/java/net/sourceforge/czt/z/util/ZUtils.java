/*
  Copyright (C) 2005, 2006, 2007 Mark Utting
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

import net.sourceforge.czt.util.Section;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.TermImpl;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

public final class ZUtils
{

  /**
   * Do not create instances of this class.
   */
  private ZUtils()
  {
  }

  public static final Factory FACTORY = createConsoleFactory();

  /**
   * Useful factory for debugging purposes. It prints ASCII names and
   * LocAnn offset by one in line/col count and no name IDs.
   * @return
   */
  public static Factory createConsoleFactory()
  {
    return createFactory(false, false, 1, 1);
  }

  /**
   * Create a factory tailored for either debugging or UI purposes. Various
   * parameters affect the base factory underlying print visitor's parameters.
   * @param printUnicode
   * @param printNameIds
   * @param printLocLineOffset
   * @param printLocColOffset
   * @return
   */
  public static Factory createFactory(boolean printUnicode, boolean printNameIds, int printLocLineOffset,
          int printLocColOffset)
  {
    // Make a factory that prints names in ASCII, not Unicode
    // (This is better for debugging and for console output).
    PrintVisitor printer = new PrintVisitor(printUnicode);
    printer.setPrintIds(printNameIds);
    printer.setOffset(printLocLineOffset, printLocColOffset);
    ZFactoryImpl tmp = new ZFactoryImpl();
    tmp.setToStringVisitor(printer);
    Factory result = new Factory(tmp);
    return result;
  }

  public static void setToStringVisitor(Term term, PrintVisitor printer)
  {
    if (term instanceof TermImpl)
    {
      ((TermImpl)term).getFactory().setToStringVisitor(printer);
    }
    else
      throw new UnsupportedAstClassException("Couldn't cast given term as TermImpl");
  }

  /**
   * Computes a list of all the NameTypePairs from the given signature
   * whose name ends with the given decoration.  If <code>decor</code>
   * is <code>null</code> a list of all undecored names with its
   * corresponding types is returned.
   */
  public static List<NameTypePair> subsignature(Signature sig,
                                                Class<?> decor)
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>(sig.getNameTypePair().size());
    for (NameTypePair pair : sig.getNameTypePair()) {
      final ZName zName = pair.getZName();
      final ZStrokeList strokeList = zName.getZStrokeList();
      final int size = strokeList.size();
      if ((size == 0 && decor == null) ||
          (size > 0 && decor != null &&
           decor.isInstance(strokeList.get(strokeList.size() - 1)))) {
        result.add(pair);
      }
    }
    return result;
  }

  public static boolean isAnonymous(ZSect zSect)
  {
    final String name = zSect.getName();
    final List<Parent> parents = zSect.getParent();
    return Section.ANONYMOUS.getName().equals(name) &&
      parents.size() == 1 &&
      Section.STANDARD_TOOLKIT.getName().equals(parents.get(0).getWord());
  }
  
  /**
   * Given a set of parent sections return it as a CSV string.
   * Should satisfy the invariant akin to parentsAsString(parentsCSVAsSetOfString(s)) = s  (ignoring order)
   * @param parents
   * @return
   */
  public static String parentsAsString(Set<String> parents)
  {
		StringBuilder result = new StringBuilder();
		String sep = "";
		for(String p : parents)
		{
		  result.append(sep);
		  result.append(p);
		  sep = ",";
		}
		return result.toString();
  }
  
  /**
   * Trims the given string considering Z NLCHAR before and after.
   * i.e. removes spaces and newlines before and after.
   * @param string
   * @return
   */
  public static String trimNLCharAware(String string)
  {
    String result = string.trim();
    while (result.startsWith(ZString.NLCHAR)) {
      result = result.substring(1).trim();
    }
    while(result.endsWith(ZString.NLCHAR)) {
      result = result.substring(0, result.length() - 1).trim();
    }
    return result;
  }

  /**
   * Gets a CSV string of Z section parents and transforms it back to a set of string
   * Should satisfy the invariant akin parentsAsString(parentsCSVAsSetOfString(s)) = s (ignoring order).
   * @param p
   * @return
   */
  public static Set<String> parentsCSVAsSetOfString(String p)
  {
      String[] parents = p.split(",");
      Set<String> parentSet = new java.util.HashSet<String>();
      for (String parent : parents) {
        parent = trimNLCharAware(parent);
        if (parent != null && ! parent.equals("")) {
          parentSet.add(parent);
        }
      }
      return parentSet;
  }

  /**
   * Transforms the set of string parents into set of AST Parents
   * @param parents
   * @return
   */
  public static Set<Parent> parentsAsSetOfParent(Set<String> parents)
  {
	  Set<Parent> result = new java.util.HashSet<Parent>();
	  for (String p : parents)
	  {
		  result.add(FACTORY.createParent(p));
	  }
	  return result;
  }

  /**
   * Transforms the set of string parents into list of AST Parents
   * @param parents
   * @return
   */
  public static List<Parent> parentsAsListOfParent(Set<String> parents)
  {
	  List<Parent> result = FACTORY.list();
	  for (String p : parents)
	  {
		  result.add(FACTORY.createParent(p));
	  }
	  return result;
  }
  
  /**
   * Given a var-arg list of strings, transforms it into a set of strings (i.e. removes duplicates).
   * @param parents
   * @return
   */
  public static Set<String> parentsArgListAsSetOfString(String... p)
  {
	  Set<String> result = new java.util.HashSet<String>();
	  for(String s : p)
	  {
		  result.add(s);
	  }
	  return result;
  }

  /** 
   * Returns true if the given term is either a boxed or unboxed Z paragraph.
   * That is, a given set, a free type, an axiomatic/generic description,
   * a schema, a horizontal definition, a conjecture, or an operator template.
   */
  public static boolean isZPara(Term term) {
    return
      (term instanceof GivenPara) ||
      (term instanceof FreePara) ||
      (term instanceof AxPara) ||
      (term instanceof ConjPara) ||
      (term instanceof OptempPara);
  }
  
  /*
   * Abstract
      <name="Expr" type="Z:Expr" abstract="true">
      <name="Expr1" type="Z:Expr1" abstract="true"
      <name="Expr2" type="Z:Expr2" abstract="true"
      <name="SchExpr2" type="Z:SchExpr2"
      <name="Expr0N" type="Z:Expr0N"
      <name="Expr2N" type="Z:Expr2N"
      <name="QntExpr" type="Z:QntExpr"
      <name="Qnt1Expr" type="Z:Qnt1Expr"

    Not schema calculus
      <name="PowerExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
      <name="NumExpr" type="Z:NumExpr" substitutionGroup="Z:Expr">
      <name="SetExpr" type="Z:Expr0N" substitutionGroup="Z:Expr0N">
      <name="ProdExpr" type="Z:Expr2N" substitutionGroup="Z:Expr2N">
      <name="TupleExpr" type="Z:Expr2N" substitutionGroup="Z:Expr2N">
      <name="SetCompExpr" type="Z:QntExpr"
      <name="TupleSelExpr" type="Z:TupleSelExpr"

    Schema calculus
      <name="SchExpr" type="Z:SchExpr" substitutionGroup="Z:Expr">
      <name="DecorExpr" type="Z:DecorExpr" substitutionGroup="Z:Expr1">
      <name="HideExpr" type="Z:HideExpr" substitutionGroup="Z:Expr1">
      <name="NegExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
      <name="PreExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
      <name="RenameExpr" type="Z:RenameExpr" substitutionGroup="Z:Expr1">
      <name="ThetaExpr" type="Z:ThetaExpr" substitutionGroup="Z:Expr1">
      <name="BindExpr" type="Z:BindExpr" substitutionGroup="Z:Expr">
      <name="BindSelExpr" type="Z:BindSelExpr" substitutionGroup="Z:Expr1">

      <name="PipeExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="ProjExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="AndExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="OrExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="ImpliesExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="IffExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
      <name="CompExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">

      Qnt1Expr = without Lambda/Let
      <name="ExistsExpr" type="Z:Qnt1Expr"substitutionGroup="Z:Qnt1Expr">
      <name="Exists1Expr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr">
      <name="ForallExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr">

    Mixed / depends 
      <name="LambdaExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr">
      <name="LetExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr">
      <name="CondExpr" type="Z:CondExpr" substitutionGroup="Z:Expr">
      <name="RefExpr" type="Z:RefExpr" substitutionGroup="Z:Expr">
      <name="ApplExpr" type="Z:ApplExpr" substitutionGroup="Z:Expr2">
      <name="MuExpr" type="Z:QntExpr" substitutionGroup="Z:QntExpr">
   */

  /**
   * Enumerated type used to distinguish what kind of Z Expr is.
   * It is useful for determining statically, without type information,
   * the kind of term being handled. For instance, DefTable uses this
   * to best guess the kind of OmitBox involved in a declaration.
   */
  // TODO: should ThetaExpr, BindExpr and BinSelExpr be PURE or SCHEMA?
  public static enum ZExprKind {
    /**
     * Pure Z Expr
     */
    PURE,
    /**
     * Schema calculus expression
     */
    SCHEMA,
    /**
     * Depends on the inner expression
     */
    MIXED,
    /**
     * Couldn't figure out statically
     */
    UNKNOWN };

  /**
   * Returns whether or not a given expression is part of schema calculus
   * @param expr
   * @return
   */
  public static ZExprKind whatKindOfZExpr(Expr term)
  {
    ZExprKind result = ZExprKind.UNKNOWN;
    if ((term instanceof PowerExpr) ||
             (term instanceof NumExpr) ||
             (term instanceof SetExpr) ||
             (term instanceof ProdExpr) ||
             (term instanceof TupleExpr) ||
             (term instanceof SetCompExpr) ||
             (term instanceof TupleSelExpr) ||
             (term instanceof BindExpr) ||    // these two are pure, although schema related
             (term instanceof ThetaExpr) ||
             (term instanceof BindSelExpr))
    {
      /*
      \begin{zed}
         BLA == \lblot x == \nat \rblot   <-- consider pure
      \end{zed}

      \begin{axdef}
          bla: \{ BLA \}
      \end{axdef}

      \begin{zed}
         val == bla.x               <-- consider pure
      \end{zed}
       *
       */
      result = ZExprKind.PURE;
    }
    else if ((term instanceof SchExpr) ||
             (term instanceof DecorExpr) ||
             (term instanceof HideExpr) ||
             (term instanceof NegExpr) ||
             (term instanceof PreExpr) ||
             (term instanceof RenameExpr) ||
             // Pipe, Proj, And, Or, Implies, Iff, Comp
             (term instanceof SchExpr2) ||
             (term instanceof ExistsExpr) ||
             (term instanceof Exists1Expr) ||
             (term instanceof ForallExpr))
    {
      result = ZExprKind.SCHEMA;
    }
    else if ((term instanceof CondExpr) ||
             (term instanceof LambdaExpr) ||
             (term instanceof LetExpr) ||
             (term instanceof MuExpr) ||
             (term instanceof ApplExpr) ||
             (term instanceof RefExpr))
    {
      result = ZExprKind.MIXED;
    }
    return result;
  }

  /** Schema or generic schema definition (vertical).
   *      AxPara.Box          = SchBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = ConstDecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = SchemaName
   *      ConstDecl.expr      = SchExpr
   *
   * Axiomatic or generic definitions
   *      AxPara.Box          = AxBox
   *      AxPara.decl         = generics
   *
   *      AxPara.SchText.decl = declared variables
   *      AxPara.SchText.pred = axiomatic predicate
   *
   * Horizontal definition
   *      AxPara.Box          = OmitBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = Constdecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
   *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
   */
  
  /** Checks whether the given term is an AxPara */
  public static boolean isAxPara(Term term)
  {
    return term instanceof AxPara;
  }
  
  private static boolean coreBoxedAxiomaticDef(Term term)
  {
    return (isAxPara(term) && ((AxPara) term).getBox().equals(Box.AxBox));
  }
  
  /**
   * Returns the generic formals as NameList of a given term if it is
   * AxPara or null otherwise.  This is valid for any kind of
   * AxPara. That is, it returns the generic parameters for generic
   * boxes, horizontal definitions, and schemas.
   */
  public static NameList getAxParaGenFormals(Term term)
  {
    return (isAxPara(term) ? ((AxPara) term).getNameList() : null);
  }

  /**
   * Returns the generic formals as ZNameList of a given term if it is
   * AxPara or null otherwise This is valid for any kind of
   * AxPara. That is, it returns the generic parameters for generic
   * boxes, horizontal definitions, and schemas.
   */
  public static ZNameList getAxParaZGenFormals(Term term)
  {
    return term == null ? null : assertZNameList(getAxParaGenFormals(term));
  }

  /**
   * Returns the ZDeclList of axiomatic or generic definitions, or
   * null if term is not an AxPara with AxBox.
   */
  public static ZDeclList getAxBoxDecls(Term term)
  {
    ZDeclList result = null;
    if (coreBoxedAxiomaticDef(term)) {          
      return ((AxPara) term).getZSchText().getZDeclList();
    }
    return result;
  }

  /**
   * Returns the Pred of axiomatic or generic definitions, or null if
   * term is not an AxPara with AxBox.
   */
  public static Pred getAxBoxPred(Term term)
  {
    Pred result = null;
    if (coreBoxedAxiomaticDef(term)) {          
      return ((AxPara) term).getZSchText().getPred();
    }
    return result;
  }

  /**
   * Return the generic formals of a given term if it is AxPara or
   * null otherwise
   */
  public static boolean isBoxedAxiomaticDef(Term term)
  {
    boolean result = coreBoxedAxiomaticDef(term);
    if (result) {
      NameList nl = getAxParaGenFormals(term);      
      result = (nl == null ||
                ((nl instanceof ZNameList) && ((ZNameList) nl).isEmpty()));
    }
    return result;
  }

  /**
   * Checks whether the given term is an AxPara with AxBox (i.e. it
   * comes from a \begin{gendef}[...]/GENAX
   */
  public static boolean isBoxedGenericDef(Term term)
  {
    boolean result = coreBoxedAxiomaticDef(term);
    if (result) {
      ZNameList nl = getAxParaZGenFormals(term);      
      result = (nl != null && !nl.isEmpty());
    }
    return result;
  }

  /**
   * Checks whether the given term is an AxPara with OmixBox.
   */
  public static boolean isHorizontalDef(Term term)
  {
    return (isAxPara(term) && ((AxPara) term).getBox().equals(Box.OmitBox));
  }

  /**
   * Checks whether the given term <code>isHorizontalDef(Term)</code>
   * and <code>isSimpleSchema(Term)</code>
   */
  public static boolean isHorizontalSchema(Term term)
  {
    return (isHorizontalDef(term) && isSimpleSchema(term));
  }

  /**
   * Checks whether the given term <code>isHorizontalDef(Term)</code>
   * and <code>!isSimpleSchema(Term)</code>
   */
  public static boolean isAbbreviation(Term term)
  {
    return (isHorizontalDef(term) && !isSimpleSchema(term));
  }

  /**
   * Returns true if the AxPara has been properly encoded as either a
   * schema box or a horizontal definition. It is useful for
   * assertions.
   */
  public static boolean isAxParaSchemaOrHorizDefValid(AxPara axp)
  {
    // ensure our understanding of the CZT encoding is right.
    return (axp.getZSchText().getPred() == null) &&
           (axp.getZSchText().getZDeclList().size() == 1) &&
           (axp.getZSchText().getZDeclList().get(0) instanceof ConstDecl);
  }

  /**
   * Checks whether the given paragraph is an <code>AxPara</code> term
   * encoded as a schema or not. That is, it checks whether the term
   * is properly encoded as either a horizontal or a boxed schema.
   * Note that this does not include schema calculus constructs like
   * R == S \land T on schemas S and T, but just SchExpr (usual) schemas.
   * For the latter we need to rely on typing information.
   */
  public static boolean isSimpleSchema(Term term)
  {
    boolean result = isAxPara(term);
    if (result) {
      AxPara axp = (AxPara) term;
      result = axp.getBox().equals(Box.SchBox);        
      // If it is not a SchBox then check for OmitBox.    
      if (!result) {
        result = axp.getBox().equals(Box.OmitBox);
        // If it is an OmitBox, check if it is a schema or not.
        if (result) {
          assert isAxParaSchemaOrHorizDefValid(axp);
          ConstDecl cdecl = (ConstDecl)axp.getZSchText().getZDeclList().get(0);
          result = (cdecl.getExpr() instanceof SchExpr);
        }
        // Otherwise, it is an AxBox and not a schema, result = false already.
      }
      // Otherwise, it is already a schema.
    }
    // Otherwise, it is not an AxPara, so not a schema.
    return result;
  }

  public static boolean isDeltaXi(Name name)
  {
    boolean result = (name instanceof ZName);
    if (result)
    {
      result = isDeltaXi(assertZName(name));
    }
    return result;
  }

  public static boolean isDeltaXi(ZName zName)
  {
    return (isDelta(zName) || isXi(zName));
  }
  
  public static boolean isXi(ZName zName)
  {
    return (zName.getWord().startsWith(ZString.XI));
  }

  public static boolean isDelta(ZName zName)
  {
    return (zName.getWord().startsWith(ZString.DELTA));
  }

  /**
   * Cloning terms
   * @param <T>
   * @param term
   * @return
   */
  public static <T extends Term> T cloneTerm(T term)
  {
    assert term != null;
    List<Term> listTerm = new ArrayList<Term>();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  /**
   * Test whether a list contains a reference to an object.
   * @param list the list to search.
   * @param o the reference to search for.
   * @return true if and only if the reference is in the list.
   */
  public static boolean containsObject(List<Term> list, Object o)
  {
    boolean result = false;
    Iterator<Term> iter = list.iterator();
    while (iter.hasNext())
    {
      Term next = iter.next();
      if (next == o)
      {
        result = true;
        break;
      }
    }
    iter = null;
    return result;
  }

  private static <T extends Term> T cloneTerm(T term, List<Term> listTerm)
  {
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object child = children[i];
      if (child instanceof Term &&
          ! containsObject(listTerm, child)) {
        children[i] = cloneTerm((Term) child, listTerm);
      }
    }
    @SuppressWarnings("unchecked")
    T result = (T)term.create(children);
    assert result.equals(term);
    cloneAnns(term, result);
    children = null;
    return result;
  }

  //copy the LocAnn and UndeclaredAnn from term1 to term2
  private static void cloneAnns(Term term1, Term term2)
  {
    if (term1.hasAnn())
    {
      for(Object obj : term1.getAnns())
      {
        if (obj instanceof Term)
        {
          Term ann = (Term)obj;
          Term cann = cloneTerm(ann);
          term2.getAnns().add(cann);
        }
        else
        {
          term2.getAnns().add(obj);
        }
      }
    }
  }

  /**
   * Get the base name of a delta or xi reference.
   */
  public static ZName getSpecialSchemaBaseName(Factory factory, ZName zName)
  {
    assert isDeltaXi(zName) : "name is not a Delta / Xi ref expr - " + zName;
    final int size = (ZString.DELTA).length();
    String baseWord = zName.getWord().substring(size);
    ZStrokeList strokes = factory.getZFactory().createZStrokeList();
    strokes.addAll(zName.getZStrokeList());
    ZName baseName = factory.createZName(baseWord, strokes);
    return baseName;
  }

  public static ZName getSpecialSchemaBaseName(ZName zName)
  {
    return getSpecialSchemaBaseName(FACTORY, zName);
  }

  public static Name buildName(Factory factory, Name name, List<Stroke> strokes)
  {
    Name result = name;
    if (strokes != null && !strokes.isEmpty() && name instanceof ZName)
    {
      ZName zname = ZUtils.assertZName(name);
      result = factory.createZName(zname.getWord(),
        factory.createZStrokeList(zname.getZStrokeList()));
      ((ZName)result).getZStrokeList().addAll(strokes);
    }
    return result;
  }

  public static Name buildName(Name name, List<Stroke> strokes)
  {
    return buildName(FACTORY, name, strokes);
  }

  /**
   * If the given paragraph <code>isSimpleSchema(para)</code>, returns the
   * declared schema name. Otherwise, the method returns null.
   */
  public static Name getSchemaName(Term term)
  {
    Name result = null;
    if (isSimpleSchema(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
    }
    return result;
  } 

  public static Expr getSchemaDefExpr(Term term)  
  {
    Expr result = null;
    if (isSimpleSchema(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getExpr();
    }
    return result;
  }

  public static ZNameList getSchemaZGenFormals(Term term)
  {
    ZNameList result = null;
    if (isSimpleSchema(term)) {
      return getAxParaZGenFormals(term);
    }
    return result;
  }

  public static Name getAxParaSchOrAbbrName(Term term)
  {
    Name result = null;
    if (isAxPara(term))
    {
      AxPara axp = (AxPara)term;
      if (isAxParaSchemaOrHorizDefValid(axp))
      {
        result = getSchemaName(term);
        if (result == null)
        {
          result = getAbbreviationName(term);
        }
      }
    }
    return result;
  }

  public static Name getAbbreviationName(Term term)  
  {
    Name result = null;
    if (isAbbreviation(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
    }
    return result;
  }

  public static Expr getAbbreviationExpr(Term term)  
  {
    Expr result = null;
    if (isAbbreviation(term)) {
      AxPara axp = (AxPara) term;
      assert isAxParaSchemaOrHorizDefValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getExpr();
    }
    return result;
  }

  public static ZNameList getAbbreviationZGenFormals(Term term)
  {
    ZNameList result = null;
    if (isAbbreviation(term)) {
      return getAxParaZGenFormals(term);
    }
    return result;
  }

  /**
   * Returns whether the given expression is an empty set as a reference to
   * <code>ZString.EMPTYSET<code>.
   */
  public static boolean isEmptySetRefExpr(Object a) 
  {      
    boolean result = (a instanceof RefExpr);        
    if (result) 
    {
      RefExpr r = (RefExpr)a;
      // false mixfix, as the result of createGenInst(...)
      result = r.getMixfix() != null && !r.getMixfix();
      if (result) 
      {
        result = r.getZName().getWord().equals(ZString.EMPTYSET);
      }
    }      
    return result;
  }

  
  public static boolean isRefExpr(Term term)
  {
    return term instanceof RefExpr;
  }

  public static boolean isApplExpr(Term term)
  {
    return term instanceof ApplExpr;
  }

  public static boolean isSetExpr(Term term)
  {
    return term instanceof SetExpr;
  }

  public static boolean isTupleExpr(Term term)
  {
    return term instanceof TupleExpr;
  }

  public static boolean isBindSelExpr(Term term)
  {
    return term instanceof BindSelExpr;
  }

  public static boolean isTupleSelExpr(Term term)
  {
    return term instanceof TupleSelExpr;
  }

  public static boolean isLambdaExpr(Term term)
  {
    return term instanceof LambdaExpr;
  }

  public static boolean isMemPred(Term term)
  {
    return term instanceof MemPred;
  }

  public static boolean isAndPred(Term term)
  {
    return term instanceof AndPred;
  }

  /**
   * Returns true if term is a reference expression. That is, a
   * RefExpr with mixfix and explicit false, and the list of
   * instantiating expressions is empty. For example: \arithmos, \num,
   * \emptyset.  For \emptyset, the typechecker transforms it to a
   * generic application and explicit remains false (see 13.2.3.3)
   * (i.e. isReferenceExpr(\emptyset) after typechecking might be
   * false if generic actuals are given, as in \emptyset[\nat]).
   */  
  public static boolean isReferenceExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (!r.getMixfix() && !r.getExplicit() &&
                r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Returns true if term is a generic operator instantiation. That
   * is, a RefExpr with mixfix false and the list of instantiating
   * expressions is non-empty (it contains [T]). The explicit
   * attribute indicates whether the instantiating expressions are
   * explicitly given in the specification (explicit is true) or
   * whether they were inferred by the typechecker (explicit is
   * false). For example: \emptyset[T] or \emptyset.
   */
  public static boolean isGenInstExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (!r.getMixfix() && !r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Another less common example would be (\_ \fun \_)[S, T].
   * In this case,
   * RefExpr(ZName("_->_"), ZExprList(
   *    RefExpr(ZName("S"), MF=F, EX=F),
   *    RefExpr(ZName("T"), MF=F, EX=F)),
   *    MF=F, EX=T)
   */
  public static boolean isExplicitGenInstExpr(Term term)
  {
    return isGenInstExpr(term) && ((RefExpr) term).getExplicit();
  }

  /**
   * Returns true if term is Generic Operator Application. That is, a
   * RefExpr with mixfix and explicit true, and the list of
   * instantiating expressions is non-empty (it contains [S,T]). For
   * example: S \fun T.
   */
  public static boolean isGenOpApplExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isRefExpr(term);
    if (result) {
      RefExpr r = (RefExpr) term;
      result = (r.getMixfix() && r.getExplicit() && 
                !r.getZExprList().isEmpty());
    }
    return result;
  }

  /**
   * Returns true whenever the given RefExpr is valid (i.e. either
   * Reference, Generic Operator application, or Generic
   * Instantiation).  It should never be false for expressions created
   * by the parser.  This is useful for assertion whenever RefExpr are
   * created on-the-fly.
   */
  public static boolean isRefExprValid(RefExpr term)
  {
    return
      isReferenceExpr(term) || isGenInstExpr(term) || isGenOpApplExpr(term);
  }

  /**
   * Returns the list of instantiating expressions in Generic Operator
   * Application RefExpr or null if it isn't one. That is, it returns
   * [S,T] from "S \fun T".  Not that it will return null if term is
   * "(\_ \fun \_)[S, T]"
   */
  public static ZExprList getGenOpApplZGenActuals(Term term)
  {
    ZExprList result = null;
    if (isGenOpApplExpr(term)) {
      result = ((RefExpr) term).getZExprList();
    }
    return result;
  }

  /** 
   * Returns true if term is an function operator application
   * expression.  That is, a ApplExpr term with mixfix TRUE,
   * and the first (left) expression as the name (e.g. " _ + _ ")
   * (a RefExpr) with mixfix FALSE, and the second (right)
   * expression as the parameters (e.g., TupleExpr (S,T)).
   * For example: "(S + T)".  There is no case of ApplExpr where
   * RefExpr mixfix is true. For instance, both "A (\_ \fun\_)[S, T] B"
   * and "(\_ \fun\_)[S, T] (A, B)" parse with ApplExpr true/false but 
   * RefExpr mixfix false in both cases.
   */  
  public static boolean isFcnOpApplExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isApplExpr(term);
    if (result) {
      ApplExpr appl = (ApplExpr) term;
      result = (appl.getMixfix() && 
                isRefExpr(appl.getLeftExpr()) &&
                ! ((RefExpr) appl.getLeftExpr()).getMixfix());
    }
    return result;
  }

  /** 
   * Returns true if term is an application expression. That is, a
   * ApplExpr term with mixfix FALSE, the first (left)
   * expression is the function name (e.g., \dom), (a RefExpr with
   * mixfix FALSE) and the second (right) expression is the
   * argument. For example: \dom~R or \id~R.  Note that this also
   * covers the case where function operator application is given
   * explicitly, as in "(_+_)(S,T)". Finally, the LEFT expr could
   * also be part of a nested ApplExpr itself (e.g., (f~x)~y).
   */ 
  public static boolean isApplicationExpr(Term term)
  {
    // NOTE: doesn't work for jokers
    boolean result = isApplExpr(term);
    if (result) {
      ApplExpr appl = (ApplExpr) term;
      Expr lhs = appl.getLeftExpr();
      result = (!appl.getMixfix() &&
                // explicit ApplExpr
                ((isRefExpr(lhs) &&
                  !((RefExpr) lhs).getMixfix())
                    ||
                 (isBindSelExpr(lhs))
                    ||
                 (isTupleSelExpr(lhs))
                    ||
                 (isLambdaExpr(lhs))
                    ||
                 (isSetExpr(lhs))
                //  ||
                // nested application expression
                //  (isApplicationExprValid(appl))
                )
               );
    }
    return result;
  }

  /**
   * Nested application expressions (e.g., (f~x)~y) are ApplExpr with
   * mixfix FALSE and left expr as an ApplExpr.
   * @param term
   * @return
   */
  public static boolean isNestedApplExpr(Term term)
  {
    // NOTE: doesn't work for jokers (?)
    boolean result = isApplExpr(term);
    if (result) {
      ApplExpr appl = (ApplExpr) term;
      result = (!appl.getMixfix() &&
                isApplExpr(appl.getLeftExpr()) &&
                isApplicationExprValid((ApplExpr)appl.getLeftExpr()));
    }
    return result;
  }

  /**
   * Returns true whenever the given ApplExpr is valid (i.e. either
   * function operator application ---implicitly or explicitly---, or
   * application).  It should never be false for expressions created
   * by the parser.  This is useful for assertion whenever ApplExpr
   * are created on-the-fly.
   */
  public static boolean isApplicationExprValid(ApplExpr term)
  {
    return isFcnOpApplExpr(term) || isApplicationExpr(term) || isNestedApplExpr(term);
  }

  /**
   * Returns the ApplExpr reference expression for the given term if it is
   * a valid ApplExpr (i.e. isApplicationExprValid), or null otherwise. The
   * reference is the first (left) expression of the ApplExpr as either a
   * RefExpr or a nested ApplExpr. 
   */
  public static Expr getApplExprRef(Term term)
  {
    Expr result = null;
    if (isApplExpr(term) && isApplicationExprValid((ApplExpr) term)) 
    {
      ApplExpr appl = (ApplExpr)term;
      result = appl.getLeftExpr();
      // either it's is a RefExpr or a nested ApplExpr or a tuple/binder selector or a lambda expr. If neither, then error!
      // ! (!isRefExpr(result) && !isBindSelExpr(result) && !isTupleSelExpr(result) && !isLambdaExpr(result) => isApplExpr(result) && isNestedApplExpr(term))
      if (!(isRefExpr(result) || isBindSelExpr(result) || isTupleSelExpr(result) || 
            isLambdaExpr(result) || isSetExpr(result) || (isApplExpr(result) && isNestedApplExpr(term))))
        throw new UnsupportedAstClassException("Invalid ApplExpr " + term);
    }
    return result;
  }

  /**
   * Returns the ApplExpr arguments for the given term if it is a
   * valid ApplExpr (i.e. isApplicationExprValid), or null
   * otherwise. The arguments are the second (right) expression of the
   * ApplExpr as a ZExprList.  If there are more than one argument
   * (i.e. ApplExpr with TupleExpr as right expr) the list is greater
   * then one.
   */
  public static ZExprList getApplExprArguments(Term term)
  {
    ZExprList result = null;
    if (isApplExpr(term) && isApplicationExprValid((ApplExpr) term)) {
      result = FACTORY.createZExprList();
      Expr arg = ((ApplExpr) term).getRightExpr();
      if (isTupleExpr(arg)) {
        result.addAll(((TupleExpr) arg).getZExprList());
      }
      else {
        result.add(arg);
      }
    }
    return result;
  }

  public static int applExprArity(ApplExpr term)
  {
    ZExprList result = getApplExprArguments(term);
    assert result != null : "Invalid ApplExpr term " + term + 
      ". ApplExpr must always have at least one parameter.";      
    return result.size();
  }

  /**
   * Returns true if term is MemPred with Mixfix=true and the second
   * (right) expression is a singleton set containing the right-hand
   * side of the equality.  For example: "n = m" has left="n" and
   * right="{m}".
   */
  public static boolean isEqualityPred(Term term)
  {
    boolean result = isMemPred(term);
    if (result) {
      MemPred mp = (MemPred) term;
      result = (mp.getMixfix() && isSetExpr(mp.getRightExpr()) &&
                ((SetExpr) mp.getRightExpr()).getZExprList().size() == 1);
    }
    return result;
  }

  /**
   * Returns true if term is MemPred with Mixfix=true, and the second
   * (right) expression is the operator name.  For example, "n < m"
   * has left="(n,m)" and right=" _ < _ ", "disjoint s" has left="s"
   * and right="disjoint _ ", and if foo was declared as a unary
   * postfix operator, then "(2,3) foo" would have left= "(2,3)" and
   * right=" _ foo".
   */
  public static boolean isRelOpApplPred(Term term)
  {
    return (isMemPred(term) && ((MemPred) term).getMixfix() && 
            isRefExpr(((MemPred) term).getRightExpr()));
  }

  /**
   * Returns true if term is MemPred with Mixfix=false, where the
   * first (left) expression is the element, and the second (right)
   * expression is the set.  For example, "n \in S" has left="n" and
   * right="S". Note that this accounts for explicit relational
   * operator application, as in (0, 1) \in (\_ < \_)
   */
  public static boolean isMembershipPred(Term term)
  {
    return isMemPred(term) && ! ((MemPred) term).getMixfix();      
  }

  /**
   * Returns true whenever the given MemPred is valid (i.e. either
   * equality, set membership, or relational operator application).
   * It should never be false for expressions created by the parser.
   * This is useful for assertion whenever MemPred are created
   * on-the-fly.
   */  
  public static boolean isMemPredValid(MemPred term)
  {
    return
      isEqualityPred(term) || isMembershipPred(term) || isRelOpApplPred(term);
  }

  /**
   * Returns the LHS of a MemPred, which is just the same as
   * term.getLeftExpr()
   */
  public static Expr getMemPredLHS(MemPred term)
  {
    return term.getLeftExpr();      
  }

  /** 
   *  Returns the RHS of a MemPred, which is just the same as
   *  term.getReftExpr(), unless term is an equality, in which case it
   *  returns the singleton set element of the RHS expression.  * For
   *  example: "n = m" has left="n" and right="{m}", yet
   *  getMemPredRHS="m"!
   */
  public static Expr getMemPredRHS(MemPred term)
  {
    Expr result = term.getRightExpr();
    if (isEqualityPred(term)) {
      result = ((SetExpr) result).getZExprList().get(0);
    }
    return result;
  }
  
  
  /**
   * Returns the relational operator name for the given term if 
   * it is a relational operator MemPred (i.e. isRelOpApplPred), 
   * or null otherwise. The name is the second (right) expression 
   * of the MemPred term returned as a RefExpr.
   */
  public static RefExpr getRelOpName(Term term) 
  {
    RefExpr result = null;
    if (isRelOpApplPred(term))
    {
      result = (RefExpr)getMemPredRHS((MemPred)term);            
    }
    return result;
  }

  /**
   * Returns the relational operator application arguments, or null if
   * term is not a MemPred relational operator application
   * (i.e. !isRelOpApplPred).  For relational operator application the
   * first (left) expression is usually a tuple containing the
   * corresponding number of arguments.  However, for a unary
   * operator, the left expression does not have to be a tuple.  For
   * example, "n &lt; m" has left="(n,m)", right=" _ &lt; _ ", and arity 2;
   * "disjoint s" has left="s", right="disjoint _ ", and arity 1; and
   * if foo was declared as a unary postfix operator, then "(2,3) foo"
   * would have left= "(2,3)", right=" _ foo", and arity 2.  As no
   * application has empty parameters (i.e. it would be a RefExpr),
   * the result should never be empty (?)
   */
  public static ZExprList getRelOpApplPredLHSArguments(Term term)
  {
    ZExprList result = null;
    if (isRelOpApplPred(term)) {
      result = FACTORY.createZExprList();
      Expr lhs = getMemPredLHS(((MemPred) term));
      if (isTupleExpr(lhs)) {
        result.addAll(((TupleExpr) lhs).getZExprList());
      }
      else {
        result.add(lhs);
      }
      assert ! result.isEmpty() :
        "Relational operator application must have at least one LHS argument";
    }
    return result;
  }

  /**
   * Returns the relational operator application aritity (i.e. its
   * number of parameters), or -1 if term is not a MemPred relational
   * operator application (i.e. !isRelOpApplPred).  For relational
   * operator application the first (left) expression is usually a
   * tuple containing the corresponding number of arguments.  However,
   * for a unary operator, the left expression does not have to be a
   * tuple.  For example, "n &lt; m" has left="(n,m)", right=" _ &lt; _ ",
   * and arity 2; "disjoint s" has left="s", right="disjoint _ ", and
   * arity 1; and if foo was declared as a unary postfix operator,
   * then "(2,3) foo" would have left= "(2,3)", right=" _ foo", and
   * arity 2.  As no application has empty parameters (i.e. it would
   * be a RefExpr), arity should never be 0 ?
   */
  public static int getRelOpApplPredArity(Term term)
  {
      /*
      int result = -1;
      if (isRelOpApplPred(term)) {
          result = 1;
          Expr lhs = getMemPredLHS(((MemPred) term));
          if (isTupleExpr(lhs)) {
              result = ((TupleExpr) lhs).getZExprList().size();
          }
      }
      assert result != 0 : "Relational operator application arity can never be 0";
      return result;       
      */
    ZExprList args = getRelOpApplPredLHSArguments(term);      
    int result = args == null ? -1 : args.size();
    assert result != 0 :
      "Relational operator application arity can never be 0";
    return result;
  }

  /** Returns true if given term is an AndPred with And.Chain */
  public static boolean isChainedConjunction(Term term)
  {
    return isAndPred(term) && ((AndPred) term).getAnd().equals(And.Chain);
  }
  
   /*
   * The ASCII strings produced are designed to be human-readable,
   * so are not necessarily in LaTeX markup.
   */
  public static void unicodeToAscii(String name, StringBuffer result)
  {
    for(int i = 0; i < name.length(); i++) {
      if (Character.isLetterOrDigit(name.codePointAt(i)) ||
          Character.isSpaceChar(name.codePointAt(i)) ||
          name.charAt(i) == '_' || name.charAt(i) == '$') {
        result.append(name.charAt(i));
      }
      else {
        result.append("U+" +
                      Integer.toHexString(name.codePointAt(i)).toUpperCase());
      }
    }
  }
    
  private static PrintVisitor zPrintVisitor_ = new PrintVisitor();
  
  public static String toStringZName(ZName name)
  {
    assert !zPrintVisitor_.getPrintIds() : "by default do not print ids at ZUtils";
    // default is (getPrintUnicode() && !zPrintVisitor_.getPrintIds())
    return zPrintVisitor_.visit(name);
  }
  
  public static String toStringZName(ZName name, boolean printUnicode, boolean printIds)
  {     
    /*
    try 
    {
      assertZPrintVisitor(assertZTermImpl(name).getFactory().getToStringVisitor()).setPrintIds(printIds);      
      assertZPrintVisitor(assertZTermImpl(name).getFactory().getToStringVisitor()).setPrintUnicode(printUnicode);                       
    } catch (UnsupportedAstClassException e)
    {      
      
    } 
    // change flags back  
     */
    
    boolean b1 = zPrintVisitor_.setPrintIds(printIds);
    boolean b2 = zPrintVisitor_.setPrintUnicode(printUnicode);
    String result = zPrintVisitor_.visit(name);
    zPrintVisitor_.setPrintIds(b1);
    zPrintVisitor_.setPrintUnicode(b2);    
    
    return result;
  }

  /**
   * <p>;
   * Changes the toString() method of ZFactory (within the given Factory),
   * so that is uses the toString() strategy for the given visitor, usually
   * one kind of PrintVisitor.
   * </p>
   * <p>
   * They are important in order to debug/inspect easily the rather complex
   * scoping mechanisms for basic (locally declared) processes.
   * </p>
   * @param f factory
   * @param toStringVisitor new visitor
   */
  protected static void setZFactoryToStringVisitor(Factory f, Visitor<String> toStringVisitor)
  {
    assertZFactoryImpl(f.getZFactory()).setToStringVisitor(toStringVisitor);
  }

  public static ZBranchList assertZBranchList(Term term)
  {
    if (term instanceof ZBranchList) {
      return (ZBranchList) term;
    }
    final String message =
      "Expected a ZBranchList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZName assertZName(Term term)
  {
    if (term instanceof ZName) {
      return (ZName) term;
    }
    final String message =
      "Expected a ZName but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNumeral assertZNumeral(Term term)
  {
    if (term instanceof ZNumeral) {
      return (ZNumeral) term;
    }
    final String message =
      "Expected a ZNumeral but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZParaList assertZParaList(Term term)
  {
    if (term instanceof ZParaList) {
      return (ZParaList) term;
    }
    final String message =
      "Expected a ZParaList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZExprList assertZExprList(Term term)
  {
    if (term instanceof ZExprList) {
      return (ZExprList) term;
    }
    final String message =
      "Expected a ZExprList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNameList assertZNameList(Term term)
  {
    if (term instanceof ZNameList) {
      return (ZNameList) term;
    }
    final String message =
      "Expected a ZNameList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZDeclList assertZDeclList(Term term)
  {
    if (term instanceof ZDeclList) {
      return (ZDeclList) term;
    }
    final String message =
      "Expected a ZDeclList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZFreetypeList assertZFreetypeList(Term term)
  {
    if (term instanceof ZFreetypeList) {
      return (ZFreetypeList) term;
    }
    final String message =
      "Expected a ZFreetypeList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZSchText assertZSchText(Term term)
  {
    if (term instanceof ZSchText) {
      return (ZSchText) term;
    }
    final String message =
      "Expected a ZSchText but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static ZStrokeList assertZStrokeList(Term term)
  {
    if (term instanceof ZStrokeList) {
      return (ZStrokeList) term;
    }
    final String message =
      "Expected a ZStrokeList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  // useful to get access to the getPrintVisitor() method
  public static ZFactoryImpl assertZFactoryImpl(Object factory) {
    if (factory instanceof ZFactoryImpl) {
      return (ZFactoryImpl) factory;
    }
    final String message = "Expected a ZFactoryImpl but found " + 
      String.valueOf(factory);
    throw new UnsupportedAstClassException(message);    
  }
  
  // useful to get access to the z.PrintVisitor class, hence set/getPrintIds()
  public static PrintVisitor assertZPrintVisitor(Object visitor) {
    if (visitor instanceof PrintVisitor) {
      return (PrintVisitor) visitor;
    }
    final String message = "Expected " + PrintVisitor.class.toString() + 
      " but found " + String.valueOf(visitor);
    throw new UnsupportedAstClassException(message);    
  }
  
  public static TermImpl assertZTermImpl(Object term) {
    if (term instanceof TermImpl) {
      return (TermImpl) term;
    }
    final String message = "Expected the default (Z) implementation of Term" +
      " but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);    
  }  
  
  public static ZSect retrieveZSect(Spec term, String sectName)
  {
    assert term != null;
    for(Sect sect : term.getSect())
    {      
      if (sect instanceof ZSect && ((ZSect)sect).getName() != null &&
          ((ZSect)sect).getName().equals(sectName))
      {
        return (ZSect)sect;
      }
    }
    return null;
  }
  
  /**
   * Transforms a list of strokes into a (unicode) string.
   */
  public static String strokeListToString(List<Stroke> strokes)
  {
    if (strokes == null) return "";
    StringBuffer result = new StringBuffer();
    for (Iterator<Stroke> iter = strokes.iterator(); iter.hasNext();)
    {
      Stroke stroke = iter.next();
      result.append(stroke.toString());
    }
    return result.toString();
  }
  
  /**
   * Test whether the base name and strokes of two ZNames are equal.
   * This ignores name ids. 
   */
  public static boolean namesEqual(ZName zName1, ZName zName2)
  {
    boolean result = zName1 != null && zName2 != null;
    if (result)
    {
      result = zName1.getWord().equals(zName2.getWord()) &&
        zName1.getStrokeList().equals(zName2.getStrokeList());
    }
    else
    {
      result = zName1 == null && zName2 == null;
    }
    return result;
  }
  
  /**
   * Test whether the base name and strokes of two Names are equal.
   * This ignores name ids
   */
  public static boolean namesEqual(Name name1, Name name2)
  {
    boolean result = false;
    if (name1 instanceof ZName && name2 instanceof ZName)
    {
      result = namesEqual((ZName) name1, (ZName) name2);
    }
    return result;
  }
  
  /**
   * Test whether a list contains a ZName.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsZName(List<ZName> list,
    ZName zName)
  {
    boolean result = false;
    for (ZName next : list)
    {
      if (namesEqual(next, zName))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  /**
   * Test whether a list contains a ZName with the same ID.
   * @param list the list to search.
   * @param zName the ZName to search for.
   * @return true if and only if the name is in the list.
   */
  public static boolean containsID(List<ZName> list,
    ZName zName)
  {
    boolean result = false;
    for (ZName next : list)
    {
      if (next.getId().equals(zName.getId()))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  public static boolean idsEqual(String id1, String id2)
  {
    boolean result = id1 != null && id2 != null && id1.equals(id2);
    return result;
  }
  
  /**
   * Sorts the name type pairs within the given signature. Sorting occurs
   * with respect to the compareTo protocol described in this class.
   */
  public static Signature sort(Signature signature)
  {
    sort(signature.getNameTypePair());
    return signature;
  }
  
  /**
   * Sorts the list of name type pairs given. Sorting occurs
   * with respect to the compareTo protocol described in this class.
   */
  public static List<NameTypePair> sort(List<NameTypePair> pairs)
  {
    for (int j = 1; j < pairs.size(); j++)
    {
      NameTypePair pair = pairs.get(j);
      int i = j - 1;
      while (i >= 0 && compareTo(pairs.get(i).getZName(),
        pair.getZName()) > 0)
      {
        pairs.set(i + 1, pairs.get(i));
        i--;
      }
      pairs.set(i + 1, pair);
    }
    return pairs;
  }
  
  public static List<ZName> sortNames(List<ZName> names)
  {
    for (int j = 1; j < names.size(); j++)
    {
      ZName zName = names.get(j);
      int i = j - 1;
      while (i >= 0 && compareTo(names.get(i), zName) > 0)
      {
        names.set(i + 1, names.get(i));
        i--;
      }
      names.set(i + 1, zName);
    }
    return names;
  }
  
  /**
   * Inserts all elements from pairsB in pairsA, provided pairsA are sorted.
   */
  public static void insert(List<NameTypePair> pairsA,
    List<NameTypePair> pairsB)
  {
    for (NameTypePair pair : pairsB)
    {
      insert(pairsA, pair);
    }
  }
  
  /**
   * Inserts all elements from namesB in namesA, provided namesA are sorted.
   */
  public static void insertNames(List<ZName> namesA,
    List<ZName> namesB)
  {
    for (ZName name : namesB)
    {
      insertNames(namesA, name);
    }
  }
  
  //precondition: pairs is sorted
  public static void insert(List<NameTypePair> pairs, NameTypePair pair)
  {
    int i = 0;
    while (i < pairs.size() &&
      compareTo(pairs.get(i).getZName(), pair.getZName()) < 0)
    {
      i++;
    }
    pairs.add(i, pair);
  }
  
  //precondition: names is sorted
  public static void insertNames(List<ZName> names, ZName name)
  {
    int i = 0;
    while (i < names.size() && compareTo(names.get(i), name) < 0)
    {
      i++;
    }
    names.add(i, name);
  }
  
  private static class ZNameComparator implements Comparator<ZName>, Serializable
  {    
    /**
	 * 
	 */
	private static final long serialVersionUID = 7870560078174949531L;

	ZNameComparator() { }    

    @Override
    public int compare(ZName n1, ZName n2) 
    {
      int result = compareTo(n1, n2);
      return result;
    }
    
    @Override
    public boolean equals(Object o) 
    {
      return o != null && o instanceof ZNameComparator;        
    }

    @Override
    public int hashCode()
    {
      int hash = 7;
      return hash;
    }
  }

  private static class ZNameIgnoreStrokesComparator implements Comparator<ZName>, Serializable
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 4365878619491704087L;

	ZNameIgnoreStrokesComparator() { }

    @Override
    public int compare(ZName n1, ZName n2)
    {
      int result = compareToIgnoreStrokes(n1, n2);
      return result;
    }

    @Override
    public boolean equals(Object o)
    {
      return o != null && o instanceof ZNameIgnoreStrokesComparator;
    }

    @Override
    public int hashCode()
    {
      int hash = 5;
      return hash;
    }
  }

  public final static Comparator<ZName> ZNAME_COMPARATOR = new ZNameComparator();
  public final static Comparator<ZName> ZNAME_IGNORE_STROKES_COMPARATOR = new ZNameIgnoreStrokesComparator();
  
  public static int compareTo(ZName zName1, ZName zName2)
  {
    String word1 = zName1.getWord();
    String word2 = zName2.getWord();
    int compareWord = word1.compareTo(word2);
    if (compareWord != 0)
    {
      return compareWord;
    }
    else
    {
      ZStrokeList strokes1 = zName1.getZStrokeList();
      ZStrokeList strokes2 = zName2.getZStrokeList();
      int lengthDiff = strokes1.size() - strokes2.size();
      if (lengthDiff != 0)
      {
        return lengthDiff;
      }
      else
      {
        //sort as ? < ! < ' < num
        for (int i = 0; i < strokes1.size(); i++)
        {
          int stroke1Val = getStrokeValue(strokes1.get(i));
          int stroke2Val = getStrokeValue(strokes2.get(i));
          int compareStroke = stroke1Val - stroke2Val;
          if (compareStroke != 0)
          {
            return compareStroke;
          }
        }
        return 0;
      }
    }
  }

  public static int compareToIgnoreStrokes(ZName zName1, ZName zName2)
  {
    String word1 = zName1.getWord();
    String word2 = zName2.getWord();
    return word1.compareTo(word2);
  }

  public static int getStrokeValue(Stroke stroke)
  {
    int result = -1;
    if (stroke instanceof InStroke)
    {
      result = 0;
    }
    else if (stroke instanceof OutStroke)
    {
      result = 1;
    }
    else if (stroke instanceof NextStroke)
    {
      result = 2;
    }
    else if (stroke instanceof NumStroke)
    {
      result = 3;
    }
    else
    {
      assert false : "Stroke instanceof " + stroke.getClass().getName();
    }
    return result;
  }

  public static final StandardZ STDZ_NAMELIST_CHECKER = new StandardZ();
}
