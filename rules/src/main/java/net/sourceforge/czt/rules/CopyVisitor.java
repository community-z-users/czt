/*
  Copyright (C) 2005, 2006 Petra Malik
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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;
import net.sourceforge.czt.parser.util.DefinitionTable;

/**
 * A visitor that copies a term using the given factory.  The main purpose
 * of this visitor is to create new Jokers that can be used by the prover
 * (the prover assumes that there is only one instance for each joker name).
 *
 * In addition, this visitor rewrites variable declarations with
 * multiple names into variable declarations with just one name,
 * (i.e. a,b:E gets rewritten to a:E;b:E) and expands a true predicate
 * to any schema text that is missing the predicate part.
 *
 * @czt.todo Doesn't copy annotations.
 *
 * @author Petra Malik
 */
public class CopyVisitor
  implements TermVisitor<Term>,
             VarDeclVisitor<Term>,
             ZDeclListVisitor<Term>,
             ZSchTextVisitor<Term>,
             JokerDeclListVisitor<Term>,
             JokerExprVisitor<Term>,
             JokerNameVisitor<Term>,
             JokerPredVisitor<Term>,
             LookupConstDeclProvisoVisitor<Term>,
             CalculateProvisoVisitor<Term>,
             TypeProvisoVisitor<Term>,
             ZNameVisitor<Term>,
             DefinitionTable.DefinitionVisitor<DefinitionTable.Definition>
{
  private Factory factory_;
  
  /**
   *  Sometimes when we copy definitions/terms, we have to
   *  generalize type parameters by converting them into jokers.
   *  This maps each type parameters onto its new joker name.
   *  When this is null, no names are transformed.
   */
  private Map<ZName, Name> typeParamMap_;
  
  public CopyVisitor(Factory factory)
  {
    factory_ = factory;
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, false);
  }

  public Term visitVarDecl(VarDecl varDecl)
  {
    NameList declNameList = (NameList)
      varDecl.getNameList().accept(this);
    Expr expr = (Expr) varDecl.getExpr().accept(this);
    if (declNameList instanceof ZNameList) {
      ZNameList zdnl = (ZNameList) declNameList;
      if (zdnl.size() > 1) {
        // here we expand a,b,c,...:T into a:T; b:T; c:T; ...
        ZDeclList zDeclList = factory_.createZDeclList();
        for (Name declName : zdnl) {
          ZNameList list = factory_.createZNameList();
          list.add(declName);
          zDeclList.add(factory_.createVarDecl(list, expr));
        }
        return zDeclList;
      }
    }
    return factory_.createVarDecl(declNameList, expr);
  }

  public Term visitZDeclList(ZDeclList zDeclList)
  {
    ZDeclList result = factory_.createZDeclList();
    for (Decl decl : zDeclList) {
      Term term = decl.accept(this);
      if (term instanceof ZDeclList) {
        result.addAll((ZDeclList) term);
      }
      else {
        result.add((Decl) term);
      }
    }
    return result;
  }

  public Term visitZSchText(ZSchText zSchText)
  {
    ZSchText result = factory_.createZSchText();
    result.setDeclList((DeclList) zSchText.getDeclList().accept(this));
    Pred pred = zSchText.getPred();
    if (pred != null) pred = (Pred) pred.accept(this);
    if (pred == null) pred = factory_.createTruePred();
    result.setPred(pred);
    return result;
  }

  public Term visitJokerDeclList(JokerDeclList joker)
  {
    return factory_.createJokerDeclList(joker.getName());
  }

  public Term visitJokerExpr(JokerExpr joker)
  {
    return factory_.createJokerExpr(joker.getName());
  }

  public Term visitJokerName(JokerName joker)
  {
    return factory_.createJokerName(joker.getName());
  }

  public Term visitJokerPred(JokerPred joker)
  {
    return factory_.createJokerPred(joker.getName());
  }

  public Term visitLookupConstDeclProviso(LookupConstDeclProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createLookupConstDeclProviso(context, left, right);
  }

  public Term visitCalculateProviso(CalculateProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createCalculateProviso(context, left, right);
  }

  public Term visitTypeProviso(TypeProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getExpr().accept(this);
    Expr right = (Expr) proviso.getType().accept(this);
    return factory_.createTypeProviso(context, left, right);
  }
  
  /** Transforms formal type parameters into expression jokers. */
  public DefinitionTable.Definition visitDefinition(DefinitionTable.Definition def)
  {
    ZNameList typeformals = def.getDeclNames();
    ZNameList typeactuals = factory_.createZNameList();
    typeParamMap_ = new HashMap<ZName, Name>();
    for (Name n : typeformals) {
      ZName zname = (ZName) n;
      Name joker = factory_.createJokerName( ((ZName) n).getWord());
      typeactuals.add(joker);
      typeParamMap_.put(zname, joker);
    }
    // this will use typeParamMap_ to transform typeformals into jokers.
    Expr expr2 = (Expr) def.getExpr().accept(this);
    typeParamMap_ = null;  // disable the type-to-joker transformation
    return new DefinitionTable.Definition(typeactuals, expr2);
  }

  public Term visitZName(ZName name)
  {
    if (typeParamMap_ != null && typeParamMap_.containsKey(name)) {
      Term joker = typeParamMap_.get(name);
      System.out.println("copy visitor transforms type "+name+" to joker "+joker);
      return joker; 
    }
    else
      return name;
  }
}
