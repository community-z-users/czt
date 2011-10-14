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

package net.sourceforge.czt.z.util.collector;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class ExprCollector extends BaseCollector<Expr>
        implements QntExprVisitor<Expr>, SchExprVisitor<Expr>, ExprVisitor<Expr> {

  protected final Map<ZName, Expr> fFreeVars;
  protected final Map<ZName, Expr> fBoundedVars;
  protected final Map<ZName, List<Expr>> fFcns;
  protected PredCollector fPredCollector;
  protected ZSchTextCollector<Expr> fZSchTextCollector;

  ExprCollector()
  {
    fFreeVars = new TreeMap<ZName, Expr>(ZUtils.ZNAME_COMPARATOR);
    fBoundedVars = new TreeMap<ZName, Expr>(ZUtils.ZNAME_COMPARATOR);
    fFcns = new TreeMap<ZName, List<Expr>>(ZUtils.ZNAME_COMPARATOR);
    fPredCollector = new PredCollector();
    fZSchTextCollector = new ZSchTextCollector<Expr>(this, fPredCollector);
  }

  @Override
  public Expr visitQntExpr(QntExpr term)
  {
    term.getZSchText().accept(fZSchTextCollector);
    return null;
  }

  @Override
  public Expr visitSchExpr(SchExpr term)
  {
    term.getZSchText().accept(fZSchTextCollector);
    return null;
  }

  @Override
  public Expr visitExpr(Expr term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

}

//  <xs:element name="Expr" type="Z:Expr"

//  <xs:element name="QntExpr" type="Z:QntExpr" substitutionGroup="Z:Expr"
//  <xs:element name="Qnt1Expr" type="Z:Qnt1Expr" substitutionGroup="Z:QntExpr"
//  <xs:element name="MuExpr" type="Z:QntExpr" substitutionGroup="Z:QntExpr">
//  <xs:element name="SetCompExpr" type="Z:QntExpr" substitutionGroup="Z:QntExpr"
//  <xs:element name="ExistsExpr" type="Z:Qnt1Expr"  substitutionGroup="Z:Qnt1Expr"
//  <xs:element name="Exists1Expr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr"
//  <xs:element name="ForallExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr"
//  <xs:element name="LambdaExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr"
//  <xs:element name="LetExpr" type="Z:Qnt1Expr" substitutionGroup="Z:Qnt1Expr">


//  <xs:element name="BindExpr" type="Z:BindExpr" substitutionGroup="Z:Expr">
//  <xs:element name="CondExpr" type="Z:CondExpr" substitutionGroup="Z:Expr">
//  <xs:element name="NumExpr" type="Z:NumExpr" substitutionGroup="Z:Expr">
//  <xs:element name="RefExpr" type="Z:RefExpr" substitutionGroup="Z:Expr">

//  <xs:element name="Expr1" type="Z:Expr1" substitutionGroup="Z:Expr"
//  <xs:element name="PowerExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
//  <xs:element name="TupleSelExpr" type="Z:TupleSelExpr" substitutionGroup="Z:Expr1">

//  <xs:element name="Expr2" type="Z:Expr2" substitutionGroup="Z:Expr"
//  <xs:element name="ApplExpr" type="Z:ApplExpr" substitutionGroup="Z:Expr2">

//  <xs:element name="Expr0N" type="Z:Expr0N" substitutionGroup="Z:Expr"
//  <xs:element name="Expr2N" type="Z:Expr2N" substitutionGroup="Z:Expr0N"
//  <xs:element name="SetExpr" type="Z:Expr0N" substitutionGroup="Z:Expr0N">
//  <xs:element name="ProdExpr" type="Z:Expr2N" substitutionGroup="Z:Expr2N">
//  <xs:element name="TupleExpr" type="Z:Expr2N" substitutionGroup="Z:Expr2N">

//  <xs:element name="SchExpr" type="Z:SchExpr" substitutionGroup="Z:Expr">
//  <xs:element name="SchExpr2" type="Z:SchExpr2" substitutionGroup="Z:Expr2"
//  <xs:element name="DecorExpr" type="Z:DecorExpr" substitutionGroup="Z:Expr1">
//  <xs:element name="HideExpr" type="Z:HideExpr" substitutionGroup="Z:Expr1">
//  <xs:element name="NegExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
//  <xs:element name="PreExpr" type="Z:Expr1" substitutionGroup="Z:Expr1">
//  <xs:element name="BindSelExpr" type="Z:BindSelExpr" substitutionGroup="Z:Expr1">
//  <xs:element name="RenameExpr" type="Z:RenameExpr" substitutionGroup="Z:Expr1">
//  <xs:element name="ThetaExpr" type="Z:ThetaExpr" substitutionGroup="Z:Expr1">
//  <xs:element name="CompExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
//  <xs:element name="PipeExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
//  <xs:element name="ProjExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
//  <xs:element name="AndExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
//  <xs:element name="OrExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">
//  <xs:element name="ImpliesExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2"
//  <xs:element name="IffExpr" type="Z:SchExpr2" substitutionGroup="Z:SchExpr2">


