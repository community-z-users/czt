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

package net.sourceforge.czt.vcg.z.transformer.feasibility;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.vcg.z.transformer.ZPredTransformer;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;

/**
 *
 * @author Leo Freitas
 * @date Aug 25, 2011
 */
public class ZPredTransformerFSB extends ZPredTransformer
{
  public ZPredTransformerFSB(Factory factory, Visitor<Pred> termV)
  {
    super(factory, termV);
  }

  public Expr trueExpr()
  {
    return getFactory().createSchExpr(getFactory().createZSchText(getFactory().createZDeclList(), truePred()));
  }

  public Expr falseExpr()
  {
    return getFactory().createSchExpr(getFactory().createZSchText(getFactory().createZDeclList(), falsePred()));
  }

  public ZSchText transformSchText(ZSchText zSchText)
  {
    assert zSchText != null : "Invalid sch text request!";
    ZSchText result = zSchText;
    if (isApplyingTransformer())
    {
      result.setPred(checkNeg(zSchText.getPred() != null ? zSchText.getPred() : truePred()));//If null, just sets null.
    }
    assert result.getPred() != null;
    return result;
  }

  public ZSchText createSchemaInclusion(Expr schRef)
  {
    assert schRef != null : "invalid schema reference for sch text inclusion";
    return factory_.createZSchText(
            factory_.createZDeclList(
              factory_.list(factory_.createInclDecl(schRef))), truePred());
  }

  public Expr forAllExpr(ZSchText zSchText, Expr expr)
  {
    assert zSchText != null && expr != null : "Invalid ForAllExpr request!";
    Expr result = null;
    if (isApplyingTransformer())
    {
      zSchText = transformSchText(zSchText);
      // (\forall D | P @ [|true]) = (\forall D | false @ Q) = true
      if ((expr instanceof SchExpr &&
          ((SchExpr)expr).getZSchText().getPred() instanceof TruePred &&
          ((SchExpr)expr).getZSchText().getZDeclList().isEmpty()) 
          ||
         zSchText.getPred() instanceof FalsePred)
      {
        result = trueExpr();
      }
    }
    if (result == null)
    {
      assert /*expr != null &&*/ zSchText.getPred() != null;
      result = getFactory().createForallExpr(zSchText, expr);
      //checkNeg(getFactory().createExprPred(getFactory().createForallExpr(zSchText, expr)));
    }
    assert result != null;
    return result;
  }

  public Expr existsExpr(ZSchText zSchText, Expr expr)
  {
    assert zSchText != null && expr != null : "Invalid ExistsExpr request!";
    Expr result = null;
    if (isApplyingTransformer())
    {
      zSchText = transformSchText(zSchText);
      // (\exists D | P @ [|false]) = (\exists D | false @ Q) = false
      if ((expr instanceof SchExpr &&
          ((SchExpr)expr).getZSchText().getPred() instanceof FalsePred &&
          ((SchExpr)expr).getZSchText().getZDeclList().isEmpty())
          ||
          zSchText.getPred() instanceof FalsePred)
      {
        result = falseExpr();
      }
    }
    if (result == null)
    {
      assert /*expr != null &&*/ zSchText.getPred() != null;
      result = getFactory().createExistsExpr(zSchText, expr);
      //checkNeg(getFactory().createExprPred(getFactory().createExistsExpr(zSchText, expr)));
    }
    assert result != null;
    return result;
  }

  public Pred asPred(Expr schExpr)
  {
    return factory_.createExprPred(schExpr);
  }

  public Pred prePred(Expr schExpr)
  {
    return asPred(factory_.createPreExpr(schExpr));
  }

  public ZExprList createGenericParamsRefExprs(ZNameList genParams)
  {
    ZExprList result = factory_.createZExprList();
    for(Name name : genParams)
    {
      result.add(factory_.createRefExpr(name));
    }
    assert result.size() == genParams.size();
    return result;
  }

  public Expr createSchRef(ZName schName, ZNameList genParams)
  {
    return genParams != null &&
           !genParams.isEmpty() ?
             factory_.createRefExpr(schName,
                createGenericParamsRefExprs(genParams), Boolean.FALSE) :
             factory_.createRefExpr(schName);

  }

  public Expr createDashedSchRef(ZName schName, ZNameList genParams)
  {
    //ZStrokeList zsl = factory_.createZStrokeList(schName.getZStrokeList());
    //zsl.add(factory_.createNextStroke());
    //ZName dashedName = factory_.createZName(schName.getWord(), zsl);
    return factory_.createDecorExpr(createSchRef(schName, genParams),
            factory_.createNextStroke());
  }

  public Pred createStateInitialisationVC(Expr absStateDash, Expr absStInit)
  {
    // original: \exists AState' @ ASinit
    // reduced : \forall CSInit @ \exists R' @ ASInit
    return asPred(factory_.createExistsExpr(
            factory_.createZSchText(
              factory_.createZDeclList(
                factory_.list(factory_.createInclDecl(absStateDash))),
              truePred()),
            absStInit));
  }

  public Pred createStateFinalisationVC(Expr absState, Expr absStFin)
  {
    // original: \exists AState @ ASFin
    return asPred(factory_.createExistsExpr(
            factory_.createZSchText(
              factory_.createZDeclList(
                factory_.list(factory_.createInclDecl(absState))),
              truePred()),
            absStFin));
  }

}
