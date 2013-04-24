/*
  Copyright (C) 2006, 2007 Petra Malik
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

package net.sourceforge.czt.print.zpatt;

import java.util.Properties;

import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.zpatt.ast.CheckPassed;
import net.sourceforge.czt.zpatt.ast.Deduction;
import net.sourceforge.czt.zpatt.ast.HeadDeclList;
import net.sourceforge.czt.zpatt.ast.JokerDeclList;
import net.sourceforge.czt.zpatt.ast.JokerDeclListBinding;
import net.sourceforge.czt.zpatt.ast.JokerExpr;
import net.sourceforge.czt.zpatt.ast.JokerExprBinding;
import net.sourceforge.czt.zpatt.ast.JokerExprList;
import net.sourceforge.czt.zpatt.ast.JokerExprListBinding;
import net.sourceforge.czt.zpatt.ast.JokerName;
import net.sourceforge.czt.zpatt.ast.JokerNameBinding;
import net.sourceforge.czt.zpatt.ast.JokerNameList;
import net.sourceforge.czt.zpatt.ast.JokerNameListBinding;
import net.sourceforge.czt.zpatt.ast.JokerPred;
import net.sourceforge.czt.zpatt.ast.JokerPredBinding;
import net.sourceforge.czt.zpatt.ast.JokerRenameList;
import net.sourceforge.czt.zpatt.ast.JokerRenameListBinding;
import net.sourceforge.czt.zpatt.ast.JokerStroke;
import net.sourceforge.czt.zpatt.ast.JokerStrokeBinding;
import net.sourceforge.czt.zpatt.ast.Jokers;
import net.sourceforge.czt.zpatt.ast.Oracle;
import net.sourceforge.czt.zpatt.ast.OracleAppl;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.ast.RuleAppl;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.ast.SequentContext;
import net.sourceforge.czt.zpatt.ast.SequentList;
import net.sourceforge.czt.zpatt.util.ZPattString;
import net.sourceforge.czt.zpatt.visitor.ZpattVisitor;

public class ZpattPrintVisitor
  extends net.sourceforge.czt.print.z.ZPrintVisitor
  implements ZpattVisitor<Object>
{
  public ZpattPrintVisitor(SectionInfo si, ZPrinter printer, Properties props)
  {
    super(si, printer, props);
  }

  @Override
public Object visitCheckPassed(CheckPassed checkPassed)
  {
    throw new UnsupportedOperationException();
  }

  public Object visitDeduction(Deduction ded)
  {
    throw new UnsupportedOperationException();
  }

  @Override
public Object visitHeadDeclList(HeadDeclList list)
  {
    visit(list.getJokerDeclList());
    print(ZKeyword.COMMA);
    visit(list.getZDeclList());
    return null;
  }

  @Override
public Object visitJokers(Jokers jokers)
  {
    throw new UnsupportedOperationException();
  }

  @Override
public Object visitJokerDeclList(JokerDeclList joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerDeclListBinding(JokerDeclListBinding binding)
  {
    visit(binding.getJokerDeclList());
    printDecorword("\u219D");
    visit(binding.getDeclList());
    return null;
  }

  @Override
public Object visitJokerExpr(JokerExpr joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerExprBinding(JokerExprBinding binding)
  {
    visit(binding.getJokerExpr());
    printDecorword("\u219D");
    visit(binding.getExpr());
    return null;
  }

  @Override
public Object visitJokerExprList(JokerExprList joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerRenameList(JokerRenameList joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerStroke(JokerStroke joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerNameList(JokerNameList joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerExprListBinding(JokerExprListBinding binding)
  {
    visit(binding.getJokerExprList());
    printDecorword("\u219D");
    visit(binding.getExprList());
    return null;
  }

  @Override
public Object visitJokerRenameListBinding(JokerRenameListBinding binding)
  {
    visit(binding.getJokerRenameList());
    printDecorword("\u219D");
    visit(binding.getRenameList());
    return null;
  }

  @Override
public Object visitJokerStrokeBinding(JokerStrokeBinding binding)
  {
    visit(binding.getJokerStroke());
    printDecorword("\u219D");
    visit(binding.getStroke());
    return null;
  }

  @Override
public Object visitJokerNameListBinding(JokerNameListBinding binding)
  {
    visit(binding.getJokerNameList());
    printDecorword("\u219D");
    visit(binding.getNameList());
    return null;
  }

  @Override
public Object visitJokerPred(JokerPred joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerPredBinding(JokerPredBinding binding)
  {
    visit(binding.getJokerPred());
    printDecorword("\u219D");
    visit(binding.getPred());
    return null;
  }

  @Override
public Object visitJokerName(JokerName joker)
  {
    printDecorword(joker.getName());
    return null;
  }

  @Override
public Object visitJokerNameBinding(JokerNameBinding binding)
  {
    visit(binding.getJokerName());
    printDecorword("\u219D");
    visit(binding.getName());
    return null;
  }

  @Override
public Object visitSequent(Sequent sequent)
  {
    visit(sequent.getPred());
    return null;
  }

  @Override
public Object visitSequentList(SequentList sequentList)
  {
    for (Sequent sequent : sequentList) {
      visit(sequent);
      print(ZToken.NL);
    }
    return null;
  }

  @Override
public Object visitRule(Rule rule)
  {
    printDecorword(ZPattString.RULE);
    printDecorword(rule.getName());
    visit(rule.getPremisses());
    printDecorword(ZPattString.RULELINE);
    visit(rule.getSequent());
    return null;
  }

  @Override
public Object visitOracle(Oracle oracle)
  {
    printDecorword(ZPattString.PROVISO);
    printDecorword(oracle.getName());
    visit(oracle.getSequent());
    return null;
  }

  @Override
public Object visitOracleAppl(OracleAppl oracleAppl)
  {
    throw new UnsupportedOperationException();
  }

  @Override
public Object visitRuleAppl(RuleAppl ruleAppl)
  {
    throw new UnsupportedOperationException();
  }

  @Override
public Object visitSequentContext(SequentContext context)
  {
    throw new UnsupportedOperationException();
  }
}
