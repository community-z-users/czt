/**
Copyright 2007, Leo Freitas
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
package net.sourceforge.czt.z.dc;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.AnnVisitor;
import net.sourceforge.czt.z.visitor.DirectiveVisitor;
import net.sourceforge.czt.z.visitor.NameSectTypeTripleVisitor;
import net.sourceforge.czt.z.visitor.NameTypePairVisitor;
import net.sourceforge.czt.z.visitor.NewOldPairVisitor;
import net.sourceforge.czt.z.visitor.OperVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.TypeVisitor;
import net.sourceforge.czt.z.visitor.ZNameListVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZStrokeListVisitor;

/**
 *
 * @author leo
 */
public abstract class InnocuousDC extends AbstractDC<Pred> implements 
    TypeVisitor<Pred>,
    NameTypePairVisitor<Pred>,
    NameSectTypeTripleVisitor<Pred>,
    AnnVisitor<Pred>,
    OperVisitor<Pred>,
    ZNameVisitor<Pred>,
    DirectiveVisitor<Pred>,
    ZNameListVisitor<Pred>,
    NewOldPairVisitor<Pred>,
    StrokeVisitor<Pred>,
    ZStrokeListVisitor<Pred>,
    TermVisitor<Pred>,
    Visitor<Pred>
{
  
  /** Creates a new instance of InnocuousDC */  
  public InnocuousDC(Factory factory)
  {
    super(factory);
  }

//Type<Pred>,
//  PowerTypeVisitor<R>,
//  GenParamTypeVisitor<R>,
//  SchemaTypeVisitor<R>,
//  GenericTypeVisitor<R>,
//  GivenTypeVisitor<R>,
//  SignatureVisitor<R>,
//  ProdTypeVisitor<R>,
  public Pred visitType(Type term)
  {
    return truePred();
  }

  public Pred visitNameTypePair(NameTypePair term)
  {
    return truePred();
  }

  public Pred visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    return truePred();
  }

//AnnVisitor<Pred>,
//  SectTypeEnvAnn Visitor<R>,
//  SignatureAnnVisitor<R>,
//  LocAnnVisitor<R>,
//  ParenAnn Visitor<R>,
//  TypeAnn Visitor<R>,
  public Pred visitAnn(Ann term)
  {
    return truePred();
  }

//OperVisitor<Pred>,
//  OperatorVisitor<R>,
//  OperandVisitor<R>,
  public Pred visitOper(Oper term)
  {
    return truePred();
  }

  public Pred visitZName(ZName term)
  {
    return truePred();
  }

  public Pred visitDirective(Directive term)
  {
    return truePred();
  }

  public Pred visitZNameList(ZNameList term)
  {
    return truePred();
  }

  public Pred visitNewOldPair(NewOldPair term)
  {
    return truePred();
  }

//StrokeVisitor<Pred>,
//  NumStroke Visitor<R>,
//  NextStrokeVisitor<R>,
//  OutStrokeVisitor<R>,
//  InStrokeVisitor<R>,
  public Pred visitStroke(Stroke term)
  {
    return truePred();
  }

  public Pred visitZStrokeList(ZStrokeList term)
  {
    return truePred();
  }
}

