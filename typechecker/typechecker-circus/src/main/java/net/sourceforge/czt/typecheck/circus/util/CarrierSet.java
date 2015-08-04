/*
  Copyright (C) 2007 Leo Freitas
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

package net.sourceforge.czt.typecheck.circus.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.NameSetTypeVisitor;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZFactory;

/**
 * This class provides carrier sets for the new Circus types.
 * That is all Type2 implementations, which excludes GenericType.
 * Signatures must also be handled by CarrierSet since they are 
 * part of composite types. Carrier sets can be either expressions
 * (for all Z types) or schema texts (for all Z signatures). The same
 * applies to Circus.
 *
 * @author Leo Freitas
 */
public class CarrierSet 
  extends net.sourceforge.czt.typecheck.z.util.CarrierSet
  implements 
    ChannelTypeVisitor<Term>, 
    ChannelSetTypeVisitor<Term>, 
//    ProcessTypeVisitor<Term>,    
//    ActionTypeVisitor<Term>,     
//    ProcessSignatureVisitor<Term>,
//    ActionSignatureVisitor<Term>,
    NameSetTypeVisitor<Term>
{    
  protected net.sourceforge.czt.circus.util.Factory circusFactory_;
  
  /** Creates a new instance of CarrierSet */
  public CarrierSet() 
  {
    this(DEFAULT_ALLOW_VARIABLE_TYPES);
  }

  public CarrierSet(boolean allowVariableTypes)
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(),
      new net.sourceforge.czt.circus.impl.CircusFactoryImpl(), 
      allowVariableTypes);
  }

  public CarrierSet(ZFactory zFactory, CircusFactory circusFactory)
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(),
      new net.sourceforge.czt.circus.impl.CircusFactoryImpl(), 
      DEFAULT_ALLOW_VARIABLE_TYPES);
  }

  public CarrierSet(ZFactory zFactory, CircusFactory circusFactory, 
    boolean allowVariableTypes)
  {
    super(zFactory, allowVariableTypes);
    circusFactory_ = new net.sourceforge.czt.circus.util.Factory(circusFactory);
  }
  
  public net.sourceforge.czt.circus.util.Factory getCircusFactory()
  {
	  return circusFactory_;
  }
  
  @Override
  public Term visitChannelType(ChannelType term)
  {
    Type2 type = term.getType();

    //if the type is null, then the type is undefined
    if (type == null) {
      throw new UndeterminedTypeException();
    }
    
    Expr expr = (Expr) type.accept(this);
    //PowerExpr result = zFactory_.createPowerExpr(expr);
    return expr;
  }
  
  /**
   * Channelset type signatures contain the channel name with the corresponding
   * type it was declared, where the given type SYNCH is used for synchronisation
   * channels. So, the resulting carrier set is just the ZSchText containing the
   * VarDecl for each channel declared in the channel set.
   */
  public Term visitChannelSetType(ChannelSetType term)
  {
    // just check the circus prelude is visible.? Only 
    //assert sectTypeEnv().visibleSections().contains(CircusUtils.CIRCUS_PRELUDE) : 
    //  "Circus prelude not yet loaded in global type environment";
    Signature sig = term.getSignature();    
    
    if (sig == null)
    {
      throw new UndeterminedTypeException();
    }
    
    return CircusUtils.CIRCUS_ID_EXPR;
//    assert false : "TODO: work out how this should be resolved. " +
//      "A channel set maximal type should be a set o pairs, unifiable " +
//      "on the fact all pairs are channel types, even though these types " +
//      "my not unify on their underlying base type (i.e., { (c, \\nat), (d, \\power \\num) }).";
  }
  
  /**
   * Nameset carrier sets are power expressions of a set expression
   * @param term
   * @return
   */
  public Term visitNameSetType(NameSetType term)
  {
    // just check the circus prelude is visible.? Only 
    //assert sectTypeEnv().visibleSections().contains(CircusUtils.CIRCUS_PRELUDE) : 
    //  "Circus prelude not yet loaded in global type environment";
      
    Signature sig = term.getSignature();    
    
    if (sig == null)
    {
      throw new UndeterminedTypeException();
    }

    return CircusUtils.CIRCUS_ID_EXPR;
  }
  
//  public Term visitProcessType(ProcessType term)
//  {
////    ProcessSignature sig = term.getProcessSignature();    
////    ProcessSignature result = (ProcessSignature)sig.accept(this);
////    return result;
//    assert false : "TODO: what should this return? an empty process? or just ProcessSignature?";
//    return null;
//  }
//  
//  private Signature schTextToSignature(ZSchText term)
//  {
//    for(Decl d : term.getZDeclList())
//    {
//      assert d instanceof VarDecl : "Cannot convert a non-VarDecl ZSchText to Signature";
//      VarDecl vd = (VarDecl)d;
//      //?      
//      assert false;
//    }
//    return null;
//  }
//  
//  public Term visitProcessSignature(ProcessSignature term)
//  {
//    SchText paramOrIndexes = (SchText)term.getFormalParamsOrIndexes().accept(this);    
//    Signature paramOrIndexesCarrier = schTextToSignature(ZUtils.assertZSchText(paramOrIndexes));     
//    //ProcessSignature result = circusFactory_.createCircusProcessSignature(
//    //  term.getProcessName(), term.getGenFormals(), paramOrIndexesCarrier, term.getKind());
//    //return result;
//    assert false ;
//    return null;
//  }
//  
//  public Term visitActionType(ActionType term)
//  {
//    ActionSignature sig = term.getActionSignature();
//    //checkForNullSignature(sig, "Null signature for ActionType " + term);            
//    SchText schText = (SchText) sig.accept(this);
//    return schText;
//  }  
//  
//  @Override
//  public Term visitActionSignature(ActionSignature term)
//  {
//    return null;
//  }  
}
