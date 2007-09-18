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
package net.sourceforge.czt.typecheck.circus;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.SigmaExpr;
import net.sourceforge.czt.circus.visitor.BasicChannelSetExprVisitor;
import net.sourceforge.czt.circus.visitor.SigmaExprVisitor;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;

/**
 * Visitor that checks Circus expressions. They are channel set display expressions,
 * and sigma expressions, which represent channel selection like "c.1" or "c.true".
 *
 * @author Leo Freitas
 */
public class ExprChecker  
  extends Checker<Type2>
  implements BasicChannelSetExprVisitor<Type2>, 
             CircusChannelSet<Type2>,
             SigmaExprVisitor<Type2>
{
  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.ExprChecker zExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zExprChecker_ = new net.sourceforge.czt.typecheck.z.ExprChecker(typeChecker);
  }

  /** For all Z and other expressions use Z typechecking */
  public Type2 visitTerm(Term term)
  {
    return term.accept(zExprChecker_);
  }
  
  /**
   * The type of channel set displays is a signature containing name-type 
   * pairs of each channel element within the display. So, for example, 
   * if we had a display like \{| x, y.0 |\} for channels "x: \num; y: \nat",
   * the resulting signature would be "\lblot x: \num; y: \num \rblot", and 
   * hence the resulting type is 
   * <br>
   * POWER_TYPE(CHANNELSET_TYPE(SIGNATURE(<(x,POWER_TYPE(\arithmos)), (y, POWER_TYPE(\arithmos))>)))   * 
   */
  public Type2 visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    // check all communications within the channel set display
    List<NameTypePair> pairs = term.getCommunication().accept(commChecker());
    
    // create channel set type with the found pairs as its signature
    Signature channelSetSig = factory().createSignature(pairs);
    ChannelSetType cstype = factory().createChannelSetType(channelSetSig);    
    
    // create product type of the collected channel set type as the result.
    PowerType result = factory().createPowerType(cstype);
    
    addTypeAnn(term, result);
    
    return result;
  }

  /**
   * <p>
   * A sigma expression is formed by a channel name and a communicated value.
   * For instance, if a channel is declared as "c: \nat", and latter used in
   * a communication as "c.0", the sigma expression would be formed as a tuple
   * "(c, 0)", where "c" is a RefExpr and (in this case) "0" is a NumExpr. Other
   * types would have other valued expressions, yet all channels are RefExpr.   * 
   * </p>
   *
   * <p>
   * The resulting type is a product type of the cross product of each of these
   * two maximal types. So, for our example, the result is 
   * <br>
   * POWER_TYPE(PROD_TYPE(typeOf(RefExpr("c")), typeOf(NumExpr("0")))
   * <br>
   * which is just
   * <br>
   * POWER_TYPE(PROD_TYPE(POWER_TYPE(\arithmos), POWER_TYPE(\arithmos)))
   * <br>
   * Note that both types within the type product type are unifiable with respect
   * to their maximal types (i.e. carrier sets).
   * </p>
   * 
   * <p>
   * With those two types, we perform type unification with respect to maximal
   * type checking of Z (i.e. at the level of carrier sets). This avoids type
   * inconsistencies like "c.\true". This does not avoid, for instance, known 
   * (FDR) errors like 'outside protocol', when a communicated value is outside 
   * the channel type domain. That is, it does NOT prevent, say, 
   * "c: \nat_1 ... c.0", as a type inconsistency. 
   * </p>
   *
   * <p>
   * These extra type enforcements are undecidable, and not implemented for the
   * automatic type checking procedure for Circus. For instance, the Circus model 
   * checker adds such type encompassment check as a verification condition 
   * conjectures for type correctness. Other tools that rely on communication 
   * (e.g. all tools using the CSP side of Circus), MUST provide such verification 
   * condition generation as well.
   * </p>
   */
  public Type2 visitSigmaExpr(SigmaExpr term)
  {
    // check both the channel and the value types within the SigmaExpr
    Type2 channelType = term.getChannel().accept(exprChecker());
    Type2 valueType = term.getValue().accept(exprChecker());
    
    // these types MUST be unifiable, otherwise we have a communication outside
    // its type-domain (ex: c: \nat ...   c.\true)    
    UResult unified = unificationEnv().unify(channelType, valueType);        
    if (unified == FAIL)
    {
      Object [] params = {term.getChannel().toStirng(),
        channelType.toString(), valueType.toString()};
      error(term, ErrorMessage.CANNOT_UNIFY_SIGMAEXPR, params);
    }    
    Type2 result = factory().createProdType(factory().list(channelType, valueType));
    //Type2 result = factory().createPowerType(prodType);
    
    addTypeAnn(term, result);
    
    return result;
  }
  
//  // CSExpression
//  /* TODO: Check... these seems wrong as term.accept(paraChecker())
//           will return a Signature rather than a Type2. if this is right,
//           the visiting protocol became mixed up without a clear reason.
   public Type2 visitCircusChannelSet(CircusChannelSet term)
  {
    Type2 type = term.getExpr().accept(exprChecker());        
    Signature sig = type.accept(signatureChecker());
    ChannelSetType result = factory().createChannelSetType(sig);
    addTypeAnn(term, result);    
    return result;
  }
//  
//  // NSExpression
//  public Type2 visitNameSet(NameSet term)
//  {
//    return null;
//  }*/
//
//  // CSExpression ::= CSExpression \cup CSExpression
//  // CSExpression ::= CSExpression \cap CSExpression
//  // CSExpression ::= CSExpression \setminus CSExpression
//  //ok - verificado em 15/09/2005 às 13:12
//  // TODO: Does it allow any Z expression now, including function applications?
//  public Type2 visitApplChannelSet(ApplChannelSet term)
//  {
//    /*
//    List<NameTypePair> allPairs = list();
//    
//    TupleExpr tupleExpr = (TupleExpr)((ApplExpr)term.getExpr()).getRightExpr();
//    
//    List<Expr> exprs = tupleExpr.getExpr();
//    ChannelSet exprChanSet = null;
//    for (Expr expr : exprs) {
//      if (expr instanceof RefExpr) {
//        exprChanSet = factory().createRefChannelSet(((RefExpr)expr).getRefName());
//      } else if (expr instanceof SetExpr) {
//        List<RefExpr> refExprs = ((SetExpr)expr).getExpr();
//        ListTerm newExprs = listTerm();
//        for(RefExpr refExpr : refExprs) {
//          newExprs.add(refExpr.getRefName());
//        }
////        exprChanSet = factory().createBasicChannelSet(((SetExpr)expr).getExpr());
//        exprChanSet = factory().createBasicChannelSet(newExprs);
//      } else {
//        exprChanSet = factory().createApplChannelSet(expr);
//      }
//      Signature sig = ((ChanSetType)exprChanSet.accept(exprChecker())).getChannels();
//      List<NameTypePair> pairs = sig.getNameTypePair();
//      for(NameTypePair pair : pairs) {
//        if(!allPairs.contains(pair)) {
//          allPairs.add(pair);
//        }
//      }
//    }
//   
//    Signature channelsSig = factory().createSignature(allPairs);
//    ChanSetType type = factory().createChanSetType(channelsSig);
//    
//    addTypeAnn(term, type);
//
//    return type;
//     */  
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    
//    TupleExpr tupleExpr = (TupleExpr)((ApplExpr)term.getExpr()).getRightExpr();
//    
//    /*List<Expr>*/ ZExprList exprs = tupleExpr.getZExprList();
//    ChannelSet exprChanSet = null;        
//    for (Expr expr : exprs) {
//      if (expr instanceof RefExpr) {
//        exprChanSet = factory().createRefChannelSet(((RefExpr)expr).getRefName());
//      } else if (expr instanceof SetExpr) {
//        ZExprList refExprs = ((SetExpr)expr).getZExprList();        
//        ZRefNameList newExprs = factory().createZRefNameList();        
//        for(Expr rexpr : refExprs) {
//          if (!(rexpr instanceof RefExpr))
//              throw new UnsupportedOperationException("Circus typechecker only supports simple set operators for application expressions of channel sets.");
//          RefExpr refExpr = (RefExpr)rexpr;
//          newExprs.add(refExpr.getZRefName());
//          // TODO: Opps... what about the generic types from refExpr.getExprList()?
//        }
//        exprChanSet = factory().createBasicChannelSet(newExprs);
//      } else {
//        exprChanSet = factory().createApplChannelSet(expr);
//      }
//      // TODO: Here something seems wrong. If you call it this way with the "Object" protocol in
//      //       visitChannelSet, it will return a Signature from paraChecker and not a ChanSetType.
//      //       Note that paraChecker() does not even implement ChannelSetVisitor, but ChannelSetParaVisitor!
//      //       So, You do need a ChannelSet environment that is updated by
//      //       the paraChecker() visitor. That is, when you find a ChannelSetPara, it is included into
//      //       the environment, and from this environment you have a look from here!
//      Signature sig = null; //((ChanSetType)exprChanSet.accept(exprChecker())).getChannels();
//      
//      List<NameTypePair> pairs = sig.getNameTypePair();
//      for(NameTypePair pair : pairs) {
//        if(!allPairs.contains(pair)) {
//          allPairs.add(pair);
//        }
//      }
//    }
//   
//    Signature channelsSig = factory().createSignature(allPairs);
//    ChanSetType type = factory().createChanSetType(channelsSig);
//    
//    addTypeAnn(term, type);
//
//    return type;
//  }
//
//  // CSExpression ::= N
//  //ok - verificado em 15/09/2005 às 11:10
//  public Type2 visitRefChannelSet(RefChannelSet term)
//  {
//    RefName chansetRef = term.getRefName();
//    Signature channelsSig = factory().createSignature(new ArrayList<NameTypePair>());
//    ChanSetType type = factory().createChanSetType(channelsSig);
//    
//    if(!isChannelSet(chansetRef)){
//      Object [] params = {assertZRefName(chansetRef).getWord()};
//      error(term, ErrorMessage.IS_NOT_CHANSET_NAME, params);
//    }
//    else{
//      type = (ChanSetType)sectTypeEnv().getType(assertZRefName(chansetRef));
//    }
//    
//    addTypeAnn(term, type);
//
//    return type;
//  }
//
//  // CSExpression ::= {| |}
//  // CSExpression ::= {| N+ |}
//  //ok - verificado em 15/09/2005 às 11:09
//  public Type2 visitBasicChannelSet(BasicChannelSet term)
//  {
//    ZRefNameList chanDecls = term.getRefNameList() == null ? factory().createZRefNameList() : term.getZRefNameList();
//    List<NameTypePair> pairs = new ArrayList<NameTypePair>();
//    
//    for(RefName chanDecl : chanDecls) {      
//      if(!isChannel(assertZRefName(chanDecl).getDecl())){ 
//        Object [] params = {assertZRefName(chanDecl).getWord()};
//        error(term, ErrorMessage.IS_NOT_CHANNEL_IN_CHANSET, params);
//      } 
//      else {
//        Type typeChan = getChannelType(assertZRefName(chanDecl).getDecl());
//        // TODO: Why not to consider the strokes of chanDecl?
//        DeclName nameChan = factory().createZDeclName(assertZRefName(chanDecl).getWord(), null, null);
//        NameTypePair pair = factory().createNameTypePair(nameChan, typeChan);
//        pairs.add(pair);
//      }
//    }
//
//    Signature channelsSig = factory().createSignature(pairs);
//    Type2 type = factory().createChanSetType(channelsSig);
//    
//    addTypeAnn(term, type);
//
//    return type;
//  }
//
//  // NSExpression ::= NSExpression \cup NSExpression
//  // NSExpression ::= NSExpression \cap NSExpression
//  // NSExpression ::= NSExpression \setminus NSExpression
//  //ok - verificado em 15/09/2005 às 13:14
//  public Type2 visitApplNameSet(ApplNameSet term)
//  {
//      /*
//    List<NameTypePair> allPairs = list();
//    
//    TupleExpr tupleExpr = (TupleExpr)((ApplExpr)term.getExpr()).getRightExpr();
//    
//    List<Expr> exprs = tupleExpr.getExpr();
//    NameSet exprNameSet = null;
//    for (Expr expr : exprs) {
//      if (expr instanceof RefExpr) {
//        exprNameSet = factory().createRefNameSet(((RefExpr)expr).getRefName());
//      } else if (expr instanceof SetExpr) {
//        //exprNameSet = factory().createBasicNameSet(((SetExpr)expr).getExprList());
//      } else {
//        exprNameSet = factory().createApplNameSet(expr);
//      }
//      Signature sig = ((NameSetType)exprNameSet.accept(exprChecker())).getNames();
//      List<NameTypePair> pairs = sig.getNameTypePair();
//      for(NameTypePair pair : pairs) {
//        if(!allPairs.contains(pair)) {
//          allPairs.add(pair);
//        }
//      }
//    }
//   
//    Signature namesSig = factory().createSignature(allPairs);
//    NameSetType type = factory().createNameSetType(namesSig);
//    
//    addTypeAnn(term, type);
//
//    return type;*/
//      
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    TupleExpr tupleExpr = (TupleExpr)((ApplExpr)term.getExpr()).getRightExpr();
//    ZExprList exprs = tupleExpr.getZExprList();
//    
//    NameSet exprNameSet = null;
//    for (Expr expr : exprs) {
//      if (expr instanceof RefExpr) {
//        exprNameSet = factory().createRefNameSet(((RefExpr)expr).getRefName());
//      } else if (expr instanceof SetExpr) {
//        ZExprList refExprs = ((SetExpr)expr).getZExprList();
//        ZRefNameList newNames = factory().createZRefNameList();        
//        for(Expr rexpr : refExprs) {
//          if (!(rexpr instanceof RefExpr))
//              throw new UnsupportedOperationException("Circus typechecker only supports simple set operators for application expressions of name sets.");
//          RefExpr refExpr = (RefExpr)rexpr;
//          newNames.add(refExpr.getZRefName());
//          // TODO: Opps... what about the generic types from refExpr.getExprList()?
//        }
//        exprNameSet = factory().createBasicNameSet(newNames);        
//        // TODO: This wouldn't work because nameset expects a list of names and not expressions!
//        //exprNameSet = factory().createBasicNameSet(((SetExpr)expr).getExprList());
//      } else {          
//        exprNameSet = factory().createApplNameSet(expr);
//      }
//      // TODO: Here something seems wrong. If you call it this way with the "Object" protocol in
//      //       visitNameSet, it will return null!!.
//      //       Note that paraChecker() does not even implement ChannelSetVisitor, but ChannelSetParaVisitor!
//      //       So, You do need a NameSet environment that is updated by the visitor who checks NameSetPara.
//      //       In LocalTypeEnv, you have getNameSets returning a list of DeclName.
//      //       You would need something that returns the actual name set declaration for you to retrieve its signature from.
//      Signature sig = null; //((NameSetType)exprNameSet.accept(exprChecker())).getNames();            
//      List<NameTypePair> pairs = sig.getNameTypePair();
//      for(NameTypePair pair : pairs) {
//        if(!allPairs.contains(pair)) {
//          allPairs.add(pair);
//        }
//      }
//    }
//    Signature namesSig = factory().createSignature(allPairs);
//    NameSetType type = factory().createNameSetType(namesSig);
//    
//    addTypeAnn(term, type);
//
//    return type;
//        
//    
//  }
//
//  // NSExpression ::= N
//  //ok - verificado em 15/09/2005 às 13:15
//  public Type2 visitRefNameSet(RefNameSet term)
//  {
//    RefName namesetRef = term.getRefName();
//    Type2 type = factory().createNameSetType();
//    ZDeclName name = factory().createZDeclName(assertZRefName(namesetRef));
//    
//    if(!localCircTypeEnv().isNameSet(name)){
//      Object [] params = {name.getWord()};
//      error(term, ErrorMessage.IS_NOT_NAMESET_NAME, params);
//    }
//    else{
//        // TODO: Check This unwrapType call wasn't present at first, but it is needed
//        //       for the visiting protocol to work properly.
//      type = unwrapType(typeEnv().getType(assertZRefName(namesetRef)));      
//    }
//
//    addTypeAnn(term, type);
//
//    return type;
//  }
//
//  // NSExpression ::= {}
//  // NSExpression ::= {N+}
//  //ok - verificado em 15/09/2005 às 13:16
//  public Type2 visitBasicNameSet(BasicNameSet term)
//  {
//    ZRefNameList nameDecls = term.getRefNameList() == null ? factory().createZRefNameList() : term.getZRefNameList();
//    NameSetType result = factory().createNameSetType();
//    List<NameTypePair> pairs = new ArrayList<NameTypePair>();
//    
//    for(RefName nameDecl : nameDecls) {
//      ZRefName zrn = assertZRefName(nameDecl);      
//      if(isLovalVar(nameDecl)) {
//        DeclName name = zrn.getDecl();
//        Type type = typeEnv().getType(zrn);
//        NameTypePair pair = factory().createNameTypePair(name, type);
//        pairs.add(pair);
//      } 
//      else {
//        Object [] params = {assertZDeclName(currentProcess()).getWord(), 
//                zrn.getWord()};
//        error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_NAMESET, params);
//        break;
//      }
//    }
//
//    Signature namesSig = factory().createSignature(pairs);
//    Type2 type = factory().createNameSetType(namesSig);
//   
//    addTypeAnn(term, type);
//
//    return type;
//  }
}
