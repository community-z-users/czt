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
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.QualifiedDecl;
import net.sourceforge.czt.circus.visitor.ChannelDeclVisitor;
import net.sourceforge.czt.circus.visitor.QualifiedDeclVisitor;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;

/**
 * This checker extends within the typechecker architecture the
 * z.DeclChecker including the new types of declarations available
 * in Circus: channels and qualified parameters. Variable declarations
 * are treated just like VarDecl.
 *
 * All visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types.
 *
 * @author Leo Freitas
 */
public class DeclChecker
  extends Checker<List<NameTypePair>>
  implements ChannelDeclVisitor<List<NameTypePair>>,     // C.4.1, C.4.2, C.4.3, C.4.4
             ZDeclListVisitor<List<NameTypePair>>,       // C.4.4, C.16.1
             QualifiedDeclVisitor<List<NameTypePair>>    // C.16.2, C.16.3, C.16.4, C.16.5
             
{ 
  //a Z decl checker
  protected net.sourceforge.czt.typecheck.z.DeclChecker zDeclChecker_;
  
  public DeclChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    zDeclChecker_ = new net.sourceforge.czt.typecheck.z.DeclChecker(typeChecker);
  }
  
  /**
   * Visits all Z declaration paragraphs. They are:  VarDecl, ConstDecl, InclDecl, and ZDeclList.
   * 
   * @law C.18.8
   */
  @Override
  public List<NameTypePair> visitTerm(Term decl)
  {
    return decl.accept(zDeclChecker_);
  }
  
  /**
   * Accounts for all type of explicit channel declarations allowed in Circus. 
   * That includes synchronisation channels, typed channels,
   * generically typed channels, and channels from schemas. The only one missing
   * is implicitly declared channels through indexed processes, which are dealt
   * with in ProcessChecker.
   *
   *@law C.4.1, C.4.2, C.4.3, C.4.4 (within visitZDeclList general protocol)
   */    
  @Override
  public List<NameTypePair> visitChannelDecl(ChannelDecl term)
  {
    // CDeclaration ::= N+
    // CDeclaration ::= N+ : Expression
    // CDeclaration ::= [N+]N+ : Expression
    
    List<NameTypePair> result = factory().list();
    
    //we enter a new variable scope for the generic parameters
    //we do that here, rather than on the ChannelPara level because
    //all ChannelDecl within the ChannelPara can contain their own 
    //generic types.
    typeEnv().enterScope();
    
    //add the generic parameter names to the local type env
    //this already checks if names are repeated.
    addGenParamTypes(term.getZGenFormals());
    
    // retrieve structures and find out about the nature of the declaration
    Expr expr = term.getExpr();
    ZNameList declNames = term.getZChannelNameList();
    assert expr != null : "ALL channels MUST have a type expression " +
      "(including synch channels). This is a dynamic creation error";    
        
    //we enter a new variable scope for the generic parameters
    //CZT Z typechecker uses a pending() environment for global names
    //declared in the current paragraph. That is because global names 
    //in the current paragraph shall not have their generic types 
    //instantiated. 
    pending().enterScope();
    
    // checks for duplicate names, and adds an error in case one is found.    
    // NoRep ln
    checkForDuplicateNames(declNames, term);
    
    // (NotInto ln \Gamma.defNames) is checked at checkParaList()
    
    //visit the expression
    // \Gamma \rhd e: Expression, C.4.2
    Type2 exprType = expr.accept(exprChecker());
    //System.out.println("type for " + declNames + " : " + exprType);
    
    // channel from declarations declare all elements from the signature
    // of a given schema reference type. That means, they must be a RefExpr
    // typed as a reference to a schema type (channelfrom S, where S is a schema). 
    // Structurally, they differ from usual declarations because the list of names
    // is empty, and that determines the next flag.
    
    //BUGFIX: this check is not strong enough because it wrongly considers
    //        usual channel declarations that have schema types as channelFrom
    //        ex: channel x: S, where S == [ a, b: \nat ]. The result is to
    //        NOT declare "x \in \power~[ a, b : \arithmos ]", but to declare
    //        a and b instead belonging to this type. The fix is easy: structurally
    //        ChannelDecl with an empty name list is a channelFrom!  
    //        
    //boolean isChannelFrom = referenceToSchema(exprType) != null;    
    boolean isChannelFrom = declNames.isEmpty();
    
    // if normal channel declaration, it is just like VarDecl:
    // the declaring type must be a power type to be type-correct.
    if (!isChannelFrom/*!CircusUtils.isChannelFrom(term)*/)
    {   
      //expr should be a set expr , just like in varDecl            
      PowerType vType = factory().createPowerType();
      UResult unified = unify(vType, exprType);
            
      //the list of name type pairs in the channel decl name list
      // possibly adds generics if needed - i.e., if term.getZGenFormals() was not
      // empty, typeEnv().getParameters().size() != 0 and z.Checker.addGenerics
      // will wrap the vType as GenericType.
      result.addAll(checkChannelDecl(declNames, expr, unified, exprType, vType));      
    }
    // otherwise, the returning type must be a schema type.
    else
    {
      // If the name in the channelFrom declaration refers to a schema type
      // the name-type pairs are the result      
      SchemaType schemaType = referenceToSchema(exprType);
      
      // This is bad: we would need to consider ConstDecl, InclDecl, etc.. :-(
      //SchExpr schemaExpr = (SchExpr)schemaType.accept(carrierSet());      
      //schemaExpr.getZSchText().getZDeclList()     
      
      if (schemaType != null)
      {  
        CarrierSet cs = carrierSet();
        // check each name type pair using checkChannelDecl
        for(NameTypePair pair : schemaType.getSignature().getNameTypePair())
        {          
          Term pairType = pair.getType().accept(cs);
          // if from a flat schema (i.e. no inclusion)
          if (pairType instanceof Expr)
          {
            Expr channelTypeExpr = (Expr)pairType;
            PowerType vType = factory().createPowerType();
            UResult unified = unify(vType, exprType);
            
            // only one pair at time, but it reuses the general code for lists. fine.
            // improve latter if needed (i.e. this construct is rarely used...)
            result.addAll(checkChannelDecl(factory().list(pair.getName()), channelTypeExpr,
              unified, exprType, vType));
          }          
          else
          {
            Object[] params = { expr, exprType, pair.getName(), pairType }; 
            error(expr, ErrorMessage.CHANNEL_FROM_INVALID_INCLDECL, params);
          }
        }
      }
      // otherwise, we have a type error
      else
      {
        Object[] params = { expr, exprType }; 
        error(expr, ErrorMessage.CHANNEL_FROM_INVALID_DECL, params);        
      }
    }            
    checkCircusNameStrokes(result);
    
    // all top-level paragraphs have type or signature annotations
    // except ChannelDecl, because of its heterogenous form.
    addSignatureAnn(term, factory().createSignature(result));
    
    //exit the pending scope 
    pending().exitScope();
    
    //exit the typing scope for channels
    typeEnv().exitScope();
    
    return result;
  }
  
  /**
   * If declaring Circus formal parameters, we can only accept VarDecl or
   * QualifiedDecl, but not ConstDecl or InclDecl. Otherwise, just follow
   * the Z protocol. When declaring formal parameters, the
   * {@link #isCheckingCircusFormalParamDecl()} flag must be on.
   *
   *@law C.4.4, C.16.1
   */
  @Override
  public List<NameTypePair> visitZDeclList(ZDeclList term)
  {
    // In case we have formal params, it must be VarDecl or QualifiedDecl.
    // Otherwise, it doesn't matter and just use the Z protocol.
    // isCheckingCircusFormalParamDecl() => VarDecl || QualifiedDecl
    // !isCheckingCircusFormalParamDecl() || VarDecl || QualifiedDecl
    
    // use the Z protocol
    List<NameTypePair> result = term.accept(zDeclChecker_);    
    
    // search for the need to add errors in case we are checking formal parameters
    if (isCheckingCircusFormalParamDecl())
    {
      int i = 1;
      //for each declaration in the list, get the declarations from that
      //and make sure they are of the appropriate subtype.
      for (Decl decl : term.getDecl()) 
      {
        if (!isValidDeclClass(decl))        
        {          
          boolean isProcess = isWithinProcessParaScope();
          Name name = (isProcess ? getCurrentProcessName() : getCurrentActionName());        
          List<Object> params = factory().list();
          
          if (isProcess)
          { 
            params.add("process");
            params.add(getCurrentProcessName());
          }
          else
          {
            params.add("action");
            params.add(getCurrentProcessName());
            //params.add(getCurrentActionName());
          }
          if (name == null)
          {                       
            assert !isWithinActionParaScope() : "within action scope but without action name for process " 
              +  getCurrentProcessName();
            params.add(i);
            error(decl, ErrorMessage.FORMAL_PARAMS_INVALID_SCOPE, params);
          }
          else 
          { 
            params.add("VarDecl or QualifiedDecl");
            params.add(decl.getClass().getName());
            params.add(i);
            error(decl, ErrorMessage.FORMAL_PARAMS_INVALID_DECL, params);
          }          
        }
        i++;
      }
    }
    return result;
  }
  
  /**
   * Accounts for all type of qualified parameter declarations
   * allowed in Circus. That includes parameter passing by value, 
   * result, or value result. To arrive here, the 
   * {@link #isCheckingCircusFormalParamDecl()} flag must be on.
   * Checking the qualified declaration is within scope is done by
   * the visitZDeclList method.
   *
   *@law C.16.2, C.16.3, C.16.4, C.16.5
   */  
  @Override
  public List<NameTypePair> visitQualifiedDecl(QualifiedDecl term)
  {
    // QualifiedDeclaration :: = val Declaration
    // QualifiedDeclaration :: = res Declaration
    // QualifiedDeclaration :: = valres Declaration
    // QualifiedDeclaration :: = QualifiedDeclaration;QualifiedDeclaration
        
    List<NameTypePair> result = factory().list();
    
    Expr expr = term.getExpr();
    ZNameList declNames = term.getZNameList();
    
    // TODO: CHECK: should this scoping be condition on whether we are 
    //              within a process or not? That is, within is localCircusTypeEnv()
    //              not within is typeEnv(). 
    // we need a scope for the parameters
    //typeEnv().enterScope();
    
    //visit the expression
    Type2 exprType = term.getExpr().accept(exprChecker());
    
    //expr should be a set expr, just like in varDecl
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, exprType);

    checkForDuplicateNames(declNames, term);
    
    //the list of name type pairs in the channel decl name list
    result.addAll(checkDeclNames(
      declNames, expr, unified, exprType, vPowerType));

    // exists the checking scope
    //typeEnv().exitScope();
    
    checkCircusNameStrokes(result);    
    
    // add variables to the calling scope.
    typeEnv().add(result);
    
    return result;
  }  
}
