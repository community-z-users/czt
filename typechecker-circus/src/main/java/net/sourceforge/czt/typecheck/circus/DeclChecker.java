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

import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.QualifiedDecl;
import net.sourceforge.czt.circus.visitor.ChannelDeclVisitor;
import net.sourceforge.czt.circus.visitor.QualifiedDeclVisitor;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
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
 * @author Manuela
 */
public class DeclChecker
  extends Checker<List<NameTypePair>>
  implements ChannelDeclVisitor<List<NameTypePair>>,
             QualifiedDeclVisitor<List<NameTypePair>>,
             ZDeclListVisitor<List<NameTypePair>>
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
   */
  public List<NameTypePair> visitTerm(Term decl)
  {
    return decl.accept(zDeclChecker_);
  }
  
  /**
   * If declaring Circus formal parameters, we can only accept VarDecl or
   * QualifiedDecl, but not ConstDecl or InclDecl.
   */
  public List<NameTypePair> visitZDeclList(ZDeclList term)
  {
    if (!isCheckingCircusFormalParamDecl())
    {
      return term.accept(zDeclChecker_);
    }
    else 
    {
      List<NameTypePair> pairs = factory().list();
      
      //for each declaration in the list, get the declarations from that
      //and make sure they are of the appropriate subtype.
      for (Decl decl : zDeclList.getDecl()) {
        if (decl instanceof VarDecl || decl instanceof QualifiedDecl)
        {
          List<NameTypePair> nextPairs = decl.accept(declChecker());
          pairs.addAll(nextPairs);
        } else
        {
          boolean isProcess = true;
          Name name = getCurrentProcessName();
          if (name == null)
          {
            isProcess = false;
            name = getCurrentActionName();
          }
          
          if (name == null)
          {            
            Object[] params = {(isProcess ? "process" : "action")};
            error(decl, ErrorMessage.INVALID_SCOPE_FOR_FORMAL_PARAMS, params);
          }
          else 
          { 
            Object[] params = {(isProcess ? "process" : "action"), 
              name.toString(), decl.getClass().toString()};
            error(decl, ErrorMessage.INVALID_DECL_IN_FORMAL_PARAMS, params);
          }          
        }
      }
      return pairs;
    }
  }
  
  /**
   * Visiting ChannelDecl accounts for all type of explicit channel declarations
   * allowed in Circus. That includes synchronisation channels, typed channels,
   * generically typed channels, and channels from schemas. The only one missing
   * is implicitly declared channels through indexed processes, which are dealt
   * with in ProcessChecker.
   */
  public List<NameTypePair> visitChannelDecl(ChannelDecl term)
  {
    // CDeclaration ::= N+
    // CDeclaration ::= N+ : Expression
    // CDeclaration ::= [N+]N+ : Expression
    
    // retrieve each structure
    List<NameTypePair> result;
    Expr expr = term.getExpr();
    ZNameList declNames = term.getZNameList();
    ZNameList genParams = term.getZGenFormals();
    boolean isChannelFrom = declNames.isEmpty();
    assert expr != null : "ALL channels MUST have a type expression (including synch channels).";
    
    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();
    
    //add the generic parameter names to the local type env
    //this already checks if names are repeated.
    addGenParamTypes(genParams);
    
    // checks for duplicate names, and adds an error in case one is found.
    checkForDuplicateNames(declNames, ErrorMessage.DUPLICATE_CHANNEL_NAME_IN_CHANDECL);
    
    //visit the expression
    Type2 exprType = expr.accept(exprChecker());
    
    // if normal channel declaration, it is just like VarDecl:
    // the declaring type must be a power type to be type-correct.
    if (!isChannelFrom)
    {
      //expr should be a set expr, just like in varDecl
      PowerType vPowerType = factory().createPowerType();
      UResult unified = unify(vPowerType, exprType);
      
      //the list of name type pairs in the channel decl name list
      result = checkDeclNames(declNames, expr, unified, exprType, vPowerType);
    }
    // otherwise, the returning type must be a schema type.
    else
    {
      // If the name in the channelFrom declaration refers to a schema type
      // the name-type pairs are the result
      SchemaType schemaType = referenceToSchema(exprType);
      if (schemaType != null)
      {
        result = schemaType.getSignature().getNameTypePair();
      }
      // otherwise, we have a type error
      else
      {
        
      }
    }
    
    //exit the variable scope
    typeEnv().exitScope();
    
    return result;
  }
  
  /**
   * Visiting ChannelDecl accounts for all type of qualified parameter declarations
   * allowed in Circus. That includes parameter passing by value, result, or value result. 
   */  
  public List<NameTypePair> visitQualifiedDecl(QualifiedDecl term)
  {
    // QualifiedDeclaration :: = val Declaration
    // QualifiedDeclaration :: = res Declaration
    // QualifiedDeclaration :: = valres Declaration
    // QualifiedDeclaration :: = QualifiedDeclaration;QualifiedDeclaration

    Expr expr = term.getExpr();
    // TODO: What about Jokers here?
    ZNameList declNames = term.getZNameList();
    
    //visit the expression
    Type2 exprType = term.getExpr().accept(exprChecker());
    
    //expr should be a set expr, just like in varDecl
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, exprType);

    checkForDuplicateNames(term.getZNameList(), ErrorMessage.DUPLICATE_PARAM_NAME_IN_QUALIFIEDDECL);
    
    //the list of name type pairs in the channel decl name list
    List<NameTypePair> result = checkDeclNames(
      term.getZNameList(), term.getExpr(), unified, exprType, vPowerType);

    return result;
  }  
}
