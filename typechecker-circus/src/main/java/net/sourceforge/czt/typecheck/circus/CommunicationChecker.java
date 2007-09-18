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

import java.util.ArrayList;
import java.util.Collections;
import static net.sourceforge.czt.z.util.ZUtils.*;
import static net.sourceforge.czt.typecheck.circus.util.GlobalDefs.*;

import java.util.List;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.ast.NameTypePair;

/**
 *
 * @author Leo Freitas
 * @author Manuela Xavier
 */
public class CommunicationChecker extends Checker<List<NameTypePair>>
  implements CommunicationVisitor<List<NameTypePair>>,
             //FieldVisitor<List<NameTypePair>>,
             DotFieldVisitor<List<NameTypePair>>,
             InputFieldVisitor<List<NameTypePair>>
             //OutputFieldVisitor<List<NameTypePair>>
{
  
  //a Z decl checker
  protected net.sourceforge.czt.typecheck.z.DeclChecker zDeclChecker_;
  
  private int position_;
  private Type chanType_;
  private ZDeclName chanName_;

  /** Creates a new instance of CommunicationChecker */
  public CommunicationChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zDeclChecker_ = new net.sourceforge.czt.typecheck.z.DeclChecker(typeChecker);
  }

  // Communication ::= N
  // Communication ::= N CParameter+
  // Communication ::= N[Expression+] CParameter+
  //ok - verificado em 15/09/2005 às 14:33
  public List<NameTypePair> visitCommunication(Communication term)
  {
      
    List<NameTypePair> result = new ArrayList<NameTypePair>();

    this.chanName_ = factory().createZDeclName(assertZRefName(term.getChanName()).getWord(), null, null);

    if(isChannel(this.chanName_)) {
        // TODO: Get from circus_toolkit when parser is ready.
      ZDeclName name = factory().createZDeclName("Synch", null, null);
      Type typeSynch = factory().createGivenType(name);

      this.chanType_ = getChannelType(this.chanName_);
      this.position_ = 0;
      
      List<Field> cParams = term.getChanFields();
      Object [] params = {assertZDeclName(currentProcess()).getWord(), this.chanName_.getWord()};
      
      // caso o canal seja de sincronização
      if(this.chanType_.equals(typeSynch)) {
        if(!cParams.isEmpty()) {
          // erro pois o canal é de sincronização e não deve ter parâmetros
          error(term, ErrorMessage.SYNCH_CHANNEL_WITH_CPARAMS_ERROR, params);
        }
      }
      else {
        if(!cParams.isEmpty()) {
          if(this.chanType_ instanceof ProdType) {
            if(((ProdType)this.chanType_).getType().size() != cParams.size()) {
              // o número de parâmetros não atende ao tipo do canal
              error(term, ErrorMessage.NUMBER_CPARAMS_INCOMPATIBLE_CHANNEL_TYPE, params);
            }
          } 
          else {
            if(cParams.size() > 1) {
              // o número de parâmetros não atende ao tipo do canal
              error(term, ErrorMessage.NUMBER_CPARAMS_INCOMPATIBLE_CHANNEL_TYPE, params);
            } 
          }
          
          // tratamento de comunicação genérica
          ZExprList zGenActuals = term.getGenActuals() == null ? null : assertZExprList(term.getGenActuals());
          if(zGenActuals != null && !zGenActuals.isEmpty()) {
            if(!isGenericChannel(this.chanName_)) {
              error(term, ErrorMessage.IS_NOT_GENERIC_CHANNEL, params);
            }
            else {
              ZExprList exprs = zGenActuals;
              List<DeclName> genParams = getGenParamsChannel(this.chanName_);
              if(exprs.size() != genParams.size()) {
                error(term, ErrorMessage.DIFF_NUMBER_IN_GENERIC_CHANNEL_INSTATIATION, params);
              }
              else {
                int i = 0;
                for(Expr expr : exprs) {
                  Type2 typeExpr = expr.accept(exprChecker());
                  DeclName genName = genParams.get(i);
                  if(typeExpr instanceof PowerType) {
                    Type2 type = ((PowerType)typeExpr).getType();
                    this.chanType_ = replaceChannelType(genName, type, this.chanType_);
                  } else {
                    error(term, ErrorMessage.EXPR_TYPE_IS_NOT_POWERSET, params);
                    break;
                  }
                  i++;
                }
              }
            }
          }

          //eh preciso um novo ambiente para tratar o seguite caso: c?x!x. O x
          //deve estar no escopo da expressão do outputField !Exp...
          typeEnv().enterScope();
          for(Field cParam : cParams) {
            List<NameTypePair> pairs = cParam.accept(communicChecker());
            List<Object> paramsError = new ArrayList<Object>();
            paramsError.add(assertZDeclName(currentProcess()).getWord());            
            // chama uma função que verifica se existe redeclaração de variáveis de entrada
            // com tipos diferentes.
            result = checkDecls(result, pairs, term, ErrorMessage.REDECLARED_INPUT_VAR_IN_PROCESS, paramsError);
            this.position_++;
            typeEnv().add(pairs);
          }
          typeEnv().exitScope();
        }
        else {
          // erro pois o canal exige parâmetros
          error(term, ErrorMessage.CHANNEL_NEEDS_CPARAMS, params);
        }
      }
      // adicionando os canais usados...
      List<NameTypePair> usedChans = new ArrayList<NameTypePair>();
      NameTypePair usedChan = factory().createNameTypePair(this.chanName_, this.chanType_);
      usedChans.add(usedChan);
      localCircTypeEnv().addUsedChans(usedChans);
      //
    } else {
      Object [] params = {this.chanName_.getWord()};
      error(term, ErrorMessage.IS_NOT_CHANNEL_NAME, params); 
    }
    
    return result;
  }
  
  //CParameter
//  public List<NameTypePair> visitField(Field term)
//  {
//    return term.accept(communicChecker());
//  }
  
  // CParameter ::= .Expression
  //ok - verificado em 15/09/2005 às 14:35
  public List<NameTypePair> visitDotField(DotField term)
  {
    Type2 exprType = term.getExpression().accept(exprChecker());
    
    Type type = this.chanType_;

    if(this.chanType_ instanceof ProdType) {
      List<Type2> types = ((ProdType)this.chanType_).getType();
      type = types.get(this.position_);
    } 

    if(!(exprType instanceof UnknownType)) {
      Type2 expectedU = unwrapType(type);
      Type2 foundU = unwrapType(exprType);
      if (unify(foundU, expectedU) != SUCC) {
        Object [] params = {assertZDeclName(currentProcess()).getWord(), 
                expectedU, this.chanName_.getWord(), foundU};
        error(term, ErrorMessage.CHANNEL_PARAM_NOT_UNIFY, params);
      }   
    }
    
    return new ArrayList<NameTypePair>();
  }
  
  // CParameter ::= ?N
  // CParameter ::= ?N : Predicate
  //ok - verificado em 15/09/2005 às 14:38
  public List<NameTypePair> visitInputField(InputField term)
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    // TODO: Check: what about strokes?
    ZDeclName varName = factory().createZDeclName(assertZRefName(term.getVariable()).getWord(), null, null);
    Type varType = factory().createUnknownType();
      
    if(this.chanType_ instanceof ProdType) {
      List<Type2> types = ((ProdType)this.chanType_).getType();
      if(types.size() > this.position_) {
        varType = types.get(this.position_);
      } else {
        Object [] params = {varName.getWord(), this.chanName_.getWord()};
        error(term, ErrorMessage.IMPOSSIBLE_EXTRACT_INPUT_VAR, params);
      }
    } else {
      if(this.position_ == 0) {
        varType = this.chanType_;
      } else {
        Object [] params = {varName.getWord(), this.chanName_.getWord()};
        error(term, ErrorMessage.IMPOSSIBLE_EXTRACT_INPUT_VAR, params);
      }
    }
    
    NameTypePair pair = factory().createNameTypePair(varName, varType);
    result.add(pair);
    
    typeEnv().enterScope();
    typeEnv().add(pair);
    term.getRestriction().accept(predChecker());
    typeEnv().exitScope();
    
    return result;
  }

  // CParameter ::= !Expression
  //ok - verificado em 15/09/2005 às 14:38
//  public Object visitOutputField(OutputField term)
//  {
//    return visitDotField(term);
//  }

  /*
   * Método auxiliar que instancia o tipo de um canal genérico
   */
  private Type replaceChannelType(DeclName genName, Type typeExpr, Type typeChan) {
    Type result = null;
    
    if(typeChan instanceof ProdType) {
      List<Type2> types = ((ProdType)typeChan).getType();
      List<Type2> typesResult = new ArrayList<Type2>();
      for(Type2 type : types) {
        Type res = replaceChannelType(genName, typeExpr,  type);
        // TODO: Check: Why not unwrapType?
        typesResult.add((Type2)res);
      }
      result = factory().createProdType(typesResult);
    }
    else if(typeChan instanceof PowerType) {
      Type2 type = ((PowerType)typeChan).getType();
      Type res = replaceChannelType(genName, typeExpr, type);
      result = factory().createPowerType((Type2)res);
    }
    else if(typeChan instanceof GenParamType) {
      ZDeclName nameType = ((GenParamType)typeChan).getName();
      if (compareDeclName(nameType, genName, true)) {
        result = typeExpr;
      } else {
        result = typeChan;
      }
    }
    else {
      result = typeChan;
    }
    
    return result;
  }

}
