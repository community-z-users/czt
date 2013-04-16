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
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * This visitor checks specification level terms, performs post checking 
 * for mutually recursive processes and actions, adds global types (e.g., SYNCH), 
 * and takes care of on-the-fly processes.
 * 
 * @author Leo Freitas
 */
public class SpecChecker extends Checker<List<NameSectTypeTriple>>
  implements ZParaListVisitor<List<NameSectTypeTriple>>, ZSectVisitor<List<NameSectTypeTriple>>
{  
  //a Z spec checker
  protected net.sourceforge.czt.typecheck.z.SpecChecker zSpecChecker_;

  /**
   * Creates a new Specification level term checker with the given typechecker.
   * This creates a z.SpecChecker for handling most terms, except ZSect.
   * It also creates a type named "SYNCH" for synchronisation channels.   
   */
  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zSpecChecker_ = new net.sourceforge.czt.typecheck.z.SpecChecker(typeChecker);   
      
    /* NOTE: add the type for SYNCH given type. The OZ typechecker uses
     *       a special OIDType AST class. This is not needed for us because
     *       we assume the user won't add a given type with the same name
     *       (which contains special chars, e.g., $$SYNCH).
     *    
     *       CircusUtils has the same name and type available, but without 
     *       the proper ID as created by the typechecker. We update this in Factory.
     */     
    NameSectTypeTriple synchTriple = factory().createNameSectTypeTriple(
      factory().createSynchName(), CircusUtils.CIRCUS_PRELUDE, factory().createSynchType());
    NameSectTypeTriple circusIdTriple = factory().createNameSectTypeTriple(
      factory().createCircusIdName(), CircusUtils.CIRCUS_PRELUDE, factory().createCircusIdType());
    NameSectTypeTriple transformerTriple = factory().createNameSectTypeTriple(
      factory().createTransformerName(), CircusUtils.CIRCUS_PRELUDE, 
      factory().createTransformerType());    
    sectTypeEnv().add(factory().list(synchTriple, circusIdTriple, transformerTriple));            
  }

  /**
   * Visits all other terms that the Z SpecChecker can deal with, or 
   * reach the global Checker.visitTerm, which cathes and flags it 
   * as an AST error.
   */
  @Override
  public List<NameSectTypeTriple> visitTerm(Term term)
  {
    // for all other terms, just use th zSpecChecker.
    return term.accept(zSpecChecker_);
  }
  
  @Override
  public List<NameSectTypeTriple> visitZSect(ZSect zSect)
  {    
    //reuse the general Checker protocol - needed to do it this way
    //to enable setSectName for WarningManager to be called rightly.
    List<NameSectTypeTriple> result = checkZSect(zSect);
    return result;
  }
  
  /**
   * Visits all global paragraphs within a section and its parents. 
   * This typechecks all top-level elements as well as on-the-fly processes.
   * It also performs post processings for mutually recursive processes.
   */
  @Override
  public List<NameSectTypeTriple> visitZParaList(ZParaList term)
  {
    // typecheck all paragraphs: both top-level and implicitly declared processes.
    checkParaList(term);
    
    /* NOTE: In Manuela's first version, she typechecked these processes at the 
     *       calling time. As the parser declare then explicitly with an internal
     *       name, they are nothing more than a parameterised process, which is
     *       typechecked normally elsewhere (i.e. ProcessChecker).
     *
     *       At the call time (i.e. CallProcess) the type checking for on-the-fly
     *       process is special and is considered according to the rule given on
     *       page 51 of Manuela MSc's. 
     */    
    // set the implicitly declared processes list, which is important for calls
    setOnTheFlyProcesses(CircusUtils.getZSectImplicitProcessParaList(sectName(), term));
    
    // ZParaList is the only production here that DOES NOT return 
    // a List<NameTypeTripple>, just like in the zSpeckChecker.
    return null;    
  }    
}