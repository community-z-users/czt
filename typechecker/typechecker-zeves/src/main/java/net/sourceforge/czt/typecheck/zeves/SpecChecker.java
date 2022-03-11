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
package net.sourceforge.czt.typecheck.zeves;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.ParentVisitor;
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
  implements ZParaListVisitor<List<NameSectTypeTriple>>, 
  			ZSectVisitor<List<NameSectTypeTriple>>, 
  			ParentVisitor<List<NameSectTypeTriple>>
{  
  //a Z spec checker
  protected net.sourceforge.czt.typecheck.z.SpecChecker zSpecChecker_;

  /**
   * Creates a new Specification level term checker with the given typechecker.
   * This creates a z.SpecChecker for handling most terms, except ZSect.
   * It also creates a type named "SYNCH" for synchronisation channels.   
   * @param typeChecker
   */
  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zSpecChecker_ = new net.sourceforge.czt.typecheck.z.SpecChecker(typeChecker); 
  }

  /**
   * Visits all other terms that the Z SpecChecker can deal with, or 
   * reach the global Checker.visitTerm, which catches and flags it
   * as an AST error.
   * @param term
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
    calculateTables(zSect);

    //reuse the general Checker protocol - needed to do it this way
    //to enable setSectName for WarningManager to be called rightly.
    List<NameSectTypeTriple> result = checkZSect(zSect);

    //System.out.println(zSect.getName() + " dependencies");
    //dependencies().dump();
    //sectTypeEnv().dumpParaIDInfo();
    //sectTypeEnv().dump();
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
    
    // ZParaList is the only production here that DOES NOT return 
    // a List<NameTypeTripple>, just like in the zSpeckChecker.
    return null;    
  }

  @Override
  public List<NameSectTypeTriple> visitParent(Parent term)
  {
    checkParent(term);
    return null;
  }
}