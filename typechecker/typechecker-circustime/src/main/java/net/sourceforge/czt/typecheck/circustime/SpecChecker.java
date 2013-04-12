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
package net.sourceforge.czt.typecheck.circustime;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.circustime.util.CircusTimeUtils;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;


public class SpecChecker extends net.sourceforge.czt.typecheck.circus.SpecChecker
{
  //a Circus spec checker
  protected net.sourceforge.czt.typecheck.circus.SpecChecker circusSpecChecker_;

  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    circusSpecChecker_ = new net.sourceforge.czt.typecheck.circus.SpecChecker(typeChecker);
    
    NameSectTypeTriple synchTriple = factory().createNameSectTypeTriple(
    	      factory().createSynchName(), CircusTimeUtils.CIRCUSTIME_PRELUDE, factory().createSynchType());
    	    NameSectTypeTriple circustimeIdTriple = factory().createNameSectTypeTriple(
    	      factory().createCircusIdName(), CircusTimeUtils.CIRCUSTIME_PRELUDE, factory().createCircusIdType());
    	    NameSectTypeTriple transformerTriple = factory().createNameSectTypeTriple(
    	      factory().createTransformerName(), CircusTimeUtils.CIRCUSTIME_PRELUDE, 
    	      factory().createTransformerType());    
    	    sectTypeEnv().add(factory().list(synchTriple, circustimeIdTriple, transformerTriple));            
    	  
  }

  @Override
  public Object visitTerm(Term term)
  {
    return term.accept(circusSpecChecker_);
  }
}
