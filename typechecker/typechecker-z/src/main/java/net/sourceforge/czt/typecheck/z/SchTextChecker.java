/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import java.util.List;


import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * <p>
 * Adds names to the current type environment scope based on the schema
 * text's declarations. This visitor is used within expressions and 
 * predicates that contain schema texts. 
 * </p>
 * <p>
 * Together with Checker.addGenParamTypes, which treats generic parameters,
 * this is the only place where name type pairs are explicit added to the
 * type environment. Interestingly, for AxPara within ParaChecker, such pairs
 * are added to the pending() type environment, since schema texts within 
 * AxPara are treated differently. 
 * </p>
 * <p>
 * Extensions to Z that require addition of global names to the environment,
 * should follow a similar protocol, which uses the pending() environment as
 * a spurious type environment used solely for typechecking purposes, and not
 * refered too later on (i.e. typeEnv() is for global declarations).
 * </p>
 */
public class SchTextChecker
  extends Checker<Signature>
  implements ZSchTextVisitor<Signature>
{
  public SchTextChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  @Override
  public Signature visitZSchText(ZSchText zSchText)
  {
    //get the list of Names declared in this schema text
    List<NameTypePair> pairs = checkSchTextDeclPart(zSchText);

    //add the pairs to the type environment
    typeEnv().add(pairs);

    // TODO: WHY THE 2nd PASS with NTP ADDED to the CONTEXT? Generic resolution?
    checkSchTextPredPart(zSchText);

    //check for duplicate names
    checkForDuplicates(pairs, null);

    //the signature for this schema text
    Signature signature = factory().createSignature(pairs);

    //add this as a type annotation
    addSignatureAnn(zSchText, signature);

    return signature;
  }
}
