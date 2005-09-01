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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;

/**
 *
 */
public class SchTextChecker
  extends Checker<Signature>
  implements SchTextVisitor<Signature>
{
  public SchTextChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Signature visitSchText(SchText schText)
  {
    //the list of Names declared in this schema text
    List<NameTypePair> pairs = list();

    //get and visit the list of declarations
    List<Decl> decls = schText.getDecl();
    for (Decl decl : decls) {
      pairs.addAll(decl.accept(declChecker()));
    }

    //add the pairs to the type environment
    typeEnv().add(pairs);

    //get and visit the pred
    Pred pred = schText.getPred();
    if (pred != null) {
      UResult solved = (UResult) pred.accept(predChecker());
      //if the are unsolved unifications in this predicate,
      //visit it again
      if (solved == PARTIAL) {
        pred.accept(predChecker());
      }
    }

    //check for duplicate names
    checkForDuplicates(pairs, null);

    //the signature for this schema text
    Signature signature = factory().createSignature(pairs);

    //add this as a type annotation
    addSignatureAnn(schText, signature);

    return signature;
  }
}
