/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.typecheck.zeves;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.visitor.ZSchTextVisitor;

/**
 *
 * @author Leo Freitas
 * @date Aug 18, 2011
 */
public class SchTextChecker extends Checker<Signature>
  implements ZSchTextVisitor<Signature>
{
  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.SchTextChecker zSchTextChecker_;

  public SchTextChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zSchTextChecker_ = new net.sourceforge.czt.typecheck.z.SchTextChecker(typeChecker);
  }

  // No need?
  @Override
  public Signature visitTerm(Term term)
  {
    return term.accept(zSchTextChecker_);
  }

  @Override
  public Signature visitZSchText(ZSchText term)
  {
    // exits the scope to allow for undeclared name checking of DeclList of ZSchText
    boolean wasWithinQntPredScope = withinConjParaPredScope();
    
    if (wasWithinQntPredScope)
      exitPredWithinConjParaScope();

    //get the list of Names declared in this schema text
    List<NameTypePair> pairs = checkSchTextDeclPart(term);

    // restore the scope to ignore undeclared name checking of remaining Pred part
    if (wasWithinQntPredScope)
      enterPredWithinConjParaScope();

    //add the pairs to the type environment
    typeEnv().add(pairs);

    checkSchTextPredPart(term);

    //check for duplicate names
    checkForDuplicates(pairs, null);

    //the signature for this schema text
    Signature signature = factory().createSignature(pairs);

    //add this as a type annotation
    addSignatureAnn(term, signature);

    return signature;
  }
}