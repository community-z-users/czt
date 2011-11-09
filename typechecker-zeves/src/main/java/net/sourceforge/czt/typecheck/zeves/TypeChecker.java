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

import java.util.Stack;
import net.sourceforge.czt.parser.util.ThmTable;
import net.sourceforge.czt.parser.zeves.ProofTable;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.zeves.util.UnificationEnv;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxSymbolVisitor;


/**
 *
 * @author Leo Freitas
 */
public class TypeChecker 
  extends net.sourceforge.czt.typecheck.z.TypeChecker
  implements TypecheckPropertiesKeys
{
  protected Name currentProofScript_;
  protected Type currentProofConjType_;
  protected String currentThmName_;

  protected Checker<ProofCommandInfo> proofCommandChecker_;
  protected ZEvesConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor_;

  protected WarningManager warningManager_;

  protected ThmTable thmTable_;
  protected ProofTable proofTable_;

  /**
   * Checks for Undeclared names in RefExpr within ConjPara. ZEves allows implicit universally quantified names
   * (E.g., like jokers for names) within theorems. So for instance, you could have  a conjecture "Op1 \iff Op2",
   * where there is no need to quantify over the state of these operators like "\forall St @ Op1 \iff Op2".
   */
  protected boolean ignoreUndeclaredNames_ = false;

  /**
   * Stack of QntPred contexts used to flag whether or not to tag undeclared names as ignoreable.
   * That is, names within QntPred DeclPart shouldn't be ignored (E.g., for the case of ingen/pregen
   * operators given inline with args - see zevesopt.tex example).
   */
  protected final Stack<Boolean> predWithinConjParaStack_;


  public TypeChecker(net.sourceforge.czt.typecheck.zeves.impl.Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, sectInfo, PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT,
        PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(net.sourceforge.czt.typecheck.zeves.impl.Factory factory,
                     SectionManager sectInfo,
                     boolean recursiveTypes,
                     boolean sortDeclNames)
  {
    // create all the checkers as default - for Z
    super(factory, sectInfo, recursiveTypes, sortDeclNames);

    predWithinConjParaStack_ = new Stack<Boolean>();

    // make sure specChecker is the first checker created
    // this is important because it creates the "Synch" channel
    // into the sectTypeEnv(), which is looked up by the
    // CommunicationChecker constructor
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    postChecker_ = new PostChecker(this);
    schTextChecker_ = new SchTextChecker(this);
    unificationEnv_ = new UnificationEnv(factory);

    proofCommandChecker_ = new ProofCommandChecker(this);
    
    warningManager_ = new WarningManager(TypeChecker.class, sectInfo);
    warningManager_.setMarkup(markup_);
    concreteSyntaxSymbolVisitor_ = new ZEvesConcreteSyntaxSymbolVisitor();
    // raise warnings has priority over hide warnings (e.g., can only hide if not raising)
    warningManager_.setWarningOutput(PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT);

    thmTable_ = null;
    proofTable_ = null;
    currentProofScript_ = null;
    currentThmName_ = null;
    ignoreUndeclaredNames_ = false;
  }

  @Override
  public final net.sourceforge.czt.typecheck.zeves.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.zeves.impl.Factory) super.getFactory();
  }

  @Override
  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }

  public WarningManager getWarningManager()
  {
    return warningManager_;
  }
}
