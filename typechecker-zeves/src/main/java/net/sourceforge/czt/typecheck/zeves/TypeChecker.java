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

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.DeclChecker;
import net.sourceforge.czt.typecheck.z.PostChecker;
import net.sourceforge.czt.typecheck.z.PredChecker;
import net.sourceforge.czt.typecheck.z.SchTextChecker;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.typecheck.z.util.UnificationEnv;
import net.sourceforge.czt.z.ast.Name;
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

  protected Checker<ProofCommandInfo> proofCommandChecker_;
  protected ZEvesConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor_;

  protected WarningManager warningManager_;

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

    // make sure specChecker is the first checker created
    // this is important because it creates the "Synch" channel
    // into the sectTypeEnv(), which is looked up by the
    // CommunicationChecker constructor
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    exprChecker_ = new ExprChecker(this);

    proofCommandChecker_ = new ProofCommandChecker(this);
    
    warningManager_ = new WarningManager(TypeChecker.class, sectInfo);
    warningManager_.setMarkup(markup_);
    concreteSyntaxSymbolVisitor_ = new ZEvesConcreteSyntaxSymbolVisitor();
    // raise warnings has priority over hide warnings (e.g., can only hide if not raising)
    warningManager_.setWarningOutput(PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT);
    
    currentProofScript_ = null;
  }

  @Override
  public final net.sourceforge.czt.typecheck.zeves.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.zeves.impl.Factory) super.getFactory();
  }

  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }

  public WarningManager getWarningManager()
  {
    return warningManager_;
  }
}
