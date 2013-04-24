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

package net.sourceforge.czt.print.zeves;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.zeves.ZEvesProofKeyword;
import net.sourceforge.czt.parser.zeves.ZEvesProofToken;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.LabelUsage;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.ZEvesUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class AstToPrintTreeVisitor extends
        net.sourceforge.czt.print.z.AstToPrintTreeVisitor
{

  public AstToPrintTreeVisitor(SectionInfo sectInfo) {
      this(sectInfo, new WarningManager(AstToPrintTreeVisitor.class));
  }

  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param sectInfo
   * @param wm
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo, WarningManager wm)
  {
    super(sectInfo, wm);
  }

  /**
   *
   * @param term
   * @param list
   */
  @Override
  protected void preprocessTerm(Term term, List<Object> list) throws PrintException
  {
    super.preprocessTerm(term, list);
    // within AxPara
    if (withinAxPara_)
    {
      // if have label
      ZEvesLabel label = ZEvesUtils.getLabel(term);
      if (label != null)
      {
        // check what kind of para for just ability or label
        boolean hasAbility = label.getLabelAbility().equals(LabelAbility.disabled);
        if (term instanceof AxPara)
        {
          // for SCH or OmitBox
          if (((AxPara)term).getBox().equals(Box.AxBox))
            throw new PrintException(getSectionInfo().getDialect(), "preprocessing ability for Schemas and Horizontal definitions only. AxBox labels are processed at predicate level.");

          if (hasAbility)
            list.add(ZEvesProofToken.DISABLEDDEFTAG);
        }
        // it's a pred, we have a label
        else if (term instanceof Pred)
        {
          // handle name
          if (label.getName() == null)
            throw new PrintException(getSectionInfo().getDialect(), "Invalid label name for labelled axiomatic predicate - " + label.toString());

          // no bother with axioms (defaults). If there is usage, put the label!
          if (//!label.getUsage().equals(LabelUsage.axiom) &&
              !label.getLabelUsage().equals(LabelUsage.none))
          {
            list.add(ZEvesProofToken.LLABEL);

            // handle ability
            if (hasAbility)
              list.add(ZEvesProofKeyword.DISABLED);

            // handle usage
            switch (label.getLabelUsage())
            {
              case rule:
                list.add(ZEvesProofKeyword.THMRULE);
                break;
              case grule:
                list.add(ZEvesProofKeyword.THMGRULE);
                break;
              case frule:
                list.add(ZEvesProofKeyword.THMFRULE);
                break;
              case axiom:
                // No need, already within AxPara - e.g., ConjPara will get axiom tag
                //list.add(ZEvesProofKeyword.THMAXIOM);
                //break;
              case none:
              default:
                // do nothing
                break;
            }
            // axiom names are not to be given/print
            list.add(visit(label.getName()));

            list.add(ZEvesProofToken.RLABEL);
          }
        }
        else
          throw new PrintException(getSectionInfo().getDialect(),"Invalid term to preprocess for printing. Neither AxPara, nor Pred " + term.getClass().getName());
      }
    }
  }
}
