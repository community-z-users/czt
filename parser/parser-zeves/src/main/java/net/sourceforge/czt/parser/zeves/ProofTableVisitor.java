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

package net.sourceforge.czt.parser.zeves;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.util.AbstractVisitor;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jul 13, 2011
 */
public class ProofTableVisitor
   extends AbstractVisitor<ProofTable>
  implements TermVisitor<ProofTable>,
             ProofScriptVisitor<ProofTable>,
             ParaVisitor<ProofTable>,
             ZParaListVisitor<ProofTable>,
             ZSectVisitor<ProofTable>
{
  private ProofTable table_;

  /**
   * Creates a new named conjecture table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.ProofTable.class</code>.
   * @param sectInfo
   */
  public ProofTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Class<ProofTable> getInfoType()
  {
    return ProofTable.class;
  }

  @Override
  public ProofTable run(Term term)
    throws CommandException
  {
    super.run(term);
    return getProofTable();
  }

  protected ProofTable getProofTable()
  {
    return table_;
  }

  @Override
  public ProofTable visitTerm(Term term)
  {
    final String message = "ProofTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  @Override
  public ProofTable visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  @Override
  public ProofTable visitProofScript(ProofScript term)
  {
    try {
      table_.add(term);
    }
    catch (ProofTable.ProofTableException e) {
      throw new CztException(e);
    }
    return null;
  }

  @Override
  public ProofTable visitPara(Para para)
  {
    return null;
  }

  @Override
  public ProofTable visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    List<ProofTable> parentTables = new ArrayList<ProofTable>(zSect.getParent().size());
    for (Parent parent : zSect.getParent()) {
      ProofTable parentTable = get(parent.getWord(), ProofTable.class);
      parentTables.add(parentTable);
    }
    table_ = new ProofTable(getSectionInfo().getDialect(), name);
    try {
      table_.addParents(parentTables);
    }
    catch (InfoTable.InfoTableException e)
    {
      throw new CztException(e);
    }
    visit(zSect.getParaList());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }
}
