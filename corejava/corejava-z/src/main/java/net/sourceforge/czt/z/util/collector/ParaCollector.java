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
package net.sourceforge.czt.z.util.collector;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;

/**
 * <p>
 * Collector class for the Para term hierarchy tree.
 * </p>
 * <p>
 * The collection occurs as follows:<br>
 * <ul>
 *      <li>NarrPara: Simply includes the term in a list.</li>
 *      <li>UnparsedPara: Simply includes the term in a list.</li>
 *      <li>LatexMarkupPara: Simply includes the term in a list.</li>
 *      <li>GivenPara: Simply includes the term in a list.</li>
 *      <li>OptempPara: Simply includes the term in a list.</li>
 *      <li>AxPara: Creates a AxDefElements and collects all its items.<br>
 *      <p>
 *      Each AxDefElements is as list of AxDefElements.
 *      </p>
 *      <li>FreePara: For each declared free type, create a map between its name an a list of its branches.</li>
 * </ul>
 * Note that for OptempPara and others, we have simply chosen not to go
 * deeper into their details, are they seem unimportant. Experience and practice
 * might require those to be added as separate element classes with specific
 * access facilities.
 * </p>
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class ParaCollector extends BaseCollector<ZSect> implements
        NarrParaVisitor<ZSect>, LatexMarkupParaVisitor<ZSect>,
        UnparsedParaVisitor<ZSect>,
        GivenParaVisitor<ZSect>, OptempParaVisitor<ZSect>,
        ConjParaVisitor<ZSect>, AxParaVisitor<ZSect>,
        FreeParaVisitor<ZSect>
{

  protected final List<NarrPara> fNarrPara;
  protected final List<UnparsedPara> fUnparsedPara;
  protected final List<LatexMarkupPara> fLatexMarkupPara;
  protected final List<GivenPara> fGivenPara;
  protected final List<OptempPara> fOptempPara;
  protected final Map<String, ConjPara> fConjPara;
  protected final List<AxDefElements> fAxPara;
  protected final Map<String, List<Branch>> fFreeTypes;
  protected final Map<String, SchemaElements> fSchemas;

  /** Creates a new instance of ParaCollector */
  ParaCollector()
  {
    super();
    fNarrPara = new ArrayList<NarrPara>();
    fUnparsedPara = new ArrayList<UnparsedPara>();
    fLatexMarkupPara = new ArrayList<LatexMarkupPara>();

    fGivenPara = new ArrayList<GivenPara>();
    fOptempPara = new ArrayList<OptempPara>();
    fConjPara = new TreeMap<String, ConjPara>();
    fAxPara = new ArrayList<AxDefElements>();
    // TODO: Change here to FreeTypeElements and include Expr collection!
    fFreeTypes = new TreeMap<String, List<Branch>>();
    fSchemas = new TreeMap<String, SchemaElements>();
  }

  /* Special Para */
  @Override
  public ZSect visitNarrPara(NarrPara term)
  {
    fNarrPara.add(term);
    return null;
  }

  @Override
  public ZSect visitLatexMarkupPara(LatexMarkupPara term)
  {
    fLatexMarkupPara.add(term);
    return null;
  }

  @Override
  public ZSect visitUnparsedPara(UnparsedPara term)
  {
    fUnparsedPara.add(term);
    return null;
  }

  /* Z Related */
  @Override
  public ZSect visitGivenPara(GivenPara term)
  {
    fGivenPara.add(term);
    return null;
  }

  @Override
  public ZSect visitFreePara(FreePara term)
  {
    for (Freetype ft : ZUtils.assertZFreetypeList(term.getFreetypeList()))
    {
      List<Branch> old = fFreeTypes.put(ft.getZName().toString(), ZUtils.assertZBranchList(ft.getBranchList()));
      if (old != null)
      {
        CztLogger.getLogger(ParaCollector.class).fine("Recalculating information for free-type para branches");
      }
      //assert old == null : "repeated free type -> " + ft.getZDeclName();
    }
    return null;
  }

  @Override
  public ZSect visitOptempPara(OptempPara term)
  {
    fOptempPara.add(term);
    return null;
  }

  @Override
  public ZSect visitConjPara(ConjPara term)
  {
    fConjPara.put(term.getName(), term);
    return null;
  }

  @Override
  public ZSect visitAxPara(AxPara term)
  {
    if (term.getBox().equals(Box.AxBox) ||
        ZUtils.isAbbreviation(term))
    {
      AxDefElements ape = new AxDefElements();
      ape.collect(term);
      fAxPara.add(ape);
    } 
    else if (term.getBox().equals(Box.SchBox) ||
             ZUtils.isHorizontalSchema(term))
      // TODO: this does not cover schema calculus: S == R \land T
    {
      SchemaElements se = new SchemaElements();
      se.collect(term);
      SchemaElements old = fSchemas.put(se.getName(), se);
      if (old != null)
      {
        CztLogger.getLogger(ParaCollector.class).fine("Recalculating information for " + old.getName());
      }
      //assert old == null : "repeated schema -> " + se.getName();
    }
    else
    {
      assert !ZUtils.isSimpleSchema(term) && !ZUtils.isAbbreviation(term);
      CztLogger.getLogger(ParaCollector.class).fine("Not yet collecting schema calculus : " + term);
      //assert old == null : "repeated abbreviation -> " + ae.getName();
    }
    return null;
  }
}
