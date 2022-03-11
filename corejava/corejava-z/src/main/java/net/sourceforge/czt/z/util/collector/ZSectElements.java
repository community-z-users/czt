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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class ZSectElements extends BaseElements<ZSect>
{

  private ZSect fZSect;
  private final ParaCollector fParaCollector;
  private final Set<String> fSectDone;
  private final GetSect fManager;

  ZSectElements(GetSect manager)
  {
    super();
    assert manager != null;
    fZSect = null;
    fManager = manager;
    fParaCollector = new ParaCollector();
    fSectDone = new TreeSet<String>();
  }

  @Override
  public void collect(ZSect term)
  {
    fZSect = term;
    setName(term.getName());
    processParents(term.getParent());
  }

  private void processParents(List<Parent> parents)
  {
    for (Parent parent : parents)
    {
      String sectionName = parent.getWord();
      if (!fSectDone.contains(sectionName))
      {
        ZSect temp = fManager.getZSect(sectionName);
        if (temp != null)
        {
          processSection(temp);
          processParents(temp.getParent());
        }
        else
        {
          CztLogger.getLogger(ParaCollector.class).warning("Could not retrieve parent section " + sectionName + " during ZSectElements collection");
        }
      }
    }
  }

  private void processSection(ZSect sect)
  {
    fParaCollector.visit(sect);
    fSectDone.add(sect.getName());
  }

  public ZSect getZSect()
  {
    return fZSect;
  }

  public List<NarrPara> getNarrPara()
  {
    return Collections.unmodifiableList(fParaCollector.fNarrPara);
  }

  public List<UnparsedPara> getUnparsedPara()
  {
    return Collections.unmodifiableList(fParaCollector.fUnparsedPara);
  }

  public List<LatexMarkupPara> getLatexMarkupPara()
  {
    return Collections.unmodifiableList(fParaCollector.fLatexMarkupPara);
  }

  public List<GivenPara> getGivenPara()
  {
    return Collections.unmodifiableList(fParaCollector.fGivenPara);
  }

  public List<OptempPara> getOptempPara()
  {
    return Collections.unmodifiableList(fParaCollector.fOptempPara);
  }

  public Collection<ConjPara> getConjPara()
  {
    return Collections.unmodifiableCollection(fParaCollector.fConjPara.values());
  }

  public List<AxDefElements> getAxPara()
  {
    return Collections.unmodifiableList(fParaCollector.fAxPara);
  }

  public boolean containsFreeType(String name)
  {
    return fParaCollector.fFreeTypes.containsKey(name);
  }

  public Set<String> getFreeTypes()
  {
    return Collections.unmodifiableSet(fParaCollector.fFreeTypes.keySet());
  }

  public List<Branch> getFreeTypeBranches(String name)
  {
    return Collections.unmodifiableList(fParaCollector.fFreeTypes.get(name));
  }

  public boolean containsSchema(String name)
  {
    return fParaCollector.fSchemas.containsKey(name);
  }

  public Set<String> getSchemas()
  {
    return Collections.unmodifiableSet(fParaCollector.fSchemas.keySet());
  }

  public SchemaElements getSchemaElements(String name)
  {
    return fParaCollector.fSchemas.get(name);
  }

  public static interface GetSect
  {
    public ZSect getZSect(String name);
  }
}
