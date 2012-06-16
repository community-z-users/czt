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

package net.sourceforge.czt.typecheck.z.impl;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.logging.Logger;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.util.Section;

/**
 *
 * @author Leo Freitas
 * @date Nov 17, 2011
 */
public class SectSummaryAnn implements TypecheckPropertiesKeys
{
  private final String sectName_;
  protected final List<Pair<String, Integer>> summary_;
  protected boolean includeParents_;
  protected boolean includeStandardSections_;

  public SectSummaryAnn(String sectName)
  {
    assert sectName != null && !sectName.isEmpty();
    sectName_ = sectName;
    includeParents_ = true;
    includeStandardSections_ = false;
    summary_ = new ArrayList<Pair<String, Integer>>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }

  public void generateSummary(SectionManager sm, ZSect zs)
  {
    assert String.valueOf(zs.getName()).equals(sectName_);
    if (summary_.isEmpty())
    {
      doSummarise(sm, zs);
    }
  }

  protected void doSummarise(SectionManager sm, ZSect zs)
  {
    assert String.valueOf(zs.getName()).equals(sectName_);
    assert summary_.isEmpty();
    summary_.add(Pair.getPair("Parents", ParentSummary.create(sm).count(zs)));
    summary_.add(Pair.getPair("Paragraphs", ParaSummary.create(sm).count(zs)));
    int cnt = AxParaSummary.create(sm, Box.SchBox).count(zs);
    if (cnt > 0)
      summary_.add(Pair.getPair("Schemas", cnt));
    cnt = AxParaSummary.create(sm, Box.AxBox).count(zs);
    if (cnt > 0)
      summary_.add(Pair.getPair("Axioms", cnt));
    cnt = SubParaSummary.create(sm, ConjPara.class).count(zs);
    if (cnt > 0)
      summary_.add(Pair.getPair("Conjectures", cnt));
  }

  public List<Pair<String, Integer>> getSectSummary()
  {
    return Collections.unmodifiableList(summary_);
  }

  public String getSectName()
  {
    return sectName_;
  }

  public static interface Summarise
  {
    public int count(ZSect zs);
    public boolean includeParents();
    public boolean includeStandardSections();
  }

  public static abstract class AbstractSummary implements Summarise
  {
    protected final SectionManager sm_;
    protected final boolean includeParents_;
    protected final boolean includeStandardSections_;
    private final Set<ZSect> visitedSects = new HashSet<ZSect>();

    protected AbstractSummary(SectionManager sm)
    {
      sm_ = sm;
      includeParents_ = sm_.hasProperty(PROP_TYPECHECK_SUMMARY_INCLUDE_PARENTS) ?
        sm_.getBooleanProperty(PROP_TYPECHECK_SUMMARY_INCLUDE_PARENTS) : PROP_TYPECHECK_SUMMARY_INCLUDE_PARENTS_DEFAULT;
      includeStandardSections_ = sm_.hasProperty(PROP_TYPECHECK_SUMMARY_INCLUDE_STDSECTS) ?
        sm_.getBooleanProperty(PROP_TYPECHECK_SUMMARY_INCLUDE_STDSECTS) : PROP_TYPECHECK_SUMMARY_INCLUDE_STDSECTS_DEFAULT;
    }

    protected AbstractSummary(SectionManager sm, boolean inclParents, boolean inclStdSects)
    {
      sm_ = sm;
      includeParents_ = inclParents;
      includeStandardSections_ = inclStdSects;
    }

    protected abstract int countSection(ZSect zs);

    @Override
    public boolean includeParents()
    {
      return includeParents_;
    }

    @Override
    public boolean includeStandardSections()
    {
      return includeStandardSections_;
    }
    
    @Override
    public int count(ZSect zs)
    {
      if (visitedSects.contains(zs)) {
        // a cyclic relationship - already visited
        return 0;
      }
      visitedSects.add(zs);
      
      int result = countSection(zs);
      for(Parent parent : zs.getParent())
      {
        final String parentSectName = parent.getWord();
        final Key<ZSect> kzs = new Key<ZSect>(parentSectName, ZSect.class);
        if (includeParents() &&
            (includeStandardSections() ||
             !Section.standardSections().contains(parentSectName)) &&
            sm_.isCached(kzs))
        {
          try
          {
            ZSect pzs = sm_.get(kzs);
            result += count(pzs);
          }
          catch (CommandException ex)
          {
            Logger.getLogger(SectSummaryAnn.class.getName()).log(
                    Level.WARNING, "Could not retrieve cached parent section {0} of {1}", new Object[]{parentSectName, zs.getName()});
          }
        }
      }
      return result;
    }
  }

  public static class ParentSummary extends AbstractSummary
  {
    private final Set<String> transitiveParents_ = new TreeSet<String>();

    protected ParentSummary(SectionManager sm)
    {
      super(sm);
    }
    
    @Override
    protected int countSection(ZSect zs)
    {
      for(Parent p : zs.getParent())
      {
        transitiveParents_.add(p.getWord());
      }
      return -1;
    }

    /**
     * Parent counting is slightly different: we need to go through parents themselves
     * during the count, and there might be repeated parents, if not cyclic (e.g., type
     * correct assumption).
     * @param zs
     * @return
     */
    @Override
    public int count(ZSect zs)
    {
      // ignore result, but collect the data from transitiveParents set - avoids repeated parents
      super.count(zs);
      //System.out.println("Transitive parents = " + transitiveParents_.toString());
      return transitiveParents_.size();
    }

//    public static Summarise create(SectionManager sm, boolean inclParents, boolean inclStdSects)
//    {
//      return new ParentSummary(sm, inclParents, inclStdSects);
//    }

    public static Summarise create(SectionManager sm)
    {
      return new ParentSummary(sm);
    }
  }

  public static class ParaSummary extends AbstractSummary
  {
    
    protected ParaSummary(SectionManager sm)
    {
      super(sm);
    }

    @Override
    protected int countSection(ZSect zs)
    {
      return zs.getZParaList().size();
    }
    
    @Override
    public int count(ZSect zs)
    {
      int result = super.count(zs);
      assert result >= 0;
      return result;
    }
 
    public static Summarise create(SectionManager sm)
    {
      return new ParaSummary(sm);
    }
  }

  public static class SubParaSummary extends ParaSummary
  {
    private final Class<? extends Para> paraCls_;

    protected SubParaSummary(SectionManager sm, Class<? extends Para> paraCls)
    {
      super(sm);
      paraCls_ = paraCls;
    }

    protected boolean shouldCount(Para p)
    {
      return paraCls_.isInstance(p);
    }

    @Override
    protected int countSection(ZSect zs)
    {
      int result = 0;
      for(Para p : zs.getZParaList())
      {
        if (shouldCount(p))
          result++;
      }
      return result;
    }

    public static Summarise create(SectionManager sm, Class<? extends Para> paraCls)
    {
      return new SubParaSummary(sm, paraCls);
    }
  }

  public static class AxParaSummary extends SubParaSummary
  {
    private final Box paraBox_;

    protected AxParaSummary(SectionManager sm, Box paraBox)
    {
      super(sm, AxPara.class);
      paraBox_ = paraBox;
    }

    @Override
    protected boolean shouldCount(Para p)
    {
      //return super.shouldCount(p) && ((AxPara)p).getBox().equals(paraBox_));
      return (p instanceof AxPara && ((AxPara)p).getBox().equals(paraBox_));
    }
    
    public static Summarise create(SectionManager sm, Box paraBox)
    {
      return new AxParaSummary(sm, paraBox);
    }
  }
}
