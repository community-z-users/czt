/*
  Copyright (C) 2006 Mark Utting
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
package net.sourceforge.czt.util;

import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;

/**
 * Common section names.
 *
 * @author Petra Malik
 * @author Leo Freitas
 */
public enum Section
{
  /**
   * The name given to an anonymous specification when rule 12.2.2.1
   * (defined in the ISO Standard for Z) is applied.
   */
  ANONYMOUS("Specification"),

  /** Z prelude and mathematical toolkits. */
  PRELUDE("z", "prelude"),
  STANDARD_TOOLKIT("z", "standard_toolkit"),
  NUMBER_TOOLKIT("z", "number_toolkit"),
  FUNCTION_TOOLKIT("z", "function_toolkit"),
  RELATION_TOOLKIT("z", "relation_toolkit"),
  SEQUENCE_TOOLKIT("z", "sequence_toolkit"),
  SET_TOOLKIT("z", "set_toolkit"),

  /** Extra toolkit names for Z */
  FUZZ_TOOLKIT("z", "fuzz_toolkit"),
  WHITESPACE("z", "whitespace"),
  ZSTATE_TOOLKIT("z", "zstate_toolkit"),

  /** Z Pattern toolkits */
  ORACLE_TOOLKIT("zpatt", "oracle_toolkit"),
  ZPATT_TOOLKIT("zpatt", "zpattern_toolkit"),

  /** ZEves toolkits */
  ZEVES_PRELUDE("zeves", "zeves_prelude"),
  ZEVES_TOOLKIT("zeves", "zeves_toolkit"),
  ZEVES_BAG_TOOLKIT("zeves", "zeves_bag_toolkit"),

  /** OZ toolkits */
  OZ_TOOLKIT("oz", "oz_toolkit"),
  WIZARD("oz", "wizard"),

  /** Circus toolkits */
  CIRCUS_PRELUDE("circus", "circus_prelude"),
  CIRCUS_TOOLKIT("circus", "circus_toolkit"),
  // circus bag toolkits not included as they are not std...?

  /** VCG toolkits */
  DC_TOOLKIT("dc_toolkit"),
  FSB_TOOLKIT("fsb_toolkit"),
  REF_TOOLKIT("ref_toolkit"),

  /** Rule toolkits */
  EXPANSION_RULES("z", "expansion_rules"),
  NORMALIZATION_RULES("z", "normalization_rules"),
  PREDICATE_NORMALIZATION_RULES("z", "predicate_normalization_rules"),
  SIMPLIFICATION_RULES("z", "simplification_rules"),
  UNFOLD("z", "unfod"),

  /** ZLive */
  PREPROCESS("z", "preprocess")
          ;

  private final String name_;
  private final String dialect_;

  Section(String name)
  {
    name_ = name;
    dialect_ = null;
  }

  Section(String dialect, String name)
  {
    name_ = name;
    dialect_ = dialect;
  }

  public String getName()
  {
    return name_;
  }

  // null = all
  public String getDialect()
  {
    return dialect_;
  }

  private static Set<String> stdSect_ = null;
  public static Set<String> standardSections()
  {
    if (stdSect_ == null)
    {
      stdSect_ = new TreeSet<String>();
      for(Section s : values())
      {
        stdSect_.add(s.getName());
      }
    }
    return Collections.unmodifiableSet(stdSect_);
  }
}
