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
 */
public enum Section
{
  /**
   * The name given to an anonymous specification when rule 12.2.2.1
   * (defined in the ISO Standard for Z) is applied.
   */
  ANONYMOUS("Specification"),

  /** The name of the prelude. */
  PRELUDE("prelude"),

  /** The name of the mathematical toolkit. */
  STANDARD_TOOLKIT("standard_toolkit"),
  NUMBER_TOOLKIT("number_toolkit"),
  FUNCTION_TOOLKIT("function_toolkit"),
  RELATION_TOOLKIT("relation_toolkit"),
  SEQUENCE_TOOLKIT("sequence_toolkit"),
  SET_TOOLKIT("set_toolkit"),

  /** Extra (Old-Z) toolkit names for Z. */
  FUZZ_TOOLKIT("fuzz_toolkit"),
  WHITESPACE("whitespace"),

  /** ZEves toolkits */
  ZEVES_PRELUDE("zeves_prelude"),
  ZSTATE_TOOLKIT("zstate_toolkit"),

  /** OZ toolkits */
  OZ_TOOLKIT("oz_toolkit"),

  /** Circus toolkits */
  CIRCUS_PRELUDE("circus_prelude"),
  CIRCUS_TOOLKIT("circus_toolkit"),

  /** VCG toolkits */
  DC_TOOLKIT("dc_toolkit"),
  FSB_TOOLKIT("fsb_toolkit"),
  REF_TOOLKIT("ref_toolkit"),
          ;

  private String name_;

  Section(String name)
  {
    name_ = name;
  }

  public String getName()
  {
    return name_;
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
