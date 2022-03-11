/*
  Copyright 2006 Mark Utting
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z2b;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZUtils;

public class Classifier
{
  private int nrOfStateVars_ = -1;
  private List<NameSectTypeTriple> state_ =
    new ArrayList<NameSectTypeTriple>();
  private List<NameSectTypeTriple> init_ =
    new ArrayList<NameSectTypeTriple>();
  private List<NameSectTypeTriple> ops_ =
    new ArrayList<NameSectTypeTriple>();

  public Classifier(SectTypeEnvAnn sectTypeEnvAnn, String section)
  {
    for (NameSectTypeTriple triple : sectTypeEnvAnn.getNameSectTypeTriple()) {
      if (section.equals(triple.getSect()) &&
          triple.getType() instanceof PowerType) {
        PowerType powerType = (PowerType) triple.getType();
        if (powerType.getType() instanceof SchemaType) {
          SchemaType schemaType = (SchemaType) powerType.getType();
          Signature sig = schemaType.getSignature();
          int sigSize = sig.getNameTypePair().size();
          if (sigSize > 0) {
            @SuppressWarnings("unused")
			List<NameTypePair> undecorated = 
              ZUtils.subsignature(sig, null);
            List<NameTypePair> primed =
              ZUtils.subsignature(sig, NextStroke.class);
            if (primed.size() == sigSize) {
              init_.add(triple);
              nrOfStateVars_ = sigSize;
            }
          }
        }
      }
    }
    for (NameSectTypeTriple triple : sectTypeEnvAnn.getNameSectTypeTriple()) {
      if (section.equals(triple.getSect()) &&
          triple.getType() instanceof PowerType) {
        PowerType powerType = (PowerType) triple.getType();
        if (powerType.getType() instanceof SchemaType) {
          SchemaType schemaType = (SchemaType) powerType.getType();
          Signature sig = schemaType.getSignature();
          int sigSize = sig.getNameTypePair().size();
          if (sigSize > 0) {
            List<NameTypePair> undecorated = 
              ZUtils.subsignature(sig, null);
            List<NameTypePair> primed =
              ZUtils.subsignature(sig, NextStroke.class);
            if (undecorated.size() == nrOfStateVars_ &&
                sigSize == nrOfStateVars_ ) {
              state_.add(triple);
            }
            if (undecorated.size() == nrOfStateVars_ &&
                primed.size()== nrOfStateVars_) {
              ops_.add(triple);
            }
          }
        }
      }
    }
  }

  public List<NameSectTypeTriple> getState()
  {
    return state_;
  }

  public List<NameSectTypeTriple> getInit()
  {
    return init_;
  }

  public List<NameSectTypeTriple> getOps()
  {
    return ops_;
  }
}
