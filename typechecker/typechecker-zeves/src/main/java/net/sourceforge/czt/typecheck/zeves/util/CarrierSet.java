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

package net.sourceforge.czt.typecheck.zeves.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.ast.ZEvesFactory;
import net.sourceforge.czt.zeves.visitor.ProofTypeVisitor;

/**
 * This class provides carrier sets for the new Circus types.
 * That is all Type2 implementations, which excludes GenericType.
 * Signatures must also be handled by CarrierSet since they are 
 * part of composite types. Carrier sets can be either expressions
 * (for all Z types) or schema texts (for all Z signatures). The same
 * applies to Circus.
 *
 * @author Leo Freitas
 */
public class CarrierSet 
  extends net.sourceforge.czt.typecheck.z.util.CarrierSet
  implements 
    ProofTypeVisitor<Term>
{    
  protected net.sourceforge.czt.zeves.util.Factory zevesFactory_;
  
  /** Creates a new instance of CarrierSet */
  public CarrierSet() 
  {
    this(DEFAULT_ALLOW_VARIABLE_TYPES);
  }

  public CarrierSet(boolean allowVariableTypes)
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(),
      new net.sourceforge.czt.zeves.impl.ZEvesFactoryImpl(),
      allowVariableTypes);
  }

  public CarrierSet(ZFactory zFactory, ZEvesFactory zevesFactory)
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(),
      new net.sourceforge.czt.zeves.impl.ZEvesFactoryImpl(),
      DEFAULT_ALLOW_VARIABLE_TYPES);
  }

  public CarrierSet(ZFactory zFactory, ZEvesFactory zevesFactory,
    boolean allowVariableTypes)
  {
    super(zFactory, allowVariableTypes);
    zevesFactory_ = new net.sourceforge.czt.zeves.util.Factory(zevesFactory);
  }
  
  @Override
  public Term visitProofType(ProofType term)
  {
    return term;
  }
 }
