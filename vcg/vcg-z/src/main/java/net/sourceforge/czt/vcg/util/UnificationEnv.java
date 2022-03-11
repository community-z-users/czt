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
package net.sourceforge.czt.vcg.util;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.GenParamType;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * Provides unification of types.
 */
public class UnificationEnv
{

  protected enum UResult
  {

    SUCC, FAIL;

    /**
     * A conjunction of two UResults.
     */
    public static UResult conj(UResult left, UResult right)
    {
      UResult result = SUCC;
      if (left == FAIL || right == FAIL)
      {
        result = FAIL;
      }
      return result;
    }
  };

  public UnificationEnv()
  {
  }

  public UResult unify(Signature sigA, Signature sigB)
  {
    UResult result = unifySignature(sigA, sigB);
    return result;
  }

  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = UResult.FAIL;

    //if the object IDs are the same, there is no need to
    //unify. Variable types are a special case
    if (typeA == typeB)
    {
      return UResult.SUCC;
    }

    if (isGivenType(typeA) && isGivenType(typeB))
    {
      result = unifyGivenType(givenType(typeA), givenType(typeB));
    }
    else if (isPowerType(typeA) && isPowerType(typeB))
    {
      result = unifyPowerType(powerType(typeA), powerType(typeB));
    }
    else if (isProdType(typeA) && isProdType(typeB))
    {
      result = unifyProdType(prodType(typeA), prodType(typeB));
    }
    else if (isSchemaType(typeA) && isSchemaType(typeB))
    {
      result = unifySchemaType(schemaType(typeA), schemaType(typeB));
    }
    else if (isGenParamType(typeA) && isGenParamType(typeB))
    {
      result = unifyGenParamType(genParamType(typeA), genParamType(typeB));
    }
    return result;
  }

  protected UResult unifyGivenType(GivenType givenTypeA, GivenType givenTypeB)
  {
    UResult result = givenTypeA.equals(givenTypeB) ? UResult.SUCC : UResult.FAIL;
    return result;
  }

  protected UResult unifyPowerType(PowerType powerTypeA, PowerType powerTypeB)
  {
    //try to unify the inner types
    UResult result = unify(powerTypeA.getType(), powerTypeB.getType());
    return result;
  }

  protected UResult unifyProdType(ProdType prodTypeA, ProdType prodTypeB)
  {
    UResult result = UResult.SUCC;

    List<Type2> typesA = prodTypeA.getType();
    List<Type2> typesB = prodTypeB.getType();

    //if the size is not equal, fail
    assert typesA.size() > 1;
    assert typesB.size() > 1;
    if (typesA.size() == typesB.size())
    {
      for (int i = 0; i < typesA.size(); i++)
      {
        // carry on with everybody, even if FAIL is found?
        UResult unified = unify(typesA.get(i), typesB.get(i));
        if (UResult.FAIL.equals(unified))
        {
          result = UResult.FAIL;
          break; //?
        }        
      }
    }
    else
    {
      result = UResult.FAIL;
    }

    return result;
  }

  protected UResult unifyGenParamType(GenParamType genParamTypeA,
          GenParamType genParamTypeB)
  {
    UResult result = genParamTypeA.equals(genParamTypeB) ? UResult.SUCC : UResult.FAIL;
    return result;
  }

  protected UResult unifySchemaType(SchemaType schemaTypeA,
          SchemaType schemaTypeB)
  {
    //try to unify the two signatures
    Signature sigA = schemaTypeA.getSignature();
    Signature sigB = schemaTypeB.getSignature();
    UResult result = unifySignature(sigA, sigB);
    return result;
  }

  //unify 2 signatures
  protected UResult unifySignature(Signature sigA, Signature sigB)
  {
    UResult result = UResult.SUCC;

    if (sigA != sigB)
    {
      result = unifyResolvedSignature(sigA, sigB);
    }
    return result;
  }

  // for signatures without variable types
  protected UResult unifyResolvedSignature(Signature sigA, Signature sigB)
  {
    Map<String, NameTypePair> mapA = new HashMap<String, NameTypePair>();
    Map<String, NameTypePair> mapB = new HashMap<String, NameTypePair>();
    for (NameTypePair pair : sigA.getNameTypePair())
    {
      //mapA.put(pair.getZName().toString(), pair);
      mapA.put(ZUtils.toStringZName(pair.getZName()), pair);
    }
    for (NameTypePair pair : sigB.getNameTypePair())
    {
      //mapB.put(pair.getZName().toString(), pair);
      mapB.put(ZUtils.toStringZName(pair.getZName()), pair);
    }

    UResult resultA = unifySignatureAux(mapA, mapB);
    UResult resultB = unifySignatureAux(mapB, mapA);
    UResult result = UResult.conj(resultA, resultB);
    return result;
  }

  //unify the signature "one-way". Use hashmaps for efficiency
  protected UResult unifySignatureAux(Map<String, NameTypePair> mapA,
          Map<String, NameTypePair> mapB)
  {
    UResult result = UResult.SUCC;
    Set<Map.Entry<String, NameTypePair>> entrySet = mapA.entrySet();
    for (Map.Entry<String, NameTypePair> first : entrySet)
    {
      NameTypePair second = mapB.get(first.getKey());
      if (second == null)
      {
        result = UResult.FAIL;
      }
      else
      {
        UResult unified = unify(unwrapType(first.getValue().getType()),
                unwrapType(second.getType()));
        if (UResult.FAIL.equals(unified))
        {
          result = UResult.FAIL;
        }
      }
    }
    return result;
  }

  /**
   * If this is a generic type, get the type without the
   * parameters. If not a generic type, return the type.
   * @param type the <code>Type</code> to unwrap
   * @return if <code>type</code> is a generic type, return the inner
   * <code>Type2</code> object. Otherwise, return <code>type</code>
   */
  public static Type2 unwrapType(Type type)
  {
    Type2 result = null;
    if (type instanceof GenericType)
    {
      GenericType gType = (GenericType) type;
      Type2 optType = null;
      if (gType.getType().size() > 1)
      {
        optType = gType.getType().get(1);
      }
      result = optType == null ? gType.getType().get(0) : optType;
    }
    else
    {
      result = (Type2) type;
    }

    return result;
  }

  /**
   * returns true if the given type is \power(SchType)
   * @param type
   * @return
   */
  protected static boolean isSchemaPowerType(Type type)
  {
    Type2 type2 = unwrapType(type);
    boolean result = (type2 instanceof PowerType) &&
      (powerType(type2).getType() instanceof SchemaType);
    return result;
  }

  protected static boolean isType2(Term term)
  {
    return (term instanceof Type2);
  }

  protected static boolean isSchemaType(Term term)
  {
    return (term instanceof SchemaType);
  }

  protected static boolean isPowerType(Term term)
  {
    return (term instanceof PowerType);
  }

  protected static boolean isGivenType(Term term)
  {
    return (term instanceof GivenType);
  }

  protected static boolean isGenericType(Term term)
  {
    return (term instanceof GenericType);
  }

  protected static boolean isGenParamType(Term term)
  {
    return (term instanceof GenParamType);
  }

  protected static boolean isProdType(Term term)
  {
    return (term instanceof ProdType);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Term term)
  {
    return (SchemaType) term;
  }

  //non-safe typecast
  protected static PowerType powerType(Term term)
  {
    return (PowerType) term;
  }

  //non-safe typecast
  protected static GivenType givenType(Term term)
  {
    return (GivenType) term;
  }

  //non-safe typecast
  protected static GenericType genericType(Term term)
  {
    return (GenericType) term;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Term term)
  {
    return (GenParamType) term;
  }

  //non-safe typecast
  protected static ProdType prodType(Term term)
  {
    return (ProdType) term;
  }

  protected void debug(Object o1, Object o2)
  {
    System.err.println("unify(" + o1 + ", " + o2 + ")");
  }
}
