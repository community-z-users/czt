package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * Updates types containing references to unknown types.
 */
public class TypeUpdatingVisitor
  implements
    PowerTypeVisitor,
    GenTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    ProdTypeVisitor,
    UnknownTypeVisitor
{
  /** A ZFactory. */
  protected ZFactory factory_ = null;

  /** The SectTypeEnv to get types. */
  protected SectTypeEnv sectTypeEnv_ = null;

  public TypeUpdatingVisitor(SectTypeEnv sectTypeEnv)
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    sectTypeEnv_ = sectTypeEnv;
  }

  public Object visitPowerType(PowerType powerType)
  {
    Type innerType = powerType.getType();

    if (innerType != null) {
      Type updatedType = (Type) innerType.accept(this);
      powerType.setType(updatedType);
    }
    return powerType;
  }

  public Object visitGenType(GenType genType)
  {
    return genType;
  }

  public Object visitGivenType(GivenType givenType)
  {
    return givenType;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    List nameTypePairs = new ArrayList();

    Signature signature = schemaType.getSignature();
    for (Iterator iter = signature.getNameTypePair().iterator();
         iter.hasNext(); ) {

      NameTypePair nameTypePair = (NameTypePair) iter.next();
      Type updatedType = (Type) nameTypePair.getType().accept(this);
      nameTypePair.setType(updatedType);
    }
    return schemaType;
  }

  public Object visitProdType(ProdType prodType)
  {
    List baseTypes = prodType.getType();
    for (int i = 0; i < baseTypes.size(); i++) {
      Type nextType = (Type) baseTypes.get(i);
      Type updatedType = (Type) nextType.accept(this);
      baseTypes.set(i, updatedType);
    }
    return prodType;
  }

  public Object visitUnknownType(UnknownType unknownType)
  {
    Type result = unknownType;
    DeclName declName = unknownType.getName();

    if (declName != null) {
      Type type = sectTypeEnv_.getType(declName);

      if (type != null) {
        if (unknownType.useBaseType()) {
          Type updatedType = (Type) type.accept(this);
          result = getBaseType(updatedType);
        }
        else {
          result = (Type) type.accept(this);
        }
      }
      else {
        result = unknownType;
      }
    }
    return result == null ? unknownType : result;
  }

  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown.
   */
  protected static Type getBaseType(Type type)
  {
    Type result = null;

    //if it's a PowerType, get the base type
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result = powerType.getType();
    }
    else if (type instanceof UnknownType) {
      result = type;
    }

    return result;
  }
}
