package net.sourceforge.czt.typecheck.util;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * An annotation for recording undeclared reference names.
 */
public class Factory
  extends net.sourceforge.czt.z.impl.ZFactoryImpl
{
  public Factory()
  {
    super();
  }

  public PowerType createPowerType(Type2 type)
  {
    PowerType result = super.createPowerType(type);
    addPossibleDependent(result, type);
    return result;
  }

  public ProdType createProdType(List types)
  {
    ProdType result = super.createProdType(types);
    for (Iterator iter = types.iterator(); iter.hasNext(); ) {
      Type2 type = (Type2) iter.next();
      addPossibleDependent(result, type);
    }

    return result;
  }

  public SchemaType createSchemaType(Signature signature)
  {
    SchemaType result = super.createSchemaType(signature);
    addPossibleDependent(result, signature);
    return result;
  }

  public GenericType createGenericType(List declName,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType result =
      super.createGenericType(declName, type, optionalType);
    addPossibleDependent(result, type);
    addPossibleDependent(result, optionalType);
    return result;
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair result = super.createNameTypePair(declName, type);
    addPossibleDependent(result, type);
    return result;
  }

  public TypeAnn createTypeAnn(Type type)
  {
    TypeAnn result = super.createTypeAnn(type);
    addPossibleDependent(result, type);
    return result;
  }

  protected void addPossibleDependent(Object parent, Object child)
  {
    if (child != null && child instanceof VariableType) {
      VariableType vType = (VariableType) child;
      if (!vType.getDependent().contains(parent)) {
        vType.getDependent().add(parent);
      }
    }

    if (child != null && child instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) child;
      if (!vSig.getDependent().contains(parent)) {
        vSig.getDependent().add(parent);
      }
    }
  }
}
