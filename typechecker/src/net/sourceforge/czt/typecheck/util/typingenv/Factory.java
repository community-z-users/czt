package net.sourceforge.czt.typecheck.util.typingenv;

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
    PowerType result = new VPowerTypeImpl();
    result.setType(type);
    return result;
  }

  public ProdType createProdType(List type)
  {
    ProdType result = new VProdTypeImpl();
    result.getType().addAll(type);
    return result;
  }

  public SchemaType createSchemaType(Signature signature)
  {
    SchemaType result = new VSchemaTypeImpl();
    result.setSignature(signature);
    return result;
  }

  public GenericType createGenericType(List declName,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType result = new VGenericTypeImpl();
    result.getName().addAll(declName);
    result.setType(type);
    result.setOptionalType(optionalType);
    return result;
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair result = new VNameTypePairImpl();
    result.setName(declName);
    result.setType(type);
    return result;
  }

  public TypeAnn createTypeAnn(Type type)
  {
    TypeAnn result = new VTypeAnnImpl();
    result.setType(type);
    return result;
  }
}
