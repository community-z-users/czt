package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * Recursively clones terms.
 */
public class CloningVisitor
  implements
    GenericTypeVisitor,
    PowerTypeVisitor,
    GenParamTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    ProdTypeVisitor,
    VariableTypeVisitor,
    UnknownTypeVisitor,
    DeclNameVisitor
{
  /** A TypeFactory. */
  protected Factory factory_ = null;

  /** List of GenParamTypes if the type is a GenericType. */
  protected List params_ = null;

  public CloningVisitor(Factory factory)
  {
    factory_ = factory;
    params_ = new ArrayList();
  }

  public Object visitGenericType(GenericType genericType)
  {
    Type2 type = genericType.getType();
    Type2 optionalType = genericType.getOptionalType();
    List declNames = genericType.getName();

    List clonedNames = new ArrayList();
    for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
      DeclName declName = (DeclName) iter.next();
      DeclName clonedName = (DeclName) declName.accept(this);
      clonedNames.add(clonedName);
    }

    params_.addAll(clonedNames);

    Type2 clonedType = (Type2) type.accept(this);
    Type2 clonedOptionalType = null;
    if (optionalType != null) {
      clonedOptionalType = (Type2) optionalType.accept(this);
    }

    params_.clear();

    GenericType clonedGenericType =
      factory_.createGenericType(clonedNames, clonedType, clonedOptionalType);

    return clonedGenericType;
  }

  public Object visitPowerType(PowerType powerType)
  {
    Type baseType = powerType.getType();
    Type2 clonedBaseType = (Type2) baseType.accept(this);
    PowerType clonedPowerType = factory_.createPowerType(clonedBaseType);
    return clonedPowerType;
  }

  public Object visitGenParamType(GenParamType genParamType)
  {
    DeclName declName = genParamType.getName();
    DeclName clonedDeclName = (DeclName) declName.accept(this);
    GenParamType clonedGenParamType =
      factory_.createGenParamType(clonedDeclName);
    return clonedGenParamType;
  }

  public Object visitGivenType(GivenType givenType)
  {
    DeclName declName = givenType.getName();
    DeclName clonedDeclName = (DeclName) declName.accept(this);
    GivenType clonedGivenType = factory_.createGivenType(clonedDeclName);
    return clonedGivenType;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    List nameTypePairs = new ArrayList();

    Signature signature = schemaType.getSignature();
    for (Iterator iter = signature.getNameTypePair().iterator();
         iter.hasNext(); ) {

      NameTypePair nameTypePair = (NameTypePair) iter.next();
      DeclName clonedDeclName =
        (DeclName) nameTypePair.getName().accept(this);
      Type clonedType = (Type) nameTypePair.getType().accept(this);
      NameTypePair clonedNameTypePair =
        factory_.createNameTypePair(clonedDeclName, clonedType);
      nameTypePairs.add(clonedNameTypePair);
    }

    Signature clonedSignature = factory_.createSignature(nameTypePairs);
    SchemaType clonedSchemaType = factory_.createSchemaType(clonedSignature);

    return clonedSchemaType;
  }

  public Object visitProdType(ProdType prodType)
  {
    List baseTypes = prodType.getType();

    List clonedBaseTypes = new ArrayList();
    for (Iterator iter = baseTypes.iterator(); iter.hasNext(); ) {
      Type nextType = (Type) iter.next();
      Type clonedType = (Type) nextType.accept(this);
      clonedBaseTypes.add(clonedType);
    }

    ProdType clonedProdType = factory_.createProdType(clonedBaseTypes);
    return clonedProdType;
  }

  public Object visitVariableType(VariableType vType)
  {
    VariableType clonedVType = factory_.createVariableType(vType.getName());
    if (vType.getValue() != vType) {
      clonedVType.setValue(vType.getValue());
    }
    return clonedVType;
  }

  public Object visitUnknownType(UnknownType unknownType)
  {
    return unknownType;
  }

  public Object visitDeclName(DeclName declName)
  {
    DeclName clonedDeclName =
      factory_.createDeclName(declName.getWord(),
                              declName.getStroke(),
                              declName.getId());

    //include type annotations
    TypeAnn typeAnn = (TypeAnn) declName.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      clonedDeclName.getAnns().add(typeAnn);
    }

    return clonedDeclName;
  }
}
