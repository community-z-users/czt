package net.sourceforge.czt.typecheck.util.typingenv;

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
    PowerTypeVisitor,
    GenTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    ProdTypeVisitor,
    UnknownTypeVisitor,
    DeclNameVisitor
{
  /** A ZFactory. */
  protected ZFactory factory_ = null;

  public CloningVisitor()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  }

  public Object visitPowerType(PowerType powerType)
  {
    Type baseType = powerType.getType();
    Type clonedBaseType = (Type) baseType.accept(this);
    PowerType clonedPowerType = factory_.createPowerType(clonedBaseType);
    return clonedPowerType;
  }

  public Object visitGenType(GenType genType)
  {
    DeclName declName = genType.getName();
    DeclName clonedDeclName = (DeclName) declName.accept(this);
    GenType clonedGenType = factory_.createGenType(clonedDeclName);
    return clonedGenType;
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

  public Object visitUnknownType(UnknownType unknownType)
  {
    return UnknownTypeImpl.create();
  }

  public Object visitDeclName(DeclName declName)
  {
    DeclName clonedDeclName =
      factory_.createDeclName(declName.getWord(),
			      declName.getStroke(),
			      declName.getId());
    return clonedDeclName;
  }
}
