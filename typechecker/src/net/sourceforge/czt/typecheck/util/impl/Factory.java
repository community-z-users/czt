package net.sourceforge.czt.typecheck.util.impl;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * A factory for creating types that hide VariableTypes
 */
public class Factory
{
  /** The factory that it use to create wrapped types. */
  protected ZFactory factory_;

  public Factory()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  }

  public Factory(ZFactory factory)
  {
    factory_ = factory;
  }

  public PowerType createPowerType()
  {
    VariableType vType = createVariableType();
    PowerType result = createPowerType(vType);
    return result;
  }

  public PowerType createPowerType(Type2 type)
  {
    PowerType powerType = factory_.createPowerType(type);
    PowerType result = new PowerTypeImpl(powerType);
    return result;
  }

  public ProdType createProdType(List type)
  {
    ProdType prodType = factory_.createProdType(type);
    ProdType result = new ProdTypeImpl(prodType);
    return result;
  }

  public SchemaType createSchemaType()
  {
    VariableSignature vSignature = createVariableSignature();
    SchemaType result = createSchemaType(vSignature);
    return result;
  }

  public SchemaType createSchemaType(Signature signature)
  {
    SchemaType schemaType = factory_.createSchemaType(signature);
    SchemaType result = new SchemaTypeImpl(schemaType);
    return result;
  }

  public GenericType createGenericType(List declName,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType genericType =
      factory_.createGenericType(declName, type, optionalType);
    GenericType result = new GenericTypeImpl(genericType);
    return result;
  }

  public GenParamType createGenParamType(DeclName declName)
  {
    return factory_.createGenParamType(declName);
  }

  public GivenType createGivenType(DeclName declName)
  {
    return factory_.createGivenType(declName);
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair nameTypePair =
      factory_.createNameTypePair(declName, type);
    NameTypePair result = new NameTypePairImpl(nameTypePair);
    return result;
  }

  public NameSectTypeTriple createNameSectTypeTriple(DeclName declName,
                                                     String section,
                                                     Type type)
  {
    NameSectTypeTriple nameSectTypeTriple =
      factory_.createNameSectTypeTriple(declName, section, type);
    NameSectTypeTriple result =
      new NameSectTypeTripleImpl(nameSectTypeTriple);
    return result;
  }

  public Signature createSignature()
  {
    return factory_.createSignature();
  }

  public Signature createSignature(List nameTypePair)
  {
    return factory_.createSignature(nameTypePair);
  }

  public VariableSignature createVariableSignature()
  {
    return new VariableSignature();
  }

  public VariableType createVariableType()
  {
    return new VariableType();
  }

  public VariableType createVariableType(DeclName declName)
  {
    return new VariableType(declName);
  }

  public TypeAnn createTypeAnn()
  {
    return factory_.createTypeAnn();
  }

  public TypeAnn createTypeAnn(Type type)
  {
    TypeAnn typeAnn = factory_.createTypeAnn(type);
    TypeAnn result = new TypeAnnImpl(typeAnn);
    return result;
  }

  public SignatureAnn createSignatureAnn(Signature signature)
  {
    return factory_.createSignatureAnn(signature);
  }

  public SectTypeEnvAnn createSectTypeEnvAnn(List nameSecTypeTriple)
  {
    return factory_.createSectTypeEnvAnn(nameSecTypeTriple);
  }

  public DeclName createDeclName(String word, List stroke, String id)
  {
    return factory_.createDeclName(word, stroke, id);
  }

  public DeclName createDeclName(DeclName declName)
  {
    return createDeclName(declName.getWord(), declName.getStroke(),
                          declName.getId());
  }

  public RefName createRefName(String word, List stroke, DeclName declName)
  {
    return factory_.createRefName(word, stroke, declName);
  }

  public RefName createRefName(RefName refName)
  {
    return factory_.createRefName(refName.getWord(), refName.getStroke(),
                                  refName.getDecl());
  }

  public RefExpr createRefExpr(RefName refName, List expr, Boolean mixfix)
  {
    return factory_.createRefExpr(refName, expr, mixfix);
  }

  public MuExpr createMuExpr(SchText schText, Expr expr)
  {
    return factory_.createMuExpr(schText, expr);
  }

  public TupleExpr createTupleExpr(List expr)
  {
    return factory_.createTupleExpr(expr);
  }

  public InStroke createInStroke()
  {
    return factory_.createInStroke();
  }

  public OutStroke createOutStroke()
  {
    return factory_.createOutStroke();
  }

  public NextStroke createNextStroke()
  {
    return factory_.createNextStroke();
  }

  public NumStroke createNumStroke(Integer number)
  {
    return factory_.createNumStroke(number);
  }
}
