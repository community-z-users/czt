package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * Converts Types into Exprs.
 */
public class TypeFormatter
  implements
    PowerTypeVisitor,
    GenTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    ProdTypeVisitor,
    UnknownTypeVisitor
{
  /** A ZFactory. */
  protected ZFactory zFactory_ =
    new net.sourceforge.czt.z.impl.ZFactoryImpl();

  public Object visitPowerType(PowerType powerType)
  {
    Type type = powerType.getType();
    Expr expr = null;
    if (type != null) {
      expr = (Expr) type.accept(this);
    }
    PowerExpr result = zFactory_.createPowerExpr(expr);
    return result;
  }

  public Object visitGenType(GenType genType)
  {
    RefName refName =
      zFactory_.createRefName(genType.getName().getWord(),
                              genType.getName().getStroke(),
                              null);
    RefExpr result =
      zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
    return result;
  }

  public Object visitGivenType(GivenType givenType)
  {
    RefName refName =
      zFactory_.createRefName(givenType.getName().getWord(),
                              givenType.getName().getStroke(),
                              null);
    RefExpr result =
      zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
    return result;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    Signature signature = schemaType.getSignature();
    List nameTypePairs = signature.getNameTypePair();

    List decls = list();
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      Expr expr = (Expr) nameTypePair.getType().accept(this);
      List name = list(nameTypePair.getName());
      VarDecl varDecl = zFactory_.createVarDecl(name, expr);
      decls.add(varDecl);
    }

    SchText schText = zFactory_.createSchText(decls, null);
    SchExpr result = zFactory_.createSchExpr(schText);

    return result;
  }

  public Object visitProdType(ProdType prodType)
  {
    List exprs = list();

    List types = prodType.getType();
    for (Iterator iter = types.iterator(); iter.hasNext(); ) {
      Type type = (Type) iter.next();
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }

    ProdExpr result = zFactory_.createProdExpr(exprs);
    return result;
  }

  public Object visitUnknownType(UnknownType unknownType)
  {
    return null;
  }

  protected List list()
  {
    return new ArrayList();
  }

  protected List list(Object o)
  {
    List list = list();
    list.add(o);
    return list;
  }
}
