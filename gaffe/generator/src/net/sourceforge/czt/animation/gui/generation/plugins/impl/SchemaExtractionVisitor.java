package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.core.ast.AxPara;
import net.sourceforge.czt.core.ast.ConstDecl;
import net.sourceforge.czt.core.ast.DeclName;
import net.sourceforge.czt.core.ast.InStroke;
import net.sourceforge.czt.core.ast.NextStroke;
import net.sourceforge.czt.core.ast.NumStroke;
import net.sourceforge.czt.core.ast.OutStroke;
import net.sourceforge.czt.core.ast.Para;
import net.sourceforge.czt.core.ast.SchExpr;
import net.sourceforge.czt.core.ast.Spec;
import net.sourceforge.czt.core.ast.Stroke;
import net.sourceforge.czt.core.ast.Term;
import net.sourceforge.czt.core.ast.ZSect;

import net.sourceforge.czt.core.jaxb.JaxbXmlReader;

import net.sourceforge.czt.core.visitor.AxParaVisitor;
import net.sourceforge.czt.core.visitor.ConstDeclVisitor;
import net.sourceforge.czt.core.visitor.SpecVisitor;
import net.sourceforge.czt.core.visitor.ZSectVisitor;

final class SchemaExtractionVisitor implements SpecVisitor, ZSectVisitor, AxParaVisitor, ConstDeclVisitor {
  private Vector schemas=null;
  public List getSchemas(Term term) {
    schemas=new Vector();
    term.accept(this);
    return new Vector(schemas);
  };

  private void visitAllOf(List list, Class clazz) {
    for (Iterator it=list.iterator(); it.hasNext();) {
      Object item=it.next();
      if (item != null && clazz.isInstance(item))
	if(item instanceof Term)
	  ((Term)item).accept(this);
    }
  };

  public Object visitSpec(Spec zedObject) {
    visitAllOf(zedObject.getSect(),ZSect.class);   return null;
  };//Only interested in ZSects
  public Object visitZSect(ZSect zedObject) {
    visitAllOf(zedObject.getPara(),AxPara.class);  return null;
  };//Containing AxParas
  public Object visitAxPara(AxPara zedObject) {//Only interested in AxParas
    visitAllOf(zedObject.getSchText().getDecl(),ConstDecl.class); return null;
  };//Containing ConstDecls
  public Object visitConstDecl(ConstDecl zedObject) {//Only interested in ConstDecls with RHS=SchExpr
    if(zedObject.getExpr() instanceof SchExpr) schemas.add(zedObject);
    return null;
  };

  public static void main(String[] args) {
    if(args.length!=1) {
      System.err.println("Requires one argument - specification file.");
      return;
    }
    
    JaxbXmlReader reader=new JaxbXmlReader();
    Term term=reader.read(new File(args[0]));
    
    SchemaExtractionVisitor extracter=new SchemaExtractionVisitor();
    List schemas=extracter.getSchemas(term);
    for(Iterator it=schemas.iterator();it.hasNext();) {
      ConstDecl schema=(ConstDecl)it.next();
      DeclName declName=schema.getDeclName();
      SchExpr schExpr=(SchExpr)schema.getExpr();
      System.err.println("Schema "+Name2String.toString(declName));      
    };
  };
};





