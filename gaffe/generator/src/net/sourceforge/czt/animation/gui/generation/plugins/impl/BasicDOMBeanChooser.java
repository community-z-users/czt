package net.sourceforge.czt.animation.gui.generation;

import java.awt.Dimension;

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.DOMBeanChooser;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.GenType;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;

import org.w3c.dom.Element;

public final class BasicDOMBeanChooser implements DOMBeanChooser {
  public Option[] getOptions() {return new Option[]{};};
  public String getHelp() {return "Generates the interface for one variable.";};  

  /**
   * @param specification Term containing the Spec, Sect, or Para the schema was found in.
   * @param schema The schema that contains the variable.
   * @param variableName The name of the variable the bean is for.
   * @param variableDeclaration The VarDecl in which the variable was declared.
   * @param availableSpace The amount of space available for the bean, or null if there is no limit.
   * @param sizeOut The actual size of the bean is recorded here by chooseBean.
   * @return The Element containing the XML to write to the file 
   */
  public Element chooseBean(Term specification, ConstDecl/*<SchExpr>*/ schema, 
			    DeclName variableName, VarDecl variableDeclaration) {
    
//      if(variableDeclaration.getExpr() instanceof RefExpr) {
//        RefExpr refExpr=variableDeclaration.getExpr();
//        RefName refName=refExpr.getRefName();
//        if(refExpr().getExpr().size()==0)
//  	if(refName.getStroke().size()==0) {
//  	  if(refName.getWord().equals("\u2124")) {
//  	    //Type is integer Z
//  	  } else if(refName.getWord().equals("\u2115")) {
//  	    //Type is natural N
//  	  } 
//  	} else if(refName.getStroke().size()==1
//  		  && refName.getStroke().get(0) instanceof NumStroke
//  		  && ((NumStroke)refName.getStroke().get(0)).getNumber()==1
//  		  &&refExpr().getRefName().getWord().equals("\u2115")) {
//  	    //Type is natural N1
//  	} 
      
//      }
    List declAnns=variableDeclaration.getAnns();
    for(Iterator it=declAnns.iterator();it.hasNext();) try {
      TypeAnn ann=(TypeAnn)it.next();
      Type type=ann.getType();
      if(type instanceof GenType) {
	break;
      } else if (type instanceof GivenType) {
	//given type/free type/number type.
	break; //textfield is fine for these
      } else if (type instanceof PowerType) {
	//set/relation/function type.
	//XXX create table using appropriate model
      } else if (type instanceof ProdType) {
	//tuple type.
	//XXX create table using appropriate model
      } else if (type instanceof SchemaType) {
	//schema type.
      } else break;
    } catch(ClassCastException ex) {
      continue;
    }
    //Deal with unknown/unhandled types:
    //XXX
    return null;
  };
};
