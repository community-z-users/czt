/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.OutputStream;

import java.net.URL;

import java.util.Iterator;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerConfigurationException;

import javax.xml.transform.dom.DOMSource; 

import javax.xml.transform.stream.StreamResult;

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.DOMBeanChooser;
import net.sourceforge.czt.animation.gui.generation.plugins.DOMInterfaceGenerator;
import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

class BasicInterfaceGenerator implements DOMInterfaceGenerator {
  Term specification;
  List/*<ConstDecl<SchExpr>>*/ schemas;
  ConstDecl/*<SchExpr>*/ stateSchema;
  ConstDecl/*<SchExpr>*/ initSchema;
  List/*<ConstDecl<SchExpr>>*/ operationSchemas;
  VariableExtractor variableExtractor;
  DOMBeanChooser beanChooser;
  Document document;
  /**
   * {@inheritDoc}
   */
  public synchronized void generateInterface(Term specification, URL specURL,
					     List/*<ConstDecl<SchExpr>>*/ schemas, 
					     ConstDecl/*<SchExpr>*/ stateSchema, 
					     ConstDecl/*<SchExpr>*/ initSchema, 
					     List/*<ConstDecl<SchExpr>>*/ operationSchemas, 
					     VariableExtractor variableExtractor,
					     DOMBeanChooser beanChooser, 
					     OutputStream os) {
    this.specification=specification;
    this.schemas=schemas;
    this.stateSchema=stateSchema;
    this.initSchema=initSchema;
    this.operationSchemas=operationSchemas;
    this.variableExtractor=variableExtractor;
    this.beanChooser=beanChooser;

    try {
      document=DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
    } catch (ParserConfigurationException ex) {
      throw new Error("exception while parsing the specification.",ex);//XXX should be some kind of exception
    };
    
    Element javaElement
      =ce("java",new String[] {"version","class"},new String[] {"1.4.2","java.beans.XMLDecoder"},
      ce_property("owner",new Element[] {
	ce_property("history",ce_object("net.sourceforge.czt.animation.gui.history.BasicHistory",null)),
	ce_property("initScript",ce_string("XXX")),
	ce_property("initScriptLanguage",ce_string("javascript")),
	ce_property("stateSchema",ce_string(Name2String.toString(stateSchema.getDeclName()))),
	ce_property("initSchema",ce_string(Name2String.toString(initSchema.getDeclName())))
      }));
    if(specURL!=null)
      javaElement.appendChild(ce_property("specificationURL",ce_string(specURL.toExternalForm())));
    
    createForms();
    
    document.appendChild(javaElement);
    try {
    TransformerFactory.newInstance().newTransformer()
      .transform(new DOMSource(document), new StreamResult(os));
    } catch (TransformerConfigurationException ex) {
      //XXX should be an exception of some kind
      throw new Error("exception while creating Transformer with which to write the interface.",ex);
    } catch (TransformerException ex) {
      //XXX should be an exception of some kind
      throw new Error("exception while creating Transformer with which to write the interface.",ex);
    };
    
  };
  
  protected void createForms() {
    createStateForm();
    for(Iterator it=operationSchemas.iterator();it.hasNext();) {
      ConstDecl/*<SchExpr>*/ operationSchema=(ConstDecl/*<SchExpr>*/)it.next();
      createInputForm(operationSchema);
      createOutputForm(operationSchema);
    };
  };
  protected void createStateForm() {
    //Create history button panel
    //Create operation button panel
    //Create variable panel
    //Arrange them
  };

  protected void createHistoryPanel(Element form, Element wrappers, Element links) {
    form.appendChild(ce_method("addBean",ce_object("javax.swing.JPanel","historyButtonPanel",
						   (Element[])null)));

    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JButton","historyPreviousSolutionSetButton",(Element[])null),
      ce_reference("historyButtonPanel")}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JLabel", "historySolutionSetLabel",(Element[])null),
      ce_reference("historyButtonPanel")}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JButton","historyNextSolutionSetButton",(Element[])null),
      ce_reference("historyButtonPanel")}));

    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JButton","historyPreviousSolutionButton",(Element[])null),
      ce_reference("historyButtonPanel")}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JLabel", "historySolutionLabel",(Element[])null),
      ce_reference("historyButtonPanel")}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("javax.swing.JButton","historyNextSolutionButton",(Element[])null),
      ce_reference("historyButtonPanel")}));
    
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.Script","historyPreviousSolutionSetScript",
		ce_property("script",ce_string("History.previousSolutionSet();")))}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.Script","historyNextSolutionSetScript",
		ce_property("script",ce_string("History.nextSolutionSet();")))}));

    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.Script","historyPreviousSolutionScript",
		ce_property("script",ce_string("History.previousSolution();")))}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.Script","historyNextSolutionScript",
		ce_property("script",ce_string("History.nextSolution();")))}));

    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.HistoryProxy","historyLabelHistoryProxy",(Element[])null)}));
    form.appendChild(ce_method("addBean",new Element[]{
      ce_object("net.sourceforge.czt.animation.gui.beans.Script","historyLabelScript",
		ce_property("script",
		   ce_string("fillBean(\"historySolutionSetLabel\",History.positionLabel);"
			     +"fillBean(\"historySolutionLabel\",History.currentSolution.positionLabel);")))
    }));
    
    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyPreviousSolutionSetScriptWrapper",
		  ce_property("bean",ce_reference("historyPreviousSolutionSetScript")))));
    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyNextSolutionSetScriptWrapper",
		  ce_property("bean",ce_reference("historyNextSolutionSetScript")))));
    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyPreviousSolutionScriptWrapper",
		  ce_property("bean",ce_reference("historyPreviousSolutionScript")))));
    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyNextSolutionScriptWrapper",
		  ce_property("bean",ce_reference("historyNextSolutionScript")))));

    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyLabelHistoryProxyWrapper",
		  ce_property("bean",ce_reference("historyLabelHistoryProxy")))));
    wrappers.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanWrapper",
		  "historyLabelScriptWrapper",
		  ce_property("bean",ce_reference("historyLabelScript")))));
    
    links.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanLink",new Element[] {
		  ce_reference("historyPreviousSolutionSetButton"),
		  ce_reference("historyPreviousSolutionSetScriptWrapper")})));
    links.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanLink",new Element[] {
		  ce_reference("historyNextSolutionSetButton"),
		  ce_reference("historyNextSolutionSetScriptWrapper")})));
    links.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanLink",new Element[] {
		  ce_reference("historyPreviousSolutionButton"),
		  ce_reference("historyPreviousSolutionScriptWrapper")})));
    links.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanLink",new Element[] {
		  ce_reference("historyNextSolutionButton"),
		  ce_reference("historyNextSolutionScriptWrapper")})));

    links.appendChild(ce_method("add",
	ce_object("net.sourceforge.czt.animation.gui.design.BeanLink",new Element[] {
		  ce_reference("historyLabelHistoryProxyWrapper"),
		  ce_reference("historyLabelScriptWrapper")})));
    
  };
  
  protected void createInputForm(ConstDecl/*<SchExpr>*/ operationSchema) {
    //XXX
  };
  protected void createOutputForm(ConstDecl/*<SchExpr>*/ operationSchema) {
    //XXX
  };
  
  protected Element createVariablePanel(Element beanWrappers, Element eventLinks) {
    //XXX
    return null;
  };
  
  protected Element ce(String tag, String[] attributeNames, String[] attributeValues, Node[] children) {
    Element el=document.createElement(tag);
    for(int i=0;attributeNames!=null && attributeValues!=null 
	  && i<attributeNames.length && i<attributeValues.length;i++) 
      el.setAttribute(attributeNames[i],attributeValues[i]);
    for(int i=0;children!=null && i<children.length;i++)
      el.appendChild(children[i]);
    return el;
  };
  protected Element ce(String tag, String attributeName, String attributeValue, Node[] children) {
    return ce(tag,new String[] {attributeName}, new String[] {attributeValue}, children);
  }; 
  protected Element ce(String tag, String[] attributeNames, String[] attributeValues, Node child) {
    return ce(tag,attributeNames,attributeValues,new Node[]{child});
  };
  protected Element ce(String tag, String attributeName, String attributeValue, Node child) {
    return ce(tag,attributeName,attributeValue,new Node[]{child});
  };

  protected Element ce_reference(String id) {
    return ce("object","id",id,(Node[])null);
  };
  protected Element ce_object(String clasz, Element[] children) {
    return ce("object","class",clasz,children);
  };
  protected Element ce_object(String clasz, String id, Element child) {
    return ce_object(clasz,id,new Element[] {child});
  };
  protected Element ce_object(String clasz, String id, Element[] children) {
    return ce("object",new String[] {"class","id"},new String[] {clasz, id},children);
  };
  protected Element ce_property(String property, Element child) {
    return ce_property(property,new Element[]{child});
  };
  protected Element ce_property(String property, Element[] children) {
    return ce("void","property",property,children);
  };  
  protected Element ce_method(String method, Element child) {
    return ce_method(method,new Element[]{child});
  };  
  protected Element ce_method(String method, Element[] children) {
    return ce("void","method",method,children);
  };  
  protected Element ce_class(Class data) {
    return ce("class",(String[])null,(String[])null,document.createTextNode(data.getName()));
  };
  protected Element ce_int(double data) {
    Element el=document.createElement("double");
    el.appendChild(document.createTextNode(""+data));
    return el;
  };
  protected Element ce_int(int data) {
    Element el=document.createElement("int");
    el.appendChild(document.createTextNode(""+data));
    return el;
  };
  protected Element ce_string(String data) {
    Element el=document.createElement("string");
    el.appendChild(document.createTextNode(data));
    return el;
  };

  public Option[] getOptions() {
    return new Option[]{};
  };
  public String getHelp() {
    return "Does the main work of creating the GAfFE interface.";
  };
};
