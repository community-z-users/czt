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

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;

import java.awt.event.ActionListener;

import java.beans.Statement;
import java.beans.XMLEncoder;

import java.io.OutputStream;

import java.net.URL;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;

import net.sourceforge.czt.animation.gui.Form;

import net.sourceforge.czt.animation.gui.beans.HistoryProxy;
import net.sourceforge.czt.animation.gui.beans.Script;

import net.sourceforge.czt.animation.gui.design.BeanLink;
import net.sourceforge.czt.animation.gui.design.BeanWrapper;

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.BeanChooser;
import net.sourceforge.czt.animation.gui.generation.plugins.BeanInterfaceGenerator;
import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;

import net.sourceforge.czt.animation.gui.history.BasicHistory;
import net.sourceforge.czt.animation.gui.history.History;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;

class BasicBeanInterfaceGenerator implements BeanInterfaceGenerator {
  Term specification;
  List/*<ConstDecl<SchExpr>>*/ schemas;
  ConstDecl/*<SchExpr>*/ stateSchema;
  ConstDecl/*<SchExpr>*/ initSchema;
  List/*<ConstDecl<SchExpr>>*/ operationSchemas;
  VariableExtractor variableExtractor;
  BeanChooser beanChooser;

  private static final class Owner {
    private History history;
    public History getHistory() {return history;};
    public void setHistory(History history) {this.history=history;};
    
    private String initScript;
    public String getInitScript() {return initScript;};
    public void setInitScript(String initScript) {
      this.initScript=initScript;
    };

    private String initScriptLanguage;
    public String getInitScriptLanguage() {return initScriptLanguage;};
    public void setInitScriptLanguage(String initScriptLanguage) {
      this.initScriptLanguage=initScriptLanguage;
    };

    private String stateSchema;
    public String getStateSchema() {return stateSchema;};
    public void setStateSchema(String stateSchema) {
      this.stateSchema=stateSchema;
    };

    private String initSchema;
    public String getInitSchema() {return initSchema;};
    public void setInitSchema(String initSchema) {
      this.initSchema=initSchema;
    };

    private String specificationURL;
    public String getSpecificationURL() {return specificationURL;};
    public void setSpecificationURL(String specificationURL) {
      this.specificationURL=specificationURL;
    };
  };
  
  /**
   * {@inheritDoc}
   */
  public synchronized void generateInterface(Term specification, URL specURL,
					     List/*<ConstDecl<SchExpr>>*/ schemas, 
					     ConstDecl/*<SchExpr>*/ stateSchema,
					     ConstDecl/*<SchExpr>*/ initSchema, 
					     List/*<ConstDecl<SchExpr>>*/ operationSchemas, 
					     VariableExtractor variableExtractor,
					     BeanChooser beanChooser, 
					     OutputStream os) {
    this.specification=specification;
    this.schemas=schemas;
    this.stateSchema=stateSchema;
    this.initSchema=initSchema;
    this.operationSchemas=operationSchemas;
    this.variableExtractor=variableExtractor;
    this.beanChooser=beanChooser;
    
    Owner owner=new Owner();
    XMLEncoder encoder=new XMLEncoder(os);
    encoder.setOwner(owner);
    encoder.writeStatement(new Statement(owner,"setHistory",new Object[] {new BasicHistory()}));
    encoder.writeStatement(new Statement(owner,"setInitScript",new Object[] {
      "XXX"
    }));
    encoder.writeStatement(new Statement(owner,"setInitScriptLanguage",new Object[] {"javascript"}));
    encoder.writeStatement(new Statement(owner,"setStateSchema",new Object[] {
      Name2String.toString(stateSchema.getDeclName())
    }));
    encoder.writeStatement(new Statement(owner,"setInitSchema",new Object[] {
      Name2String.toString(initSchema.getDeclName())
    }));
    if(specURL!=null)
      encoder.writeStatement(new Statement(owner,"setSpecificationURL",new Object[] {
      specURL.toExternalForm()
    }));
    
    createForms(encoder);

    encoder.close();
  };
  
  protected void createForms(XMLEncoder encoder) {
    createStateForm(encoder);
    for(Iterator it=operationSchemas.iterator();it.hasNext();) {
      ConstDecl/*<SchExpr>*/ operationSchema=(ConstDecl/*<SchExpr>*/)it.next();
      createInputForm(operationSchema,encoder);
      createOutputForm(operationSchema,encoder);
    };
  };
  protected void createStateForm(XMLEncoder encoder) {
    Form form=new Form(Name2String.toString(stateSchema.getDeclName()));
    form.setLayout(new BorderLayout());
    Vector wrappers=new Vector();
    Vector eventLinks=new Vector();
    JPanel historyButtonPanel=createHistoryButtonPanel(form,wrappers,eventLinks);
    JPanel operationButtonPanel=createStateButtonPanel(form,wrappers,eventLinks);
    JPanel variablePanel=createVariablePanel(form,wrappers,eventLinks,
					     variableExtractor.getPrimedStateVariables(stateSchema),false);
    
    JPanel statePanel=new JPanel();
    statePanel.setLayout(new BorderLayout());
    statePanel.add(variablePanel,BorderLayout.CENTER);
    statePanel.add(operationButtonPanel,BorderLayout.SOUTH);
    form.addBean(statePanel);
    form.add(statePanel,BorderLayout.CENTER);
    form.add(historyButtonPanel,BorderLayout.SOUTH);
    encoder.writeObject(form);
    encoder.writeObject(wrappers);
    encoder.writeObject(eventLinks);
  };
  protected JPanel createStateButtonPanel(Form form, Vector wrappers, Vector eventLinks) {
    JPanel mainPanel=new JPanel();
    form.addBean(mainPanel);
    mainPanel.setLayout(new BorderLayout());
    
    JPanel panel=new JPanel();
    mainPanel.add(panel,BorderLayout.CENTER);
    form.addBean(panel,mainPanel);
    panel.setLayout(new FlowLayout(FlowLayout.CENTER));
    
    for(Iterator it=operationSchemas.iterator();it.hasNext();) {
      ConstDecl/*<SchExpr>*/ operationSchema=(ConstDecl/*<SchExpr>*/)it.next();
      String opSchemaName=Name2String.toString(operationSchema.getDeclName());
      JButton opButton=new JButton(opSchemaName);
      form.addBean(opButton,panel);
      Script opScript=new Script();
      opScript.setScript("Forms.lookup(\""+opSchemaName+" input\").setVisible(true);");
      BeanWrapper wrapper=new BeanWrapper(opScript);
      form.addBean(opScript);wrappers.add(wrapper);
      eventLinks.add(new BeanLink(opButton,wrapper,ActionListener.class));
    }
    JPanel secondPanel=new JPanel();
    mainPanel.add(secondPanel,BorderLayout.CENTER);
    form.addBean(secondPanel,mainPanel);
    secondPanel.setLayout(new FlowLayout(FlowLayout.CENTER));

    JButton showOutputsButton=new JButton("Show Outputs");
    form.addBean(showOutputsButton,secondPanel);
    Script showOutputScript=new Script();
    showOutputScript.setScript("XXXX");//XXX write this script
    BeanWrapper wrapper=new BeanWrapper(showOutputScript);
    form.addBean(showOutputScript);wrappers.add(wrapper);
    eventLinks.add(new BeanLink(showOutputsButton,wrapper,ActionListener.class));
    
    JButton quitButton=new JButton("Quit");
    form.addBean(quitButton,secondPanel);
    Script quitScript=new Script();
    quitScript.setScript("System.exit(0);");//XXX should be done as a service through bean context?
    wrapper=new BeanWrapper(quitScript);
    form.addBean(quitScript);wrappers.add(wrapper);
    eventLinks.add(new BeanLink(quitButton,wrapper,ActionListener.class));
  };
  
  protected JPanel createHistoryButtonPanel(Form form, Vector wrappers, Vector eventLinks) {
    JPanel panel=new JPanel();
    form.addBean(panel);
    panel.setLayout(new FlowLayout(FlowLayout.CENTER));
		    
    JButton prevSolutionSetB=new JButton("< History");
    form.addBean(prevSolutionSetB,panel);
    JLabel  solutionSetL=new JLabel("History: ?/?");  solutionSetL.setName("historyPanel.historyLabel");
    form.addBean(solutionSetL,panel);
    JButton nextSolutionSetB=new JButton("History >");
    form.addBean(nextSolutionSetB,panel);
    
    JButton prevSolutionB=new JButton("< Solutions");
    form.addBean(prevSolutionSetB,panel);
    JLabel  solutionL=new JLabel("Solutions: ?/?");  solutionSetL.setName("historyPanel.solutionLabel");
    form.addBean(solutionL,panel);
    JButton nextSolutionB=new JButton("Solutions >");
    form.addBean(nextSolutionSetB,panel);
    
    BeanWrapper wrapper;
    Script prevSolutionSetBScript=new Script();
    prevSolutionSetBScript.setScript("History.prevSolutionSet();");
    form.addBean(prevSolutionSetBScript);wrappers.add(wrapper=new BeanWrapper(prevSolutionSetBScript));
    eventLinks.add(new BeanLink(prevSolutionSetB,wrapper,ActionListener.class));
    Script nextSolutionSetBScript=new Script();
    nextSolutionSetBScript.setScript("History.nextSolutionSet();");
    form.addBean(nextSolutionSetBScript);wrappers.add(wrapper=new BeanWrapper(nextSolutionSetBScript));
    eventLinks.add(new BeanLink(nextSolutionSetB,wrapper,ActionListener.class));
    
    Script prevSolutionBScript=new Script();
    prevSolutionBScript.setScript("History.prevSolution();");
    form.addBean(prevSolutionBScript);wrappers.add(wrapper=new BeanWrapper(prevSolutionBScript));
    eventLinks.add(new BeanLink(prevSolutionB,wrapper,ActionListener.class));
    Script nextSolutionBScript=new Script();
    nextSolutionBScript.setScript("History.nextSolution();");
    form.addBean(nextSolutionBScript);wrappers.add(wrapper=new BeanWrapper(nextSolutionBScript));
    eventLinks.add(new BeanLink(nextSolutionB,wrapper,ActionListener.class));
    
    BeanWrapper wrapper2;
    HistoryProxy hp=new HistoryProxy();
    form.addBean(hp);wrappers.add(wrapper=new BeanWrapper(hp));
    Script labelScript=new Script();
    labelScript
      .setScript("thisForm.lookup(\"historyPanel.historyLabel\").text=\"Solutions: \"+History.positionLabel;"
		 +"thisForm.lookup(\"historyPanel.solutionLabel\").text=\"Solutions: \"+History.currentSolution.positionLabel;");
    form.addBean(labelScript);wrappers.add(wrapper2=new BeanWrapper(labelScript));
    eventLinks.add(new BeanLink(wrapper,wrapper2,ActionListener.class));
    
  };
  protected void createInputForm(ConstDecl/*<SchExpr>*/ operationSchema, XMLEncoder encoder) {
    //XXX
  };
  protected void createOutputForm(ConstDecl/*<SchExpr>*/ operationSchema, XMLEncoder encoder) {
    //XXX
  };
  
  protected JPanel createVariablePanel(Form form, Vector wrappers, Vector eventLinks, 
				       Map/*<DeclName, VarDecl>*/ variables) {
    JPanel panel=new JPanel();
    GridBagLayout layout=new GridBagLayout();
    panel.setLayout(layout);
    GridBagConstraints nameConstraint=new GridBagConstraints();
    nameConstraint.anchor=GridBagConstraints.FIRST_LINE_START;
    nameConstraint.weightx=0;
    GridBagConstraints varConstraint=new GridBagConstraints();
    varConstraint.anchor=GridBagConstraints.FIRST_LINE_START;
    varConstraint.fill=GridBagConstraints.HORIZONTAL;
    varConstraint.gridwidth=GridBagConstraints.REMAINDER;
    varConstraint.weightx=1;

    for(Iterator it=variables.keySet().iterator();it.hasNext();) {
      DeclName name=(DeclName)it.next();
      String nameString=Name2String.toString(name);
      
      JLabel nameLabel=new JLabel(nameString);
      layout.setConstraints(nameLabel,nameConstraint);
      panel.add(nameLabel);
      
      //XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXUP TO HERE
    }
  };
  
  public Option[] getOptions() {
    return new Option[]{};
  };
  public String getHelp() {
    return "Does the main work of creating the GAfFE interface.";
  };
};
