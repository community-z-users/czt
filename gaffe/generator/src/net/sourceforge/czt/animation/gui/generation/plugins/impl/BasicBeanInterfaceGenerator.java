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
import java.awt.Color;
import java.awt.Component;
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

import javax.swing.BorderFactory;
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
import net.sourceforge.czt.animation.gui.history.History;
import net.sourceforge.czt.animation.gui.history.ZLiveHistory;
import net.sourceforge.czt.animation.gui.persistence.GaffeEncoder;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.VarDecl;

public class BasicBeanInterfaceGenerator implements BeanInterfaceGenerator
{
  Term specification;

  List<ConstDecl/*<SchExpr>*/> schemas;

  ConstDecl/*<SchExpr>*/stateSchema;

  ConstDecl/*<SchExpr>*/initSchema;

  List<ConstDecl/*<SchExpr>*/> operationSchemas;

  VariableExtractor variableExtractor;

  BeanChooser beanChooser;

  public static final class Owner
  {
    private History history;

    public History getHistory()
    {
      return history;
    };

    public void setHistory(History history)
    {
      this.history = history;
    };

    private String initScript;

    public String getInitScript()
    {
      return initScript;
    };

    public void setInitScript(String initScript)
    {
      this.initScript = initScript;
    };

    private String initScriptLanguage;

    public String getInitScriptLanguage()
    {
      return initScriptLanguage;
    };

    public void setInitScriptLanguage(String initScriptLanguage)
    {
      this.initScriptLanguage = initScriptLanguage;
    };

    private String stateSchema;

    public String getStateSchema()
    {
      return stateSchema;
    };

    public void setStateSchema(String stateSchema)
    {
      this.stateSchema = stateSchema;
    };

    private String initSchema;

    public String getInitSchema()
    {
      return initSchema;
    };

    public void setInitSchema(String initSchema)
    {
      this.initSchema = initSchema;
    };

    private String specificationURL;

    public String getSpecificationURL()
    {
      return specificationURL;
    };

    public void setSpecificationURL(String specificationURL)
    {
      this.specificationURL = specificationURL;
    };
  };

  /**
   * {@inheritDoc}
   */
  public synchronized void generateInterface(Term specification, URL specURL,
      List<ConstDecl/*<SchExpr>*/> schemas,
      ConstDecl/*<SchExpr>*/stateSchema, ConstDecl/*<SchExpr>*/initSchema,
      List<ConstDecl/*<SchExpr>*/> operationSchemas,
      VariableExtractor variableExtractor, BeanChooser beanChooser,
      OutputStream os)
  {
    this.specification = specification;
    this.schemas = schemas;
    this.stateSchema = stateSchema;
    this.initSchema = initSchema;
    this.operationSchemas = operationSchemas;
    this.variableExtractor = variableExtractor;
    this.beanChooser = beanChooser;

    Owner owner = new Owner();
    GaffeEncoder encoder = new GaffeEncoder(os);
    encoder.setOwner(owner);
    encoder.writeStatement(new Statement(owner, "setHistory",
        new Object[]{new ZLiveHistory(stateSchema.getDeclName().toString(),
            initSchema.getDeclName().toString(),specURL)}));
    encoder
        .writeStatement(new Statement(
            owner,
            "setInitScript",
            new Object[]{"function getScript(url) {"
                + "  importClass(Packages.org.apache.bsf.util.IOUtils);"
                + "  importClass(java.io.InputStreamReader);"
                + "  return String(IOUtils.getStringFromReader(new InputStreamReader(url)));"
                + "};"
                + "function getLibraryScript(name) {"
                + "  importClass(java.lang.ClassLoader);"
                + "  return getScript(ClassLoader.getSystemResourceAsStream("
                + "      \"net/sourceforge/czt/animation/gui/scripts/\"+name+\".js\"));"
                + "};" + "eval(getLibraryScript(\"fillBeans\"));"
                + "eval(getLibraryScript(\"fillHistory\"));"
                + "eval(getLibraryScript(\"clearBeans\"));"}));
    encoder.writeStatement(new Statement(owner, "setInitScriptLanguage",
        new Object[]{"javascript"}));
    if (specURL != null)
      encoder.writeStatement(new Statement(owner, "setSpecificationURL",
          new Object[]{specURL.toExternalForm()}));

    createForms(encoder);

    encoder.close();
  };

  protected void createForms(XMLEncoder encoder)
  {
    createStateForm(encoder);
    for (Iterator it = operationSchemas.iterator(); it.hasNext();) {
      ConstDecl/*<SchExpr>*/operationSchema = (ConstDecl/*<SchExpr>*/) it
          .next();
      createInputForm(operationSchema, encoder);
      createOutputForm(operationSchema, encoder);
    };
  };

  protected void addWrappedBeans(Form form, Vector<BeanWrapper> wrappers)
  {
    for (Iterator it = wrappers.iterator(); it.hasNext();)
      form.addBean(((BeanWrapper) it.next()).getBean());
  };

  protected void createStateForm(XMLEncoder encoder)
  {
    Form form = new Form(stateSchema.getDeclName().toString());
    form.setStartsVisible(true);
    form.setLayout(new BorderLayout());
    Vector<BeanWrapper> wrappers = new Vector<BeanWrapper>();
    Vector<BeanLink> eventLinks = new Vector<BeanLink>();
    JPanel historyButtonPanel = createHistoryButtonPanel(wrappers, eventLinks);
    JPanel operationButtonPanel = createStateButtonPanel(wrappers, eventLinks);
    JPanel variablePanel = createVariablePanel(stateSchema, variableExtractor
        .getStateVariables(stateSchema), false, true);

    JPanel statePanel = new JPanel();
    statePanel.setLayout(new BorderLayout());
    statePanel.add(variablePanel, BorderLayout.CENTER);
    statePanel.add(operationButtonPanel, BorderLayout.SOUTH);

    form.add(statePanel, BorderLayout.CENTER);
    form.add(historyButtonPanel, BorderLayout.SOUTH);

    HistoryProxy historyProxy = new HistoryProxy();
    wrappers.add(new BeanWrapper(historyProxy));
    Script stateUpdateScript = new Script(
        "fillBeans(thisForm);\n"
            + "lastOutputWindow=Forms.lookup(History.currentSolutionSet.schemaName+\" output\");\n"
            + "thisForm.lookup(\"historyPanel . previousHistory\").setEnabled(History.hasPreviousSolutionSet());\n"
            + "thisForm.lookup(\"historyPanel . nextHistory\").setEnabled(History.hasNextSolutionSet());\n"
            + "thisForm.lookup(\"historyPanel . previousSolution\").setEnabled(History.hasPreviousSolution());\n"
            + "thisForm.lookup(\"historyPanel . nextSolution\").setEnabled(History.hasNextSolution());\n"
            + "var opsButtons=thisForm.lookup(\"Operation Panel\").components;\n"
            + "for(var i in opsButtons) if(opsButtons[i] instanceof Packages.javax.swing.JButton)\n"
            + "  opsButtons[i].enabled=History.hasCurrentSolution();\n"
            + "thisForm.lookup(\"Show Outputs Button\").setEnabled(lastOutputWindow!=null);");
    wrappers.add(new BeanWrapper(stateUpdateScript));
    eventLinks.add(new BeanLink(historyProxy, stateUpdateScript,
        ActionListener.class));

    addWrappedBeans(form, wrappers);

    //The border won't be saved, but it will make sure that the size looks right in the designer.
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory
        .createLineBorder(Color.black), form.getName()));
    form.setSize(form.getPreferredSize());
    form.validate();

    encoder.writeObject(form);
    encoder.writeObject(wrappers);
    encoder.writeObject(eventLinks);
  };

  protected JPanel createStateButtonPanel(Vector<BeanWrapper> wrappers,
      Vector<BeanLink> eventLinks)
  {
    JPanel mainPanel = new JPanel();
    mainPanel.setLayout(new BorderLayout());

    JPanel panel = new JPanel();
    mainPanel.add(panel, BorderLayout.CENTER);
    panel.setLayout(new FlowLayout(FlowLayout.LEFT));
    panel.setName("Operation Panel");
    for (Iterator it = operationSchemas.iterator(); it.hasNext();) {
      ConstDecl/*<SchExpr>*/operationSchema = (ConstDecl/*<SchExpr>*/) it
          .next();
      String opSchemaName = operationSchema.getDeclName().toString();
      JButton opButton = new JButton(opSchemaName);
      panel.add(opButton);
      Script opScript = new Script("Forms.lookup(\"" + opSchemaName
          + " input\").setVisible(true);");
      wrappers.add(new BeanWrapper(opScript));
      eventLinks.add(new BeanLink(opButton, opScript, ActionListener.class));
    }
    JPanel secondPanel = new JPanel();
    mainPanel.add(secondPanel, BorderLayout.EAST);
    secondPanel.setLayout(new FlowLayout(FlowLayout.RIGHT));

    JButton showOutputsButton = new JButton("Show Outputs");
    showOutputsButton.setName("Show Outputs Button");
    showOutputsButton.setEnabled(false);//Immediately after animator start there is no outputs.
    secondPanel.add(showOutputsButton);
    Script showOutputScript = new Script(
        "if(typeof(lastOutputWindow)==\"undefined\" || lastOutputWindow==null)"
            + "  thisForm.lookup(\"" + showOutputsButton.getName()
            + "\").enabled=false;" + "else"
            + "  lastOutputWindow.setVisible(true);");//XXX write this script
    wrappers.add(new BeanWrapper(showOutputScript));
    eventLinks.add(new BeanLink(showOutputsButton, showOutputScript,
        ActionListener.class));

    JButton quitButton = new JButton("Quit");
    secondPanel.add(quitButton);
    Script quitScript = new Script("java.lang.System.exit(0);");//XXX should be done as a service through bean context?
    wrappers.add(new BeanWrapper(quitScript));
    eventLinks.add(new BeanLink(quitButton, quitScript, ActionListener.class));

    mainPanel.validate();
    return mainPanel;
  };

  protected JPanel createHistoryButtonPanel(Vector<BeanWrapper> wrappers,
      Vector<BeanLink> eventLinks)
  {
    JPanel panel = new JPanel();
    panel.setLayout(new FlowLayout(FlowLayout.CENTER));

    JButton prevSolutionSetB = new JButton("< History");
    prevSolutionSetB.setName("historyPanel . previousHistory");
    prevSolutionSetB.setEnabled(false);
    panel.add(prevSolutionSetB);
    JLabel solutionSetL = new JLabel("History: 1/1");
    solutionSetL.setName("historyPanel . historyLabel");
    panel.add(solutionSetL);
    JButton nextSolutionSetB = new JButton("History >");
    nextSolutionSetB.setName("historyPanel . nextHistory");
    nextSolutionSetB.setEnabled(false);
    panel.add(nextSolutionSetB);

    JButton prevSolutionB = new JButton("< Solutions");
    prevSolutionB.setName("historyPanel . previousSolution");
    prevSolutionB.setEnabled(false);
    panel.add(prevSolutionB);
    JLabel solutionL = new JLabel("Solutions: 1/1");
    solutionL.setName("historyPanel . solutionLabel");
    panel.add(solutionL);
    JButton nextSolutionB = new JButton("Solutions >");
    nextSolutionB.setName("historyPanel . nextSolution");
    nextSolutionB.setEnabled(false);
    panel.add(nextSolutionB);

    Script prevSolutionSetBScript = new Script("History.previousSolutionSet();");
    wrappers.add(new BeanWrapper(prevSolutionSetBScript));
    eventLinks.add(new BeanLink(prevSolutionSetB, prevSolutionSetBScript,
        ActionListener.class));
    Script nextSolutionSetBScript = new Script("History.nextSolutionSet();");
    wrappers.add(new BeanWrapper(nextSolutionSetBScript));
    eventLinks.add(new BeanLink(nextSolutionSetB, nextSolutionSetBScript,
        ActionListener.class));

    Script prevSolutionBScript = new Script("History.previousSolution();");
    wrappers.add(new BeanWrapper(prevSolutionBScript));
    eventLinks.add(new BeanLink(prevSolutionB, prevSolutionBScript,
        ActionListener.class));
    Script nextSolutionBScript = new Script("History.nextSolution();");
    wrappers.add(new BeanWrapper(nextSolutionBScript));
    eventLinks.add(new BeanLink(nextSolutionB, nextSolutionBScript,
        ActionListener.class));

    HistoryProxy hp = new HistoryProxy();
    wrappers.add(new BeanWrapper(hp));
    Script labelScript = new Script(
        "thisForm.lookup(\"historyPanel . historyLabel\").text=\"History: \"+History.positionLabel;\n"
            + "thisForm.lookup(\"historyPanel . solutionLabel\").text=\"Solutions: \"+(History.hasCurrentSolution()?History.currentSolutionSet.positionLabel:\"0/0\");"
            + "importClass(Packages.javax.swing.JOptionPane);"
            + "if(!History.hasCurrentSolution())"
            + "  JOptionPane.showMessageDialog(null, \"The operation you chose produced no solutions.\", \"Operation Failed\", "
            + "                                JOptionPane.WARNING_MESSAGE);");
    wrappers.add(new BeanWrapper(labelScript));
    eventLinks.add(new BeanLink(hp, labelScript, ActionListener.class));
    return panel;
  };

  protected void createInputForm(ConstDecl/*<SchExpr>*/operationSchema,
      XMLEncoder encoder)
  {
    Form form = new Form(operationSchema.getDeclName().toString() + " input");
    form.setLayout(new BorderLayout());
    Vector<BeanWrapper> wrappers = new Vector<BeanWrapper>();
    Vector<BeanLink> eventLinks = new Vector<BeanLink>();
    String schemaName = operationSchema.getDeclName().toString();
    JPanel buttonPanel = createInputButtonPanel(schemaName, wrappers,
        eventLinks);
    JPanel variablePanel = createVariablePanel(stateSchema, variableExtractor
        .getInputVariables(operationSchema), true, false);

    form.add(variablePanel, BorderLayout.CENTER);
    form.add(buttonPanel, BorderLayout.SOUTH);

    addWrappedBeans(form, wrappers);

    //The border won't be saved, but it will make sure that the size looks right in the designer.
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory
        .createLineBorder(Color.black), form.getName()));
    form.setSize(form.getPreferredSize());
    form.validate();

    encoder.writeObject(form);
    encoder.writeObject(wrappers);
    encoder.writeObject(eventLinks);
  };

  protected JPanel createInputButtonPanel(String schemaName,
      Vector<BeanWrapper> wrappers, Vector<BeanLink> eventLinks)
  {

    JPanel panel = new JPanel();
    panel.setLayout(new FlowLayout(FlowLayout.CENTER));

    JButton okButton = new JButton("OK");
    panel.add(okButton);
    Script okScript = new Script("fillHistory(thisForm);\n"
        + "History.activateSchema(\"" + schemaName + "\");\n"
        + "clearBeans(thisForm);\n" + "thisForm.setVisible(false);\n"
        + "var outputWindow=Forms.lookup(\"" + schemaName + " output\");\n"
        + "if(outputWindow!=null)\n" + "  outputWindow.setVisible(true);");
    wrappers.add(new BeanWrapper(okScript));
    eventLinks.add(new BeanLink(okButton, okScript, ActionListener.class));

    JButton cancelButton = new JButton("Cancel");
    panel.add(cancelButton);
    Script cancelScript = new Script("clearBeans(thisForm);"
        + "thisForm.setVisible(false);");
    wrappers.add(new BeanWrapper(cancelScript));
    eventLinks.add(new BeanLink(cancelButton, cancelScript,
        ActionListener.class));

    return panel;
  };

  protected void createOutputForm(ConstDecl/*<SchExpr>*/operationSchema,
      XMLEncoder encoder)
  {
    Map<DeclName, VarDecl> variableMap = variableExtractor
        .getOutputVariables(operationSchema);
    if (variableMap.isEmpty())
      return;

    Form form = new Form(operationSchema.getDeclName().toString() + " output");
    form.setLayout(new BorderLayout());
    Vector<BeanWrapper> wrappers = new Vector<BeanWrapper>();
    Vector<BeanLink> eventLinks = new Vector<BeanLink>();
    JPanel buttonPanel = createOutputButtonPanel(operationSchema.getDeclName(),
        wrappers, eventLinks);
    JPanel variablePanel = createVariablePanel(stateSchema, variableMap, false,
        false);

    form.add(variablePanel, BorderLayout.CENTER);
    form.add(buttonPanel, BorderLayout.SOUTH);

    HistoryProxy historyProxy = new HistoryProxy();
    wrappers.add(new BeanWrapper(historyProxy));
    Script outputUpdateScript = new Script("fillBeans(thisForm)");
    wrappers.add(new BeanWrapper(outputUpdateScript));
    eventLinks.add(new BeanLink(historyProxy, outputUpdateScript,
        ActionListener.class));

    addWrappedBeans(form, wrappers);

    //The border won't be saved, but it will make sure that the size looks right in the designer.
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory
        .createLineBorder(Color.black), form.getName()));
    form.setSize(form.getPreferredSize());
    form.validate();

    encoder.writeObject(form);
    encoder.writeObject(wrappers);
    encoder.writeObject(eventLinks);
  };

  protected JPanel createOutputButtonPanel(DeclName schemaName,
      Vector<BeanWrapper> wrappers, Vector<BeanLink> eventLinks)
  {
    JPanel panel = new JPanel();
    panel.setLayout(new FlowLayout(FlowLayout.CENTER));

    JButton closeButton = new JButton("Close");
    panel.add(closeButton);
    Script closeScript = new Script("thisForm.setVisible(false);");
    wrappers.add(new BeanWrapper(closeScript));
    eventLinks
        .add(new BeanLink(closeButton, closeScript, ActionListener.class));

    return panel;
  };

  private static final GridBagConstraints nameConstraint;

  private static final GridBagConstraints varConstraint;
  static {
    nameConstraint = new GridBagConstraints();
    nameConstraint.anchor = GridBagConstraints.FIRST_LINE_START;
    nameConstraint.weightx = 0;
    varConstraint = new GridBagConstraints();
    varConstraint.anchor = GridBagConstraints.FIRST_LINE_START;
    varConstraint.fill = GridBagConstraints.BOTH;
    varConstraint.gridwidth = GridBagConstraints.REMAINDER;
    varConstraint.weightx = 1;
  };

  protected JPanel createVariablePanel(ConstDecl/*<SchExpr>*/schema,
      Map<DeclName, VarDecl> variables, boolean editable, boolean state)
  {
    JPanel panel = new JPanel();
    GridBagLayout layout = new GridBagLayout();
    panel.setLayout(layout);

    for (Iterator it = variables.keySet().iterator(); it.hasNext();) {
      DeclName name = (DeclName) it.next();
      String nameString = name.toString();

      JLabel nameLabel = new JLabel(nameString);
      layout.setConstraints(nameLabel, nameConstraint);
      panel.add(nameLabel);

      Component varComponent = beanChooser.chooseBean(specification, schema,
          nameString + (state ? "'" : ""), (VarDecl) variables.get(name),
          editable);
      layout.setConstraints(varComponent, varConstraint);
      panel.add(varComponent);
    }
    return panel;
  };

  public Option[] getOptions()
  {
    return new Option[]{};
  };

  public String getHelp()
  {
    return "Does the main work of creating the GAfFE interface.";
  };
};
