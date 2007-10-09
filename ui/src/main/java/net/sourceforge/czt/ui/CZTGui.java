package net.sourceforge.czt.ui;


import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.MenuKeyEvent;
import javax.swing.event.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.plaf.basic.BasicHTML;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.util.TermTreeNode;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.util.ConcreteSyntaxDescriptionVisitor;

import net.sourceforge.czt.animation.eval.*;
/**
 *  Description of the Class
 *
 *@author     yt49
 *@created    July 31, 2007
 */
public class CZTGui implements ActionListener
{
  SectionManager manager;
  
  String softwarename = "CZT";

  JFileChooser chooser = new JFileChooser();
  
  JFrame frame = new JFrame(softwarename);
  JFrame helpFrame = new JFrame("CZT Help");

  JPanel treeViewPanel = new JPanel();
  JLabel treeViewLabel = new JLabel("Specification Structure Explorer");
  JTree treeView = null;

  JPanel resultPanel = new JPanel();
  JLabel resultLabel = new JLabel("Output");

  /*DefaultListModel resultListModel = new DefaultListModel();
  JList resultList = new JList();
  **/
  JTextArea resultConsole = new JTextArea();

  JTextArea statusBar = new JTextArea("status");

  JPanel specificationPanel = new JPanel();
  JTextField specText = new JTextField(12);
  JLabel specificationLabel = new JLabel("Specification:");
  JButton specBrowseButton = new JButton("...");

  JPanel specMidPanel = new JPanel();

  JPanel languagePanel = new JPanel();
  JLabel languageLabel = new JLabel("Language: ");
  String[] languageOptions = {"Standard Z", "Object Z", "Circus"};
  JComboBox languageCombo = new JComboBox(languageOptions);

  JPanel markupPanel = new JPanel();
  JLabel markupLabel = new JLabel("Markup: ");
  String[] markupOptions = {"Latex", "UTF8","UTF16", "XML"};
  JComboBox markupCombo = new JComboBox(markupOptions);

  /*JPanel encodingPanel = new JPanel();
  JLabel encodingLabel = new JLabel("Encoding: ");
  String[] encodingOptions = {"Default", "UTF8", "UTF16"};
  JComboBox encodingCombo = new JComboBox(encodingOptions);**/

  JPanel typecheckPanel = new JPanel();
  JLabel typecheckLabel = new JLabel("Typecheck? ");
  JCheckBox typecheckCheckBox = new JCheckBox("", true);

  JPanel specOKCancelPanel = new JPanel();
  JButton specOKButton = new JButton("OK");
  JButton specCancelButton = new JButton("Cancel");

  final JDialog specDialog = new JDialog(frame, "Specification", true);

  JMenuBar menubar = new JMenuBar();
  JMenu filemenu = new JMenu("File");
  JMenuItem open = new JMenuItem("Open");
  JMenuItem startConsole = new JMenuItem("Start Console");
  JMenu saveas = new JMenu("Export to");
  JMenuItem saveasLatex = new JMenuItem("Latex");
  JMenuItem saveasUnicode8 = new JMenuItem("Unicode(utf8)");
  JMenuItem saveasUnicode16 = new JMenuItem("Unicode(utf16)");
  JMenuItem saveasXML = new JMenuItem("XML");
  JMenuItem close = new JMenuItem("Close");
  JMenuItem exit = new JMenuItem("Exit");
  JMenu helpmenu = new JMenu("Help");
  JMenuItem czthelp = new JMenuItem("CZT Help");
  JScrollPane scrollResults = new JScrollPane(resultConsole);
  JScrollPane scrollTreeStructure = new JScrollPane();
  JSplitPane split = null;
  File file = null;
  File fileForExporting = null;
  
  private PrintStream out;
  /**
   *  Constructor for the CZTGui object
   */
  public CZTGui()
  {
    chooser.setAcceptAllFileFilterUsed(true);
    chooser.addChoosableFileFilter(new CZTFilter());
    specDialog.setLocationRelativeTo(frame);
    statusBar.setEditable(false);
    resultConsole.setEditable(true);
    saveas.setEnabled(false);
    close.setEnabled(false);
    
    /*
    out = new PrintStream(new CZTGuiZLiveOutputRedirect( resultConsole ) );
    System.setOut(out);
    System.setErr(out);
    */
    
    /*try{
    JEditorPane tc = new JEditorPane(CZTGui.class.getResource("czt_help.html"));
    //tc.setContentType("text/html");
    //tc.setEditable(false);
    //tc.setText("<body bgcolor='red'><h1>hellow world</h1><p>bla bla</p><h2>jiberish</h2></body>");
    helpFrame.getContentPane().add(BorderLayout.NORTH, tc);
    }catch(IOException exception){
    System.out.println("cannot read html");
    }**/
    
    try {
      FileInputStream fileStream = new FileInputStream(getSettingsFileName());
      ObjectInputStream os = new ObjectInputStream(fileStream);

      Object pathObject = os.readObject();
      String path = (String) pathObject;
      chooser.setCurrentDirectory(new File(path));

      os.close();
    }
    catch (Exception e) {
      //e.printStackTrace();
    }
  }

  private String getSettingsFileName()
  {
    String userHome = System.getProperty("user.home");
    String result = userHome + "/." + softwarename;
    return result;
  }

  /**
   *  The main program for the CZTGui class
   *
   *@param  args  The command line arguments
   */
  public static void main(String[] args)
  {
    CZTGui gui = new CZTGui();
    gui.go();
  }


  /**
   *  Description of the Method
   */
  public void go()
  {
    treeViewPanel.setLayout(new BoxLayout(treeViewPanel, BoxLayout.Y_AXIS));
    treeViewPanel.add(BorderLayout.CENTER, treeViewLabel);
    treeViewPanel.add(BorderLayout.CENTER, scrollTreeStructure);
    
    resultPanel.setLayout(new BoxLayout(resultPanel, BoxLayout.Y_AXIS));
    resultPanel.add(BorderLayout.CENTER, resultLabel);
    resultPanel.add(BorderLayout.CENTER, scrollResults);

    split = new JSplitPane(JSplitPane.VERTICAL_SPLIT, treeViewPanel, resultPanel);
    split.setDividerLocation(400);

    open.addActionListener(this);
    startConsole.addActionListener(this);
    saveasLatex.addActionListener(this);
    saveasUnicode8.addActionListener(this);
    saveasUnicode16.addActionListener(this);
    saveasXML.addActionListener(this);
    close.addActionListener(this);
    exit.addActionListener(this);
    czthelp.addActionListener(this);
    
    filemenu.add(open);
    filemenu.add(startConsole);
    saveas.add(saveasLatex);
    saveas.add(saveasUnicode8);
    saveas.add(saveasUnicode16);
    saveas.add(saveasXML);
    filemenu.add(saveas);
    filemenu.add(close);
    filemenu.add(exit);
    helpmenu.add(czthelp);

    menubar.add(filemenu);
    menubar.add(helpmenu);

    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.getContentPane().add(BorderLayout.NORTH, menubar);
    frame.getContentPane().add(BorderLayout.CENTER, split);
    frame.getContentPane().add(BorderLayout.SOUTH, statusBar);
    frame.setSize(600, 600);
    frame.setVisible(true);

    specificationPanel.add(BorderLayout.WEST, specificationLabel);
    specificationPanel.add(BorderLayout.CENTER, specText);
    specificationPanel.add(BorderLayout.EAST, specBrowseButton);
    specBrowseButton.addActionListener(this);

    languagePanel.add(BorderLayout.WEST, languageLabel);
    languagePanel.add(BorderLayout.CENTER, languageCombo);

    markupPanel.add(BorderLayout.WEST, markupLabel);
    markupPanel.add(BorderLayout.CENTER, markupCombo);

    typecheckPanel.add(BorderLayout.WEST, typecheckLabel);
    typecheckPanel.add(BorderLayout.EAST, typecheckCheckBox);

    specMidPanel.setLayout(new BoxLayout(specMidPanel, BoxLayout.Y_AXIS));
    specMidPanel.add(languagePanel);
    specMidPanel.add(markupPanel);
    specMidPanel.add(typecheckPanel);

    specOKCancelPanel.add(BorderLayout.WEST, specOKButton);
    specOKCancelPanel.add(BorderLayout.WEST, specCancelButton);
    specOKButton.addActionListener(this);
    specCancelButton.addActionListener(this);

    specDialog.getContentPane().add(BorderLayout.NORTH, specificationPanel);
    specDialog.getContentPane().add(BorderLayout.CENTER, specMidPanel);
    specDialog.getContentPane().add(BorderLayout.SOUTH, specOKCancelPanel);
    specDialog.setSize(300, 200);

  }


  private void clearTreeView(){
    treeView = null;
    scrollTreeStructure.setViewportView(treeView);
  }
  private void clearErrorList(){
    //resultListModel.clear();
    resultConsole.setText("");
  }
  private void closeProject(){
    file = null;
    specText.setText("");
    frame.setTitle(softwarename);
    saveas.setEnabled(false);
    close.setEnabled(false);
    clearTreeView();
    clearErrorList();
    statusBar.setText("status");
  }
  
  private void successfulSaveMessage(boolean success){
    if(success == true)
      statusBar.setText("Finished exporting to "+fileForExporting.getName());
    if(success == false)
      statusBar.setText("Failed exporting to "+fileForExporting.getName());
  }
  
  private void saveSpec(String path,String markup){
    
    FileSource source = new FileSource(file);
    Writer writer = null;
    
    try{
      try{
        FileOutputStream stream = new FileOutputStream(path);
        
    if(markup.equals("latex")){
    LatexString latex = (LatexString)
    manager.get(new Key(new FileSource(file).getName(), LatexString.class));
    writer = new OutputStreamWriter(stream);
    writer.write(latex.toString());
    writer.close();
    successfulSaveMessage(true);
    }
    
    if(markup.equals("utf8")){
    UnicodeString unicode = (UnicodeString)
    manager.get(new Key(source.getName(), UnicodeString.class));
    writer = new OutputStreamWriter(stream, "UTF-8");
    writer.write(unicode.toString());
    writer.close();
    successfulSaveMessage(true);
    }
    
    if(markup.equals("utf16")){
    UnicodeString unicode = (UnicodeString)
    manager.get(new Key(source.getName(), UnicodeString.class));
    writer = new OutputStreamWriter(stream, "UTF-16");
    writer.write(unicode.toString());
    writer.close();
    successfulSaveMessage(true);
    }
    
    if(markup.equals("xml")){
    XmlString xml = (XmlString)
    manager.get(new Key(source.getName(), XmlString.class));
    writer = new OutputStreamWriter(stream, "UTF-8");
    writer.write(xml.toString());
    writer.close();
    successfulSaveMessage(true);
    }
      }catch(IOException exception){
        successfulSaveMessage(false);
      }
    }
    catch(CommandException exception) {
      printErrors(exception);
    }
  }

  private void printErrors(CommandException exception)
  {
    Throwable cause = exception.getCause();
    saveas.setEnabled(false);
    if (cause instanceof CztErrorList) {
      List<CztError> errors = new ArrayList<CztError>();
      errors.addAll(((CztErrorList) cause).getErrors());
      Collections.sort(errors);
      for (Object o : errors) {
        //resultListModel.addElement(o.toString());
        resultConsole.append(o.toString());
      }
    }
    else if (cause instanceof IOException) {
      String message = "Input output error: " + cause.getMessage();
      //resultListModel.addElement(message);
      resultConsole.append(message);
    }
    else {
      String message = cause + getClass().getName();
      //resultListModel.addElement(message);
      resultConsole.append(message);
    }
    //resultList.setModel(resultListModel);
  }

   
  /**
   *  Description of the Method
   */
  private void loadFile()
  { 
    statusBar.setText("Reading "+file.getName()+"...done");
    
    String selectedLanguage = "";
    String selectedEncoding = "";
    int nrOfZSects = 0;
    
    clearTreeView();
    clearErrorList();
    
    specDialog.setVisible(false);

    frame.setTitle(softwarename + " - " + file.getName());
    
    //obtain language selection
    if(((String)languageCombo.getSelectedItem()).equals("Standard Z"))
      selectedLanguage = "z";
    else
      if(((String)languageCombo.getSelectedItem()).equals("Object Z"))
        selectedLanguage = "oz";
    else
      if(((String)languageCombo.getSelectedItem()).equals("Circus"))
        selectedLanguage = "circus";
    
    manager = new SectionManager(selectedLanguage);
    manager.setProperty("czt.path", file.getParent());
    
    FileSource source = new FileSource(file);
    
    //set markup selection
    if(((String)markupCombo.getSelectedItem()).equals("Latex")){
      source.setMarkup(Markup.LATEX);
      source.setEncoding("Default");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("UTF8")){
      source.setMarkup(Markup.UNICODE);
      source.setEncoding("utf8");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("UTF16")){
      source.setMarkup(Markup.UNICODE);
      source.setEncoding("utf16");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("XML")){
      source.setMarkup(Markup.ZML);
    }
    
    manager.put(new Key(source.getName(), Source.class), source);

    try {
      FileOutputStream fileStream =
        new FileOutputStream(getSettingsFileName());
      ObjectOutputStream os = new ObjectOutputStream(fileStream);
      os.writeObject(file.getPath());
      os.close();
    }
    catch (Exception e) {
      //e.printStackTrace();
    }

    try {
      Spec spec = (Spec)
      manager.get(new Key(source.getName(), Spec.class));
      TermTreeNode node = new TermTreeNode(0, spec, null);
      if ("circus".equals(selectedLanguage)) {
        node.setToStringVisitor(new net.sourceforge.czt.circus.util.ConcreteSyntaxDescriptionVisitor());
      }
      else {
        node.setToStringVisitor(new ConcreteSyntaxDescriptionVisitor());
      }
      treeView = new JTree(node);
      scrollTreeStructure.setViewportView(treeView);

      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          String sectionName = zSect.getName();
          System.out.println(sectionName);
          if (typecheckCheckBox.isSelected()) {
            manager.get(new Key(sectionName,SectTypeEnvAnn.class));
          }
          if (zSect.getParaList() instanceof ZParaList && 
              ((ZParaList) zSect.getParaList()).size() > 0) {
            nrOfZSects++;
          }
        }
      }
      if (nrOfZSects < 1) {
        String msg = "WARNING: No Z sections found in " + source;
        //resultListModel.addElement(msg);
        //resultList.setModel(resultListModel);
        resultConsole.append(msg);
      }
      statusBar.setText("Finished parsing "+file.getName());
      saveas.setEnabled(true);
      close.setEnabled(true);
    }
    catch (CommandException exception) {
      printErrors(exception);
    }
    catch (Throwable e) {
      String message =
        "Caught " + e.getClass().getName() + ": " + e.getMessage();
        //resultListModel.addElement(message);
        //resultList.setModel(resultListModel);
        resultConsole.append(message);
    }
  }

  public void ZLive(){
    Runnable zliveConsole = new ZLiveConsole();
    Thread zliveConsoleThread = new Thread(zliveConsole);
    zliveConsoleThread.start();
    //execute(resultConsole,command);
  }
  
  public class ZLiveConsole implements Runnable, ActionListener{
    JFrame consoleFrame = new JFrame("ZLive");
    JTextArea consoleArea = new JTextArea();
    JScrollPane consoleScroller = new JScrollPane(consoleArea);
    JTextField inputField = new JTextField(15);
    JButton executeButton = new JButton("Execute");
    JPanel inputPanel = new JPanel();
    private ZLive zlive_ = new ZLive();;
    private TextUI ui = new TextUI(zlive_, null);
    
    public void run(){
      //executeButton.setMnemonic(KeyEvent.VK_ENTER);
      inputPanel.add(BorderLayout.CENTER, inputField);
      inputPanel.add(BorderLayout.EAST, executeButton);            
      consoleFrame.getContentPane().add(BorderLayout.NORTH, inputPanel);
      consoleFrame.getContentPane().add(BorderLayout.CENTER, consoleScroller);
      consoleFrame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
      consoleFrame.setSize(300,200);
      consoleFrame.setVisible(true);
      executeButton.addActionListener(this);
      
    }
    
    public void execute(/*Console console,**/ JTextArea output, String command)
  {
    if (! command.equals("")) {
      String parts[] = command.split(" ",2);
      StringWriter out = new StringWriter();
      ui.setOutput(new PrintWriter(out));
      ui.processCmd(parts[0], parts.length > 1 ? parts[1] : "");
      output.append(out.toString());
    }
    //output.commandDone();
  }
    
    public void actionPerformed(ActionEvent event){
      if(event.getSource() == executeButton){
        consoleArea.append(inputField.getText()+"\n");
        execute(consoleArea,inputField.getText());
        inputField.setText("");
        inputField.requestFocus();
      }
    }
  }
      
  
  /**
   *  Description of the Method
   *
   *@param  event  Description of the Parameter
   */
  public void actionPerformed(ActionEvent event)
  {
    if(event.getSource() == startConsole){
      ZLive();
    }
    
    if(event.getSource() == czthelp){
      helpFrame.setSize(600,600);
      helpFrame.setVisible(true);
    }
    /*int n = 0;**/
    //display the spec dialog
    if (event.getSource() == open) {
      if(!(statusBar.equals("status"))){
        statusBar.setText("status");
      }
      specDialog.setVisible(true);
    }
    //choose a file
    if (event.getSource() == specBrowseButton) {
      int returnValOpen = chooser.showOpenDialog(frame);
      if (returnValOpen == JFileChooser.APPROVE_OPTION) {
        specText.setText(chooser.getSelectedFile().getPath());
        
        if(specText.getText().endsWith("zed")||specText.getText().endsWith("tex")){
          markupCombo.setSelectedItem("Latex");
        }
        if(specText.getText().endsWith("utf8")){
          markupCombo.setSelectedItem("UTF8");
        }
        if(specText.getText().endsWith("utf16")){
          markupCombo.setSelectedItem("UTF16");
        }
        if(specText.getText().endsWith("xml")||specText.getText().endsWith("zml")){
          markupCombo.setSelectedItem("XML");
        }
      }
    }
    //load the file
    if (event.getSource() == specOKButton) {
      if (!specText.equals("")) {
        file = new File(specText.getText());
        if (!file.isFile()) {
          file = null;
          JOptionPane.showMessageDialog(frame,
            "File Does Not Exist",
            "Error",
            JOptionPane.ERROR_MESSAGE);
        }
        else {
          loadFile();
        }
      }
    }
    //if the cancel button is clicked on the spec dialog then hid it
    if (event.getSource() == specCancelButton) {
      specDialog.setVisible(false);
    }
    //save
    if (event.getSource() == saveasLatex) {
      String[] s = (file.getPath()).split("[.]");
      chooser.setSelectedFile(new File(s[0]+".tex"));
      int returnValSave = chooser.showSaveDialog(frame);
      if (returnValSave == JFileChooser.APPROVE_OPTION) {
        fileForExporting = chooser.getSelectedFile();
        saveSpec(fileForExporting.getPath(),"latex");
      }
    }
        if (event.getSource() == saveasUnicode8) {
      String[] s = (file.getPath()).split("[.]");
      chooser.setSelectedFile(new File(s[0]+".utf8"));
      int returnValSave = chooser.showSaveDialog(frame);
      if (returnValSave == JFileChooser.APPROVE_OPTION) {
        fileForExporting = chooser.getSelectedFile();
        saveSpec(fileForExporting.getPath(),"utf8");
      }
    }
        if (event.getSource() == saveasUnicode16) {
      String[] s = (file.getPath()).split("[.]");
      chooser.setSelectedFile(new File(s[0]+".utf16"));
      int returnValSave = chooser.showSaveDialog(frame);
      if (returnValSave == JFileChooser.APPROVE_OPTION) {
        fileForExporting = chooser.getSelectedFile();
        saveSpec(fileForExporting.getPath(),"utf16");
      }
    }
        if (event.getSource() == saveasXML) {
      String[] s = (file.getPath()).split("[.]");
      chooser.setSelectedFile(new File(s[0]+".xml"));
      int returnValSave = chooser.showSaveDialog(frame);
      if (returnValSave == JFileChooser.APPROVE_OPTION) {
        fileForExporting = chooser.getSelectedFile();
        saveSpec(fileForExporting.getPath(),"xml");
      }
    }
    //close the project and set back to defaults
    if (event.getSource() == close) {
      closeProject();
    }
    //exit program and asks if user wants to save if a file is opened
    if (event.getSource() == exit) {
        System.exit(0);
    }
  }

}
