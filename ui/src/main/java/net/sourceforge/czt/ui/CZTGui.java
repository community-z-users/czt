package net.sourceforge.czt.ui;


import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.HTMLFrameHyperlinkEvent;
import javax.swing.text.html.HTMLDocument;
import javax.swing.event.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.plaf.basic.BasicHTML;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.net.URL;
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
public class CZTGui implements ActionListener,HyperlinkListener
{
  SectionManager manager;

  String softwarename = "Community Z Tools";
  Image czticon;

  JFileChooser chooser = new JFileChooser();

  JFrame frame = new JFrame(softwarename);
  JFrame helpFrame = new JFrame(softwarename+" Help");
  JEditorPane helpEditor = new JEditorPane();
  JScrollPane helpScrollPane = new JScrollPane(helpEditor);

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
  String[] languageOptions = {"Standard Z","Object Z","Circus","Z Rules"};
  JComboBox languageCombo = new JComboBox(languageOptions);

  JPanel markupPanel = new JPanel();
  JLabel markupLabel = new JLabel("Markup: ");
  String[] markupOptions = {"Latex", "UTF8","UTF16", "XML"};
  JComboBox markupCombo = new JComboBox(markupOptions);

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
  JMenu console = new JMenu("Animate");
  JMenuItem startConsole = new JMenuItem("Start ZLive Default");
  JMenu startConsoleWith = new JMenu("Start ZLive Animator with");
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
  FileSource loadSource = null;
  FileSource saveSource = null;

  private ZLive zlive_ = new ZLive();;
  private TextUI ui = new TextUI(zlive_, null);
  private boolean animationFirstStart;
  ArrayList<JMenuItem> zliveSectionMenuItems = new ArrayList<JMenuItem>();
  //used to stop backspaces at a certain point to avoid deleting the prompt
  //note: pasting text onto the textarea could result in previously undeletable
  //text deletable
  int currentCharCount = 0;
  
  /**
   *  Constructor for the CZTGui object
   */
  public CZTGui()
  {

    //sets a customized icon for the gui instead of the default java cup
    URL iconurl = this.getClass().getResource("images/CZTicon.png");
    ImageIcon icon = new ImageIcon(iconurl);
    czticon = icon.getImage();
    frame.setIconImage(czticon);
    helpFrame.setIconImage(czticon);
    
    //to let gui know whether zlive has parsed a spec already
    animationFirstStart = true;
    
    chooser.setAcceptAllFileFilterUsed(true);
    chooser.addChoosableFileFilter(new CZTFilter());
    specDialog.setLocationRelativeTo(frame);
    statusBar.setEditable(false);
    resultConsole.setEditable(true);
    saveas.setEnabled(false);
    close.setEnabled(false);
    startConsoleWith.setEnabled(false);
    //listen for enter key to execute commands
    resultConsole.addKeyListener(new ZLiveConsole());
    //listen for hyperlink clicks
    helpEditor.setEditable(false);
    helpEditor.addHyperlinkListener(this);

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

    helpFrame.getContentPane().add(BorderLayout.CENTER, helpScrollPane);
    helpFrame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
    helpFrame.setSize(600,600);

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
    console.add(startConsole);
    console.add(startConsoleWith);
    saveas.add(saveasLatex);
    saveas.add(saveasUnicode8);
    saveas.add(saveasUnicode16);
    saveas.add(saveasXML);
    filemenu.add(saveas);
    filemenu.add(close);
    filemenu.add(exit);
    helpmenu.add(czthelp);

    menubar.add(filemenu);
    menubar.add(console);
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
    startConsoleWith.setEnabled(false);
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

    saveSource = new FileSource(file);
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
    manager.get(new Key(saveSource.getName(), UnicodeString.class));
    writer = new OutputStreamWriter(stream, "UTF-8");
    writer.write(unicode.toString());
    writer.close();
    successfulSaveMessage(true);
    }

    if(markup.equals("utf16")){
    UnicodeString unicode = (UnicodeString)
    manager.get(new Key(saveSource.getName(), UnicodeString.class));
    writer = new OutputStreamWriter(stream, "UTF-16");
    writer.write(unicode.toString());
    writer.close();
    successfulSaveMessage(true);
    }

    if(markup.equals("xml")){
    XmlString xml = (XmlString)
    manager.get(new Key(saveSource.getName(), XmlString.class));
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
    //unable to start zlive with a spec unless no errors
    //and clear the sections each time a new file is opened
    zliveSectionMenuItems.clear();
    startConsoleWith.setEnabled(false);
    animationFirstStart = true;
    
    close.setEnabled(true);

    String selectedLanguage = "";
    String selectedEncoding = "";
    int nrOfZSects = 0;

    clearTreeView();
    clearErrorList();
    
    //other than zlive command started it should be 0 to allow editing
    currentCharCount = 0;
    
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
    else
      if(((String)languageCombo.getSelectedItem()).equals("Z Rules"))
        selectedLanguage = "zpatt";

    manager = new SectionManager(selectedLanguage);
    loadSource = new FileSource(file);
    
    manager.setProperty("czt.path", file.getParent());
    zlive_.getSectionManager().setProperty("czt.path", file.getParent());

    //set markup selection
    if(((String)markupCombo.getSelectedItem()).equals("Latex")){
      loadSource.setMarkup(Markup.LATEX);
      loadSource.setEncoding("Default");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("UTF8")){
      loadSource.setMarkup(Markup.UNICODE);
      loadSource.setEncoding("utf8");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("UTF16")){
      loadSource.setMarkup(Markup.UNICODE);
      loadSource.setEncoding("utf16");
    }
    else
    if(((String)markupCombo.getSelectedItem()).equals("XML")){
      loadSource.setMarkup(Markup.ZML);
    }

    manager.put(new Key(loadSource.getName(), Source.class), loadSource);
    zlive_.reset();
    zlive_.getSectionManager().put(new Key(loadSource.getName(), Source.class), loadSource);
    
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
      manager.get(new Key(loadSource.getName(), Spec.class));
      TermTreeNode node = new TermTreeNode(0, spec, null);
      if ("circus".equals(selectedLanguage)) {
        node.setToStringVisitor(new net.sourceforge.czt.circus.util.ConcreteSyntaxDescriptionVisitor());
      }
      else {
        node.setToStringVisitor(new ConcreteSyntaxDescriptionVisitor());
      }
      treeView = new JTree(node);
      scrollTreeStructure.setViewportView(treeView);
      //remove all section items before adding new ones
      startConsoleWith.removeAll();//
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          String sectionName = zSect.getName();

          //add menu items for starting zlive with a prefered specification
          zliveSectionMenuItems.add(new JMenuItem(sectionName));
          
          zlive_.getSectionManager().put(new Key(sectionName, Source.class),loadSource);
          
          if (typecheckCheckBox.isSelected()) {
            manager.get(new Key(sectionName,SectTypeEnvAnn.class));
            //only allow animation if typechecking is done
            startConsoleWith.setEnabled(true);
          }
          if (zSect.getParaList() instanceof ZParaList &&
              ((ZParaList) zSect.getParaList()).size() > 0) {
            nrOfZSects++;
          }
        }
      }
      
      if(!zliveSectionMenuItems.isEmpty()){
        for(int i=0;i<zliveSectionMenuItems.size();i++){
        zliveSectionMenuItems.get(i).addActionListener(this);
        startConsoleWith.add(zliveSectionMenuItems.get(i));
        }
      }
      
      if (nrOfZSects < 1) {
        String msg = "WARNING: No Z sections found in " + loadSource;
        //resultListModel.addElement(msg);
        //resultList.setModel(resultListModel);
        resultConsole.append(msg);
      }
      //only if no errors
      statusBar.setText("Finished parsing "+file.getName());
      
      saveas.setEnabled(true);
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
  
  public void execute(/*Console console,**/ JTextArea output, String command)
  {
    if (! command.equals("")) {
      String parts[] = command.split(" ",2);
      StringWriter out = new StringWriter();
      ui.setOutput(new PrintWriter(out));
      ui.processCmd(parts[0], parts.length > 1 ? parts[1] : "");
      output.append("\n"+out.toString());
    }
    //output.commandDone();
  }

  //listens for the enter key pressed and executes the command
  public class ZLiveConsole implements KeyListener{
  
        /** Handle the key typed event from the text field. */
    public void keyTyped(KeyEvent e) {
      if(resultConsole.getCaretPosition()<=(currentCharCount-1)){
        e.consume();
      }
    }

    /** Handle the key-pressed event from the text field. */
    public void keyPressed(KeyEvent e) {
      if(e.getKeyChar()=='\n'){
        e.consume();
        zliveGo();
      }
      if(e.getKeyChar()=='\b'){
        if(resultConsole.getCaretPosition()<=currentCharCount){
          e.consume();
        }
      }
      if(e.getKeyChar()==KeyEvent.VK_DELETE){
        if(resultConsole.getCaretPosition()<=(currentCharCount-1)){
          e.consume();
        }
      }
    }

    /** Handle the key-released event from the text field. */
    public void keyReleased(KeyEvent e) {
	//no keyReleased events needed
    }
    
    public void zliveGo(){
      int linecount = resultConsole.getLineCount();
      int offset = 0;
      int length = 0;
      
      String command = null;
      
      //get contents of the last line and check and execute
      try{
        if(linecount > 1){
          offset = resultConsole.getLineStartOffset(linecount-1);
          length = resultConsole.getLineEndOffset(linecount-1)-offset;
          command = resultConsole.getText(offset,length);
        }else{
          command = resultConsole.getText();
        }
        if(command.startsWith(zlive_.getCurrentSection())){
          command = command.substring(zlive_.getCurrentSection().length()+2);
          execute(resultConsole,command);
          if(command.equals(""))
            resultConsole.append("\n");
          showZLivePrompt();
        }
      }catch(BadLocationException e){
        e.printStackTrace();
      }
    }
  
  }
  
  public void showZLivePrompt(){
    resultConsole.append(zlive_.getCurrentSection()+"> ");
    currentCharCount = resultConsole.getText().length();
  }
  
  public void startZLive(String sectName){
      try{
        zlive_.setCurrentSection(sectName);
      }catch(CommandException ex){
        resultConsole.append("Error Loading Specification\n");
      }
    
    resultConsole.setText("");
    showZLivePrompt();
  }
  
  /**
   *  Description of the Method
   *
   *@param  event  Description of the Parameter
   */
  public void actionPerformed(ActionEvent event)
  {

    for(int i=0;i<zliveSectionMenuItems.size();i++){
      if(event.getSource() == zliveSectionMenuItems.get(i)){
        if(animationFirstStart){
          try{
            zlive_.getSectionManager().get(new Key(loadSource.getName(), Spec.class));
            animationFirstStart = false;
          }catch(CommandException e){
            e.printStackTrace();
          }
        }
        startZLive(event.getActionCommand());
      }
    }
    
    if(event.getSource() == startConsole){
      startZLive("ZLiveDefault");
    }

    if(event.getSource() == czthelp){
      URL url = this.getClass().getResource("czt_help.html");
      helpEditor.setContentType("text/html");
      
      try{
      helpEditor.setPage(url);
      }catch(IOException e){}
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
        String extension = specText.getText();

        if(extension.endsWith("zed")||extension.endsWith("tex")){
          languageCombo.setSelectedItem("Standard Z");
          markupCombo.setSelectedItem("Latex");
        }
        if(extension.endsWith("zed8")){
          languageCombo.setSelectedItem("Standard Z");
          markupCombo.setSelectedItem("UTF8");
        }
        if(extension.endsWith("zed16")){
          languageCombo.setSelectedItem("Standard Z");
          markupCombo.setSelectedItem("UTF16");
        }
        if(extension.endsWith("oz")){
          languageCombo.setSelectedItem("Object Z");
          markupCombo.setSelectedItem("Latex");
        }
        if(extension.endsWith("oz8")){
          languageCombo.setSelectedItem("Object Z");
          markupCombo.setSelectedItem("UTF8");
        }
        if(extension.endsWith("oz16")){
          languageCombo.setSelectedItem("Object Z");
          markupCombo.setSelectedItem("UTF16");
        }
        if(extension.endsWith("circus")){
          languageCombo.setSelectedItem("Circus");
          markupCombo.setSelectedItem("Latex");
        }
        if(extension.endsWith("circus8")){
          languageCombo.setSelectedItem("Circus");
          markupCombo.setSelectedItem("UTF8");
        }
        if(extension.endsWith("circus16")){
          languageCombo.setSelectedItem("Circus");
          markupCombo.setSelectedItem("UTF16");
        }
        if(extension.endsWith("zedpatt")){
          languageCombo.setSelectedItem("Z Rules");
          markupCombo.setSelectedItem("Latex");
        }
        if(extension.endsWith("zedpatt8")){
          languageCombo.setSelectedItem("Z Rules");
          markupCombo.setSelectedItem("UTF8");
        }
        if(extension.endsWith("zedpatt16")){
          languageCombo.setSelectedItem("Z Rules");
          markupCombo.setSelectedItem("UTF16");
        }
        if(extension.endsWith("utf8")){
          markupCombo.setSelectedItem("UTF8");
        }
        if(extension.endsWith("utf16")){
          markupCombo.setSelectedItem("UTF16");
        }
        if(extension.endsWith("xml")||extension.endsWith("zml")){
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
 
         public void hyperlinkUpdate(HyperlinkEvent e) {
             if (e.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                 JEditorPane pane = (JEditorPane) e.getSource();
                 if (e instanceof HTMLFrameHyperlinkEvent) {
                     HTMLFrameHyperlinkEvent  evt = (HTMLFrameHyperlinkEvent)e;
                     HTMLDocument doc = (HTMLDocument)pane.getDocument();
                     doc.processHTMLFrameHyperlinkEvent(evt);
                 } else {
                     try {
                         pane.setPage(e.getURL());
                     } catch (Throwable t) {
                         t.printStackTrace();
                     }
                 }
             }
         }  
}
