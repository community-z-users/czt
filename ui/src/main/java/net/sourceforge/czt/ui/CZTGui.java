package net.sourceforge.czt.ui;

import java.awt.BorderLayout;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import javax.swing.text.html.HTMLFrameHyperlinkEvent;
import javax.swing.text.html.HTMLDocument;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import javax.swing.BoxLayout;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTree;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkListener;
import javax.swing.text.BadLocationException;
import net.sourceforge.czt.animation.eval.TextUI;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.base.impl.BaseFactory;

import net.sourceforge.czt.base.util.TermTreeNode;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.zpatt.util.ZPattConcreteSyntaxDescriptionVisitor;

import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;


/**
 *  Description of the Class
 *
 *@author     yt49
 *@created    July 31, 2007
 */
public class CZTGui implements ActionListener,HyperlinkListener
{
  private SectionManager manager;

  private String softwarename = "Community Z Tools";
  private Image czticon;

  private JFileChooser chooser = new JFileChooser();

  private JFrame frame = new JFrame(softwarename);
  private JFrame helpFrame = new JFrame(softwarename+" Help");
  private JEditorPane helpEditor = new JEditorPane();
  private JScrollPane helpScrollPane = new JScrollPane(helpEditor);

  private JPanel treeViewPanel = new JPanel();
  private JLabel treeViewLabel = new JLabel("Specification Structure Explorer");
  private JTree treeView = null;

  private JPanel resultPanel = new JPanel();
  private JLabel resultLabel = new JLabel("Output");

  private JTextArea resultConsole = new JTextArea();

  private JTextArea statusBar = new JTextArea("status");

  private JPanel specificationPanel = new JPanel();
  private JTextField specText = new JTextField(12);
  private JLabel specificationLabel = new JLabel("Specification:");
  private JButton specBrowseButton = new JButton("...");

  private JPanel specMidPanel = new JPanel();

  private JPanel languagePanel = new JPanel();
  private JLabel languageLabel = new JLabel("Language: ");
  private String[] languageOptions = {"Standard Z","Object Z","Circus","Circus Time","Z Rules", "Z/EVES"};
  private JComboBox<?> languageCombo = new JComboBox<>(languageOptions);

  private JPanel markupPanel = new JPanel();
  private JLabel markupLabel = new JLabel("Markup: ");
  private String[] markupOptions = {"Latex", "UTF8","UTF16", "XML"};
  private JComboBox<?> markupCombo = new JComboBox<>(markupOptions);

  private JPanel typecheckPanel = new JPanel();
  private JLabel typecheckLabel = new JLabel("Typecheck? ");
  private JCheckBox typecheckCheckBox = new JCheckBox("", true);

  private JPanel specOKCancelPanel = new JPanel();
  private JButton specOKButton = new JButton("OK");
  private JButton specCancelButton = new JButton("Cancel");

  final JDialog specDialog = new JDialog(frame, "Specification", true);

  private JMenuBar menubar = new JMenuBar();
  private JMenu filemenu = new JMenu("File");
  private JMenuItem open = new JMenuItem("Open");
  private JMenuItem reload = new JMenuItem("Reload current spec");
  private JMenu console = new JMenu("Animate");
  private JMenuItem startConsole = new JMenuItem("Start ZLive Default");
  private JMenu startConsoleWith = new JMenu("Start ZLive Animator with");
  private JMenu saveas = new JMenu("Export to");
  private JMenuItem saveasLatex = new JMenuItem("Latex");
  private JMenuItem saveasUnicode8 = new JMenuItem("Unicode(utf8)");
  private JMenuItem saveasUnicode16 = new JMenuItem("Unicode(utf16)");
  private JMenuItem saveasXML = new JMenuItem("XML");
  private JMenuItem close = new JMenuItem("Close");
  private JMenuItem exit = new JMenuItem("Exit");
  private JMenu helpmenu = new JMenu("Help");
  private JMenuItem czthelp = new JMenuItem("CZT Help");
  private JMenuItem cztlicense = new JMenuItem("CZT License");
  private JMenuItem cztabout = new JMenuItem("About CZT");
  private JScrollPane scrollResults = new JScrollPane(resultConsole);
  private JScrollPane scrollTreeStructure = new JScrollPane();
  private JSplitPane split = null;
  private File file = null;
  private File fileForExporting = null;
  private FileSource loadSource = null;
  private FileSource saveSource = null;

  private ZLive zlive_ = new ZLive();;
  private TextUI ui = new TextUI(zlive_, null);
  private boolean animationFirstStart;
  private ArrayList<JMenuItem> zliveSectionMenuItems = new ArrayList<JMenuItem>();
  /**
   *variable used to keep count of the characters currently displayed
   *in the output window which can then be used to stop text from being
   *entered/removed at certain points
   */
  private int currentCharCount = 0;

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
    reload.setEnabled(false);
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
      ObjectInputStream os = null;
      try {
        os = new ObjectInputStream(fileStream);
  
        Object pathObject = os.readObject();
        String path = (String) pathObject;
        chooser.setCurrentDirectory(new File(path));
      } finally {
        if (os != null) {
          os.close();
        } else {
          fileStream.close();
        }
      }
    }
    catch (Exception e) {
      //e.printStackTrace();
    }
  }

  /**
   * Retrieves the home path.
   */
  private String getSettingsFileName()
  {
    String userHome = System.getProperty("user.home");
    String result = userHome + "/." + softwarename;
    return result;
  }

  /**
   * The main program for the CZTGui class.
   *
   * @param  args  The command line arguments
   */
  public static void main(String[] args)
  {
    CZTGui gui = new CZTGui();
    gui.go();
  }


  /**
   * Initialises all the graphical components and add listeners for buttons
   * and menu clicks which will then perform operations depends which button
   * or menu item clicked.
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

    split =
      new JSplitPane(JSplitPane.VERTICAL_SPLIT, treeViewPanel, resultPanel);
    split.setDividerLocation(400);

    open.addActionListener(this);
    reload.addActionListener(this);
    startConsole.addActionListener(this);
    saveasLatex.addActionListener(this);
    saveasUnicode8.addActionListener(this);
    saveasUnicode16.addActionListener(this);
    saveasXML.addActionListener(this);
    close.addActionListener(this);
    exit.addActionListener(this);
    czthelp.addActionListener(this);
    cztlicense.addActionListener(this);
    cztabout.addActionListener(this);

    filemenu.add(open);
    filemenu.add(reload);
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
    helpmenu.add(cztlicense);
    helpmenu.add(cztabout);

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

  /**
   * Makes the tree structure view blank.
   */
  private void clearTreeView()
  {
    treeView = null;
    scrollTreeStructure.setViewportView(treeView);
  }

  /**
   * Makes the output text area blank.
   */
  private void clearErrorList()
  {
    //resultListModel.clear();
    resultConsole.setText("");
  }

  /**
   * Resets various graphical components to blank
   * and also disconnect opened file sources.
   */
  private void closeProject()
  {
    file = null;
    specText.setText("");
    frame.setTitle(softwarename);
    reload.setEnabled(false);
    saveas.setEnabled(false);
    close.setEnabled(false);
    startConsoleWith.setEnabled(false);
    zlive_.reset();
    clearTreeView();
    clearErrorList();
    statusBar.setText("status");
  }

  /**
   * Displays a success or failed message on the status bar.
   */
  private void successfulSaveMessage(boolean success)
  {
    if(success == true)
      statusBar.setText("Finished exporting to " + fileForExporting.getName());
    else
      statusBar.setText("Failed exporting to " + fileForExporting.getName());
  }

  /**
   * Converts the current specification into a preferred mark up.
   */
  private void saveSpec(String path,String markup)
  {
    saveSource = new FileSource(file);
    Writer writer = null;

    try{
      try{
        FileOutputStream stream = new FileOutputStream(path);
        if (markup.equals("latex")) {
          final Key<LatexString> key =
            new Key<LatexString>(new FileSource(file).getName(), LatexString.class);
          LatexString latex = manager.get(key);
          writer = new OutputStreamWriter(stream);
          writer.write(latex.toString());
          writer.close();
          successfulSaveMessage(true);
        }
        else if (markup.equals("utf8")) {
          UnicodeString unicode =
            manager.get(new Key<UnicodeString>(saveSource.getName(), UnicodeString.class));
          writer = new OutputStreamWriter(stream, "UTF-8");
          writer.write(unicode.toString());
          writer.close();
          successfulSaveMessage(true);
        }
        else if (markup.equals("utf16")) {
          UnicodeString unicode =
            manager.get(new Key<UnicodeString>(saveSource.getName(), UnicodeString.class));
          writer = new OutputStreamWriter(stream, "UTF-16");
          writer.write(unicode.toString());
          writer.close();
          successfulSaveMessage(true);
        }
        else if (markup.equals("xml")) {
          XmlString xml =
            manager.get(new Key<XmlString>(saveSource.getName(), XmlString.class));
          writer = new OutputStreamWriter(stream, "UTF-8");
          writer.write(xml.toString());
          writer.close();
          successfulSaveMessage(true);
        }
      }
      catch(IOException exception) {
        successfulSaveMessage(false);
      }
    }
    catch(CommandException exception) {
      printErrors(exception);
    }
  }

  /**
   * Uses the caught exception to display errors on the output area
   * by iterating through the list of errors.
   */
  private void printErrors(CommandException exception)
  {
    Throwable cause = exception.getCause();
    saveas.setEnabled(false);
    if (cause instanceof CztErrorList) {
      List<CztError> errors = new ArrayList<CztError>();
      errors.addAll(((CztErrorList) cause).getErrors());
      Collections.sort(errors);
      for (Object o : errors) {
        resultConsole.append(o.toString()+"\n");
      }
    }
    else if (cause instanceof IOException) {
      String message = "Input output error: " + cause.getMessage();
      resultConsole.append(message);
    }
    else {
      String message = cause + getClass().getName();
      resultConsole.append(message);
    }
  }

  private void loadFile()
  {
    statusBar.setText("Reading "+file.getName()+"...done");
    //unable to start zlive with a spec unless no errors
    //and clear the sections each time a new file is opened
    zliveSectionMenuItems.clear();
    startConsoleWith.setEnabled(false);
    animationFirstStart = true;
    reload.setEnabled(true);
    close.setEnabled(true);

    Dialect selectedLanguage = SectionManager.DEFAULT_EXTENSION;
//    String selectedEncoding = "";
    int nrOfZSects = 0;

    clearTreeView();
    clearErrorList();

    //other than zlive command started it should be 0 to allow editing
    currentCharCount = 0;

    specDialog.setVisible(false);

    frame.setTitle(softwarename + " - " + file.getName());

    //obtain language selection
    if(((String)languageCombo.getSelectedItem()).equals("Standard Z"))
      selectedLanguage = Dialect.Z;
    else
      if(((String)languageCombo.getSelectedItem()).equals("Object Z"))
        selectedLanguage = Dialect.OZ;
      else
        if(((String)languageCombo.getSelectedItem()).equals("Circus"))
          selectedLanguage = Dialect.CIRCUS;
        else
          if(((String)languageCombo.getSelectedItem()).equals("Z Rules"))
            selectedLanguage = Dialect.ZPATT;
          else
            if(((String)languageCombo.getSelectedItem()).equals("Z/EVES"))
              selectedLanguage = Dialect.ZEVES;
      else
        if(((String)languageCombo.getSelectedItem()).equals("Circus Time"))
          selectedLanguage = Dialect.CIRCUSTIME;

    manager = new SectionManager(selectedLanguage);
    BaseFactory.resetInstanceCounter();
    loadSource = new FileSource(file);

    String cztpath = manager.getProperty("czt.path");
    String filename = file != null ? file.getParent() : null;
    cztpath = ((cztpath == null || cztpath.isEmpty()) ?
      filename : filename + File.pathSeparator + cztpath);
    if (cztpath != null && !cztpath.isEmpty())
    {
      manager.setProperty("czt.path", cztpath);
      zlive_.getSectionManager().setProperty("czt.path", cztpath);
    }

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
    manager.put(new Key<Source>(loadSource.getName(), Source.class), loadSource);
    zlive_.reset();
    zlive_.getSectionManager().put(new Key<Source>(loadSource.getName(), Source.class), loadSource);

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
      Spec spec =
        manager.get(new Key<Spec>(loadSource.getName(), Spec.class));
      TermTreeNode node = new TermTreeNode(0, spec, null);
      if ("circus".equals(selectedLanguage)) {
        node.setToStringVisitor(new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor());
      }
      else {
        node.setToStringVisitor(new ZPattConcreteSyntaxDescriptionVisitor());
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

          zlive_.getSectionManager().put(new Key<Source>(sectionName, Source.class),loadSource);

          if (typecheckCheckBox.isSelected()) {
            manager.get(new Key<SectTypeEnvAnn>(sectionName,SectTypeEnvAnn.class));
            //only allow animation if typechecking is done
            startConsoleWith.setEnabled(true);
          }
          if (zSect.getParaList() instanceof ZParaList &&
              ((ZParaList) zSect.getParaList()).size() > 0) {
            nrOfZSects++;
          }
        }
      }

      if(!zliveSectionMenuItems.isEmpty()) {
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
      statusBar.setText("Finished parsing "+file.getName() + "; AST instance count = " + BaseFactory.howManyInstancesCreated());

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

  /**
   * Uses the TextUI Class to execute ZLive commands and displays the output
   * in the output text area.
   */
  public void execute(JTextArea output, String command)
  {
    if (! command.equals("")) {
      String parts[] = command.split(" ",2);
      StringWriter out = new StringWriter();
      ui.setOutput(new PrintWriter(out));
      ui.processCmd(parts[0], parts.length > 1 ? parts[1] : "");
      output.append("\n"+out.toString());
    }
  }

  /**
   * Inner Class that listens for the enter key pressed and executes
   * the command and also consumes key presses at certain positions of
   * the text area so that the ZLive prompt and results cannot be
   * removed/modified.
   */
  public class ZLiveConsole implements KeyListener
  {
    /**
     * Handle the key typed event from the text area.
     */
    public void keyTyped(KeyEvent e) {
      if(resultConsole.getCaretPosition()<=(currentCharCount-1)){
        e.consume();
      }
    }

    /**
     * Handle the key-pressed event from the text area.
     */
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
      if(e.getKeyCode()==KeyEvent.VK_DELETE){
        if(resultConsole.getCaretPosition()<=(currentCharCount-1)){
          e.consume();
        }
      }
    }

    /**
     * Handle the key-released event from the text area .
     */
    public void keyReleased(KeyEvent e)
    {
      //no keyReleased events needed
    }

    /**
     * Retrieves the user input command from the text area
     * and passes it to the exceute() method.
     */
    public void zliveGo()
    {
      int linecount = resultConsole.getLineCount();
      int offset = 0;
      int length = 0;
      String command = null;

      //get contents of the last line and check and execute
      try {
        if(linecount > 1){
          offset = resultConsole.getLineStartOffset(linecount-1);
          length = resultConsole.getLineEndOffset(linecount-1)-offset;
          command = resultConsole.getText(offset,length);
        }
        else{
          command = resultConsole.getText();
        }
        if (command.startsWith(zlive_.getCurrentSection())){
          command = command.substring(zlive_.getCurrentSection().length()+2);
          execute(resultConsole,command);
          if (command.equals(""))
            resultConsole.append("\n");
          if (command.equals("reset"))
            startConsoleWith.setEnabled(false);
          showZLivePrompt();
        }
      }
      catch(BadLocationException e){
        e.printStackTrace();
      }
    }
  }

  public void showZLivePrompt()
  {
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

  public void actionPerformed(ActionEvent event)
  {
    //exit program
    if (event.getSource() == exit) {
      System.exit(0);
    }
    try {
      for(int i=0;i<zliveSectionMenuItems.size();i++){
        if(event.getSource() == zliveSectionMenuItems.get(i)){
          if(animationFirstStart){
            zlive_.getSectionManager().get(new Key<Spec>(loadSource.getName(), Spec.class));
            animationFirstStart = false;
          }
          startZLive(event.getActionCommand());
        }
      }

      if(event.getSource() == startConsole) {
        startZLive("ZLiveDefault");
      }

      if(event.getSource() == czthelp) {
        showHtmlPage("czt_help.html");
      }
      if (event.getSource() == cztlicense) {
        showHtmlPage("czt_license.html");
      }
      if (event.getSource() == cztabout) {
        showHtmlPage("czt_about.html");
      }
      /*int n = 0;**/
      //display the spec dialog
      if (event.getSource() == open) {
        if (!(statusBar.getText().equals("status"))) {
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

          if(extension.endsWith("zed")||extension.endsWith("tex")) {
            languageCombo.setSelectedItem("Standard Z");
            markupCombo.setSelectedItem("Latex");
          }
          if (extension.endsWith("zed8")) {
            languageCombo.setSelectedItem("Standard Z");
            markupCombo.setSelectedItem("UTF8");
          }
          if (extension.endsWith("zed16")) {
            languageCombo.setSelectedItem("Standard Z");
            markupCombo.setSelectedItem("UTF16");
          }
          if (extension.endsWith("oz")) {
            languageCombo.setSelectedItem("Object Z");
            markupCombo.setSelectedItem("Latex");
          }
          if (extension.endsWith("oz8")) {
            languageCombo.setSelectedItem("Object Z");
            markupCombo.setSelectedItem("UTF8");
          }
          if (extension.endsWith("oz16")) {
            languageCombo.setSelectedItem("Object Z");
            markupCombo.setSelectedItem("UTF16");
          }
          if (extension.endsWith("circus")) {
            languageCombo.setSelectedItem("Circus");
            markupCombo.setSelectedItem("Latex");
          }
          if (extension.endsWith("circus8")) {
            languageCombo.setSelectedItem("Circus");
            markupCombo.setSelectedItem("UTF8");
          }
          if (extension.endsWith("circus16")) {
            languageCombo.setSelectedItem("Circus");
            markupCombo.setSelectedItem("UTF16");
          }
          if (extension.endsWith("zedpatt")) {
            languageCombo.setSelectedItem("Z Rules");
            markupCombo.setSelectedItem("Latex");
          }
          if (extension.endsWith("zedpatt8")) {
            languageCombo.setSelectedItem("Z Rules");
            markupCombo.setSelectedItem("UTF8");
          }
          if (extension.endsWith("zedpatt16")) {
            languageCombo.setSelectedItem("Z Rules");
            markupCombo.setSelectedItem("UTF16");
          }
          if (extension.endsWith("zev")) {
            languageCombo.setSelectedItem("Z/EVES");
            markupCombo.setSelectedItem("Latex");
          }
          if (extension.endsWith("utf8")) {
            markupCombo.setSelectedItem("UTF8");
          }
          if (extension.endsWith("utf16")) {
            markupCombo.setSelectedItem("UTF16");
          }
          if (extension.endsWith("xml")||extension.endsWith("zml")) {
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
      if(event.getSource() == reload){
        loadFile();
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
    }
    catch (java.lang.OutOfMemoryError ex) {
      resultConsole.append("Out of memory error: "+ex.getLocalizedMessage()+"\n");
      resultConsole.append("Try allocating more memory (eg. java -Xmx512m ...) and restarting...\n");
      throw ex;
    }
    catch (Exception ex) {
      // show the error message in the console panel.
      resultConsole.append("Exception error: "+ex.getLocalizedMessage()+"\n");
    }
  }

  public void hyperlinkUpdate(HyperlinkEvent e)
  {
    if (e.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
      JEditorPane pane = (JEditorPane) e.getSource();
      if (e instanceof HTMLFrameHyperlinkEvent) {
        HTMLFrameHyperlinkEvent  evt = (HTMLFrameHyperlinkEvent)e;
        HTMLDocument doc = (HTMLDocument)pane.getDocument();
        doc.processHTMLFrameHyperlinkEvent(evt);
      }
      else {
        try {
          pane.setPage(e.getURL());
        }
        catch (Throwable t) {
          t.printStackTrace();
        }
      }
    }
  }
  
  public void showHtmlPage(String filename)
  {
    URL url = this.getClass().getResource(filename);
    helpEditor.setContentType("text/html");
    try{
      helpEditor.setPage(url);
    }
    catch(IOException e) {
      throw new RuntimeException("Cannot open help file "+filename, e);
    }
    helpFrame.setVisible(true);
  }
}
