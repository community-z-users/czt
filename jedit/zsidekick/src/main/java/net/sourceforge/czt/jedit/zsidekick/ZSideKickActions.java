/*
 * ZSideKickActions.java
 * Copyright (C) 2006, 2007 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package net.sourceforge.czt.jedit.zsidekick;

import errorlist.DefaultErrorSource;
import errorlist.ErrorSource;
import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import javax.swing.JOptionPane;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.OldLatexString;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;

import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.prover.ProofTree;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.ZSect;
import org.gjt.sp.jedit.Buffer;
import org.gjt.sp.jedit.Mode;
import org.gjt.sp.jedit.View;
import org.gjt.sp.jedit.jEdit;
import org.gjt.sp.jedit.textarea.JEditTextArea;
import org.gjt.sp.jedit.textarea.Selection;
import sidekick.SideKickParsedData;

public class ZSideKickActions 
{
  public static ParsedData getParsedData(View view)
  {
    final SideKickParsedData data = SideKickParsedData.getParsedData(view);
    if (data instanceof ParsedData) {
      return (ParsedData) data;
    }
    reportError(view, "Buffer hasn't been parsed by a CZT parser.");
    return null;
  }

  public static void toLatex(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key<LatexString> key = new Key<LatexString>(view.getBuffer().getPath(), LatexString.class);
      LatexString latex = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding",
                               System.getProperty( "file.encoding"));
      buffer.setMode(latex.getExtension().toString() + "latex");
      buffer.insert(0, latex.toString());
    }
  }

  public static void toOldLatex(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key<OldLatexString> key = new Key<OldLatexString>(view.getBuffer().getPath(), OldLatexString.class);
      OldLatexString latex = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding",
                               System.getProperty( "file.encoding"));
      buffer.setMode(latex.getExtension().toString() + "latex");
      buffer.insert(0, latex.toString());
    }
  }

  public static void toUnicode(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key<UnicodeString> key = new Key<UnicodeString>(view.getBuffer().getPath(), UnicodeString.class);
      UnicodeString unicode = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding", "UTF-16");
      buffer.setMode(unicode.getExtension().toString());
      buffer.insert(0, unicode.toString());
    }
  }

  public static void toXml(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key<XmlString> key = new Key<XmlString>(view.getBuffer().getPath(), XmlString.class);
      XmlString xml = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding", "UTF-8");
      buffer.insert(0, xml.toString());
    }
  }

  public static void showOptions(View view)
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null && parsedData.getManager() != null)
    {
      JOptionPane.showMessageDialog(view, parsedData.getManager().getProperties().toString().replaceAll(", ", "\n "), "CZT Properties", JOptionPane.INFORMATION_MESSAGE);
    }
    else
    {
      JOptionPane.showMessageDialog(view, "No manager created yet. Parse first!", "CZT Properties", JOptionPane.INFORMATION_MESSAGE);
    }
    if (ZSideKickPlugin.debug_)
    {
      String jEditlog = (view.getBuffer() != null ? view.getBuffer().getDirectory() : "./");
      jEditlog += jEditlog.endsWith("/") ?  "jedit-log.txt" : "/jedit-log.txt";
      try
      {
        jEdit.getProperties().store(new java.io.FileWriter(jEditlog), "show-options");
        JOptionPane.showMessageDialog(view, "Saved jEdit properties to " + jEditlog, "CZT Properties", JOptionPane.INFORMATION_MESSAGE);
      }
      catch (IOException ex)
      {
         JOptionPane.showMessageDialog(view, "Failed to save jEdit properties to " + jEditlog, "CZT Properties", JOptionPane.ERROR_MESSAGE);
      }
    }
  }

  @SuppressWarnings("deprecation")
private static final DefaultErrorSource vcgErrors_ = new DefaultErrorSource("VCG errors");

  /**
   *
   * @param <R>
   * @param view
   * @param utils
   * @param vcFileNameSuffix
   * @throws CommandException
   */
  public static <T, B> void vcg(View view, VCGUtils<T, B> utils, String vcFileNameSuffix) throws CommandException
  {
    vcgErrors_.clear();
    ErrorSource.unregisterErrorSource(vcgErrors_);
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) 
    {
      SectionManager manager = parsedData.getManager();
      Buffer buffer = parsedData.getBuffer();
      final String bufferPath = buffer.getPath(); // full qualified file name
      final File file = new File(bufferPath);
      final String name = file.getName(); // just last name of file
      //final String path = file.getParent() != null ? file.getParent() : "."; // just the file directory
      try
      {
        final String dcFileName = VCGUtils.getVCFileName(name, vcFileNameSuffix);
        utils.setSectionManager(manager);
        ZSideKickPlugin.setProperties(manager); // MUST BE AFTER SET SECT MANAGER TO AVOID DEFAULT OVERRIDE !
        if (ZSideKickPlugin.debug_) { showOptions(view); }
        utils.vcgToFile(file);
//        DCVCEnvAnn r = manager.get(new Key<DCVCEnvAnn>(VCGUtils.getSourceName(name), DCVCEnvAnn.class));
//        JOptionPane.showMessageDialog(view, "DCVC size = " + r.getVCs().size());
        Buffer bufferDC = jEdit.openFile(view, dcFileName);
        bufferDC.setStringProperty("encoding", System.getProperty( "file.encoding"));
        String mode = Markup.getMarkup(name).equals(Markup.LATEX) ? "latex" : "";
        buffer.setMode(manager.getDialect() + mode);
        buffer.reload(jEdit.getActiveView());
      }
      catch (CommandException e)
      {
        if (e instanceof VCCollectionException &&
            e.getCause() != null && e.getCause() instanceof VCGException &&
            e.getCause().getCause() instanceof DefinitionException)
        {

          //JOptionPane.showMessageDialog(view, "Could not calculate VCs with " + utils.getVCG().getClass().getSimpleName() + " for " + name
          //  + ". Detailed error message:\n" + ((DefinitionException)e.getCause().getCause()).getMessage(true), "Command Error!", JOptionPane.ERROR_MESSAGE);
          CztParser.printErrors(((DefinitionException)e.getCause().getCause()).getErrors(), buffer, vcgErrors_);
          if (vcgErrors_.getErrorCount() != 0)
          {
            ErrorSource.registerErrorSource(vcgErrors_);
          }
        }
        else
        {
          e.printStackTrace(System.err);
          JOptionPane.showMessageDialog(view, "Could not calculate VCs with " + utils.getVCG().getClass().getSimpleName() + " for " + name
            + ". Detailed error message:\n" + e.getMessage(), "Command Error!", JOptionPane.ERROR_MESSAGE);
        }
      }
    }
  }

  public static WffHighlight getWffHighlight(View view)
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      return parsedData.getWffHighlight();
    }
    return null;
  }

  public static void highlightNextWff(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      wffHighlight.next();
      Term term = wffHighlight.getSelectedWff();
      if (term != null) {
        String message;
        ParsedData parsedData = getParsedData(view);
        if (parsedData == null)
          message = term.accept(new net.sourceforge.czt.z.util.ZConcreteSyntaxDescriptionVisitor());
        else
        {
          Buffer buffer = getParsedData(view).getBuffer();
          Mode mode = buffer.getMode();
          if (mode != null && mode.getName() != null && mode.getName().startsWith("circus"))
            message = term.accept(new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor());
          else
            message = term.accept(new net.sourceforge.czt.z.util.ZConcreteSyntaxDescriptionVisitor());
        }
        view.getStatus().setMessage(message);
      }
    }
  }

  public static Term getSelectedTerm(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      return wffHighlight.getSelectedWff();
    }
    return null;
  }

  public static Type getTypeForCurrentWff(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term != null) {
        TypeAnn typeAnn = term.getAnn(TypeAnn.class);
        if (typeAnn != null) return typeAnn.getType();
        else reportError(view, "Selected formula doesn't have a type");
      }
      else reportError(view, "No formula selected");
    }
    return null;
  }

  public static void insertTypeForCurrentWff(View view)
  {
    Type type = getTypeForCurrentWff(view);
    if (type != null) {
      net.sourceforge.czt.base.util.BasePrintVisitor visitor = null;
      ParsedData parsedData = getParsedData(view);
      if (parsedData == null)
        visitor = new net.sourceforge.czt.z.util.PrintVisitor();
      else
      {
        Buffer buffer = parsedData.getBuffer();
        Mode mode = buffer.getMode();
        if (mode == null)
          visitor = new net.sourceforge.czt.z.util.PrintVisitor();
        else if (mode.getName().startsWith("circus"))
          visitor = new net.sourceforge.czt.circus.util.PrintVisitor();
        else if (mode.getName().startsWith("oz"))
          visitor = new net.sourceforge.czt.oz.util.PrintVisitor();
        else //if (mode.getName().startsWith("z"))
          visitor = new net.sourceforge.czt.z.util.PrintVisitor();
      }
      final String text = type.accept(visitor);
      final JEditTextArea textArea = view.getTextArea();
      final int caretPos = textArea.getCaretPosition();
      Selection selection = new Selection.Range(caretPos,
                                                caretPos + text.length());
      textArea.setSelectedText(text);
      textArea.setSelection(selection);
    }
  }

  /*
  public static void gotoDefinition(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof ZName) {
        ZRefName refName = (ZRefName) term;
        DeclName declName = refName.getDecl();
        if (declName != null) {
          LocAnn locAnn = (LocAnn) declName.getAnn(LocAnn.class);
          if (locAnn != null && locAnn.getLoc() != null) {
            if (locAnn.getLoc().equals(view.getBuffer().getPath()) &&
                locAnn.getStart() != null) {
              int pos = locAnn.getStart().intValue();
              view.getTextArea().setCaretPosition(pos);
            }
            else {
              String message = "Defined in " + locAnn.getLoc();
              if (locAnn.getLine() != null)
                message += " line " + locAnn.getLine();
              reportMessage(view, message);
            }
          }
          else {
            final String message =
              "Could not find location information for declaring name";
            reportError(view, message);
          }
        }
        else {
          final String message = "Could not find a declaration";
          reportError(view, message);
        }
      }
      else {
        reportError(view, "Highlighted term is not a referencing name");
      }
    }
  }
  */

  public static void prove(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Pred) {
        Pred pred = (Pred) term;
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            final String section = zSect.getName();
            try {
              RuleTable rules = 
                manager.get(new Key<RuleTable>(section, RuleTable.class));
              if (rules != null) {
                ProofTree.createAndShowGUI(
                  ProverUtils.createSequent(pred, true),
                  rules,
                  manager,
                  section);
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
              e.printStackTrace();
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        reportError(view, "Highlighted term is not a predicate");
      }
    }
  }

  public static void innermost(View view)
    throws UnboundJokerException
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      CopyVisitor copy = new CopyVisitor(ProverUtils.FACTORY);
      term = term.accept(copy);
      ParsedData parsedData = getParsedData(view);
      if (parsedData != null) {
        SectionManager manager = parsedData.getManager();
        ZSect zSect = wffHighlight.findZSectForCurrentWff();
        if (zSect != null) {
          String section = zSect.getName();
          try {
            RuleTable rules = 
              manager.get(new Key<RuleTable>(section, RuleTable.class));
            if (rules != null) {
              RewriteVisitor rewriter =
                new RewriteVisitor(rules, manager, section);
              Term result = Strategies.innermost(term, rewriter);
              if (! replaceWff(term, result, view, manager, section)) {
                reportError(view, "Rewriting failed");
              }
            }
            else {
              reportError(view, "Cannot find rules");
            }
          }
          catch (CommandException e) {
            e.printStackTrace();
            reportError(view, "Cannot get rule table");
          }
        }
        else {
          reportError(view, "Cannot find Z section for selected term");
        }
      }
    }
  }

  public static void interactive_rewrite(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Expr ||
          term instanceof Pred ||
          term instanceof SchText) {
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            String section = zSect.getName();
            try {
              RuleTable rules = 
                manager.get(new Key<RuleTable>(section, RuleTable.class));
              if (rules != null) {
                if (term instanceof Expr) {
                  ProofTree.createAndShowGUI(
                     ProverUtils.createRewriteSequent((Expr) term, true),
                     rules,
                     manager,
                     section);
                }
                else if (term instanceof Pred) {
                  ProofTree.createAndShowGUI(
                     ProverUtils.createRewriteSequent((Pred) term, true),
                     rules,
                     manager,
                     section);
                }
                else {
                  ProofTree.createAndShowGUI(                     
                     ProverUtils.createRewriteSequent((SchText) term, true),
                     rules,
                     manager,
                     section);
                }
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
              e.printStackTrace();
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        final String msg = "Highlighted term is neither a predicate " +
          "nor an expression nor a schema text";
        reportError(view, msg);
      }
    }
  }

  public static int getColumn(int pos, View view)
  {
    final JEditTextArea textArea = view.getTextArea();
    final int line = textArea.getLineOfOffset(pos);
    return pos - textArea.getLineStartOffset(line);
  }

  private static Markup getMarkup(View view)
  {
    String modeName = view.getBuffer().getMode().toString();
    return modeName.endsWith("latex") ? Markup.LATEX : Markup.UNICODE;
  }

  public static boolean replaceWff(Term oldTerm, Term newTerm, View view,
                                   SectionManager manager, String section)
  {
    if (newTerm != null && oldTerm != newTerm) {
      final LocAnn locAnn = oldTerm.getAnn(LocAnn.class);
      final int start = locAnn.getStart().intValue();
      Selection selection =
        new Selection.Range(start,
                            start + locAnn.getLength().intValue());
      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(newTerm, writer, manager, section, getMarkup(view));
      }
      catch (Exception e) {
        e.printStackTrace();
        net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter jaxbWriter =
          new net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter();
        jaxbWriter.write(newTerm, writer);
      }
      replaceSelection(view, selection, writer.toString());
      return true;
    }
    return false;
  }

  public static void prettyPrint(View view, int width)
    throws Exception
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      ParsedData parsedData = getParsedData(view);
      if (parsedData != null) {
        SectionManager manager = parsedData.getManager();
        manager.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, "" + width);
        ZSect zSect = wffHighlight.findZSectForCurrentWff();
        if (zSect != null) {
          String section = zSect.getName();
          final LocAnn locAnn = term.getAnn(LocAnn.class);
          final int start = locAnn.getStart().intValue();
          Selection selection =
            new Selection.Range(start,
                                start + locAnn.getLength().intValue());
          StringWriter writer = new StringWriter();
          PrintUtils.print(term, writer, manager, section, getMarkup(view));
          replaceSelection(view, selection, writer.toString());
        }
      }
    }
  }

  public static void replaceSelection(View view,
                                      Selection selection,
                                      String text)
  {
    final JEditTextArea textArea = view.getTextArea();
    textArea.setSelection(selection);
    textArea.setSelectedText(text);
    int start = selection.getStart();
    Selection newSelection = new Selection.Range(start, start + text.length());
    textArea.setSelection(newSelection);
  }

  public static void reportMessage(View view, String message)
  {
    view.getStatus().setMessage(message);
  }

  public static void reportError(View view, String message)
  {
    view.getStatus().setMessage(message);
    view.getToolkit().beep();
  }
}
