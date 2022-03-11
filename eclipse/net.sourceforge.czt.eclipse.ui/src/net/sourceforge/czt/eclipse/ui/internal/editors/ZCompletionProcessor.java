package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map.Entry;
import java.util.AbstractMap.SimpleEntry;

import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.session.Markup;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.texteditor.HippieProposalProcessor;

/**
 * A content-assist (completion) support for Z editors. Currently it provides content
 * assist for Z character input. The character completion support is available for both
 * unicode and LaTeX input. The proposals are generated based on matching on LaTeX 
 * commands or character descriptions.
 * 
 * Furthermore, simple word matching is enabled by available Eclipse functionality.
 * 
 * @author Andrius Velykis
 */
public class ZCompletionProcessor implements IContentAssistProcessor
{

  /**
   * Enumerated match types which order dictates sorting of proposals.
   *  
   * @author Andrius Velykis
   */
  private enum CompletionMatchType {
    CHAR_LATEX_FULL,
    CHAR_LATEX_NAME,
    CHAR_DESC
  }
  
  private static final ICompletionProposal[] NO_PROPOSALS= new ICompletionProposal[0];
  private static final IContextInformation[] NO_CONTEXTS= new IContextInformation[0];
  
  private String lastError = null;
  
  private final ZEditor editor;
  
  /**
   * A word completion provider
   */
  private final IContentAssistProcessor wordCompletionProcessor = new HippieProposalProcessor();

  public ZCompletionProcessor(ZEditor editor)
  {
    this.editor = editor;
  }

  /**
   * Method declared on IContentAssistProcessor
   */
  @Override
  public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset)
  {
    clearState();
    
    try {

      String prefix = getPrefix(viewer, offset);
      
      if (prefix == null || prefix.length() == 0) {
        return NO_PROPOSALS;
      }
      
      ZDialectSupport dialectSupport = ZDialectSupport.INSTANCE;
      ZCharTable characterTable = dialectSupport.getCharacterTable(dialectSupport.getCurrentDialect());
      
      List<Entry<ICompletionProposal, CompletionMatchType>> rankedProposals = 
          new ArrayList<Entry<ICompletionProposal, CompletionMatchType>>();
      
      // try matching characters in the table
      List<ZChar> zChars = getCharacters(characterTable);
      for (ZChar zChar : zChars) {
        CompletionMatchType matchType = matchZChar(prefix, zChar, offset);
        if (matchType != null) {
          rankedProposals.add(rankedProposal(
              new ZCharCompletionProposal(editor.getMarkup(), prefix, zChar, offset), matchType));
        }
      }

      // sort by CompletionMathType order
      Collections.sort(rankedProposals, new Comparator<Entry<ICompletionProposal, CompletionMatchType>>()
      {
        @Override
        public int compare(Entry<ICompletionProposal, CompletionMatchType> o1,
            Entry<ICompletionProposal, CompletionMatchType> o2)
        {
          return o1.getValue().compareTo(o2.getValue());
        }
      });
      
      List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>();
      for (Entry<ICompletionProposal, CompletionMatchType> rankedProp : rankedProposals) {
        proposals.add(rankedProp.getKey());
      }
      
      // debug only, displays the current prefix
//      proposals.add(new CompletionProposal(
//          prefix, offset, prefix.length(), prefix.length(), null, prefix, null, null));

      
      // also add word completion proposals
      proposals.addAll(Arrays.asList(wordCompletionProcessor.computeCompletionProposals(viewer, offset)));
      
      return proposals.toArray(new ICompletionProposal[proposals.size()]);
      
    }
    catch (BadLocationException e) {
      lastError = e.getMessage();
      // ignore and return no proposals
      return NO_PROPOSALS;
    }
  }
  
  private List<ZChar> getCharacters(ZCharTable characterTable) {
    
    if (characterTable == null) {
      return Collections.emptyList();
    }
    
    Object[][] charTable = characterTable.getZCharTable();
    List<ZChar> characters = new ArrayList<ZChar>();
    
    for (int r = 0; r < charTable.length; r++) {

      int cols = charTable[r].length;

      // start from 1, because the first column is title
      for (int c = 1; c < cols; c++) {
        ZChar zChar = (ZChar) charTable[r][c];
        if (zChar != null) {
          characters.add(zChar);
        }
      }
    }
    
    return characters;
  }
  
  private CompletionMatchType matchZChar(String prefix, ZChar zChar, int offset)
  {
    
    // lower case the prefix for case-insensitive matching
    prefix = prefix.toLowerCase();
    
    // match the LaTeX prefix (lower case as well, for case-insensitivity)
    String latex = zChar.getLatex().toLowerCase();
    if (latex.startsWith(prefix)) {
      return CompletionMatchType.CHAR_LATEX_FULL;
    }
    
    // match the latex name, e.g. if someone is typing "cup", "\cup" would be matched
    if (latex.startsWith("\\" + prefix)) {
      return CompletionMatchType.CHAR_LATEX_NAME;
    }
    
    // also try matching the description, 
    // e.g. allow someone to type "Partial" to have "pfun" proposal
    String desc = zChar.getDescription().toLowerCase();
    /*
     * first split the description, if it has many words - we will allow matching 
     * on every word, so that both "Partial" and "Function" give "pfun" proposal.
     */
    String[] descWords = desc.split(" ");
    for (String descWord : descWords) {
      if (descWord.startsWith(prefix)) {
        return CompletionMatchType.CHAR_DESC;
      }
    }
    
    return null;
  }
  
  private Entry<ICompletionProposal, CompletionMatchType> rankedProposal(
      ICompletionProposal proposal, CompletionMatchType type)
  {
   return new SimpleEntry<ICompletionProposal, CompletionMatchType>(proposal, type);
  }
  
  private void clearState()
  {
    lastError = null;
  }
  
  private String getPrefix(ITextViewer viewer, int offset) throws BadLocationException
  {
    IDocument doc = viewer.getDocument();
    if (doc == null || offset > doc.getLength())
      return null;

    int length = 0;
    while (--offset >= 0 && !Character.isWhitespace(doc.getChar(offset))) {
      length++;
    }

    return doc.get(offset + 1, length);
  }

  /**
   * Method declared on IContentAssistProcessor
   */
  @Override
  public IContextInformation[] computeContextInformation(ITextViewer viewer,
      int documentOffset)
  {
    return NO_CONTEXTS;
  }

  /**
   * Method declared on IContentAssistProcessor
   */
  @Override
  public char[] getCompletionProposalAutoActivationCharacters()
  {
    return new char[]{'\\'};
  }

  /**
   * Method declared on IContentAssistProcessor
   */
  @Override
  public char[] getContextInformationAutoActivationCharacters()
  {
    return null;
  }

  /**
   * For Context information
   * 
   * Method declared on IContentAssistProcessor
   */
  @Override
  public IContextInformationValidator getContextInformationValidator()
  {
    return null;
  }

  /**
   * Method declared on IContentAssistProcessor
   */
  @Override
  public String getErrorMessage()
  {
    return lastError;
  }
  
  private static class ZCharCompletionProposal implements ICompletionProposal {

    private final Markup markup;
    
    private final String prefix;
    private final ZChar zChar;
    private int offset;
    
    public ZCharCompletionProposal(Markup markup, String prefix, ZChar zChar, int offset)
    {
      this.markup = markup;
      this.prefix = prefix;
      this.zChar = zChar;
      this.offset = offset;
    }

    @Override
    public void apply(IDocument document)
    {
      int replacementLength = prefix.length();
      int replacementOffset = offset - replacementLength;
      
      try {
        document.replace(replacementOffset, replacementLength, getReplacementString());
      }
      catch (BadLocationException x) {
        // ignore
      }
    }
    
    private String getReplacementString() {
      return markup == Markup.UNICODE ? zChar.getUnicode() : zChar.getLatex();
    }

    @Override
    public Point getSelection(IDocument document)
    {
      // TODO
      return null;
//      return new Point(fOffset + fString.length(), 0);
    }

    @Override
    public String getAdditionalProposalInfo()
    {
      // for multi-line replacements, display them here 
      String replacementStr = getReplacementString();
      if (replacementStr.contains("\n")) {
        return replacementStr;
      }
      
      return null;
    }

    @Override
    public String getDisplayString()
    {
      
      String label = zChar.getLabel();
      String replStr = getReplacementString();

      String typeStr = "";
      if (!label.equals(replStr)) {
        // if label is different from what is typed, display the typed text
        // e.g. for LaTeX input, or for complex unicode input
        
        // if replacement is newline, use just the first line
        int nlIndex = replStr.indexOf("\n");
        if (nlIndex > 0) {
          replStr = replStr.substring(0, nlIndex) + "...";
        }
        
        typeStr = replStr + " : ";
      }
      
      return label + "\t" + typeStr + zChar.getDescription();
    }

    @Override
    public Image getImage()
    {
      return null;
    }

    @Override
    public IContextInformation getContextInformation()
    {
      return null;
    }

  }
}
