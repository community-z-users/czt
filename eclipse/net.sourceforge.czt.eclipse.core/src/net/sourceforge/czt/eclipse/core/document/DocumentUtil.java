package net.sourceforge.czt.eclipse.core.document;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.core.parser.StringFileSource;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;

public class DocumentUtil
{

  /**
   * Tries to resolve the file path of the given source object.
   * 
   * @param source
   * @return the path, or <code>null</code> if could not resolve it
   */
  public static String getPath(Source source) {
    if (source instanceof FileSource) {
      FileSource fileSource = (FileSource) source;
      // TODO something more deterministic than toString() to get the path?
      return fileSource.toString();
    }
    
    if (source instanceof StringFileSource) {
      return ((StringFileSource) source).getPath();
    }
    
    return null;
  }
  
  public static String print(Term term, SectionManager sectInfo, String sectName, Markup markup,
      int textWidth, boolean display) throws CommandException
  {

    SectionManager sectMan = sectInfo.clone();

    // TODO externalise preferences?
    sectMan.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, String.valueOf(textWidth));
    sectMan.setProperty(PrintPropertiesKeys.PROP_PRINTING_ONTHEFLY_SECTION_NAME, sectName);

    if ("zeves".equals(sectMan.getDialect())) {
      sectMan.setProperty(PrintPropertiesKeys.PROP_PRINT_ZEVES, String.valueOf(true));
    }
    
    // set pretty-printing for structured goals
    sectMan.setProperty(PrintPropertiesKeys.PROP_PRINTING_STRUCTURED_GOAL, String.valueOf(true));
    
    String keyId = "zeditor-utils-print";
    sectMan.put(new Key<Term>(keyId, Term.class), term);
    CztPrintString out = sectMan.get(getPrintKey(keyId, markup));

    return tidyPrinted(out.toString(), markup, display);
  }
  
  private static Key<? extends CztPrintString> getPrintKey(String keyId, Markup markup)
  {
    switch (markup) {
      case UNICODE :
        return new Key<UnicodeString>(keyId, UnicodeString.class);
      case ZML :
        return new Key<XmlString>(keyId, XmlString.class);
        // use LaTeX by default
      case LATEX :
      default :
        return new Key<LatexString>(keyId, LatexString.class);
    }
  }
  
  public static String tidyPrinted(String result, Markup markup, boolean display)
  {
    result = result.replace("[ ", "[").replace(" ]", "]")//.replace(" [", "[")
                   .replace(" ,", ",").replace(" ;", ";")
                   .replace("( ", "(").replace(" )", ")")
                   .replace("{ ", "{").replace(" }", "}")
                   .replace(" : ", ": ");

    if (markup == Markup.LATEX) {
      result = result.replace("\\_ \\_ ", "\\_\\_");

      if (display) {
        // clear \t0 .. \t9 symbols
        for (int index = 0; index <= 9; index++) {
          result = result.replace("\\t" + index, "");
        }
      }
    }

    return clean(result);
  }
  
  public static String clean(String text)
  {
    /*
     * This special clean function is necessary, because CZT sometimes
     * uses strange characters, e.g. #8232, which mess up the output.
     */
    return text.replace("\u2028", "");
  }

}
