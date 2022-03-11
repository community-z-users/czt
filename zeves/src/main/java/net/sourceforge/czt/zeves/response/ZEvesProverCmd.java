package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.form.ZEvesLetDef;
import net.sourceforge.czt.zeves.response.form.ZEvesTheoremRef;

/**
 * <!ELEMENT provercmd ((%form; | letdef | theoremref)*, provercmd?)>
 * 
 * The provercmd form allows for the different kinds of commands to be
 * represented.
 * 
 * @author Andrius Velykis
 */
public class ZEvesProverCmd {
  
  private static final Map<String, String> COMMAND_FORMATS;
  
  static {
    Map<String, String> commandFormats = new HashMap<String, String>();
    
    // %1$s - command
    // %2$s - letDefs, comma-separated
    // %3$s - theoremRef
    // %4$s - form, full list, comma-separated
    // %5$s.. %n$s - form, each element separately
    commandFormats.put("apply",                 "apply %5$s");
    commandFormats.put("apply-to-expression",   "apply %5$s to expression %6$s");
    commandFormats.put("apply-to-predicate",    "apply %5$s to predicate %6$s");
    commandFormats.put("cases",                 "cases");
    commandFormats.put("conjunctive",           "conjunctive");
    commandFormats.put("disjunctive",           "disjunctive");
    // equality substitute is a special case, because form may not exist
    commandFormats.put("equality-substitute",   "equality substitute %5$s");
    commandFormats.put("instantiate",           "instantiate %2$s");
    commandFormats.put("invoke",                "invoke %5$s");
    commandFormats.put("invoke-predicate",      "invoke predicate %5$s");
    commandFormats.put("next",                  "next");
    commandFormats.put("prenex",                "prenex");
    commandFormats.put("prove-by-reduce",       "prove by reduce");
    commandFormats.put("prove-by-rewrite",      "prove by rewrite");
    commandFormats.put("rearrange",             "rearrange");
    commandFormats.put("reduce",                "reduce");
    commandFormats.put("rewrite",               "rewrite");
    commandFormats.put("simplify",              "simplify");
    commandFormats.put("split",                 "split %5$s");
    commandFormats.put("trivial-rewrite",       "trivial rewrite");
    commandFormats.put("trivial-simplify",      "trivial simplify");
    commandFormats.put("use",                   "use %3$s");
    commandFormats.put("with-disabled",         "with disabled ( %4$s ) %1$s");
    commandFormats.put("with-enabled",          "with enabled ( %4$s ) %1$s");
    commandFormats.put("with-expression",       "with expression ( %5$s ) %1$s");
    commandFormats.put("with-normalization",    "with normalization %1$s");
    commandFormats.put("with-predicate",        "with predicate ( %5$s ) %1$s");
    commandFormats.put("try-lemma",             "try lemma %5$s");
    
    COMMAND_FORMATS = Collections.unmodifiableMap(commandFormats);
  }
  
  private static final String DEFAULT_FORMAT = "%4$s; %3$s; %2$s; %1$s";
  
  /**
   * <!ATTLIST provercmd name CDATA #REQUIRED>
   */
  @XmlAttribute
  private String name;

  @XmlElement(name = "provercmd")
  private ZEvesProverCmd command;

  @XmlElement(name = "letdef")
  private List<ZEvesLetDef> letDefs = new ArrayList<ZEvesLetDef>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @XmlElement(name = "theoremref")
  private ZEvesTheoremRef theoremRef;

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @Override
  public String toString()
  {
    return print(new ToStringPrinter());
  }
  
  public String print(ZEvesResponsePrinter printer) {
    
    String format = COMMAND_FORMATS.get(name);
    if (format == null) {
      format = name + ": " + DEFAULT_FORMAT;
    }
    
    List<String> letDefsStr = printList(letDefs, printer);
    List<String> formStr = printList(form, printer);
    
    String letDefsConcat = !letDefsStr.isEmpty() ? ZEvesResponseUtil.concat(letDefsStr, ", ") : "";
    String formConcat = !formStr.isEmpty() ? ZEvesResponseUtil.concat(formStr, "; ") : "";
    
    String commandStr = command != null ? command.print(printer) : "";
    String theoremRefStr = theoremRef != null ? printer.print(theoremRef) : "";
    
    List<Object> formatArgs = new ArrayList<Object>(6);
    formatArgs.add(commandStr);
    formatArgs.add(letDefsConcat);
    formatArgs.add(theoremRefStr);
    formatArgs.add(formConcat);
    formatArgs.addAll(formStr);
    
    // add an empty string as the last single-form element
    // this is needed when no form is available, but a format requires (e.g. for equality substitute)
    formatArgs.add("");
    
    return String.format(format, formatArgs.toArray()).trim();
  }
  
  private List<String> printList(List<?> elems, ZEvesResponsePrinter printer) {
    
    List<String> printed = new ArrayList<String>(elems.size());
    
    for (Object e : elems) {
      printed.add(printer.print(e));
    }
    
    return printed;
  }
  
  private static class ToStringPrinter implements ZEvesResponsePrinter {
    
    @Override
    public String print(Object zEvesElem)
    {
      return zEvesElem.toString();
    }
  }
  
}
