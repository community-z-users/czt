package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.form.ZEvesBlurb;
import net.sourceforge.czt.zeves.response.form.ZEvesNumber;

/**
 * <!ELEMENT zoutput (%para; | zsectionbegin | zsectionend | zsectionproofbegin
 * 							 | zsectionproofend | provercmd | blurb)*>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "zoutput")
public class ZEvesOutput
{

  public static final String UNPRINTABLE_PREDICATE = "An unprintable predicate";
  
  @XmlElement(name = "provercmd")
  private ZEvesProverCmd command;

  @XmlElements({
      // TODO proper classes - not used in Z/EVES at the moment?
      @XmlElement(name = "zsectionbegin"), @XmlElement(name = "zsectionend"),
      @XmlElement(name = "zsectionproofbegin"), @XmlElement(name = "zsectionproofend")})
  private Object sectionTag;

  @XmlElement(name = "blurb")
  private ZEvesBlurb info;

  @XmlAnyElement(lax = true)
  private List<?> para = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  
  private ZEvesProofTrace trace;

  public List<?> getResults()
  {
    return Collections.unmodifiableList(para);
  }

  public Object getFirstResult()
  {
    if (para.isEmpty()) {
      return null;
    }

    return para.get(0);
  }

  public ZEvesProverCmd getCommand()
  {
    return command;
  }

  public ZEvesBlurb getInfo()
  {
    return info;
  }
  
  public ZEvesProofTrace getProofTrace() {
    if (trace == null) {
      trace = new ZEvesProofTrace(getInfo());
    }
    
    return trace;
  }
  
  /**
   * Retrieves the proof case, if this information is available. Proof
   * cases are available for ZEvesOutputs from get-goal-proof-step
   * commands.
   * 
   * The proof case is represented as a list of case numbers, where
   * a subsequent case number represents a deeper proof case. 
   * 
   * @return
   */
  public List<Integer> getProofCase() {
    // proof case is a list of numbers, that go after
    // the proof result (first element in the para)
    // thus take all numbers starting from the second element
    List<Integer> proofCaseNumbers = new ArrayList<Integer>(para.size());
    for (int index = 1; index < para.size(); index++) {
      
      Object zEvesElem = para.get(index);
      if (!(zEvesElem instanceof ZEvesNumber)) {
        continue;
      }
      
      String valStr = ((ZEvesNumber) zEvesElem).getValue();

      try {
        proofCaseNumbers.add(Integer.valueOf(valStr));
      }
      catch (NumberFormatException e) {
        // ignore?
      }
    }
    
    return proofCaseNumbers;
  }

  public boolean isEmpty()
  {
    return command == null && sectionTag == null && info == null && para.isEmpty();
  }

  @Override
  public String toString()
  {

    String cmdStr = command != null ? "Command sent: " + String.valueOf(command) + "\n" : "";
    String infoStr = info != null ? String.valueOf(info) + "\n" : "";
    String sectionStr = sectionTag != null ? String.valueOf(sectionTag) + "\n" : "";

    return cmdStr + infoStr + sectionStr + ZEvesResponseUtil.concat(para, "\n");

  }

}
