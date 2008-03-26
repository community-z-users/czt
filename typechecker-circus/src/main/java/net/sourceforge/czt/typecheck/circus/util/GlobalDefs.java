/*
 * GlobalDefs.java
 *
 * Created on 27 de Junho de 2005, 17:36
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.circus.util;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionSignatureAnn;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.CommunicationList;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.typecheck.circus.impl.Factory;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZNameList;

/**
 * 
 * @author Leo Freitas
 */
public class GlobalDefs
  extends net.sourceforge.czt.typecheck.z.util.GlobalDefs
{  
  public static final Factory CIRCUS_FACTORY = new Factory();
    
  //non-safe typecast
  public static ActionType actionType(Object o)
  {
    return (ActionType) o;
  }
  
  public static ProcessType processType(Object o)
  {
    return (ProcessType) o;
  }
  
  public static NameSetType nameSetType(Object o)
  {
    return (NameSetType) o;
  }
  
  public static CallAction callAction(Object o)
  {
    return (CallAction)o;
  }
  
  public static CallProcess callProcess(Object o)
  {
    return (CallProcess)o;
  }
  
  public static MuAction muAction(Object o)
  {
    return (MuAction)o;
  }
  
  public static boolean isIgnorePara(Para term)
  {
    return 
      (term instanceof NarrPara) ||
      (term instanceof LatexMarkupPara) ||
      (term instanceof UnparsedPara);      
  }
  
  public static <T> void addNoDuplicates(T source, Collection<T> target)
  {
    if (!target.contains(source))
    {
      target.add(source);
    }    
  }
  
  public static <T> void addNoDuplicates(int index, T source, List<T> target)
  {
    if (!target.contains(source))
    {
      target.add(index, source);
    }    
  }
  
  public static <T> void addAllNoDuplicates(Collection<? extends T> source, Collection<T> target)
  {
    for(T t : source)
    {
      addNoDuplicates(t, target);
    }
  }
  
  public static <T> void addAllNoDuplicates(int index, Collection<? extends T> source, List<T> target)
  {
    for(T t : source)
    {
      addNoDuplicates(index, t, target);
    }
  }
  
  /**
   * This is a convenience method. It filters the getUsedCommunications() communication list
   * so that, within each Communication in the list, we extract the underlying channel name and
   * type for that communication (if present). Note this may include implicit and generic channels. 
   * If no type annotation is available, the signature just contains a list of names.
   */
  public static Signature getUsedChannels(CommunicationList commList)
  {
    // 
    return null;
//    for(Communication comm : getUsedCommunications())
//    {
//    }
  }
  
  /**
   * This is a convenience method. It filters the getUsedCommunications() communication list
   * so that, within each Communication in the list, we extract the underlying channel name 
   * for hat communication (if present). Note this may include generic channels. 
   * Implicit channels have the index added to their names.
   */
  public static Map<CommPattern, ZNameList> getAlphabet()
  {
    return null;
  }
  
  // expand scopes of local vars within aSig ?
  //public static flattenLocalVariables(ActionSignature aSig)
  
  
  public static ActionSignature getActionSignatureFromAnn(Term term)
  {
    ActionSignature result;
    ActionSignatureAnn ann = term.getAnn(ActionSignatureAnn.class);    
    if (ann != null)
    {
      result = ann.getActionSignature();
    }
    else
    {
      result = CIRCUS_FACTORY.createEmptyActionSignature();
    }
    return result;
  }
  
}
