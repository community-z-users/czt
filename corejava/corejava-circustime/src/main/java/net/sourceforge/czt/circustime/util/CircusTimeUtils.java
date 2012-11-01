/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.circustime.util;

import java.math.BigInteger;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusStateAnn;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.OutputFieldAnn;
import net.sourceforge.czt.circus.ast.ParamQualifier;
import net.sourceforge.czt.circus.ast.ProcessD;
import net.sourceforge.czt.circus.ast.ProofObligationAnn;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionTransformerPred;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.CircusFieldList;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessTransformerPred;
import net.sourceforge.czt.circus.ast.CircusNameSetList;
import net.sourceforge.czt.circus.ast.CircusChannelSetList;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.ZName;

/**
 *
 * @author leo
 */
public final class CircusTimeUtils
{

  /**
   * Do not create instances of this class.
   */
  private CircusTimeUtils()
  {
  }
  public static final Factory FACTORY = new Factory();
  /** The name of the basic Circus toolkit. */
  public static final String CIRCUSTIME_TOOLKIT = "circustime_toolkit";
  /** The name of the Circus prelude. */
  public static final String CIRCUSTIME_PRELUDE = "circustime_prelude";
  
  /**
   * Concrete syntax symbol visitor that can be used everywhere.
   */
  public static final CircusTimeConcreteSyntaxSymbolVisitor 
    CIRCUSTIME_CONCRETE_SYNTAXSYMBOL_VISITOR = new CircusTimeConcreteSyntaxSymbolVisitor();
  
}
