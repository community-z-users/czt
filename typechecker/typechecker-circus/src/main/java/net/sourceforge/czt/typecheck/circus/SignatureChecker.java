/*
  Copyright (C) 2007 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.circus;

import java.util.List;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.visitor.ActionSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ActionTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.circus.visitor.NameSetTypeVisitor;
import net.sourceforge.czt.circus.visitor.ProcessSignatureVisitor;
import net.sourceforge.czt.circus.visitor.ProcessTypeVisitor;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.impl.UnknownTypeVisitor;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.PowerTypeVisitor;
import net.sourceforge.czt.z.visitor.ProdTypeVisitor;
import net.sourceforge.czt.z.visitor.SchemaTypeVisitor;
import net.sourceforge.czt.z.visitor.SignatureVisitor;

/**
 * <p>
 * This checker transforms a given type into a Signature.
 * For most cases this just unpacks the signature already 
 * available within the type itself. Otherwise, it calculates
 * the name/type pairs from the available types by giving then 
 * implicit names (in case of certain type, such as ProdType).
 * </p>
 * <p> 
 * This is useful for the typechecking of certain complex Circus
 * paragraphs, such as ProcessType carrier set construction, or 
 * ChannelSet paragraphs where the expression is not a (basic) 
 * channel set display expression (e.g. CS == f(c) \cup g(d), for
 * channels c and d).
 * </p>
 * <p>
 * This includes checking all types within the Z type system, 
 * as well as all types within the Circus type system. For any
 * other type (or indeed Term) a warning is logged, as defined
 * by the general protocol in z.Checker.
 * </p>
 * @author Leo Freitas
 */
public class SignatureChecker
    extends Checker<Signature>
    implements // Z type system
               PowerTypeVisitor<Signature>,
               //GenParamTypeVisitor<Signature>,
               //GivenTypeVisitor<Signature>,
               SchemaTypeVisitor<Signature>,
               SignatureVisitor<Signature>,
               ProdTypeVisitor<Signature>,
               //VariableTypeVisitor<Signature>,
               //VariableSignatureVisitor<Signature>,
               UnknownTypeVisitor<Signature>,
  
               // Circus type system
               ChannelTypeVisitor<Signature>, 
               ChannelSetTypeVisitor<Signature>, 
               ProcessTypeVisitor<Signature>,    
               ActionTypeVisitor<Signature>, 
               NameSetTypeVisitor<Signature>,
               ProcessSignatureVisitor<Signature>,
               ActionSignatureVisitor<Signature>
{
  
  /** Creates a new instance of SignatureChecker */
  public SignatureChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }
  
  /** Fresh str name ID seed */
  private static long id_ = 0;
  
  private static synchronized void incrementId()
  {
	  id_++;
  }
  
  /** Default signature variable name */
  private static final String DEFAULT_SIGNATURE_IMPLICIT_NAME = "$$sigVar";
  
  /**
   * Returns a fresh signature variable string name.
   */
  protected String freshStrName()
  {
    String result = DEFAULT_SIGNATURE_IMPLICIT_NAME + id_;
    incrementId();
    return result;
  }
  
  /**
   * From the given list of Types return the corresponding NameTypePair list
   * where the variable names have been constructed using #freshStrName. 
   * The resulting list must have the same size as the given list.
   */
  protected <T extends Type> List<NameTypePair> createNameTypePairsFromType(List<T> list)
  {
    List<NameTypePair> result = factory().list();    
    for(T type : list)
    {
      ZName name = factory().createZDeclName(freshStrName());
      NameTypePair pair = factory().createNameTypePair(name, type);
      result.add(pair);
    }    
    assert result.size() == list.size() : "Resulting name type pair list size different from type list size.";
    return result;
  }
  
  public Signature visitSignature(Signature term)
  {
    // this covers: Signature and VariableSignature
    return term;
  }
 
  public Signature visitSchemaType(SchemaType term)
  {
    return term.getSignature();
  }

  public Signature visitPowerType(PowerType term)
  {    
    return term.getType().accept(signatureChecker());
  }
  
  public Signature visitProdType(ProdType term)
  {
    List<NameTypePair> pairs = createNameTypePairsFromType(term.getType());
    Signature result = factory().createSignature(pairs);
    return result;
  }
    
  public Signature visitType2(Type2 term)
  {
    // this covers: GivenType, GenParamType, VariableType, 
    List<NameTypePair> pairs = createNameTypePairsFromType(factory().list(term));
    Signature result = factory().createSignature(pairs);
    return result;
  }


  public Signature visitUnknownType(UnknownType unknownType)
  {
//    Signature result =
    		visitType2(unknownType); // ?
    throw new UndeterminedTypeException();
    //return result;
  }  
  
  public Signature visitChannelType(ChannelType term)
  {
    return factory().createSignature();//term.getSignature();
  }
  
  public Signature visitChannelSetType(ChannelSetType term)
  {
    return term.getSignature();
  }  

  public Signature visitNameSetType(NameSetType term)
  {
    return term.getSignature();
  }
  
  public Signature visitProcessType(ProcessType term)
  {
    return term.getProcessSignature().accept(signatureChecker());
  }

  /**
   * For complex Circus types (i.e. Processes and Action signatures),
   * just wrap the ProcessSignatures back into the type but extracting their
   * declaring names as part of the resulting Signature.
   * In case we don't need to change this "way" of calculation, we could 
   * just extract this directly from visitProcessType.
   */
  public Signature visitProcessSignature(ProcessSignature term)
  {
    // this covers: ProcessSignature and BasicProcessSignature
    ProcessType pType = factory().createProcessType(term);
    NameTypePair pair = factory().createNameTypePair(term.getProcessName(), pType);
    Signature result = factory().createSignature(pair);
    return result;
  }
  
  public Signature visitActionType(ActionType term)
  {
    return term.getActionSignature().accept(signatureChecker());
  }
    
  public Signature visitActionSignature(ActionSignature term)
  {    
    ActionType aType = factory().createActionType(term);
    NameTypePair pair = factory().createNameTypePair(term.getActionName(), aType);
    Signature result = factory().createSignature(pair);
    return result;
  }
}
