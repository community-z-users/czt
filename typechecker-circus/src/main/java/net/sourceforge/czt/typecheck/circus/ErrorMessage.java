/*
  Copyright (C) 2006, 2007 Leo Freitas, Manuela Xavier
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

/**
 * // TODO: use warning manager. think about warnings and better error messages
 * @author Leo Freitas
 */
public enum ErrorMessage 
{
  /**
   * Messages within Checker.java 
   */  
  // Process/action scope
  INVALID_PROCESS_PARA_SCOPE,
  INVALID_ACTION_PARA_SCOPE,
  NESTED_PROCESSPARA_SCOPE,
  NESTED_ACTIONPARA_SCOPE,
  
  // Process/action call - actual parameters check
  PARAM_PROC_CALL_UNDECLARED_VAR,
  PARAM_ACTION_CALL_UNDECLARED_VAR,
  PARAM_PROC_CALL_NOT_UNIFY,
  PARAM_ACTION_CALL_NOT_UNIFY,
  PARAM_PROC_CALL_DIFF_NUMBER_EXPRS,
  PARAM_ACTION_CALL_DIFF_NUMBER_EXPRS,    
  
  // Process/action call - consistency check
  IS_NOT_ACTION_NAME,      
  
  // Basic process state variables 
  SCHEXPR_ACTION_VAR_OUT_OF_SCOPE,
  SCHEXPR_ACTION_FAIL_UNIFY,

  // Binary actions signature 
  INVALID_ACTION_SIGNATURE_JOIN,
  
  REDECLARED_DEF,
  
  /* Messages within ParaChecker.java */
  
  /**
   * Messages within DeclChecker.java 
   */  
  
  // Formal parameters 
  FORMAL_PARAMS_INVALID_SCOPE,
  FORMAL_PARAMS_INVALID_DECL,
  
  // Channel from 
  CHANNEL_FROM_INVALID_DECL,
  CHANNEL_FROM_INVALID_INCLDECL,
  
  // Duplicate names in Circus declarations
  CHANDECL_DUPLICATE_CHANNEL_NAME,  
  QUALIFIEDDECL_DUPLICATE_PARAM_NAME,
  
  /** Messages within ProcessChecker.java */  
  
  /** Messages within ProcessParaChecker.java */  
  
  /** Messages within BasicProcessChecker.java */  
  
  BASIC_PROCESS_PARA_WRONG_TYPE,
  
  /** Messages within ActionChecker.java */  
  
  SCHEXPR_ACTION_WITHOUT_SCHEXPR,  
  
  /** Messages within CommunicationChecker.java */  
  
  COMM_CHANNEL_FIELDS_ERROR,
  //COMM_SYNCH_CHANNEL_WITH_FIELDS,
  IS_NOT_CHANNEL_NAME,
  COMM_FIELDS_DONT_UNIFY,
  COMM_DOTFIELD_DONT_UNIFY,
  COMM_FIELD_FAILED_INVARIANT,

  /** Messages within PostChecker.java */  
  
  POSTCHECKING_CALL_ERROR;
  
  /** Messages within SpecChecker.java */  
  /** Messages within ExprChecker.java */  
  /** Messages within PredChecker.java */  
  /** Messages within CharTupleChecker.java */  
  /** Messages within SchTextChecker.java */  
  
  

  

//  
//  
//  
//  
//  REDECLARED_PARENT,
//  REDECLARED_SECTION,
//  SELF_PARENT,
//  REDECLARED_GLOBAL_NAME,
//  REDECLARED_CHANNEL_NAME,
//  REDECLARED_GEN,
//  IS_NOT_CHANNEL_IN_CHANSET,
//  IS_NOT_CHANSET_NAME,
//  REDECLARED_CHANSET_NAME,
//  REDECLARED_PROCESS_NAME,
//  IS_NOT_PROCESS_NAME,
//  REDECLARED_IMPLICIT_CHANNEL_NAME,    
//  IS_NOT_INDEX_PROCESS_IN_PROC_CALL,
//  PROC_RENAME_DIFF_NUMBER_CHANS,
//  PROC_RENAME_NOT_UNIFY,
//  IMPOSSIBLE_EXTRACT_INPUT_VAR,
//  REDECLARED_INPUT_VAR_IN_PROCESS,
//  REDECLARED_INPUT_VAR_IN_ACTION,
//  REDECLARED_LOCAL_NAME,
//  PREFIX_PROC_REDECLARED_VAR,
//  REDECLARED_NAMESET_NAME,
//  IS_NOT_LOCAL_VAR_NAME_IN_NAMESET,
//  IS_NOT_NAMESET_NAME,
//  REDECLARED_ACTION_NAME,
//  REDECLARED_PARAM_IN_ACTION,
//  REDECLARED_PARAM_IN_PROCESS,
//  REDECLARED_INDEX_IN_PROCESS,
//  REDECLARED_VAR_IN_PROCESS_ITE,
//  REDECLARED_VAR_IN_PROCESS_IDX,
//  
//  ,
//  REDECLARED_VAR_IN_ACTION_ITE,    
//  ACTION_RENAME_NOT_UNIFY,
//  ACTION_RENAME_DIFF_NUMBER_VARS,
//  RENAME_ACTION_UNDECLARED_VAR,
//  NAMES_ARE_NOT_CHANNELS_IN_PROC_RENAME,
//  REDECLARED_GLOBAL_NAME_WITH_DIFF_TYPE,
//  MU_PROC_CALL_ERROR,
//  IS_NOT_GEN_PROCESS_IN_PROC_CALL,
//  GEN_PROCESS_INSTANTIATION_ERROR,
//  PROC_CALL_NEEDS_PARAMS,
//  REC_PROC_CALL_ERROR,
//  REC_ACTION_CALL_ERROR,
//  MU_ACTION_CALL_ERROR,
//  IS_NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION,
//  IS_NOT_LOCAL_VAR_NAME_IN_SPEC_COMMAND,
//  DUPLICATE_VAR_NAME_IN_FRAME_OF_SPEC_COMMAND,
//  IS_NOT_LOCAL_VAR_NAME_IN_ASSIG_COMMAND,
//  DUPLICATE_VAR_NAME_IN_ASSIG_COMMAND,
//  ASSIG_COMMAND_ERROR,
//  DIFF_NUM_ASSIG_COMMAND_ERROR,
//  IS_NOT_POWER_TYPE_IN_GEN_PROCESS,
//  IS_NOT_GENERIC_CHANNEL,
//  DIFF_NUMBER_IN_GENERIC_CHANNEL_INSTATIATION,
//  EXPR_TYPE_IS_NOT_POWERSET,
//  REDECLARED_PARAM_IN_PARCOMMAND,
//  INFINITY_VALUES_IN_ACTION_ITE,
//  INFINITY_VALUES_IN_PROCESS_ITE;

}
