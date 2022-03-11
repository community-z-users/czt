package net.sourceforge.czt.eclipse.zeves.ui.preferences;

import java.util.Arrays;

import net.sourceforge.czt.eclipse.ui.compile.IZProblemSeverityProvider;
import net.sourceforge.czt.eclipse.ui.compile.ZProblemSeverity;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.zeves.ErrorMessage;
import net.sourceforge.czt.typecheck.zeves.WarningMessage;

import static net.sourceforge.czt.eclipse.zeves.ui.preferences.ZEvesPreferenceConstants.*;

public class ZEvesProblemSeverityProvider implements IZProblemSeverityProvider {

	@Override
	public ZProblemSeverity getSeverity(String dialect, CztError problem) {
		
		if (!"zeves".equals(dialect)) {
			return null;
		}
		
		if (problem instanceof ErrorAnn) {
			String messageKey = ((ErrorAnn) problem).getErrorMessage();
			if (messageKey == null) {
				return null;
			}
			
			if (WarningMessage.IGNORE_NAME_COMPLEX_SCHEMA_CALULUS_EXPR.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNDECIDABLE_SCHEMA_CALCULUS);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.UNDECLARED_NAME_ERROR_AS_WARNING.name(),
					ErrorMessage.UNDECLARED_NAME_ERROR_AS_WARNING.name())) {
				return getSeverityPref(SEVERITY_UNDECLARED_NAME_ERROR);
			}
			
			if (ErrorMessage.PRED_ERROR_AS_WARNING.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_PRED_TYPE_MISMATCH);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.SUBST_CMD_INVALID_EQS.name(), 
					WarningMessage.SUBST_CMD_INVALID_INVOKE.name(),
					WarningMessage.SPLIT_CMD_INVALID_PRED.name(),
					WarningMessage.APPLY_CMD_INVALID.name(),
					WarningMessage.SUBST_CMD_INVALID_INVOKE.name())) {
				return getSeverityPref(SEVERITY_PROOF_COMMAND_PARSE_PROBLEMS);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.SUBST_CMD_EXPR_EQS.name(), 
					WarningMessage.APPLY_CMD_EXPR.name(),
					WarningMessage.IGNORE_PROOF_EXPR.name(),
					WarningMessage.IGNORE_PROOF_PRED.name(),
					WarningMessage.IGNORE_ZEVES_THMREPLACEMENT_TYPECHECK.name())) {
				return getSeverityPref(SEVERITY_PROOF_COMMAND_UNCHECKED_EXPR);
			}
			
			if (WarningMessage.UNKNOWN_TERM.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNKNOWN_TERM);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.ZSECT_THMTBL_ERROR.name(), 
					WarningMessage.ZSECT_PROOFTBL_ERROR.name())) {
				return getSeverityPref(SEVERITY_TABLE_PROBLEMS);
			}
			
			if (WarningMessage.PARENT_ERRORS_WARNING.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_PARENT_PROBLEMS);
			}
			
			if (oneOf(messageKey, 
					ErrorMessage.USE_CMD_THMREF.name(), 
					ErrorMessage.APPLY_CMD_THMNAME.name(),
					ErrorMessage.SUBST_CMD_PRED_INVOKE.name(),
					ErrorMessage.WITH_CMD_THMNAME.name())) {
				// typecheck theorem references
				return getSeverityPref(SEVERITY_INCOMPATIBLE_THEOREM_REF);
			}
			
			if (oneOf(messageKey, 
					ErrorMessage.QNT_CMD_INST.name(), 
					ErrorMessage.USE_CMD_REPL.name())) {
				// typecheck instantiations
				return getSeverityPref(SEVERITY_INCOMPATIBLE_INSTS);
			}
			
			if (ErrorMessage.BINDEXPR_ERROR_AS_WARNING.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNCHECKED_BIND_EXPR);
			}
		}
		
		return null;
	}
	
	private boolean oneOf(String messageKey, String... messages) {
		return Arrays.asList(messages).contains(messageKey);
	}
	
	private ZProblemSeverity getSeverityPref(String prefKey) {
		return ZEvesPreferenceConstants.getSeverityPref(ZEvesUIPlugin.getDefault().getPreferenceStore(), prefKey);
	}

}
