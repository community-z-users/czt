package net.sourceforge.czt.eclipse.zeves.preferences;

import net.sourceforge.czt.eclipse.editors.parser.IZProblemSeverityProvider;
import net.sourceforge.czt.eclipse.editors.parser.ZProblemSeverity;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.zeves.WarningMessage;

import static net.sourceforge.czt.eclipse.zeves.preferences.ZEvesPreferenceConstants.*;

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
			
			if (WarningMessage.UNDECIDABLE_SCHEMA_CALULUS_EXPR.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNDECIDABLE_SCHEMA_CALCULUS);
			}
			
			if (WarningMessage.UNDECLARED_NAME_ERROR_AS_WARNING.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNDECLARED_NAME_ERROR);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.SUBST_CMD_INVALID_EQS, 
					WarningMessage.SUBST_CMD_INVALID_INVOKE,
					WarningMessage.SPLIT_CMD_INVALID_PRED,
					WarningMessage.APPLY_CMD_INVALID,
					WarningMessage.SUBST_CMD_INVALID_INVOKE)) {
				return getSeverityPref(SEVERITY_PROOF_COMMAND_PARSE_PROBLEMS);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.SUBST_CMD_EXPR_EQS, 
					WarningMessage.APPLY_CMD_EXPR,
					WarningMessage.IGNORE_PROOF_EXPR,
					WarningMessage.IGNORE_PROOF_PRED,
					WarningMessage.IGNORE_ZEVES_THMREPLACEMENT_TYPECHECK)) {
				return getSeverityPref(SEVERITY_PROOF_COMMAND_UNCHECKED_EXPR);
			}
			
			if (WarningMessage.UNKNOWN_TERM.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_UNKNOWN_TERM);
			}
			
			if (oneOf(messageKey, 
					WarningMessage.ZSECT_THMTBL_ERROR, 
					WarningMessage.ZSECT_PROOFTBL_ERROR)) {
				return getSeverityPref(SEVERITY_TABLE_PROBLEMS);
			}
			
			if (WarningMessage.PARENT_ERRORS_WARNING.name().equals(messageKey)) {
				return getSeverityPref(SEVERITY_PARENT_PROBLEMS);
			}
		}
		
		return null;
	}
	
	private boolean oneOf(String messageKey, WarningMessage... messages) {
		for (WarningMessage message : messages) {
			if (message.name().equals(messageKey)) {
				return true;
			}
		}
		
		return false;
	}
	
	private ZProblemSeverity getSeverityPref(String prefKey) {
		return ZEvesPreferenceConstants.getSeverityPref(ZEvesPlugin.getDefault().getPreferenceStore(), prefKey);
	}

}
