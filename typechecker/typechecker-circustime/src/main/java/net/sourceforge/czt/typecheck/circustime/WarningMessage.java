package net.sourceforge.czt.typecheck.circustime;

/**
 * 
 * @author leo
 */
public enum WarningMessage {

	CIRCUS_TIME_UNKNOWN_WARNING("Not yet implemented");

	private final String message_;
	private final String explanation_;
	private boolean flagged_;

	WarningMessage(String message) {
		this(message, null);
	}

	WarningMessage(String message, String explanation) {
		message_ = message;
		explanation_ = explanation;
		flagged_ = false;
	}

	String getMessage() {
		return message_;
	}

	String getExplanation() {
		String result = explanation_;
		flagged_ = true;
		return result;
	}

	boolean alreadyFlagged() {
		return flagged_;
	}

	String getFullMessage() {
		String result = getMessage();
		if (!flagged_)
			result += "\n\t" + getExplanation();
		return result;
	}
}
