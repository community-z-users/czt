package net.sourceforge.czt.zeves;

import net.sourceforge.czt.zeves.response.ZEvesError;

public class ZEvesException extends Exception {

	private ZEvesError zEvesErr;
	
	public ZEvesException() {
	}

	public ZEvesException(String message) {
		super(message);
	}

	public ZEvesException(Throwable cause) {
		super(cause);
	}

	public ZEvesException(String message, Throwable cause) {
		super(message, cause);
	}
	
	public ZEvesException(ZEvesError error) {
		super(error.toString());
		
		this.zEvesErr = error;
	}
	
	public ZEvesError getZEvesError() {
		return zEvesErr;
	}
	
}
