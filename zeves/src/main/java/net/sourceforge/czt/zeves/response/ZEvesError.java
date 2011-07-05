package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement(name = "zerror")
public class ZEvesError {

	@XmlElement(name = "errormessage")
	private List<ZEvesErrorMessage> errors = new ArrayList<ZEvesErrorMessage>();

	@Override
	public String toString() {
		return ZEvesResponseUtil.concat(errors, "\n");
	}

}
