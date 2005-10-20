/*
 * ZEvesResponse.java
 *
 * Created on 21 September 2005, 13:44
 */

package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Iterator;


/**
 *
 * @author leo
 */
public class ZEvesResponse {
    
    private final StringBuilder fToStringView;
    private final StringBuilder fAsStringView;
    private final ArrayList<ZEvesOutput> fOutputs;
    private final ArrayList<ZEvesErrorMessage> fErrors;
    
    /** Creates a new instance of ZEvesResponse */
    public ZEvesResponse(String zevesResponse) {
        if (zevesResponse == null)
            throw new NullPointerException("Invalid Z/Eves server response");
        if (!((zevesResponse.startsWith("<zerror>") && zevesResponse.endsWith("</zerror>")) ||
             (zevesResponse.startsWith("<zoutput>") && zevesResponse.endsWith("</zoutput>"))))
            throw new IllegalArgumentException("Z/Eves server response must be either an zerror or zoutput: " + zevesResponse);
        fOutputs = new ArrayList<ZEvesOutput>();
        fErrors = new ArrayList<ZEvesErrorMessage>();
        fToStringView = new StringBuilder("");
        fAsStringView = new StringBuilder("");
        interpret(zevesResponse);
        buildViews();
    }
    
    protected void interpret(String zevesError) {
        zevesError = zevesError.substring("<zerror>".length(), zevesError.indexOf("</zerror>")).trim();
        int errMsgTagLength = "<errormessage>".length();
        while (!zevesError.equals("")) {
            int nextMsgIdx = zevesError.indexOf("</errormessage>");
            assert zevesError.startsWith("<errormessage>") && nextMsgIdx != -1;
            String error = zevesError.substring(errMsgTagLength, nextMsgIdx);
            processError(error);
            zevesError = zevesError.substring(nextMsgIdx+errMsgTagLength+1);// +1 for the "/"
        }
        //String[] errors = .split("<errormessage>"); regex not used to avoid problems with linebreaks, for instance.
    }
    
    protected void processError(String error) {
        assert error != null && !error.equals("");
        int errNameIdx = error.indexOf("<name ident=\"");
        int errNameClsIdx = error.indexOf("\" class=\"");
        int errCtsIdx = error.indexOf("\"/>");
        assert errNameIdx != -1 && errNameClsIdx != -1 && errCtsIdx != -1;
        String prelude = error.substring(0, errNameIdx).trim();
        String name = error.substring(errNameIdx+"<name ident=\"".length(), errNameClsIdx).trim();
        String namecls = error.substring(errNameClsIdx+"class=\"".length(), errCtsIdx).trim();
        String contents = error.substring(errCtsIdx+"\"/>".length()).trim();
        ZEvesErrorMessage zem = new ZEvesErrorMessage(prelude, name, namecls, contents);
        fErrors.add(zem);
    }
    
    protected void buildViews() {
        if (fErrors.isEmpty()) {
            fToStringView.append("<zoutput></zoutput>");
            fAsStringView.append("success");
        } else {
            fToStringView.append("<zerror>");
            for(ZEvesErrorMessage zem : fErrors) {
                fToStringView.append(zem.toString());
            }            
            fToStringView.append("</zerror>");            
            fAsStringView.append(getErrorCount() + " error(s):\n");
            for(ZEvesErrorMessage zem : fErrors) {
                fAsStringView.append(zem.asString() + "\n");
            }                        
        }
    }
    
    public int getErrorCount() {
        return fErrors.size();
    }
    
    public Iterator<ZEvesErrorMessage> errors() {
        return fErrors.iterator();
    }
    
    public String toString() {
        return fToStringView.toString();
    }
    
    public String asString() {
        return fAsStringView.toString();
    }
}
