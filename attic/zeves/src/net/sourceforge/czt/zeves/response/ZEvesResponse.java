/*
 * ZEvesResponse.java
 *
 * Created on 21 September 2005, 13:44
 */

package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


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
        if (!((zevesResponse.startsWith("<zerror>") || zevesResponse.startsWith("<zoutput>")) &&
            (zevesResponse.endsWith("/>") || zevesResponse.endsWith("</zerror>") || zevesResponse.endsWith("</zoutput>"))))        
            throw new IllegalArgumentException("Z/Eves server response must be either an zerror or zoutput: " + zevesResponse);
        fOutputs = new ArrayList<ZEvesOutput>();
        fErrors = new ArrayList<ZEvesErrorMessage>();
        fToStringView = new StringBuilder("");
        fAsStringView = new StringBuilder("");
        if (zevesResponse.startsWith("<zerror>"))
            interpretError(zevesResponse);
        else 
            interpretOutput(zevesResponse);
        buildViews();
    }
    
    protected void interpretError(String zevesError) {
        if (zevesError.indexOf("/>") == -1)
            zevesError = zevesError.substring("<zerror>".length(), zevesError.indexOf("</zerror>")).trim();
        else
            zevesError = zevesError.substring("<zerror>".length(), zevesError.indexOf("/>")).trim();
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
    
    protected void interpretOutput(String zevesOutput) {
        if (zevesOutput.indexOf("/>") == -1)
            zevesOutput = zevesOutput.substring("<zoutput>".length(), zevesOutput.indexOf("</zoutput>")).trim();
        else
            zevesOutput = zevesOutput.substring("<zoutput>".length(), zevesOutput.indexOf("/>")).trim();
        // So far we only identify ZEvesBooleanOutput.        
        if (zevesOutput.equals("<name ident=\"true\"")) {
            ZEvesBooleanOutput bool = new ZEvesBooleanOutput(true);
            fOutputs.add(bool);
        }        
        else if (zevesOutput.equals("<name ident=\"false\"")) {
            ZEvesBooleanOutput bool = new ZEvesBooleanOutput(false);
            fOutputs.add(bool);
        }        
        else if (zevesOutput.equals("")) {
            ZEvesEmptyOutput empty = new ZEvesEmptyOutput();
            fOutputs.add(empty);
        } else {
            ZEvesStringOutput str = new ZEvesStringOutput(zevesOutput);
            fOutputs.add(str);
        }        
    }
    // <zoutput><name ident="true"/></zoutput>
    
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
            for(ZEvesOutput out : fOutputs) {                  
                fToStringView.append(out.toString());                
                if (out instanceof ZEvesBooleanOutput) {
                    fAsStringView.append("success");
                } else 
                    fAsStringView.append(out.toString());
                fToStringView.append("\n");
                fAsStringView.append("\n");
            }                        
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
    
    public int getOutputCount() {
        return fOutputs.size();
    }
    
    public List<ZEvesErrorMessage> errors() {
        return Collections.unmodifiableList(fErrors);
    }
    
    public List<ZEvesOutput> outputs() {
        return Collections.unmodifiableList(fOutputs);
    }
    
    public String toString() {
        return fToStringView.toString();
    }
    
    public String asString() {
        return fAsStringView.toString();
    }
}
