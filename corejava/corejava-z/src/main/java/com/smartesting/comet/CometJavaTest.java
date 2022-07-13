package com.smartesting.comet;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import com.smartesting.comet.api.PrioritizationsApi;
import com.smartesting.comet.api.ProjectsApi;
import com.smartesting.comet.api.TestCyclesApi;
// import tech.tablesaw.api.*;
// import java.io.*;
// import java.lang.reflect.Array;
import com.smartesting.comet.auth.ApiKeyAuth;
import com.smartesting.comet.model.Prioritization;
import com.smartesting.comet.model.Project;
import com.smartesting.comet.model.Test;
import com.smartesting.comet.model.TestCycle;

// import static com.google.common.collect.Lists.newArrayList;
// import static com.smartesting.comet.Configuration.getDefaultApiClient;
// import static java.util.stream.IntStream.range;

/**
 * Corejava-z Comet Java Test
 */

public class CometJavaTest {
    private final static String urlService = "https://chiron.comet.smartesting.com";
    private final static String apiKey = "6b3277b2-fbbe-4256-bbf5-7da7fae84eba";
    private final static String prjName = "Corejava Z";

    public static void main(String[] args) {

        // Initialize the client
        ApiClient defaultClient = Configuration.getDefaultApiClient();
        defaultClient.setBasePath(urlService);
  
        // Configure API key authorization: ApiKeyAuth
        ApiKeyAuth ApiKeyAuth = (ApiKeyAuth) defaultClient.getAuthentication("ApiKeyAuth");
        ApiKeyAuth.setApiKey(apiKey);
  
        PrioritizationsApi prioritizationsApi = new PrioritizationsApi(defaultClient);
        ProjectsApi projectsApi = new ProjectsApi(defaultClient);
        TestCyclesApi testCyclesApi = new TestCyclesApi(defaultClient);

        //showProject(projectsApi);
        
        // Get prioritisation
        List<TestCycle> prevCycles = listCycles(testCyclesApi);
        List<String> tests = new ArrayList<>();
        try {
          TestCycle lastCycle = testCyclesApi.showLastTestCycle(prjName);
          if (prevCycles.size() >= 10) {
            // get prioritisation
            Prioritization prioritization = prioritizationsApi.prioritize(prjName, lastCycle.getId());
            // System.out.println(prioritization);
            tests = prioritization.getTests();

          } else {
            // Return random list order since prioritisation can't be used with < 10 cycles
            System.out.print("There are only " + prevCycles.size() + " tests");
            
            // Get tests from last uploaded cycle
            for (Test test : lastCycle.getTests()) {
              tests.add(test.getId());
            }
          }
        } catch (NullPointerException | ApiException e) {
          System.err.println("No test cycles");
          System.exit(1);
        }

        // Run tests
        try {
          Runtime r = Runtime.getRuntime();

          for(String id : tests) {
            System.out.println("mvn surefire:test -Dtest=\"" + id + "\"");
            Process p = r.exec("mvn surefire:test -DfailIfNoTests=false -Dtest=" + id);
            BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;
            while ((line = b.readLine()) != null) {
              System.out.println(line);
            }
            b.close();
            p.waitFor();
            if (p.exitValue() != 0) {
              System.out.println(p);
              break;
            }
            
          }

      } catch (java.lang.InterruptedException | java.io.IOException  e) {
          System.out.println("java.lang.InterruptedException");
      }


        // Update api with results

        System.exit(0);
    }

    static private void showProject(ProjectsApi projectsApi) {
        try {
          Project result = projectsApi.showProject(prjName);
          System.out.println("[INFO] Project State:");
          System.out.println(result);
        } catch (ApiException e) {
          System.out.println("Problem showing up project");
          System.err.println("Status code: " + e.getCode());
          System.err.println("Reason: " + e.getResponseBody());
          System.err.println("Response headers: " + e.getResponseHeaders());
        }
    }

    static private List<TestCycle> listCycles(TestCyclesApi cyclesApi) {
      try {
        List<TestCycle> result = cyclesApi.listTestCycles(prjName);
        return result;
      } catch (ApiException e) {
        System.out.println("Problem getting test cycles");
        return null;
      }
  }

    static private void removeProject(ProjectsApi projectsApi) {
        try {
          projectsApi.deleteProject(prjName);
          System.out.println("[INFO] Project State:");
        } catch (ApiException e) {
          System.out.println("Problem deleting project");
        }
    }
}
