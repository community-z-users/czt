package com.smartesting.comet;

import java.util.*;
import java.io.*;
import com.smartesting.comet.model.*;
import com.smartesting.comet.api.*; 
import com.smartesting.comet.auth.*; 
// import tech.tablesaw.api.*;
// import java.io.*;
// import java.lang.reflect.Array;

// import static com.google.common.collect.Lists.newArrayList;
// import static com.smartesting.comet.Configuration.getDefaultApiClient;
// import static java.util.stream.IntStream.range;

/**
 * Corejava-z Comet Java Client
 */

public class CometJavaClient {
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
        // Uncomment the following line to set a prefix for the API key, e.g. "Token" (defaults to null)
        //ApiKeyAuth.setApiKeyPrefix("Token");
  
        PrioritizationsApi prioritizationsApi = new PrioritizationsApi(defaultClient);
        ProjectsApi projectsApi = new ProjectsApi(defaultClient);

        // Compile test cycle
        // Do Coverage based tcp within this module and create prioritisation list with following details:
        //  - id: name of test
        //  - classChanged (whether the source class that this test covers changed
        //  - testChanged (whether this class changed)
        System.out.println(prjName + " Comet Java Client");
        Runtime r = Runtime.getRuntime();
        ArrayList<Test> tests = new ArrayList<>();
        
        try {
            Process p = r.exec("../../ci_scripts/test/comet/prioritise_module.py");
            p.waitFor();

            BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;

            while ((line = b.readLine()) != null) {
              String[] tokens = line.split(",");
              Test test = new Test();
              test.setId(tokens[0]);
              test.setClassChanged(tokens[1].equals("True"));
              test.setTestChanged(tokens[1].equals("True"));
              System.out.println(line);
              tests.add(test);
            }

            b.close();

        } catch (java.lang.InterruptedException | java.io.IOException e) {
            System.out.println("java.lang.InterruptedException");
        }


        /*
         * 1) Create project if it doesn't exist and display it's state
         * 2) Add tests and receive prioritisation
         */
        // Create Project
        try {
          final Project project = new Project();
          project.setName(prjName);
          projectsApi.createProject(project);
        } catch (ApiException e) {
          System.out.print("[INFO] " + prjName + " Project aready exists");
        } finally {
          showProject(projectsApi);
        }

        // Create test cycles and tests
        // Add test cycle
        TestCyclesApi testCyclesApi = new TestCyclesApi(defaultClient);
        int numCycles = 10;
        TestsApi testApi = new TestsApi(defaultClient);
        for (int cycleId = 0; cycleId < numCycles; cycleId++) {
          try {
              TestCycle testCycle = new TestCycle();
              String testCycleId = "testCycle" + String.valueOf(cycleId);
              testCycle.id(testCycleId);
              System.out.println("Adding " + testCycleId);
              testCyclesApi.addTestCycle(prjName, testCycle, false); //cycleId == 0 ? false : true);

              for(Test test : tests) {
                testApi.addTest(prjName, testCycleId, test);
              }
          } catch (ApiException e) {
            System.err.println("Status code: " + e.getCode());
            System.err.println("Reason: " + e.getResponseBody());
            System.err.println("Response headers: " + e.getResponseHeaders());
            // removeProject(projectsApi);
            //System.exit(1);
          }
        }

        
        System.exit(0);

        //showProject(projectsApi);

        /*
        // Delete test cycles
        System.out.println("\n Deleting test cycles");
        for (int cycleId = 0; cycleId < numCycles; cycleId++) {
          String testCycleId = "testCycle" + String.valueOf(cycleId);
          try {
            testCyclesApi.deleteTestCycle(prjName, testCycleId);
          } catch (ApiException e) {
            System.err.println("Status code: " + e.getCode());
            System.err.println("Reason: " + e.getResponseBody());
            System.err.println("Response headers: " + e.getResponseHeaders());
            e.printStackTrace();
          }
        }
        showProject(projectsApi);
        */
    }

    static private void showProject(ProjectsApi projectsApi) {
        try {
          Project result = projectsApi.showProject(prjName);
          System.out.println("[INFO] Project State:");
          System.out.println(result);
        } catch (ApiException e) {
          System.out.println("Problem showing up project");
        }
    }

    static private List<TestCycle> listCycles(TestCyclesApi cyclesApi) {
      try {
        List<TestCycle> result = cyclesApi.listTestCycles(prjName);
        return result;
      } catch (ApiException e) {
        System.out.println("Problem showing up project");
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
