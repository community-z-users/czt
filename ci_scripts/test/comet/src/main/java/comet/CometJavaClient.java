package comet;

// Java Dependencies
import java.util.*;
import java.io.*;

// Comet Dependencies
import com.smartesting.comet.model.*;
import com.smartesting.comet.api.*; 
import com.smartesting.comet.auth.*;
import com.smartesting.comet.*;

/**
 * Comet Java Client
 */

public class CometJavaClient {
    private final static String urlService = "https://chiron.comet.smartesting.com";
    private final static String apiKey = "6b3277b2-fbbe-4256-bbf5-7da7fae84eba";
    private final static String prjName = "CZT";

    public static void main(String[] args) {

        // Initialize the client
        ApiClient defaultClient = Configuration.getDefaultApiClient();
        defaultClient.setBasePath(urlService);
  
        // Configure API key authorization: ApiKeyAuth
        ApiKeyAuth ApiKeyAuth = (ApiKeyAuth) defaultClient.getAuthentication("ApiKeyAuth");
        ApiKeyAuth.setApiKey(apiKey);
  
        ProjectsApi projectsApi = new ProjectsApi(defaultClient);

        /*
         * Do Coverage based tcp within this module and create prioritisation list with following details:
         *  - id: name of test
         *  - classChanged (whether the source class that this test covers changed
         *  - testChanged (whether this class changed)
         */
        System.out.println(prjName + " Comet Java Client");
        Runtime r = Runtime.getRuntime();
        ArrayList<Test> tests = new ArrayList<>();
        try {
            Process p = r.exec("./util/get_tests.py");
            p.waitFor();

            BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;

            while ((line = b.readLine()) != null) {
              String[] tokens = line.split(",");
              Test test = new Test();
              test.setId(tokens[0]);
              test.setClassChanged(tokens[1].equals("True"));
              test.setTestChanged(tokens[1].equals("True"));
              //System.out.println(line);
              tests.add(test);
            }
            b.close();
        } catch (java.lang.InterruptedException | java.io.IOException e) {
            System.out.println("java.lang.InterruptedException");
        }

        /*
         * Add test cycle to comet API
         * - Create project if it doesn't exist and display it's state
         * - Add tests and receive prioritisation
         */
        try {
          final Project project = new Project();
          project.setName(prjName);
          projectsApi.createProject(project);
        } catch (ApiException e) {
          System.out.print("[INFO] " + prjName + " Project aready exists");
        } finally {
          showProject(projectsApi);
        }

        // Add test cycle
        TestCyclesApi testCyclesApi = new TestCyclesApi(defaultClient);
        int numCycles = 1;
        TestsApi testApi = new TestsApi(defaultClient);
        for (int cycleId = 0; cycleId < numCycles; cycleId++) {
          try {
              TestCycle testCycle = new TestCycle();
              String testCycleId = "testCycle" + String.valueOf(cycleId);
              testCycle.id(testCycleId);
              System.out.println("Adding " + testCycleId);
              testCyclesApi.addTestCycle(prjName, testCycle, false);

              for(Test test : tests) {
                testApi.addTest(prjName, testCycleId, test);
              }
          } catch (ApiException e) {
            System.err.println("Status code: " + e.getCode());
            System.err.println("Reason: " + e.getResponseBody());
            System.err.println("Response headers: " + e.getResponseHeaders());
            //System.exit(1);
          }
        }

        showProject(projectsApi);
        System.exit(0);
    }

    public static void showProject(ProjectsApi projectsApi) {
        try {
          Project result = projectsApi.showProject(prjName);
          System.out.println("[INFO] Project State:");
          System.out.println(result);
        } catch (ApiException e) {
          System.out.println("Problem showing up project");
        }
    }

    public static List<TestCycle> listCycles(TestCyclesApi cyclesApi) {
      try {
        List<TestCycle> result = cyclesApi.listTestCycles(prjName);
        return result;
      } catch (ApiException e) {
        System.out.println("Problem showing up project");
        return null;
      }
    }

    public static void removeProject(ProjectsApi projectsApi) {
        try {
          projectsApi.deleteProject(prjName);
          System.out.println("Deleting Project");
        } catch (ApiException e) {
          System.out.println("Problem deleting project");
        }
    }
}
