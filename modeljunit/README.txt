              -----------------------------------
                    Welcome to ModelJUnit
              -----------------------------------

  ModelJUnit is a Java library that extends JUnit to support model-based
  testing.  It is an open source tool, released under the GNU GPL license.

  ModelJUnit allows you to write simple FSM or EFSM models as Java classes,
  then generate tests from those models and measure various model coverage
  metrics.  The principles behind ModelJUnit are described in Sections 5.2
  and 5.3 of our book: {{{http://www.cs.waikato.ac.nz/~marku/mbt} Mark Utting
  and Bruno Legeard: <Practical Model-Based Testing: A Tools Approach>,
  Elsevier 2007}}.

  This is a version 1.1 of ModelJUnit.  Note that it uses the annotations
  feature of Java 5.0, so requires JDK 1.5 or higher to run.


Compilation

  To compile modeljunit you need Maven 2.0.4 or higher from maven.apache.org.
  Then you can run the following Maven command in this modeljunit directory
  (which should contain this README.txt file, a pom.xml file, and directories
  called jdsl and src).  The parent directory must contain the CZT top-level
  pom.xml file.

+-----------------+
    mvn install
+-----------------+

  This will compile ModelJUnit, run its unit tests, and create a
  modeljunit.jar file in the <<<target>>> directory.


Documentation

  Maven can also generate Javadocs for ModelJUnit.  Run this command

+----------------------+
  mvn javadoc:javadoc
+----------------------+

  then point your web browser at <<<target/site/apidocs/index.html>>>.
  Start by reading the "description" section in the
  net.sourceforge.czt.modeljunit package.

  These Java docs are also available from
  {{{http://www.cs.waikato.ac.nz/~marku/mbt/modeljunit} here}}.



Using ModelJUnit

  See {{{http://www.cs.waikato.ac.nz/~marku/mbt/modeljunit} instructions
  and examples}} on how to use ModelJUnit to generate tests.  
  There are also lots of examples in the 
  <<<src/main/java/net/sourceforge/czt/modeljunit/examples>>>
  directory of this distribution.

