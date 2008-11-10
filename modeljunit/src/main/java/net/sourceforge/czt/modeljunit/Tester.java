/**
Copyright (C) 2007 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.modeljunit;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.timing.TimedFsmModel;
import net.sourceforge.czt.modeljunit.timing.TimedModel;

/**
 * An abstract superclass for all the test generation algorithms.
 * Each subclass must implement a {@link #generate()} method that
 * generates the next step in a test sequence.
 * <p>
 * Note that many test generation algorithms use randomness,
 * so this class provides a setter and getter for a random number
 * generator.  By default this is set to <code>new Random(FIXEDSEED)</code>,
 * so that test generation is deterministic.
 *
 * @author marku
 *
 */
public abstract class Tester
{
  public static final long FIXEDSEED = 123456789L;

  /**
   * The model from which tests will be generated.
   */
  protected Model model_;

  /**
   *  A Random number generator for use in test generation.
   */
  protected Random rand_ = new Random(FIXEDSEED);

  /**
   *  Create a test generator for the given model.
   * @param model  Must be non-null.
   */
  public Tester(Model model)
  {
    assert model != null;
    model_ = model;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public Tester(FsmModel fsm)
  {
	  if(fsm instanceof TimedFsmModel)
		  model_ = new TimedModel((TimedFsmModel)fsm);
	  else
		  model_ = new Model(fsm);
  }
  


  /** The name of this test generation algorithm. */
  public abstract String getName();

  /** A brief description of this test generation algorithm. */
  public abstract String getDescription();

  /**
   * @return The model that is driving the test generation.
   */
  public Model getModel()
  {
    return model_;
  }

  /** Get the random number generator that is used for test generation. */
  public Random getRandom()
  {
    System.out.println("getRandom returns "+rand_);
    return rand_;
  }

  /** This allows you to specify a random number generator.
   *  The default is to use new Random(FIXEDSEED), so that test
   *  generation is repeatable (that is, each instance of this class
   *  will generate the same test sequences).
   *
   * @param rand  A non-null instance of Random.
   */
  public void setRandom(Random rand)
  {
    rand_ = rand;
  }

  /**
   *  A convenience method for adding known listeners and coverage metrics.
   *  This is equivalent to <code>getModel().addListener(name)</code>.
   *
   *  See the Factory class for the set of known names.
   *
   *  @param name The name of a known listener.
   *  @return     The listener that has been added (now or earlier).
   */
  public ModelListener addListener(String name)
  {
    return model_.addListener(name);
  }

  /** @deprecated Use addListener(listener) instead. */
  public void addListener(String name, ModelListener listen)
  {
    model_.addListener(listen);
  }

  /** This is equivalent to addListener(metric), but more convenient.
   * @param metric  A non-null coverage metric to add.
   * @return metric, or a previously-added metric with the same name (if any).
   */
  public CoverageMetric addCoverageMetric(CoverageMetric metric)
  {
    return (CoverageMetric) model_.addListener(metric);
  }

  /**
   *  A convenience method that adds a listener object.
   *  This is equivalent to <code>getModel().addListener(listener)</code>.
   * @param listener  Must be non-null.
   * @return     The listener that has been added (now or earlier).
   */
  public ModelListener addListener(ModelListener listener)
  {
    return model_.addListener(listener);
  }

  /** Prints the name and toString message from each coverage metric.
   *  They are printed in alphabetical order.
   */
  public void printCoverage()
  {
    List<String> names = new ArrayList<String>(model_.getListenerNames());
    Collections.sort(names);
    for (String name : names) {
      ModelListener listen = model_.getListener(name);
      if (listen instanceof CoverageMetric) {
        model_.printMessage(name+": "+listen.toString());
      }
    }
  }

  /** Performs a user-requested reset of the model. */
  public void reset()
  {
    model_.doReset();  // a user-requested reset
  }

  /** Generate one more test step in the current sequence.
   *  This may reset and start a new test sequence if necessary.
   *
   *  @return the number of the action taken, or -1 if a reset was done.
   */
  public abstract int generate();

  /** Generate some test sequences, with the given total length.
   *  The default implementation of this just calls generate()
   *  length times.
   *
   * @param length
   */
  public void generate(int length)
  {
    for (int i=0; i<length; i++)
      generate();
  }

  /** Equivalent to buildGraph(10000). */
  public GraphListener buildGraph()
  {
    return buildGraph(10000);
  }

  /** Equivalent to buildGraph(MaxSteps,true). */
  public GraphListener buildGraph(int maxSteps)
  {
    return buildGraph(maxSteps, true);
  }

  /** Calls {@code generate()} repeatedly until the graph seems to be complete.
   *  <p>
   *  Note that this method uses a fresh random number generator
   *  (with FIXEDSEED) to avoid modifying the random number
   *  generator {@link #getRandom()} that is used for test generation.
   *  </p>
   *  @param maxSteps An upper bound on the number of calls to generate,
   *              to avoid eternal exploration of large graphs.
   *  @param clear If this is true, the TODO and DONE flags on each
   *            transition of the graph are cleared after the graph is built.
   *            This is recommended, so that algorithms like GreedyTester
   *            get a fresh view of the graph.
   *  @see GraphListener.isComplete()
   */
  public GraphListener buildGraph(int maxSteps, boolean clear)
  {
    Random old = rand_;
    rand_ = new Random(FIXEDSEED);
    // make sure there is a graph listener
    GraphListener graph = (GraphListener) model_.addListener("graph");
    boolean wasTesting = model_.setTesting(false);
    model_.doReset("Buildgraph");
    do {
      generate(10);
      maxSteps -= 10;
    }
    while (graph.numTodo() > 0 && maxSteps > 0);

    int todo = graph.numTodo();
    if (todo > 0) {
      model_.printWarning("buildgraph stopped with "
          + graph.getGraph().numEdges() + " transitions and "
          + graph.getGraph().numVertices() + " states, but "
          + todo + " unexplored branches.");
    }
    model_.setTesting(wasTesting);
    model_.doReset("Buildgraph");
    if (clear) {
      graph.clearDoneTodo();
    }

    // restore the original random number generator.
    rand_ = old;
    return graph;
  }
}
