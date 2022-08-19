package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class Module implements Iterable<Object> {

  private final List<Object> elementsByOrder;

  private final List<Sig> sigs;
  private final List<Fact> facts;
  private final List<Func> funcs;
  private final List<Command> commands;

  private final Map<String, Sig> sigByLabel;
  private final Map<String, Fact> factByLabel;
  private final Map<String, Func> funcByLabel;
  private final Map<String, Command> commandByLabel;

  private final List<Module> includedModules;

  public Module() {
    this.sigs = new ArrayList<Sig>();
    this.facts = new ArrayList<Fact>();
    this.funcs = new ArrayList<Func>();
    this.commands = new ArrayList<Command>();

    this.sigByLabel = new HashMap<String, Sig>();
    this.factByLabel = new HashMap<String, Fact>();
    this.funcByLabel = new HashMap<String, Func>();
    this.commandByLabel = new HashMap<String, Command>();

    this.elementsByOrder = new ArrayList<Object>();

    this.includedModules = new ArrayList<Module>();
  }

  public void addSig(Sig sig) {
    sigs.add(sig);
    sigByLabel.put(sig.label(), sig);
    elementsByOrder.add(sig);
  }

  public void addFact(Fact fact) {
    facts.add(fact);
    factByLabel.put(fact.label(), fact);
    elementsByOrder.add(fact);
  }

  public void addFunc(Func func) {
    funcs.add(func);
    funcByLabel.put(func.label(), func);
    elementsByOrder.add(func);
  }

  public void addCommand(Command command) {
    commands.add(command);
    commandByLabel.put(command.label(), command);
    elementsByOrder.add(command);
  }

  public List<Sig> sigs() {
    List<Sig> totalSigs = new ArrayList<Sig>(sigs);
    for (Module m : includedModules) {
      totalSigs.addAll(m.sigs());
    }
    return totalSigs;
  }

  public List<Fact> facts() {
    List<Fact> totalFacts = new ArrayList<Fact>(facts);
    for (Module m : includedModules) {
      totalFacts.addAll(m.facts());
    }
    return totalFacts;
  }

  public List<Func> funcs() {
    List<Func> totalFuncs = new ArrayList<Func>(funcs);
    for (Module m : includedModules) {
      totalFuncs.addAll(m.funcs());
    }
    return totalFuncs;
  }

  public List<Command> commands() {
    List<Command> totalCommands = new ArrayList<Command>(commands);
    for (Module m : includedModules) {
      totalCommands.addAll(m.commands());
    }
    return totalCommands;
  }

  public Sig getSig(String label) {
    if (sigByLabel.containsKey(label))
      return sigByLabel.get(label);
    for (Module m : includedModules) {
      if (m.sigByLabel.containsKey(label))
        return m.sigByLabel.get(label);
    }
    return null;
  }

  public Fact getFact(String label) {
    if (factByLabel.containsKey(label))
      return factByLabel.get(label);
    for (Module m : includedModules) {
      if (m.factByLabel.containsKey(label))
        return m.factByLabel.get(label);
    }
    return null;
  }

  public Func getFunc(String label) {
    if (funcByLabel.containsKey(label))
      return funcByLabel.get(label);
    for (Module m : includedModules) {
      Func f = m.getFunc(label);
      if (f != null) {
        return f;
      }
    }
    return null;
  }

  public Command getCommand(String label) {
    if (commandByLabel.containsKey(label))
      return commandByLabel.get(label);
    for (Module m : includedModules) {
      if (m.commandByLabel.containsKey(label))
        return m.commandByLabel.get(label);
    }
    return null;
  }

  public boolean containsSig(String label) {
    return getSig(label) != null;
  }

  public boolean containsFact(String label) {
    return getFact(label) != null;
  }

  public boolean containsFunc(String label) {
    return getFunc(label) != null;
  }

  public boolean containsCommand(String label) {
    return getCommand(label) != null;
  }

  public Iterator<Object> iterator() {
    List<Object> totalElements = new ArrayList<Object>(elementsByOrder);
    for (Module m : includedModules) {
      totalElements.addAll(m.elementsByOrder);
    }
    return totalElements.iterator();
  }

  public void addModule(Module m) {
    includedModules.add(m);
  }

}
