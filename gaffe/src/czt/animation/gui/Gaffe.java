package czt.animation.gui;
import czt.animation.gui.design.DesignerCore;
import javax.swing.*;
import java.awt.GridLayout;
import java.awt.event.KeyEvent;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.Arrays;
import java.beans.Beans;
import java.io.*;

/**
 ** The main class for GAfFE.
 ** Provides the main program, and the ability to select animate or design mode.
 */
public class Gaffe extends JFrame {
  private static String[] getArgsTail(String[] args) {
    //chop off args[0]
    return (String[])Arrays.asList(args).subList(1,args.length).toArray(new String[0]);
  };
  
  public static void main(String[] args) {
    if(args.length>0) 
      if(args[0].equals("--design")) {
	DesignerCore.run(getArgsTail(args));
	return;
      } else if (args[0].equals("--animate")) {
	AnimatorCoreBase.run(getArgsTail(args));
	return;
      } else if (args[0].equals("--help")) {
	System.err.println("Usage: gaffe [--design|--animate] <arguments>");
	System.err.println("  or:  gaffe --help");
	System.err.println();
	System.err.println("  --design\tdesign mode");
	System.err.println("  --animate\tanimate mode");
	System.err.println("  --help\tthis help page");
	System.err.println("  [otherwise]\trun gui chooser");
	return;
      };
    if(Beans.isGuiAvailable())
      (new Gaffe(args)).show();
    else {
      BufferedReader br=new BufferedReader(new InputStreamReader(System.in));
      System.err.println("Please choose (a)nimate, or (d)esign mode, or (q)uit:");
      while(true) {
	String input;
	try {
	  input=br.readLine().toLowerCase();
	} catch(IOException e) {
	  System.err.println("IO Exception while reading input");
	  System.err.println(e);
	  return;
	};
	
	if(input.equals("q"))
	  return;
	else if(input.equals("a")) {
	  System.err.println("At present animate mode hasn't been implemented.");
	  //xxx	  AnimatorCoreBase.run(args);
	}
	else if(input.equals("d")) {
	  DesignerCore.run(args);
	  return;
	}
      }
    }
  };

  protected Gaffe() {
    this(new String[0]);
  };
  protected Gaffe(final String[] args) {
    setSize(300,300);
    setTitle("GAfFE");
    getContentPane().setLayout(new GridLayout(4,1));
    
    getContentPane().add(new JLabel("Please choose animate or design mode:",JLabel.CENTER));
    JButton animate, design, quit;
    getContentPane().add(animate=new JButton("Animate"));
    animate.setMnemonic(KeyEvent.VK_A);
    animate.setEnabled(false);
    getContentPane().add(design=new JButton("Design"));
    design.setMnemonic(KeyEvent.VK_D);
    getContentPane().add(quit=new JButton("Quit"));
    quit.setMnemonic(KeyEvent.VK_Q);
    
    design.addActionListener(new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	  dispose();
	  DesignerCore.run(args);
	};
      });
    animate.addActionListener(new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	  dispose();
	    AnimatorCoreBase.run(args);
	};
      });
    quit.addActionListener(new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	  dispose();
	};
      });
    setDefaultCloseOperation(DISPOSE_ON_CLOSE);
  };  
};
