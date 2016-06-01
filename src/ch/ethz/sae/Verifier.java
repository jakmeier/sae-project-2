package ch.ethz.sae;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Interval;
import apron.Manager;
import apron.MpqScalar;
import apron.Tcons1;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import soot.Unit;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.internal.JDivExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.spark.sets.DoublePointsToSet;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.SparkTransformer;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.PAG;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.ValueBox;
import soot.toolkits.graph.BriefUnitGraph;

public class Verifier {
	
	public static void main(String[] args) {
		if (args.length != 1) {
			System.err.println("Usage: java -classpath soot-2.5.0.jar:./bin ch.ethz.sae.Verifier <class to test>");
			System.exit(-1);
		}
		String analyzedClass = args[0];
		SootClass c = loadClass(analyzedClass);

		PAG pointsToAnalysis = doPointsToAnalysis(c);

		int programCorrectFlag = 1;
		int divisionByZeroFlag = 1;

		for (SootMethod method : c.getMethods()) {

			Analysis analysis = new Analysis(new BriefUnitGraph(method.retrieveActiveBody()), c);
			analysis.run();

			if (!verifyBounds(method, analysis, pointsToAnalysis)) {
				programCorrectFlag = 0;
			}
			if (!verifyDivisionByZero(method, analysis)) {
				divisionByZeroFlag = 0;
			}
		}
		
		if (divisionByZeroFlag == 1) {
			System.out.println(analyzedClass + " NO_DIV_ZERO");
		} else {
			System.out.println(analyzedClass + " MAY_DIV_ZERO");
		}
		
		if (programCorrectFlag == 1) {
            System.out.println(analyzedClass + " NO_OUT_OF_BOUNDS");
        } else {
            System.out.println(analyzedClass + " MAY_OUT_OF_BOUNDS");
        }
	}
	
	private static boolean verifyDivisionByZero(SootMethod method, Analysis fixPoint) {
		for (Unit u : method.retrieveActiveBody().getUnits()) {
			AWrapper state = fixPoint.getFlowBefore(u);
			try {
		    		if (state.get().isBottom(Analysis.man))
	    			// unreachable code
					continue;
			} catch (ApronException e) {
				e.printStackTrace();
			} 
			
			
			//TODO: Check that all divisors are not zero
			for (ValueBox inani: u.getUseBoxes()) {
				if ( inani.getValue() instanceof JDivExpr ) {
					System.out.println("Guess what I found: " + inani.toString() + " of class: " + inani.getClass() + " (a JDivExpr)");
					//System.out.println("By the way, 2 / 0 = " + ((Integer)(2/0)).toString());
					Value divisor = ((JDivExpr) inani.getValue()).getOp2();
					if ( divisor instanceof JimpleLocal ) {
						Texpr1Node isihlukanisi = new Texpr1VarNode(((JimpleLocal) divisor).getName());
						try {
							Interval boundary = state.get().getBound(state.get().getCreationManager(), new Texpr1Intern(state.get().getEnvironment(), isihlukanisi));
							Interval zero = new Interval(0,0);
							if ( boundary.cmp(zero) == 0 || boundary.cmp(zero) == 1 || boundary.cmp(zero) == -1 ) return false;
						} catch (ApronException e) {
							e.printStackTrace();
						}
								
					} else if (divisor instanceof IntConstant) {
						if ( ((IntConstant) divisor).value == 0 ) {
							//System.out.println("Constant used as divisor may be zero. | " + divisor.toString());
							return false;
						}
					}
					else {
						System.out.println("Unexpected divisor: " + divisor.toString() + " of type " + divisor.getType().toString());
					}
				}
			}
	    }
		
		//Return true if the method has no division by zero errors
	    return true;
	}
	
	static List<Interval> paInterval;
	
	private static boolean verifyBounds(SootMethod method, Analysis fixPoint,
			PAG pointsTo) {
				
		//TODO: Create a list of all allocation sites for PrinterArray
		
		paInterval = new ArrayList<Interval>();
		
		for (Unit u : method.retrieveActiveBody().getUnits()) {
			AWrapper state = fixPoint.getFlowBefore(u);
		
			try {
				if (state.get().isBottom(Analysis.man)) {
					// unreachable code
					continue;
				} 
			} catch (ApronException e) {
				e.printStackTrace();
			} 

			
			if (u instanceof JInvokeStmt && ((JInvokeStmt) u).getInvokeExpr() instanceof JSpecialInvokeExpr) {
				System.out.println("Special invoke found");
				// TODO: Get the size of the PrinterArray given as argument to the constructor
				JSpecialInvokeExpr inkulumo = (JSpecialInvokeExpr) ((JInvokeStmt) u).getInvokeExpr(); 
				System.out.println("Declaring class: " + inkulumo.getMethod().getDeclaringClass());
				if (inkulumo.getMethod().getDeclaringClass().toString().equals("PrinterArray")) {
					System.out.println("Declaring class printer invoke");
					Value size = inkulumo.getArg(0);
					if ( size instanceof IntConstant ) {
						System.out.println("Add interval");
						paInterval.add( new Interval (0, ((IntConstant) size).value -1 ));
					}
					else {
						System.out.println("PrinterArray was constructed with an argument that is not a IntConstant: " + size);
					}
				}

			}
			
			if (u instanceof JInvokeStmt && ((JInvokeStmt) u).getInvokeExpr() instanceof JVirtualInvokeExpr) {
				
				JInvokeStmt jInvStmt = (JInvokeStmt)u;
				
				JVirtualInvokeExpr invokeExpr = (JVirtualInvokeExpr)jInvStmt.getInvokeExpr();
				
				Local base = (Local) invokeExpr.getBase();
				DoublePointsToSet pts = (DoublePointsToSet) pointsTo
						.reachingObjects(base);
				
				if (invokeExpr.getMethod().getName().equals(Analysis.functionName)) {
					
					// TODO: Check whether the 'sendJob' method's argument is within bounds
					Value v = invokeExpr.getArg(0);
					Interval arrayIndex = Analysis.getInterval(state, v);
					
					
					// Visit all allocation sites that the base pointer may reference
					MyP2SetVisitor visitor = new MyP2SetVisitor(arrayIndex);
					if (! pts.forall(visitor)){
						return false;
					}
				}
			}
		}

		return true;
	}

	private static SootClass loadClass(String name) {
		SootClass c = Scene.v().loadClassAndSupport(name);
		c.setApplicationClass();
		return c;
	}

	private static PAG doPointsToAnalysis(SootClass c) {
		Scene.v().setEntryPoints(c.getMethods());

		HashMap<String, String> options = new HashMap<String, String>();
		options.put("enabled", "true");
		options.put("verbose", "false");
		options.put("propagator", "worklist");
		options.put("simple-edges-bidirectional", "false");
		options.put("on-fly-cg", "true");
		options.put("set-impl", "double");
		options.put("double-set-old", "hybrid");
		options.put("double-set-new", "hybrid");

		SparkTransformer.v().transform("", options);
		PAG pag = (PAG) Scene.v().getPointsToAnalysis();

		return pag;
	}	
}

class MyP2SetVisitor extends P2SetVisitor{
	
	public MyP2SetVisitor (Interval i) {
		this.arrayIndex = i;
		this.returnValue = true;
	}
	
	private Interval arrayIndex; 
	
	@Override
	public void visit(Node arg0) {
		//TODO: Check whether the argument given to sendJob is within bounds
		System.out.println("Node number: " + arg0.getNumber() + " Node: " + arg0);
		Interval paInterval = Verifier.paInterval.get(arg0.getNumber()-1);
		if (!( paInterval.cmp(this.arrayIndex) == 0 || paInterval.cmp(this.arrayIndex) == 1 )) {
			this.returnValue = false;
		}
	}
}
