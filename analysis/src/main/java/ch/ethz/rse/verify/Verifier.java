package ch.ethz.rse.verify;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import apron.ApronException;
import apron.Environment;
import apron.Interval;//added import
import apron.MpqScalar;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import ch.ethz.rse.VerificationProperty;
import ch.ethz.rse.numerical.NumericalAnalysis;
import ch.ethz.rse.numerical.NumericalStateWrapper;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.pointer.TrainStationInitializer;
import ch.ethz.rse.utils.Constants;
import soot.Local;
import soot.SootClass;
import soot.SootHelper;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.IntConstant;//added Import
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.jimple.spark.pag.Node;//added import
/**
 * Main class handling verification
 * 
 */
public class Verifier extends AVerifier {

	private static final Logger logger = LoggerFactory.getLogger(Verifier.class);

	private final SootClass c;
	private final PointsToInitializer pointsTo;
	private final Map<SootMethod, NumericalAnalysis> numericalAnalysis = new HashMap<SootMethod, NumericalAnalysis>();

	/**
	 * 
	 * @param c class to verify
	 */
	public Verifier(SootClass c) {
		logger.debug("Analyzing {}", c.getName());

		this.c = c;
		// pointer analysis
		this.pointsTo = new PointsToInitializer(this.c);
		// numerical analysis
		this.runNumericalAnalysis();
	}

	
	
	
	
	//go through every method of the test class and put a key mapping 
	//the method to the corresponding analysis
	
	private void runNumericalAnalysis() {
		
		for (SootMethod method : c.getMethods()) {

			NumericalAnalysis analysis = new NumericalAnalysis(method,new BriefUnitGraph(
					            method.retrieveActiveBody()), pointsTo);
			numericalAnalysis.put(method, analysis);
		}
		
	}

	
	

	
	

	
	
	
	
	
	
	
	
	
	
	
	
	@Override
	public boolean checkTrackNonNegative() {
		// FILL THIS OUT
		for (SootMethod method : c.getMethods()) {

			NumericalAnalysis analysis = this.numericalAnalysis.get(method);
			for (Unit u : method.retrieveActiveBody().getUnits()) {
				NumericalStateWrapper state = analysis.getFlowBefore(u);//loopHeadState.get(u);
				
				try {
					if (state.get().isBottom(analysis.man)) {
						// unreachable code
						continue;
					}
				} catch (ApronException e) {
					e.printStackTrace();
				}
				
				if (u instanceof JInvokeStmt
						&& ((JInvokeStmt) u).getInvokeExpr() instanceof JVirtualInvokeExpr) {

					JInvokeStmt invokeStmt = (JInvokeStmt) u;

					JVirtualInvokeExpr invokeExpr = (JVirtualInvokeExpr) invokeStmt
							.getInvokeExpr();

					Local base = (Local) invokeExpr.getBase();
					/*
					if (pointsTo.reachingObjects(base) instanceof EmptyPointsToSet) {
						return false;
					}
					*/
					if (invokeExpr.getMethod().getName()
							.equals("arrive")) { //instead of analysis.functionName


						Value argValue = invokeExpr.getArg(0);
						Interval argInterval = state.getInterval(argValue);
						logger.debug("argument to the arrive function "+argInterval.toString());
						//debug("VirtualInvokeExpr with argument: " + argInterval);
						
						// According to project descriptions only values between -10k and 10k are used
						// So need to check if the argument is a subset of [-10000,-1] to check for non-negativity
						logger.debug("the checkInterval that we compare with argument to Interval "+argInterval.inf().cmp(0));
						// I'm assuming this is the correct method to call
						// Again the documentation is not really helpful
						if(argInterval.inf().cmp(0)==-1) {
							return false;
						}
					}
				}
				
			}
		}
		// no calls to method arrive violated non-negativity
	return true;

	}
	
	
	
	
	
	
	
	
	
	
	

	
//check the CheckTrackNonNegative first and then run this		
	@Override
	public boolean checkTrackInRange() {
		/**
		//go through the hashmap and add t
		for (Map.Entry<SootMethod, NumericalAnalysis> entry : numericalAnalysis.entrySet()) {
		    SootMethod method = entry.getKey();
		    NumericalAnalysis fixPoint = entry.getValue();
		    
		    
			for (Unit u : method.retrieveActiveBody().getUnits()) {
				//the state in line  before the execution of statement u
				NumericalStateWrapper state = fixPoint.getFlowBefore(u);
				//see whether a line of code or in other words u is executed at all 
				//so one toDo is that we handle invoke in NumericalAnalysis and make sure that
				//if an invoke stm is reached we set the state corresponding to the stm to Top
				//so that it doesn't stay bottom and we know after, that invoke stm could be 
				//reached and was not in a branch of if or while or ... that could never be reached
				//according to our numerical analysis
				try {
					if (state.get().isBottom(fixPoint.man)) {
						// unreachable code
						continue;
					}
				} catch (ApronException e) {
					e.printStackTrace();
				}
				
				
				//we handle  JSpecialInvokeExpr in PointstoInitalization, basically the constructors of the trainstation objects
				if (u instanceof JInvokeStmt
						&& ((JInvokeStmt) u).getInvokeExpr() instanceof JSpecialInvokeExpr) {
				}
				
				
				//call to arrive function
				if (u instanceof JInvokeStmt
						&& ((JInvokeStmt) u).getInvokeExpr() instanceof JVirtualInvokeExpr) {

					JInvokeStmt invokeStmt = (JInvokeStmt) u;

					JVirtualInvokeExpr invokeExpr = (JVirtualInvokeExpr) invokeStmt
							.getInvokeExpr();
					

					Local base = (Local) invokeExpr.getBase();
					//check whether the base object is a initialized
					Collection<Node> nodes=pointsTo.reachingObjects(base);
					
					if (nodes.isEmpty()) {
						return false;
					}
					
					//check whether the function is arrive()
					if (invokeExpr.getMethod().getName()
							.equals("arrive")) {
						
						Value argValue = invokeExpr.getArg(0);
						//this is a bit different from michael's code because 
						//I added the getInterval method in the NumericalAnalysis class
						Interval argInterval = fixPoint
								.getInterval(state, argValue);

						logger.info("VirtualInvokeExpr with argument: " + argInterval);
						//for every TrainStationInitializer object (which corresponds to one node)
						//that the base variable points to, check whether its ntracks field is in ranger
						for(Node node:nodes) {
							TrainStationInitializer tsObject=pointsTo.get_initializers().get(node);
							int ntracks=tsObject.nTracks;
							if (!(argInterval.isLeq(new Interval(0, ntracks-1)))) 
								return false;
						}
						
					}
				}
			}		    
		}
		
		//if none of the methods contain an arrive with out of bound argument
		//then return true
		 
		 */
		return true;	
		
	}
	

	

	@Override
	public boolean checkNoCrash() {
		return true;
	}


}
