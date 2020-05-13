package ch.ethz.rse.pointer;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import apron.ApronException;
import ch.ethz.rse.numerical.NumericalAnalysis;
import ch.ethz.rse.numerical.NumericalStateWrapper;
import ch.ethz.rse.utils.Constants;
import soot.Local;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.spark.pag.Node;

public class PointsToInitializer {

	private static final Logger logger = LoggerFactory.getLogger(PointsToInitializer.class);

	/**
	 * Internally used points-to analysis
	 */
	private final PointsToAnalysisWrapper pointsTo;

	/**
	 * class for which we are running points-to
	 */
	private final SootClass c;

	/**
	 * Maps abstract object indices to initializers
	 */
	private final Map<Node, TrainStationInitializer> initializers = new HashMap<Node, TrainStationInitializer>();

	/**
	 * All {@link TrainStationInitializer}s, keyed by method
	 */
	private final Multimap<SootMethod, TrainStationInitializer> perMethod = HashMultimap.create();

	public PointsToInitializer(SootClass c) {
		this.c = c;
		logger.debug("Running points-to analysis on " + c.getName());
		this.pointsTo = new PointsToAnalysisWrapper(c);
		logger.debug("Analyzing initializers in " + c.getName());
		this.analyzeAllInitializers();
	}
   
	private void analyzeAllInitializers() {
		//a unique Integer Id for every TrainStation Object. see Incrementation below
		int Id=0;
		for (SootMethod method : this.c.getMethods()) {
			
			if (method.getName().contains("<init>")) {
				// skip constructor of the class
				continue;
			}

			// populate data structures
			// mapping from internal object abstraction of soot which is based on Node
			//to our own object abstraction which is Trainstationinitializer.
			
		    //TrainStationInitializer class assigns a unique integer to every trainstation object 
		    //and saves the invoked constructor expression that initialized the trainstation object.
		    //This is another way of abstracting objects as opposed to the lecture where we 
		    //used the allocation line number as the abstraction of our objects
		    
			for (Unit u : method.retrieveActiveBody().getUnits()) {

				if (u instanceof JInvokeStmt
						&& ((JInvokeStmt) u).getInvokeExpr() instanceof JSpecialInvokeExpr) {
					
					JInvokeStmt invokeStmt = (JInvokeStmt) u;

					JSpecialInvokeExpr invokeExpr = (JSpecialInvokeExpr) invokeStmt
							.getInvokeExpr();
					//base is just the local variable that refers to a trainstation object
					//I think object initialization in jimple
					//is represented as sth like c.alloc('constructor arguments') which has c as base
					Local base = (Local) invokeExpr.getBase();
					//all the nodes in pointer abstract that can be reached by the by base
					Collection<Node> pts =  pointsTo.getNodes(base);
					Value argValue = invokeExpr.getArg(0);

					if (argValue instanceof IntConstant) {
						//we increment Id everytime we see an object allocation in any method 
						Id++;
						int argInt = ((IntConstant) argValue).value;
						for(Node node:pts) {
							TrainStationInitializer tsObject=new TrainStationInitializer(invokeStmt,Id,argInt);
							initializers.put(node, tsObject);
							//add this tsObject to the objects that belong to this method
							perMethod.put(method, tsObject);
						}
						
					} else {
						//I think we don't handle other cases because it is stated in the Project Description. 
						//that the constructor argument is always an IntConstant
					}
				
				}			
			}	
		}
	}
	
	public SootClass get_class() {
		return this.c;
	}
	//added getters 
	public Map<Node, TrainStationInitializer>  get_initializers() {
		return this.initializers;
	}
	public Multimap<SootMethod, TrainStationInitializer> get_perMethod(){
		return this.perMethod;}

}
