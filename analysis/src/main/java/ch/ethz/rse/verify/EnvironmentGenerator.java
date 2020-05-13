package ch.ethz.rse.verify;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import com.google.common.collect.Iterables;

import apron.Environment;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.pointer.TrainStationInitializer;
import soot.IntegerType;
import soot.Local;
import soot.SootField;  // IMPORTED BY MYSELF
import soot.SootMethod;
import soot.Value;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JimpleLocal;
import soot.util.Chain;

/**
 * Container for environment containing all relevant values
 *
 */
public class EnvironmentGenerator {

	private final SootMethod method;
	private final PointsToInitializer pointsTo;

	/**
	 * List of names for integer variables relevant when analyzing the program
	 */
	private List<String> ints = new LinkedList<String>();


	private final Environment env;

	/**
	 * 
	 * @param method
	 * @param pointsTo
	 */
	public EnvironmentGenerator(SootMethod method, PointsToInitializer pointsTo) {
		this.method = method;
		this.pointsTo = pointsTo;

		// populate this.ints
		
		// FILL THIS OUT
		// getting local ints
		// Question: Handle ParamRefs seperately?
		Chain<Local> locals = method.getActiveBody().getLocals();
		Iterator<Local> it = locals.iterator();
		while (it.hasNext()) {
			JimpleLocal next = (JimpleLocal) it.next();
			String name = next.getName();
			if (next.getType() instanceof IntegerType)
				ints.add(name);
		}
		
		// TODO: getting field ints of TrainStation objects
		// SootField was not imported so this was probably not intended to be solved like this
		// Thus might not work
		Chain<SootField> ifields = (pointsTo.get_class()).getFields();
		Iterator<SootField> it2 = ifields.iterator();
		it2 = ifields.iterator();
		while (it.hasNext()) {
			SootField next = it2.next();
			String name = next.getName();
			if (next.getType() instanceof IntegerType)
				ints.add(name);
		}
		
		String ints_arr[] = Iterables.toArray(this.ints, String.class);
		String reals[] = {}; // we are not analyzing real numbers
		this.env = new Environment(ints_arr, reals);
	}

	public Environment getEnvironment() {
		return this.env;
	}
	

}
