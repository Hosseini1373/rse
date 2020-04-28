package ch.ethz.rse.numerical;

import java.util.HashMap;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.pointer.TrainStationInitializer;
import ch.ethz.rse.utils.Constants;
import ch.ethz.rse.verify.EnvironmentGenerator;
import soot.ArrayType;
import soot.DoubleType;
import soot.IntegerType;
import soot.Local;
import soot.RefType;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AddExpr;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.MulExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JDivExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;

public class NumericalAnalysis extends ForwardBranchedFlowAnalysis<NumericalStateWrapper> {

	private static final Logger logger = LoggerFactory.getLogger(NumericalAnalysis.class);

	private final SootMethod method;

	private final PointsToInitializer pointsTo;

	/**
	 * number of times this loop head was encountered during analysis
	 */
	private HashMap<Unit, IntegerWrapper> loopHeads = new HashMap<Unit, IntegerWrapper>();
	/**
	 * Previously seen abstract state for each loop head
	 */
	private HashMap<Unit, NumericalStateWrapper> loopHeadState = new HashMap<Unit, NumericalStateWrapper>();

	/**
	 * Numerical abstract domain to use for analysis: COnvex polyhedra
	 */
	//added field
	public static String resourceArrayName = "PrinterArray";
	public final Manager man = new Polka(true);

	public final Environment env;

	/**
	 * We apply widening after updating the state at a given merge point for the
	 * {@link WIDENING_THRESHOLD}th time
	 */
	private static final int WIDENING_THRESHOLD = 6;

	/**
	 * 
	 * @param method   method to analyze
	 * @param g        control flow graph of the method
	 * @param pointsTo result of points-to analysis
	 */
	public NumericalAnalysis(SootMethod method, UnitGraph g, PointsToInitializer pointsTo) {
		super(g);

		this.method = method;
		this.pointsTo = pointsTo;

		this.env = new EnvironmentGenerator(method, this.pointsTo).getEnvironment();

		// initialize counts for loop heads
		for (Loop l : new LoopNestTree(g.getBody())) {
			loopHeads.put(l.getHead(), new IntegerWrapper(0));
		}

		// perform analysis by calling into super-class
		logger.info("Analyzing {} in {}", method.getName(), method.getDeclaringClass().getName());
		doAnalysis();
	}

	/**
	 * Report unhandled instructions, types, cases, etc.
	 * 
	 * @param task description of current task
	 * @param what
	 */
	public static void unhandled(String task, Object what, boolean raiseException) {
		String description = task + ": Can't handle " + what.toString() + " of type " + what.getClass().getName();

		if (raiseException) {
			throw new UnsupportedOperationException(description);
		} else {
			logger.error(description);

			// print stack trace
			StackTraceElement[] stackTrace = Thread.currentThread().getStackTrace();
			for (int i = 1; i < stackTrace.length; i++) {
				logger.error(stackTrace[i].toString());
			}
		}
	}

	@Override
	protected void copy(NumericalStateWrapper source, NumericalStateWrapper dest) {
		source.copyInto(dest);
	}

	@Override
	protected NumericalStateWrapper newInitialFlow() {
		// should be bottom (only entry flows are not bottom originally)
		return NumericalStateWrapper.bottom(man, env);
	}

	@Override
	protected NumericalStateWrapper entryInitialFlow() {
		// state of entry points into function
		NumericalStateWrapper ret = NumericalStateWrapper.top(man, env);


		return ret;
	}

	@Override
	protected void merge(Unit succNode, NumericalStateWrapper w1, NumericalStateWrapper w2, NumericalStateWrapper w3) {
		logger.debug("in merge: " + succNode);

		logger.debug("join: ");
		NumericalStateWrapper w3_new = w1.join(w2);

	}

	@Override
	protected void merge(NumericalStateWrapper src1, NumericalStateWrapper src2, NumericalStateWrapper trg) {
		// this method is never called, we are using the other merge instead
		throw new UnsupportedOperationException();
	}
	
	
	//added method for handling if statement
	private void handleIf(AbstractBinopExpr eqExpr, Abstract1 in, NumericalStateWrapper ow,
			NumericalStateWrapper ow_branchout) throws ApronException {

		Value leftOp = eqExpr.getOp1();
		Value rightOp = eqExpr.getOp2();

		Texpr1Node leftNode = null;

		if (leftOp instanceof IntConstant) {
			leftNode = new Texpr1CstNode(new MpqScalar(
					((IntConstant) leftOp).value));
		} else if (leftOp instanceof JimpleLocal) {
			if (leftOp.getType().toString().equals(NumericalAnalysis.resourceArrayName)) {
				ow.set(new Abstract1(man, in));
				ow_branchout.set(new Abstract1(man, in));
				return;
			}
			leftNode = new Texpr1VarNode(((JimpleLocal) leftOp).getName());
		} else {
			unhandled("unexpected leftOp in eqExpr: " , leftOp.getClass(),true);
		}

		Texpr1Node rightNode = null;

		if (rightOp instanceof IntConstant) {
			rightNode = new Texpr1CstNode(new MpqScalar(
					((IntConstant) rightOp).value));
		} else if (rightOp instanceof JimpleLocal) {
			if (rightOp.getType().toString().equals(NumericalAnalysis.resourceArrayName)) {
				ow.set(new Abstract1(man, in));
				ow_branchout.set(new Abstract1(man, in));
				return;
			}
			rightNode = new Texpr1VarNode(((JimpleLocal) rightOp).getName());
		} else {
			unhandled("unexpected rightOp in eqExpr: " , rightOp.getClass(),true);
		}

		Texpr1Node lmrExpr = new Texpr1BinNode(Texpr1BinNode.OP_SUB, leftNode,
				rightNode);
		Texpr1Node rmlExpr = new Texpr1BinNode(Texpr1BinNode.OP_SUB, rightNode,
				leftNode);

		// Constraints we add to the abstract element are of the following form:
		// - leftNode - rightNode (cmp_kind) 0, e.g., lmrExpr >= 0
		// - rightNode - leftNode (cmp_kind) 0, e.g., rmlExpr == 0
		Tcons1 branchCons = null, fallCons = null;

		// TODO: Handle required conditional expressions
		// @andrinadenzler 2016-05-29 20:16 implemented except for imprecision
		// in cases like (n != 0): (n != 0) is treated as (n in [-oo,+oo])
		//  and provides no constraint on n at all
		if (eqExpr instanceof JEqExpr) {
			branchCons = new Tcons1(env, Tcons1.EQ, lmrExpr);
			fallCons = new Tcons1(env, Tcons1.DISEQ, lmrExpr);
		} else if (eqExpr instanceof JNeExpr) {
			branchCons = new Tcons1(env, Tcons1.DISEQ, lmrExpr);
			fallCons = new Tcons1(env, Tcons1.EQ, lmrExpr);
		} else if (eqExpr instanceof JGeExpr) {
			branchCons = new Tcons1(env, Tcons1.SUPEQ, lmrExpr);
			fallCons = new Tcons1(env, Tcons1.SUP, rmlExpr);
		} else if (eqExpr instanceof JGtExpr) {
			branchCons = new Tcons1(env, Tcons1.SUP, lmrExpr);
			fallCons = new Tcons1(env, Tcons1.SUPEQ, rmlExpr);
		} else if (eqExpr instanceof JLeExpr) {
			branchCons = new Tcons1(env, Tcons1.SUPEQ, rmlExpr);
			fallCons = new Tcons1(env, Tcons1.SUP, lmrExpr);
		} else if (eqExpr instanceof JLtExpr) {
			branchCons = new Tcons1(env, Tcons1.SUP, rmlExpr);
			fallCons = new Tcons1(env, Tcons1.SUPEQ, lmrExpr);
		} else {
			unhandled("unexpected eqExpr: " , eqExpr.getClass(),true);
		}

		ow.set(in.meetCopy(man, fallCons));
		ow_branchout.set(in.meetCopy(man, branchCons));

		NumericalStateWrapper state = new NumericalStateWrapper(man,in);
//TODO: make the logging work 
//		logger.debug("Bin_Op1: " + getInterval(state, leftOp));
//		logger.debug("Bin_Op2: " + getInterval(state, rightOp));
//		logger.debug("Bin_Res: " + eqExpr.getClass() + ": " + branchCons);
	}

	@Override
	protected void flowThrough(NumericalStateWrapper inWrapper, Unit op, List<NumericalStateWrapper> fallOutWrappers,
			List<NumericalStateWrapper> branchOutWrappers) {
		logger.debug(inWrapper + " " + op + " => ?");

		Stmt s = (Stmt) op;

		// wrapper for state after running op, assuming we move to the next statement
		assert fallOutWrappers.size() <= 1;
		NumericalStateWrapper fallOutWrapper = null;
		if (fallOutWrappers.size() == 1) {
			fallOutWrapper = fallOutWrappers.get(0);
			inWrapper.copyInto(fallOutWrapper);
		}

		// wrapper for state after running op, assuming we follow a jump
		assert branchOutWrappers.size() <= 1;
		NumericalStateWrapper branchOutWrapper = null;
		if (branchOutWrappers.size() == 1) {
			branchOutWrapper = branchOutWrappers.get(0);
			inWrapper.copyInto(branchOutWrapper);
		}

		try {
			if (s instanceof DefinitionStmt) {
				// handle assignment

				DefinitionStmt sd = (DefinitionStmt) s;
				Value left = sd.getLeftOp();
				Value right = sd.getRightOp();

				// We are not handling these cases:
				if (!(left instanceof JimpleLocal)) {
					unhandled("Assignment to non-local variable", left, true);
				} else if (left instanceof JArrayRef) {
					unhandled("Assignment to a non-local array variable", left, true);
				} else if (left.getType() instanceof ArrayType) {
					unhandled("Assignment to Array", left, true);
				} else if (left.getType() instanceof DoubleType) {
					unhandled("Assignment to double", left, true);
				} else if (left instanceof JInstanceFieldRef) {
					unhandled("Assignment to field", left, true);
				}

				if (left.getType() instanceof RefType) {
					// assignments to references are handled by pointer analysis
					// no action necessary
				} else {
					// handle assignment
					handleDef(fallOutWrapper, left, right);
				}

			} else if (s instanceof JIfStmt) {
				// handle if
				
				IfStmt ifs = (JIfStmt) s;
				Value condition = ifs.getCondition();

				if (condition instanceof JEqExpr
						|| condition instanceof JNeExpr
						|| condition instanceof JGeExpr
						|| condition instanceof JLeExpr
						|| condition instanceof JLtExpr
						|| condition instanceof JGtExpr) {
					AbstractBinopExpr eqExpr = (AbstractBinopExpr) condition;
					
					Abstract1 in = ((NumericalStateWrapper) inWrapper).get();
					Abstract1 o = new Abstract1(man, in);
					NumericalStateWrapper ow = new NumericalStateWrapper(man,in);
					NumericalStateWrapper ow_branchout = new NumericalStateWrapper(man,in);
					Abstract1 o_branchout = new Abstract1(man, in);
					handleIf(eqExpr, in, ow, ow_branchout);
					o = ow.get();
					o_branchout = ow_branchout.get();
				}

			} else if (s instanceof JInvokeStmt && ((JInvokeStmt) s).getInvokeExpr() instanceof JVirtualInvokeExpr) {
				// handle invocations

				JInvokeStmt jInvStmt = (JInvokeStmt) s;
				handleInvoke(jInvStmt, fallOutWrapper);
			}

			// log outcome
			if (fallOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[fallout] " + fallOutWrapper);
			}
			if (branchOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[branchout] " + branchOutWrapper);
			}

		} catch (ApronException e) {
			throw new RuntimeException(e);
		}
	}

	public void handleInvoke(JInvokeStmt jInvStmt, NumericalStateWrapper fallOutWrapper) throws ApronException {
		// FILL THIS OUT
	}


	/**
	 *
	 * handle assignment
	 *
	 * @param in
	 * @param left
	 * @param right
	 * @return state of in after assignment
	 */
	private void handleDef(NumericalStateWrapper outWrapper, Value left, Value right) throws ApronException {
		// FILL THIS OUT
	}

}
