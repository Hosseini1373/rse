package ch.ethz.rse.numerical;

import java.util.HashMap;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Interval;//added import
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
import soot.jimple.ConditionExpr;//added import
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;//added import
import soot.jimple.MulExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
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
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.jimple.toolkits.thread.mhp.Counter;
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

	
	
	
	
	
	
	
	
	
	
	private void handleDef(NumericalStateWrapper fallOutWrapper, Value left, Value right)
			throws ApronException {
	Abstract1 o=fallOutWrapper.get();
	Texpr1Node lAr = null;
	Texpr1Node rAr = null;
	Texpr1Intern xp = null;

	if (left instanceof JimpleLocal) {
		String varName = ((JimpleLocal) left).getName();

		if (right instanceof IntConstant) {
			IntConstant constant = (IntConstant) right;
			rAr = new Texpr1CstNode(new MpqScalar(constant.value));
			xp = new Texpr1Intern(env, rAr);
			o.assign(man, varName, xp, null);
		} else if (right instanceof JimpleLocal) {
			JimpleLocal local = (JimpleLocal) right;
			if (isIntValue(local)) {
				rAr = new Texpr1VarNode(local.getName());
				xp = new Texpr1Intern(env, rAr);
				o.assign(man, varName, xp, null);
			} else {
				unhandled("JimpleLocal of non-integer type in numerical analysis."
						, local.getType() ,true);
			}
		} else if (right instanceof AbstractBinopExpr) {
			AbstractBinopExpr binopExpr = (AbstractBinopExpr) right;

			Value leftOp = binopExpr.getOp1();
			Value rightOp = binopExpr.getOp2();

			Texpr1Node leftNode = null;

			if (leftOp instanceof IntConstant) {
				leftNode = new Texpr1CstNode(new MpqScalar(
						((IntConstant) leftOp).value));
			} else if (leftOp instanceof JimpleLocal) {
				leftNode = new Texpr1VarNode(
						((JimpleLocal) leftOp).getName());
			} else {
				unhandled("unexpected leftOp in binopExpr: ",
						 leftOp.getClass(),true);
			}

			Texpr1Node rightNode = null;

			if (rightOp instanceof IntConstant) {
				rightNode = new Texpr1CstNode(new MpqScalar(
						((IntConstant) rightOp).value));
			} else if (rightOp instanceof JimpleLocal) {
				rightNode = new Texpr1VarNode(
						((JimpleLocal) rightOp).getName());
			} else {
				unhandled("unexpected rightOp in binopExpr: ",
						 rightOp.getClass(),true);
			}

			if (binopExpr instanceof JMulExpr) {
				rAr = new Texpr1BinNode(Texpr1BinNode.OP_MUL, leftNode,
						rightNode);
			} else if (binopExpr instanceof JSubExpr) {
				rAr = new Texpr1BinNode(Texpr1BinNode.OP_SUB, leftNode,
						rightNode);
			} else if (binopExpr instanceof JAddExpr) {
				rAr = new Texpr1BinNode(Texpr1BinNode.OP_ADD, leftNode,
						rightNode);
			} else if (binopExpr instanceof JDivExpr) {
				rAr = new Texpr1BinNode(Texpr1BinNode.OP_DIV, leftNode,
						rightNode);
			}
			
			NumericalStateWrapper state = new NumericalStateWrapper(man,o);
			logger.debug("Bin_Op1: " + getInterval(state, leftOp));
			logger.debug("Bin_Op2: " + getInterval(state, rightOp));

			xp = new Texpr1Intern(env, rAr);
			if (binopExpr instanceof JDivExpr
					&& rightOp instanceof IntConstant
					&& ((IntConstant) rightOp).value == 0) {
				o = new Abstract1(man, env, true);
			} else {
				o.assign(man, varName, xp, null);
			}

			logger.debug("Bin_Res: " + binopExpr.getClass() + ": "
					+ getInterval(state, left));
		}
		// TODO: Handle other kinds of assignments (e.g. x = y * z)
		// implemented except for some
		// potential corner cases
		else {

		}
	 }
	//back to NumericalStateWrapper
	fallOutWrapper.set(o);
	}
	
	
	
	
	
	
	
	
	
	
	
	
	/// computes the output states of applying an if statement
	public void handleIf(JIfStmt jIf, NumericalStateWrapper fallOutWrapper, NumericalStateWrapper branchOutWrapper) throws ApronException {
		final boolean verbose = false;
		Abstract1 fall=fallOutWrapper.get();
		Abstract1 branch=branchOutWrapper.get();
		// parse expressions on either side
		ConditionExpr cond = (ConditionExpr) jIf.getCondition();
		Texpr1Node l = toExpr(cond.getOp1());
		Texpr1Node r = toExpr(cond.getOp2());

		// parse (in-)equality for easier logic later in toConstraint
		boolean equality = cond instanceof JEqExpr || cond instanceof JNeExpr; // ==, !=
		boolean strict = cond instanceof JGtExpr || cond instanceof JLtExpr; // >, <
		boolean negated = cond instanceof JNeExpr || cond instanceof JLeExpr || cond instanceof JLtExpr; // !=, <=, <
		

		// apply constraints for un-/fulfillment
		applyConstraint(branch, l, r, equality, strict, negated);
		applyConstraint(fall, l, r, equality, !strict, !negated);
		//back to NumericalStateWrapper
		fallOutWrapper.set(fall);
		branchOutWrapper.set(branch);
	}
	
	// wraps around toConstraint (applying it) with special handling for inequality
	public void applyConstraint(Abstract1 state, Texpr1Node l, Texpr1Node r, boolean equality, boolean strict, boolean negated) throws ApronException {
		if (equality && negated) {
			// special handling for inequality, because polyhedra are imprecise for it
			Abstract1 copy = new Abstract1(man, state);
			applyConstraint(state, l, r, false, true, false);
			applyConstraint(copy, l, r, false, true, true);
			state.join(man, copy);
		} else {
			// handle everything else normally
			state.meet(man, toConstraint(l, r, equality, strict, negated));
		}
	}

	// converts an (in-)equality of a given type to a Tcons1 linear constraint (e.g. l >= r -> l-r >= 0; l < r -> r-l > 0 -> r-l-1 >= 0)
	public Tcons1 toConstraint(Texpr1Node l, Texpr1Node r, boolean equality, boolean strict, boolean negated) {
		// if negated, constrain r-l, otherwise l-r
		Texpr1BinNode sub = new Texpr1BinNode(Texpr1BinNode.OP_SUB, negated ? r : l, negated ? l : r);
		int cons;
		if (equality)
			cons = negated ? Tcons1.DISEQ : Tcons1.EQ;
		else
			cons = strict ? Tcons1.SUP : Tcons1.SUPEQ;
		// something not to be confused by: SUP is just SUPEQ with the bound adjusted by one
		return new Tcons1(env, cons, sub);
	}

	// extracts the (arithmetic) operation of a Soot binary expression
	public static int getOp(BinopExpr bin) {
		if (bin instanceof JAddExpr) return Texpr1BinNode.OP_ADD;
		if (bin instanceof JSubExpr) return Texpr1BinNode.OP_SUB;
		if (bin instanceof JMulExpr) return Texpr1BinNode.OP_MUL;
		// not even supposed to handle this: if (bin instanceof JDivExpr) return Texpr1BinNode.OP_DIV;
		unhandled("Couldn't convert value of type to op", bin.getClass(), true);
		return -1;
	}

	// converts a Soot expression (Value) to an Apron expression (Texpr1Node)
	public static Texpr1Node toExpr(Value value) {
		if (value instanceof BinopExpr) {
			BinopExpr bin = (BinopExpr) value;
			int op = getOp(bin);
			Texpr1Node l = toExpr(bin.getOp1());
			Texpr1Node r = toExpr(bin.getOp2());
			return new Texpr1BinNode(op, l, r);
		}
		if (value instanceof IntConstant) {
			int val = ((IntConstant) value).value;
			return new Texpr1CstNode(new MpqScalar(val));
		}
		if (value instanceof JimpleLocal) {
			String name = ((JimpleLocal) value).getName();
			return new Texpr1VarNode(name);
		}
		// this is fine - failedConversion(value, "expr");
		return null;
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
	
	
	
	
	
	
	
	
	//I modified the method here
	@Override
	protected void merge(Unit succNode, NumericalStateWrapper w1, NumericalStateWrapper w2, NumericalStateWrapper w3) {

		IntegerWrapper count = loopHeads.get(succNode);

		Abstract1 a1 = w1.get();
		Abstract1 a2 = w2.get();
		Abstract1 a3 = null;

		try {
			if (count != null) {
				++count.value;
				if (count.value < WIDENING_THRESHOLD) {
					a3 = a1.joinCopy(man, a2);
				} else {
					//Logger.log("widening", a1, "with", a2);
					if (a2.isBottom(man))
						a3 = a2;
					else
						a3 = a1.widening(man, a2);
				}
			} else {
				a3 = a1.joinCopy(man, a2);
			}
			w3.set(a3);
		} catch (Exception e) {
			System.out.println(e);
		}
	}

	@Override
	protected void merge(NumericalStateWrapper src1, NumericalStateWrapper src2, NumericalStateWrapper trg) {
		// this method is never called, we are using the other merge instead
		throw new UnsupportedOperationException();
	}

	@Override
	protected void flowThrough(NumericalStateWrapper inWrapper, Unit op, List<NumericalStateWrapper> fallOutWrappers,
			List<NumericalStateWrapper> branchOutWrappers) {
		logger.debug(inWrapper + " " + op + " => ?");

		Stmt s = (Stmt) op;


		/**For most statements, only fallOut is relevant, you can ignore branchOut for them.
		
		As you say, both fallOut and branchOut are relevant for ifs and loops. Both ifs and loops get transformed to conditional jumps in Jimple, so it suffices to think in terms of conditional jumps.
		
		For `if cond goto A`, `fallOut` contains the state after "falling out" of the statement, i.e., if the condition is false. `branchOut` contains the state after "branching out" of the statement, i.e., if the condition is true.
		
		With this definition, it does not matter which transformation Jimple uses, both will be handled correctly. */
				
		assert fallOutWrappers.size() <= 1;
		NumericalStateWrapper fallOutWrapper = null;
		if (fallOutWrappers.size() == 1) {
			fallOutWrapper = fallOutWrappers.get(0);
			inWrapper.copyInto(fallOutWrapper);
		}

		// wrapper for state after running op, assuming we follow a jump
		//branchOutWrapper branch is the state when we enter an if branch(condition holds)
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
				handleIf((JIfStmt)s,fallOutWrapper,branchOutWrapper);
				// FILL THIS OUT

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



	
	
	
	
	
	//added method that goes with the getIntervalmethod
	public static final boolean isIntValue(Value val) {
		return val.getType().toString().equals("int")
				|| val.getType().toString().equals("short")
				|| val.getType().toString().equals("byte");
	}
	
	
	
	//added method to 
	public final Interval getInterval(NumericalStateWrapper state, Value val) {
		Interval top = new Interval();
		top.setTop();
		if (!isIntValue(val)) {
			return top;
		}
		if (val instanceof IntConstant) {
			int value = ((IntConstant) val).value;
			return new Interval(value, value);
		}
		if (val instanceof Local) {
			String var = ((Local) val).getName();
			Interval interval = null;
			try {
				interval = state.get().getBound(man, var);
			} catch (ApronException e) {
				e.printStackTrace();
			}
			return interval;
		}
		if (val instanceof InvokeExpr) {
			return top;
		}
		return top;
	}
	
	
	
	
	
	
	
	
	

}
