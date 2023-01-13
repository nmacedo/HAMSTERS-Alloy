module HAMSTERS

abstract sig Task {}
abstract sig Atomic extends Task {
	var guard : lone True
}
one sig True {}
abstract sig Composite extends Task {
	subtasks : seq Task
}
abstract sig Disable, Suspend, Concurrent, Choice extends Composite {}

abstract sig Sequence extends Composite {
	var log : seq Task
}

one sig Root in Task {}
sig Iterative, Optional, Input in Task {}

sig Erroneous in Atomic {}

// Derived parent relationship
fun parent : Task -> Task {
	{ a,b : Task | a in elems[b.subtasks] }
}

// Derived successor relationship between sibling tasks
fun succ : Task -> Task {
	{ x, y : Task | some p : Task | x+y in elems[p.subtasks] and idxOf[p.subtasks,y] = idxOf[p.subtasks,x].next }
}

// Static semantics

fact Tree {
	// The task model forms a tree
	no Root.parent
	all t : Task-Root | one t.parent
	all t : Task | t not in t.^parent
}

fact WellFormed {

	// Composite tasks must have at least two (non-duplicate) subtasks
	all t : Composite | not lone elems[t.subtasks] and not hasDups[t.subtasks]

	// The following are requirements in CTT, not sure if HAMSTERS has the same requirements

	// Choice, disable, and suspend tasks cannot have optional children
	all t : Choice+Disable+Suspend | no parent.t & Optional

	// The first subtask of a sequence task cannot be iterative 
	all t : Sequence | no succ.(parent.t) & Iterative

	// The following also seems reasonable
 	all t : Sequence+Concurrent | some parent.t - Optional

	// Erroneous tasks are input atomic sub-tasks of sequences
	all t : Erroneous | t in Input and some t.parent & Sequence
}

// Dynamic semantics

var sig executed, enabled, running, finished, done in Task {}

fact Behavior { no executed and no log and always {
	// Possible events
	nop or (some t : Atomic | execute[t]) or (some t : Task | reset[t])
	// The enabled tasks
	enabled = { t : Task | {
		// The parent is enabled
		t.parent in enabled
		// If atomic the guard must be true and cannot be done
		t in Atomic implies t.guard = True and (t in Erroneous or t not in done)
		// If inside a choice no sibling can be running
		some t.parent & Choice implies no (parent.(t.parent) - t) & running
		// If inside a sequence the predecessor is done (unless the task is erroneous) or is optional and is not running
		some t.parent & Sequence implies all x : ^succ.t | ((t in Erroneous or x in done) or (x in Optional and x not in running))
		// And the successors cannot be running or done (unless the task is erroneous)
		some t.parent & Sequence implies no t.^succ & running and (t in Erroneous or no t.^succ & done)
		// If inside a disable the successor cannot be running or done
		some t.parent & Disable implies no t.succ & (running + done)
		// If inside a suspend the successor cannot be running
		some t.parent & Suspend implies no t.succ & running
		}}
	// The running tasks are those not yet done but that already started
	running = { t : Task | t not in done and some ^parent.t & done }
	// The tasks that finished executing
	finished = { t : Task | { 
		// An atomic task is finished if it done
		t in Atomic implies t in executed
		// With the exception of disables, a composite task is only finished if no children is still running
		t not in Disable implies no parent.t & running
		// If it is sequence the last non-optional sub-task must be done
		t in Sequence implies (all t : parent.t - Optional | no t.^succ - Optional implies t in done)
		// Likewise for concurrent tasks
		t in Concurrent implies parent.t - Optional in done
		// If it is a choice some children must be done
		t in Choice implies some parent.t & done
		// If it is a suspend the first task must be done
		t in Suspend implies parent.t - (parent.t).succ in done
		// If it is a disable the last task must be done
		t in Disable implies parent.t - succ.(parent.t) in done
		}}
	// The non-iterative and non-suspending tasks that already finished
	done = { t : Task | t in finished - Iterative - (parent.Suspend).succ }
	}
}

// The enabled atomic tasks, for visualization purposes
var sig Enabled in Atomic {}
fact {
	always Enabled = enabled & Atomic
}

// Not executing a task
pred nop {
	executed' = executed
	log' = log
}

// Executing an atomic task
pred execute [t : Atomic] {
	t in enabled
	executed' = executed + t

	all x : Sequence & t.parent | x.log' = x.log.add[t]

	all x : Sequence - t.parent {
		some parent.x & (finished' - finished) 
		implies x.log' = x.log.add[parent.x & (finished' - finished)] 
		else x.log' = x.log
	}
}

// Reseting an iterative or suspending task
pred reset [t : Task] {
	t in enabled & (finished - done)
	executed' = executed - *parent.t
	all x : *parent.t | no x.log'
	all x : Sequence - *parent.t | x.log' = x.log
}

pred WF_Task[t:Task] {
	// Weak fairness
	t in Atomic implies (eventually always (t in enabled) implies always eventually execute[t])
	eventually always (t in enabled and t in finished - done) implies always eventually reset[t]
}

pred WF {
	// Weak fairness
	all t : Atomic | eventually always (t in enabled) implies always eventually execute[t]
	all t : Task | eventually always (t in enabled and t in finished - done) implies always eventually reset[t]
}

pred SF_Task[t:Task] {
	// Strong fairness
	t in Atomic implies (always eventually (t in enabled) implies always eventually execute[t])
	always eventually (t in enabled and t in finished - done) implies always eventually reset[t]
}

pred SF {
	// Strong fairness
	all t : Atomic |  always eventually (t in enabled) implies always eventually execute[t]
	all t : Task |  always eventually (t in enabled and t in finished - done) implies always eventually reset[t]
}

pred Complete {
	// The overal task is complete when the root is done
	Root in done
}

pred Deadlock {
	no t : Atomic | t in enabled
 	no t : Task | t in enabled and t in finished - done
}

run Complete {
	no Erroneous and eventually Complete
}

run ErroneousComplete {
	some Erroneous and eventually Complete
}

assert NoDeadlock {
	// If the task is not complete and guards are true then some event must be enabled
	no Erroneous
	implies 
	always (guard.True = Atomic and not Complete implies not Deadlock)
}
check NoDeadlock for 6 but 3 seq, 10 steps expect 0

