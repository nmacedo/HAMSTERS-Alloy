module AMAN

open HAMSTERS
open util/ordering[Slot]

// The state of the AMAN

// The landing sequence model 
sig Plane {
	// The slot alocated to a plane in the LS
	var slot : lone Slot
}
// The planes detected by the radar
var sig radar in Plane {}
// The planes on hold and the slots shown with label holding
var sig holding in Plane+Slot {}
// The blocked slots
var sig blocked in Slot {}

// The (ordered) slots in the LS
sig Slot {
	// The planes shown in each slot label
	var label : set Plane
}
// The desired zoom level
one var sig zoom in Slot {}
// The displayed slots
var sig displayed in Slot {}
// The planes and slots selected to put on hold or block
var sig selected in Plane+Slot {}

// derived showHolding for planes
fun showHolding : Plane {
	holding.label
}


// The AMAN task model

one sig ManageSector extends Disable {} {
	subtasks = 0->ManageLS + 1->StopManageLS
}
one sig StopManageLS extends Atomic {} {
	// Can only stop if there are no deteceted planes to manage
	guard = True iff no radar
}
one sig ManageLS extends Suspend {} {
	subtasks = 0->ManageLandingSequenceLS + 1->AMANAutonomousActivity
}
one sig ManageLandingSequenceLS extends Concurrent {} {
	subtasks = 0->MonitorLS + 1->ChangeZoom + 2->PutAircraftOnHold + 3->ModifyLS + 4->BlockTimeSlot
}
one sig MonitorLS extends Atomic {} {
	guard = True
}
one sig ModifyLS extends Atomic {} {
	// Can only occur if the there is at least one displayed label and one displayed non-blocked free slot
	guard = True iff (some Slot.label and some displayed - Plane.slot - blocked)
}
one sig ChangeZoom extends Sequence {} {
	subtasks = 0->ModifyZoom + 1->DisplayLSAfterZoom
}
one sig ModifyZoom extends Atomic {} {
	// Can only occur if there is more than one slot
	guard = True iff some Slot-zoom
}
one sig DisplayLSAfterZoom extends Atomic {} {
	guard = True
}
one sig PutAircraftOnHold extends Sequence {} {
	subtasks = 0->SelectAircraftLabel + 1->ClickHoldButton
}
one sig SelectAircraftLabel extends Atomic {} {
	// Can only occur if there is some displayed plane that is not on hold 
	guard = True iff (some (Slot-holding).label)
}
one sig ClickHoldButton extends Atomic {} {
	// Can only occur if exactly one plane is selected
	guard = True iff one selected & Plane
}
one sig AMANAutonomousActivity extends Sequence {} {
	subtasks = 0->ReceiveRadarInformation + 1->ComputeLS + 2->DisplayLS
}
one sig ReceiveRadarInformation, ComputeLS, DisplayLS extends Atomic {} {
	guard = True
}
one sig BlockTimeSlot extends Sequence {} {
	subtasks = 0->SelectSlot + 1->DisplaySlotLocked
}
one sig SelectSlot extends Atomic {} {
	// Can only occur if there is some displayed slot that is not blocked
	guard = True iff (some displayed - blocked)
}
one sig DisplaySlotLocked extends Atomic {} {
	// Can only occur if exactly one block is selected
	guard = True iff one selected & Slot
}

fact {
	Iterative = ManageLS
	Optional = ChangeZoom+PutAircraftOnHold+ModifyLS+BlockTimeSlot
	Input = ModifyLS+ModifyZoom+SelectAircraftLabel+ClickHoldButton+SelectSlot
}

// The events

pred stutter {
	no t : Atomic | execute[t]

	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
	selected' = selected
	blocked' = blocked
}

pred stopManageLS {
	execute[StopManageLS]

	zoom' = zoom

	no radar'
	no slot'
	no label'
	no holding' 
	no displayed' 
	no selected'
	no blocked'
}

pred monitorLS {
	execute[MonitorLS]

	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
	selected' = selected	
	blocked' = blocked
}

pred receiveRadarInformation {
	execute[ReceiveRadarInformation]

	// Radar is changed non-deterministically
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
	selected' = selected
	blocked' = blocked
}

pred computeLS {
	execute[ComputeLS]

	// Computes the LS non-deterministically for all planes detected by the radar
	slot'.Slot = radar
 	all s : Slot | lone slot'.s

	// planes can't be placed into blocked slots
	no Plane.slot' & blocked

	// Holding planes are restricted to those that continue to be detected by the radar
	Plane <: holding' = holding & radar
	
	Slot <: holding' = Slot <: holding
	radar' = radar
	label' = label
	displayed' = displayed
	zoom' = zoom
	selected' = selected
	blocked' = blocked
}

pred displayLS {
	execute[DisplayLS] or execute[DisplayLSAfterZoom]
		
	// Shows everything in the slots currently displayed by the zoom level
	displayed' = zoom.*prev
	label' = ~(slot :> displayed')
	Slot <: holding' = label.holding & displayed'

	radar' = radar
	slot' = slot // Changing to last does not satisfy Feedback
	zoom' = zoom
	Plane <: holding' = Plane <: holding 
	selected' = selected
	blocked' = blocked
}

pred modifyZoom {
	execute[ModifyZoom]

	zoom' != zoom

	radar' = radar
	slot' = slot
	label' = label
	holding' = holding
	displayed' = displayed
	selected' = selected
	blocked' = blocked
}

pred modifyLS {
	execute[ModifyLS]

	// Non-deterministically chooses one plane to change
	some p : Slot.label, s : displayed - Plane.slot - blocked | slot' = slot ++ p->s
	// Updates the displayed planes
	label' = ~(slot' :> displayed)

	holding' = holding
	displayed' = displayed
	radar' = radar
	zoom' = zoom	
	selected' = selected
	blocked' = blocked
}

pred selectAircraftLabel {
	execute[SelectAircraftLabel]

	// Non-deterministically selects one of the shown planes
	some s : (Slot-holding).label | Plane <: selected' = s
	
	Slot <: selected' = Slot <: selected
	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
	blocked' = blocked
}

pred clickHoldButton {
	execute[ClickHoldButton]

	// Puts the selected plane on hold
	holding' = holding + Plane <: selected
	no Plane <: selected'

	Slot <: selected' = Slot <: selected
	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	blocked' = blocked
}

pred selectSlot {
	execute[SelectSlot] 

	// Non-deterministically selects a displayed non blocked slot
	some s : displayed - blocked | Slot <: selected' = s

	Plane <: selected' = Plane <: selected
	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
	blocked' = blocked
}

pred displaySlotBlocked {
	execute[DisplaySlotLocked]

	// Blocks the selected slot
	blocked' = blocked + Slot <: selected
	no Slot <: selected'

	Plane <: selected' = Plane <: selected
	radar' = radar
	slot' = slot
	label' = label
	displayed' = displayed
	zoom' = zoom
	holding' = holding
}

fact {
	// Inital zoom is chosen non-deterministically
	displayed = zoom.*prev
	no radar
	no slot
	no label
	no holding
	no selected
	no blocked

	always {
		stutter or 
		stopManageLS or 
		receiveRadarInformation or 
		computeLS or 
		displayLS or 
		modifyZoom or 
		monitorLS or 
		modifyLS or
		selectAircraftLabel or 
		clickHoldButton or 
		selectSlot or 
		displaySlotBlocked  
	}
}

pred AMAN10s {
	// AMAN 10s rule is modelled by strong fairness
	always eventually AMANAutonomousActivity in enabled 
	implies 
	always eventually AMANAutonomousActivity in running
}

// Scenarios

run Simulation {
	no Erroneous
} for 3 but 5 seq, exactly 3 Plane, exactly 4 Slot, 20 steps expect 1

run Complete {
	// A minimal scenario where the task completes
	no Erroneous
	eventually Complete
} for 3 but 5 seq, 20 steps expect 1

run NeverComplete {
	// A minimal scenario where the task never completes
	no Erroneous
	WF
	SF_Task[AMANAutonomousActivity]
	always not Complete
} for 3 but 5 seq, 20 steps expect 1

run AllExecute {
	// A minimal scenario where all atomic tasks execute
	no Erroneous
	all t : Atomic | eventually execute[t]
} for 3 but 5 seq, 20 steps expect 1

run SomeHolding {
	// Interesting scenario showing that the fastest way to display the holding tag is by the moving the zoom
	no Erroneous
	eventually (some Slot & holding)
} for 3 but 5 seq, 20 steps expect 1

// Erroneous scenarios

run AnyError {
	// an error has occurred if
	eventually (
		some st : Sequence | 
			// a sequential task is finished and
			// the sequence of tasks executed differs from
			// the expected sequence 
			st in finished and
			st.log != st.subtasks
	)
} for 3 but 5 seq, 20 steps expect 1

run OmitError {
	// A type of error where the user omits some action
	eventually (
		some st : Sequence | 
			st in finished and
			// the length of the executed atomic tasks is less than
			// that of the expected sequence
			some i : seq/Int, x : Task | st.subtasks = insert[st.log,i,x]
	)
} for 3 but 5 seq, 20 steps expect 1


run RepeatError {
	// A type of error where the user inserts an unexpected action
	eventually (
		some st : Sequence | 
			st in finished and
			// the length of the executed atomic tasks is greater than
			// that of the expected sequence
			some i : seq/Int, x : Task | st.log = insert[st.subtasks,i,x]			
	)
}  for 3 but 5 seq, 20 steps expect 1

run ReorderError {
	// A type of error where the user reorders certain tasks
	eventually (
		some st : Sequence | 
			st in finished and
			// the executed and expected task sequence have the length
			// but they are different
			#st.log = #st.subtasks and
			elems[st.log] = elems[st.subtasks] and
			st.log != st.subtasks)
} for 3 but 5 seq, 20 steps expect 1


// Assertions

assert HoldingInRadar {
	// A trivially false assertion
	no Erroneous implies always holding in radar 
}
check HoldingInRadar for 3 but 5 seq, 20 steps expect 1

assert LabelsInLS {
	// Another trivially false assertion
	no Erroneous implies always label in ~slot
}
check LabelsInLS for 3 but 5 seq, 20 steps expect 1

assert NoLabelOverlap {
	// Req5 
	// Aircraft labels should not overlap
	no Erroneous implies 
	always (all s : Slot | lone s.label)
} 
check NoLabelOverlap for 3 but 5 seq, 20 steps expect 0

assert NoLabelsBlockedA {
	// Req6 
	// An aircraft label cannot be moved into a blocked time period
	no Erroneous implies 
	always (no p : Plane | some label.p & blocked)
}
check NoLabelsBlockedA for 3 but 5 seq, 20 steps expect 1

assert NoLabelsBlockedB {
	// Req6 
	// Only temporarily can there be labels on blocked slots
	no Erroneous and 
	WF implies always {
		eventually (no p : Plane | some label.p & blocked)
	}
}
check NoLabelsBlockedB for 3 but 5 seq, 20 steps expect 0


pred DisplayChanges {
	label' != label or 
    holding' & Slot != holding & Slot or 
	displayed' != displayed or 
	selected' & Slot.label' != selected & Slot.label or
	selected' & displayed' != selected & displayed or
	blocked' & displayed' != blocked & displayed or
	zoom' != zoom
}

assert Feedback {
	// Req9
	// Every user input task is followed by some changes in the displayed information
	no Erroneous and 
	WF implies all t : Input | always (execute[t] implies eventually DisplayChanges)
}
check Feedback for 3 but 5 seq, 20 steps expect 0

assert NoDeadlock {
	// Req14
	// If the task is not complete then some event must be enabled
	no Erroneous implies 
	always (Root not in done implies not Deadlock)
}
check NoDeadlock for 3 but 5 seq, 20 steps expect 0

assert SelectAvailable {
	// If a non holding plane is on the display it should be possible to select it to put on hold
	no Erroneous and 
	SF implies always (always (some (Slot-holding).label) implies eventually (SelectAircraftLabel in enabled))
} 
check SelectAvailable for 3 but 5 seq, 20 steps expect 0

check AMAN_fairness {
    WF implies AMAN10s
} for 3 but 5 seq, 20 steps
