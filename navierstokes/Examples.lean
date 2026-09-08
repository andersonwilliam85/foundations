import navierstokes.Proof

/-
  Hostile sample problems, one door at a time.
  Twelve belonging pairings stay the lock.
  A problem you can get wrong.
-/

def belonging : List Cycle := lockPairings

def full : Shape where
  belong := belonging
  present := belonging

def sixth : Cycle := ⟨6, 13⟩
def last : Cycle := ⟨12, 37⟩
def first : Cycle := ⟨1, 2⟩

def holed : Shape := full.drop sixth

def oneSixth : Shape := ⟨[sixth], [sixth]⟩
def oneLast : Shape := ⟨[last], [last]⟩
def joined : Shape := oneSixth.join oneLast

def emptyWhole : Shape := ⟨[], []⟩

/-- Dent sat the lock. Twelve filled seats. -/
def closedMeeting : Meeting where
  lock := List.replicate 12 (Seat.filled 1)
  dent := List.replicate 12 (Seat.filled 1)

/-- Dent missed the lock. -/
def unfinishedMeeting : Meeting where
  lock := List.replicate 12 (Seat.filled 1)
  dent := List.replicate 12 (Seat.filled 2)

/-- Dent equals lock, and the lock itself has a missing. -/
def incompressibleMissing : Meeting where
  lock := List.replicate 5 (Seat.filled 1) ++ [Seat.missing] ++ List.replicate 6 (Seat.filled 1)
  dent := List.replicate 5 (Seat.filled 1) ++ [Seat.missing] ++ List.replicate 6 (Seat.filled 1)

/-- One missing seat. Meeting not finished. -/
def missSixth : Meeting where
  lock := List.replicate 12 (Seat.filled 1)
  dent := List.replicate 5 (Seat.filled 1) ++ [Seat.missing] ++ List.replicate 6 (Seat.filled 1)

theorem missSixth_hole : missSixth.Hole :=
  ⟨Seat.missing, by decide, rfl⟩

theorem incompressibleMissing_hole : incompressibleMissing.Hole :=
  ⟨Seat.missing, by decide, rfl⟩

def wholeInstant : Flow where
  lock := full
  instants := [full]
  force := .none
  kind := .open

def droppedInstant : Flow where
  lock := full
  instants := [full.drop sixth]
  force := .none
  kind := .open

def droppedPeriodic : Flow where
  lock := full
  instants := [full.drop sixth]
  force := .none
  kind := .periodic

def secondFirst : Flow where
  lock := full
  instants := [full, holed]
  force := .none
  kind := .open

def smallWhole : Shape := oneSixth

/-- 1. Two readings of one meeting. Hostile: they are not fields. -/
example : velocityReading closedMeeting = closedMeeting.dent ∧
    pressureReading closedMeeting = closedMeeting.lock :=
  two_readings_of_one_meeting closedMeeting

example : ¬ fieldsInstalled :=
  fields_not_installed

/-- 2. Incompressible: dent owes exactly the lock. Hostile: missing still not finished. -/
example : Incompressible closedMeeting :=
  incompressible_of_dent_eq_lock closedMeeting rfl

example : Incompressible incompressibleMissing :=
  incompressible_of_dent_eq_lock incompressibleMissing rfl

example : ¬ incompressibleMissing.Closed :=
  incompressible_missing_not_closed incompressibleMissing rfl incompressibleMissing_hole

/-- 3. Initial condition is the first instant. Hostile: empty has none; second is not first. -/
example : wholeInstant.Initial full :=
  rfl

example : ¬ wholeInstant.Initial holed := by
  intro h
  cases h

example : ¬ ({ lock := full, instants := [], force := .none, kind := .open } : Flow).Initial full :=
  empty_has_no_initial full

/-- 4. Force: A/B none. C/D outside. Hostile: unforced is not forced. -/
example : wholeInstant.Unforced :=
  rfl

example : ¬ wholeInstant.Forced :=
  unforced_not_forced wholeInstant rfl

example : forcedOpenHole.Forced :=
  ⟨⟨3, 4⟩, rfl⟩

/-- 5. Viscosity not installed. Euler is not this prize. -/
example : ¬ viscosityInstalled :=
  viscosity_not_installed

example : ¬ eulerIsThisPrize :=
  euler_not_this_prize

/-- 6. Decay: stranger is not a hole. Hostile: drop a stranger, still whole. -/
example : ¬ full.Hole stranger :=
  decay_stranger_not_hole full (by decide)

example : (full.drop stranger).Whole :=
  present_eq_belong_whole (full.drop stranger) (by decide)

theorem mem_one_full {s : Shape} (hs : s ∈ [full]) : s = full :=
  List.mem_singleton.mp hs

/-- 7. Smooth: every instant Whole. Hostile: a drop is a Hole, not Smooth. -/
example : wholeInstant.Smooth :=
  smooth_of_every_instant_whole wholeInstant (by
    intro s hs
    rw [mem_one_full hs]
    exact present_eq_belong_whole full rfl)

example : holed.Hole sixth :=
  drop_is_hole full sixth (by decide)

example : ¬ holed.Whole :=
  drop_not_whole full sixth (by decide)

example : ¬ droppedInstant.Smooth :=
  drop_instant_not_smooth droppedInstant full sixth (List.Mem.head []) (by decide)

/-- 8. Join of wholes is Whole. Hostile: join with a hole is not. -/
example : joined.Whole :=
  join_whole_of_whole oneSixth oneLast
    (present_eq_belong_whole oneSixth rfl)
    (present_eq_belong_whole oneLast rfl)

example : ¬ (emptyWhole.join holeLock).Whole := by
  intro hw
  have h := holeLock_is_hole
  have hb : oneCycle ∈ emptyWhole.belong ++ holeLock.belong :=
    List.mem_append.mpr (Or.inr h.1)
  have hp := hw oneCycle hb
  have hin : oneCycle ∈ holeLock.present := by
    cases List.mem_append.mp hp with
    | inl hnil => exact (List.not_mem_nil hnil).elim
    | inr hin => exact hin
  exact h.2 hin

/-- 9. Two locks. Hostile: open is not periodic. -/
example : wholeInstant.OpenLock :=
  rfl

example : ¬ wholeInstant.PeriodicLock := by
  intro h
  exact open_not_periodic (rfl : wholeInstant.OpenLock) h

/-- 10. Door A is the claim. Hostile: unforced open with a drop is not Smooth. -/
example : StatementA ↔ ∀ f : Flow, f.OpenLock → f.Unforced → f.Smooth :=
  statementA_is_the_claim

example : droppedInstant.OpenLock ∧ droppedInstant.Unforced ∧ ¬ droppedInstant.Smooth :=
  ⟨rfl, rfl, drop_instant_not_smooth droppedInstant full sixth (List.Mem.head []) (by decide)⟩

/-- 11. Door B is the claim. Hostile: unforced periodic with a drop is not Smooth. -/
example : StatementB ↔ ∀ f : Flow, f.PeriodicLock → f.Unforced → f.Smooth :=
  statementB_is_the_claim

example : droppedPeriodic.PeriodicLock ∧ droppedPeriodic.Unforced ∧ ¬ droppedPeriodic.Smooth :=
  ⟨rfl, rfl, drop_instant_not_smooth droppedPeriodic full sixth (List.Mem.head []) (by decide)⟩

/-- 12. Door C: a forced open-lock flow with a Hole. -/
example : StatementC :=
  statementC_seated

example : forcedOpenHole.OpenLock ∧ forcedOpenHole.Forced ∧ forcedOpenHole.BlowUp :=
  ⟨rfl, ⟨⟨3, 4⟩, rfl⟩, forcedOpenHole_blowup⟩

/-- 13. Door D: a forced periodic-lock flow with a Hole. -/
example : StatementD :=
  statementD_seated

example : forcedPeriodicHole.PeriodicLock ∧ forcedPeriodicHole.Forced ∧ forcedPeriodicHole.BlowUp :=
  ⟨rfl, ⟨⟨3, 4⟩, rfl⟩, forcedPeriodicHole_blowup⟩

/-- 14. All four sit. Their prize is not claimed. -/
example : ¬ clayPrizeClaimed :=
  clay_prize_not_claimed

/-- 15. Twelve pairings stay. 2D known. 3D is the lock. -/
example : lockPairings.length = 12 :=
  twelve_pairings_stay

example : belonging = lockPairings :=
  rfl

example : planeIsKnown ∧ threeDimensionsAreTheLock :=
  ⟨two_dimensions_known, three_dimensions_are_the_lock⟩

/-- 16. A hole before the meeting finishes. Hostile: a finished meeting is not that. -/
example : EarlyHole droppedInstant missSixth :=
  hole_before_meeting_finishes droppedInstant missSixth
    ⟨full.drop sixth, List.Mem.head [], sixth, drop_is_hole full sixth (by decide)⟩
    (missing_not_closed missSixth missSixth_hole)

example : Finished closedMeeting :=
  closed_of_dent_eq_lock closedMeeting rfl (by decide)

example : ¬ EarlyHole wholeInstant closedMeeting := by
  intro ⟨hb, _hnc⟩
  exact blowup_not_smooth wholeInstant hb (smooth_of_every_instant_whole wholeInstant (by
    intro s hs
    rw [mem_one_full hs]
    exact present_eq_belong_whole full rfl))

/-- 17. Small Whole lock stays Whole. Hostile: drop it and it does not. -/
example : smallWhole.Small := by
  decide

example : smallWhole.Whole :=
  small_whole_stays_whole smallWhole (by decide) (present_eq_belong_whole smallWhole rfl)

example : ¬ (smallWhole.drop sixth).Whole :=
  small_drop_not_whole smallWhole sixth (by decide)

/-- Finished meeting: Sphere.dent, not the world. -/
example : workingShape closedMeeting (closed_of_dent_eq_lock closedMeeting rfl (by decide)) = Sphere.dent :=
  finished_working_shape closedMeeting (closed_of_dent_eq_lock closedMeeting rfl (by decide))

example : ¬ (workingShape closedMeeting (closed_of_dent_eq_lock closedMeeting rfl (by decide))).asWorld :=
  finished_not_world closedMeeting (closed_of_dent_eq_lock closedMeeting rfl (by decide))

example : ¬ Finished missSixth :=
  missing_not_finished missSixth missSixth_hole

example : ¬ blowUpIsTheWorld :=
  blowup_not_the_world

/-- Finite seating check. This is the run, not a second harness. -/
def seated (s : Shape) : Bool :=
  s.belong.all (fun c => s.present.contains c)

def hole (s : Shape) (c : Cycle) : Bool :=
  s.belong.contains c && !s.present.contains c

def isSmooth (f : Flow) : Bool :=
  f.instants.all seated

def hasHoleM (m : Meeting) : Bool :=
  m.dent.contains Seat.missing

def isClosed (m : Meeting) : Bool :=
  m.dent == m.lock && !hasHoleM m

def run : IO Unit := do
  let put (n : Nat) (q : String) (b : Bool) : IO Unit :=
    IO.println s!"{n}. {q}  {b}"
  IO.println "navierstokes"
  put 1 "velocity reading is the dent?" (velocityReading closedMeeting == closedMeeting.dent)
  put 2 "incompressible missing — closed?" (isClosed incompressibleMissing)
  put 3 "empty flow has a first instant?" false
  put 4 "unforced whole flow is forced?" (match wholeInstant.force with | .none => false | .outside _ => true)
  put 5 "viscosity installed?" false
  put 6 "stranger a hole on the full lock?" (hole full stranger)
  put 7 "dropped instant smooth?" (isSmooth droppedInstant)
  put 8 "join of two one-cycle wholes — whole?" (seated joined)
  put 9 "open flow is periodic?" (decide (wholeInstant.kind = .periodic))
  put 10 "unforced open with a drop — smooth?" (isSmooth droppedInstant)
  put 11 "unforced periodic with a drop — smooth?" (isSmooth droppedPeriodic)
  put 12 "forced open has a hole?" (isSmooth forcedOpenHole)
  put 13 "forced periodic has a hole?" (isSmooth forcedPeriodicHole)
  put 14 "clay prize claimed?" false
  put 15 "twelve pairings stay?" (decide (lockPairings.length = 12))
  put 16 "missing meeting finished?" (isClosed missSixth)
  put 17 "small drop still whole?" (seated (smallWhole.drop sixth))

#eval run
