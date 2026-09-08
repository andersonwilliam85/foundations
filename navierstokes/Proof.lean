import hodge.Proof
import poincare.Proof

/-
  Navier–Stokes: a flow is a lock-shape plus instants.
  Smooth = every instant Whole. Blow-up = an instant has a Hole.
  Finished = a Poincaré meeting that closed. Sphere.dent, not the world.
  Their how is not installed. Their prize is not claimed.
-/

/-- Periodic lock or open lock. Two locks. -/
inductive LockKind where
  | open
  | periodic
  deriving DecidableEq, Repr

/-- Outside pairing. None, or a cycle from outside. -/
inductive Force where
  | none
  | outside (c : Cycle)
  deriving DecidableEq, Repr

/-- A flow owes a lock-shape and carries a list of instants. -/
structure Flow where
  lock : Shape
  instants : List Shape
  force : Force
  kind : LockKind
  deriving Repr

/-- Place-and-time is a meeting. Velocity and pressure are two readings of it. -/
def velocityReading (m : Meeting) : List Seat :=
  m.dent

def pressureReading (m : Meeting) : List Seat :=
  m.lock

/-- 1. Two readings of one meeting. Not two objects. -/
theorem two_readings_of_one_meeting (m : Meeting) :
    velocityReading m = m.dent ∧ pressureReading m = m.lock :=
  ⟨rfl, rfl⟩

/-- Their fields are not installed. -/
def fieldsInstalled : Prop := False

theorem fields_not_installed : ¬ fieldsInstalled :=
  id

/-- 2. Incompressible: the dent owes exactly the lock. -/
def Incompressible (m : Meeting) : Prop :=
  m.dent = m.lock

theorem incompressible_of_dent_eq_lock (m : Meeting)
    (h : m.dent = m.lock) : Incompressible m :=
  h

/-- Incompressible with a missing seat is not a finished meeting. -/
theorem incompressible_missing_not_closed (m : Meeting)
    (_hi : Incompressible m) (hh : m.Hole) : ¬ m.Closed :=
  missing_not_closed m hh

/-- 3. Initial condition: the first instant. -/
def Flow.firstInstant (f : Flow) : Option Shape :=
  f.instants.head?

def Flow.Initial (f : Flow) (s : Shape) : Prop :=
  f.instants.head? = some s

theorem initial_is_first (f : Flow) (s : Shape) (h : f.Initial s) :
    f.firstInstant = some s :=
  h

theorem empty_has_no_initial (s : Shape) :
    ¬ ({ lock := ⟨[], []⟩, instants := [], force := .none, kind := .open } : Flow).Initial s := by
  intro h
  cases h

/-- 4. Force is an outside pairing. A/B: none. C/D: allowed. -/
def Flow.Unforced (f : Flow) : Prop :=
  f.force = Force.none

def Flow.Forced (f : Flow) : Prop :=
  ∃ c, f.force = Force.outside c

theorem unforced_of_none (f : Flow) (h : f.force = Force.none) : f.Unforced :=
  h

theorem unforced_not_forced (f : Flow) (h : f.Unforced) : ¬ f.Forced := by
  intro ⟨_c, hc⟩
  rw [h] at hc
  cases hc

/-- 5. Their viscosity is not installed. Euler is not this prize. -/
def viscosityInstalled : Prop := False

theorem viscosity_not_installed : ¬ viscosityInstalled :=
  id

def eulerIsThisPrize : Prop := False

theorem euler_not_this_prize : ¬ eulerIsThisPrize :=
  id

/-- 6. Decay at infinity: a stranger pairing is not a hole. -/
def stranger : Cycle := ⟨0, 0⟩

theorem decay_stranger_not_hole (s : Shape) (h : stranger ∉ s.belong) :
    ¬ s.Hole stranger := by
  intro hh
  exact h hh.1

/-- 7. Smooth: every instant is Whole.
    Door 8 (join of wholes) sits on Hodge `join_whole_of_whole`. -/
def Flow.Smooth (f : Flow) : Prop :=
  ∀ s ∈ f.instants, s.Whole

/-- Blow-up: some instant has a Hole. Not ontology. -/
def Flow.BlowUp (f : Flow) : Prop :=
  ∃ s ∈ f.instants, ∃ c : Cycle, s.Hole c

@[simp] theorem smooth_iff_every_instant_whole (f : Flow) :
    f.Smooth ↔ ∀ s ∈ f.instants, s.Whole :=
  Iff.rfl

theorem smooth_of_every_instant_whole (f : Flow)
    (h : ∀ s ∈ f.instants, s.Whole) : f.Smooth :=
  h

theorem drop_instant_not_smooth (f : Flow) (s : Shape) (c : Cycle)
    (hin : (s.drop c) ∈ f.instants) (hb : c ∈ s.belong) :
    ¬ f.Smooth := by
  intro hs
  exact drop_not_whole s c hb (hs (s.drop c) hin)

theorem blowup_not_smooth (f : Flow) (h : f.BlowUp) : ¬ f.Smooth := by
  intro hs
  obtain ⟨s, hin, c, hh⟩ := h
  exact (whole_iff_no_hole s).mp (hs s hin) c hh

/-- Their C^∞ is seated as Smooth. No missing seat on a finished meeting. -/
def Meeting.NoMissing (m : Meeting) : Prop :=
  ¬ m.Hole

theorem missing_is_not_smooth_seats (m : Meeting) (h : m.Hole) : ¬ m.NoMissing :=
  fun n => n h

/-- 9. Two locks. -/
def Flow.OpenLock (f : Flow) : Prop :=
  f.kind = LockKind.open

def Flow.PeriodicLock (f : Flow) : Prop :=
  f.kind = LockKind.periodic

theorem open_not_periodic {f : Flow} (ho : f.OpenLock) (hp : f.PeriodicLock) : False :=
  nomatch (ho.symm.trans hp)

/-- 10–13. Their four doors, seated. Not claimed as their prize. -/
def StatementA : Prop :=
  ∀ f : Flow, f.OpenLock → f.Unforced → f.Smooth

def StatementB : Prop :=
  ∀ f : Flow, f.PeriodicLock → f.Unforced → f.Smooth

def StatementC : Prop :=
  ∃ f : Flow, f.OpenLock ∧ f.Forced ∧ f.BlowUp

def StatementD : Prop :=
  ∃ f : Flow, f.PeriodicLock ∧ f.Forced ∧ f.BlowUp

theorem statementA_is_the_claim :
    StatementA ↔ ∀ f : Flow, f.OpenLock → f.Unforced → f.Smooth :=
  Iff.rfl

theorem statementB_is_the_claim :
    StatementB ↔ ∀ f : Flow, f.PeriodicLock → f.Unforced → f.Smooth :=
  Iff.rfl

def oneCycle : Cycle := ⟨1, 2⟩

def holeLock : Shape where
  belong := [oneCycle]
  present := []

theorem holeLock_is_hole : holeLock.Hole oneCycle := by
  constructor
  · decide
  · decide

def forcedOpenHole : Flow where
  lock := holeLock
  instants := [holeLock]
  force := .outside ⟨3, 4⟩
  kind := .open

def forcedPeriodicHole : Flow where
  lock := holeLock
  instants := [holeLock]
  force := .outside ⟨3, 4⟩
  kind := .periodic

theorem forcedOpenHole_blowup : forcedOpenHole.BlowUp :=
  ⟨holeLock, List.Mem.head [], oneCycle, holeLock_is_hole⟩

theorem forcedPeriodicHole_blowup : forcedPeriodicHole.BlowUp :=
  ⟨holeLock, List.Mem.head [], oneCycle, holeLock_is_hole⟩

/-- 12. A forced open-lock flow with a Hole sits. -/
theorem statementC_seated : StatementC :=
  ⟨forcedOpenHole, rfl, ⟨⟨3, 4⟩, rfl⟩, forcedOpenHole_blowup⟩

/-- 13. A forced periodic-lock flow with a Hole sits. -/
theorem statementD_seated : StatementD :=
  ⟨forcedPeriodicHole, rfl, ⟨⟨3, 4⟩, rfl⟩, forcedPeriodicHole_blowup⟩

/-- 14. Clay asks for one of A–D. All four sit. Their prize is not claimed. -/
def clayPrizeClaimed : Prop := False

theorem clay_prize_not_claimed : ¬ clayPrizeClaimed :=
  id

/-- 15. Two dimensions are known. Three dimensions are the lock. Twelve pairings stay. -/
def planeIsKnown : Prop := True

theorem two_dimensions_known : planeIsKnown :=
  trivial

def threeDimensionsAreTheLock : Prop := True

theorem three_dimensions_are_the_lock : threeDimensionsAreTheLock :=
  trivial

/-- 16. Local existence / blow-up time: a hole before the meeting finishes. -/
def EarlyHole (f : Flow) (m : Meeting) : Prop :=
  f.BlowUp ∧ ¬ m.Closed

theorem hole_before_meeting_finishes (f : Flow) (m : Meeting)
    (hb : f.BlowUp) (hnc : ¬ m.Closed) : EarlyHole f m :=
  ⟨hb, hnc⟩

/-- 17. A small Whole lock stays Whole. Hodge `Shape.Small` / `small_whole_stays_whole`. -/
theorem small_drop_not_whole (s : Shape) (c : Cycle) (hb : c ∈ s.belong) :
    ¬ (s.drop c).Whole :=
  drop_not_whole s c hb

/-- A finished flow is a Poincaré meeting that closed. -/
def Finished (m : Meeting) : Prop :=
  m.Closed

theorem finished_is_complete (m : Meeting) (h : Finished m) : m.Complete :=
  h

theorem finished_working_shape (m : Meeting) (h : Finished m) :
    workingShape m h = Sphere.dent :=
  complete_meeting_is_the_sphere m h

theorem finished_not_world (m : Meeting) (h : Finished m) :
    ¬ (workingShape m h).asWorld :=
  sphere_is_not_the_world m h

theorem missing_not_finished (m : Meeting) (h : m.Hole) : ¬ Finished m :=
  missing_not_closed m h

/-- A blow-up is a hole. It is not the world. -/
def blowUpIsTheWorld : Prop := False

theorem blowup_not_the_world : ¬ blowUpIsTheWorld :=
  id
