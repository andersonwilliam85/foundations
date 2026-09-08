import hodge.Proof

/-
  Hostile examples from the Hodge seating.
  Twelve belonging pairings stay the lock.
  Score any official door wrong and the example fails.
-/

def belonging : List Cycle :=
  lockPairings

def full : Shape :=
  thisLock

def first : Cycle := ⟨1, 2⟩
def sixth : Cycle := ⟨6, 13⟩
def last : Cycle := ⟨12, 37⟩
def stranger : Cycle := ⟨0, 0⟩

/-- Same owed pairings, sitting in a different order. -/
def shuffled : Shape where
  belong := belonging
  present := belonging.reverse

/-- Drop the sixth pairing. -/
def dropSixth : Shape :=
  full.drop sixth

/-- Drop the sixth and the last. -/
def dropSixthLast : Shape :=
  (full.drop sixth).drop last

/-- Eleven of twelve: last not seated. -/
def eleven : Shape where
  belong := belonging
  present := belonging.take 11

/-- Seat the last (from eleven), then drop the sixth. The hole moved. -/
def seatedLast : Shape :=
  { eleven with present := eleven.present ++ [last] }

def moved : Shape :=
  seatedLast.drop sixth

/-- Drop a pairing the lock never owed. -/
def dropStranger : Shape :=
  full.drop stranger

/-- Owes nothing. Extras sitting. -/
def vacuousExtras : Shape :=
  ⟨[], belonging⟩

/-- Two holes, then restore only the sixth. Last still missing. -/
def restoreOne : Shape :=
  { dropSixthLast with present := dropSixthLast.present ++ [sixth] }

/-- One-cycle wholes for the join. -/
def oneSixth : Shape :=
  ⟨[sixth], [sixth]⟩

def oneLast : Shape :=
  ⟨[last], [last]⟩

def joined : Shape :=
  oneSixth.join oneLast

/-- Owes sixth and last. Only sixth is sitting. -/
def owesTwoHasSixth : Shape :=
  ⟨[sixth, last], [sixth]⟩

/-- Door 1. The lock is what is owed. Their equation system is not the object. -/
example : ¬ theirAlgebraicEquationSystemIsTheObject :=
  not_their_equation_system

example : full.lock = full.belong :=
  lock_is_what_is_owed full

/-- Door 2. Present is what sat. A sitting is not a hole. -/
example : ¬ furtherEquationsAreASecondTopology :=
  not_a_second_topology

example : ¬ full.Hole sixth :=
  present_is_not_a_hole full sixth (by decide)

example : (sixth ∈ full.belong ∧ sixth ∈ full.present) ↔ sixth ∈ full.seated :=
  how_much_of_the_lock_sat full sixth

/-- Door 3. Small lock (three pairings) is Whole and stays Whole. -/
example : smallLock.Small :=
  small_lock_is_small

example : smallLock.Whole :=
  small_lock_is_whole

example : smallLock.Small → smallLock.Whole → smallLock.Whole :=
  small_whole_stays_whole smallLock

/-- Door 4. Four pairings can be Whole or holed. Not a new object. Not unseated. -/
example : ¬ fourIsANewObject :=
  four_is_not_a_new_object

example : ¬ unsolvedMeansUnseated :=
  not_unsolved_as_unseated

example : fourWhole.Whole :=
  four_pairings_can_be_whole

example : ¬ fourHoled.Whole :=
  four_pairings_can_be_holed

example : fourHoled.Hole fourLast :=
  drop_is_hole fourWhole fourLast (by decide)

/-- Door 5. Join of two whole one-cycle shapes is Whole. -/
example : joined.Whole :=
  glued_wholes_are_whole oneSixth oneLast
    (present_eq_belong_whole oneSixth rfl)
    (present_eq_belong_whole oneLast rfl)

/-- Door 6. Extras the lock never owed are not holes. -/
example : ¬ extraIsTheHole :=
  refuse_extra_as_the_hole

example : ¬ noGeometricInterpretationIsTheHole :=
  refuse_extra_as_geometric_hole

example : dropStranger.Whole :=
  present_eq_belong_whole dropStranger (by decide)

example : ¬ dropStranger.Hole stranger :=
  extra_not_hole dropStranger stranger (by decide)

example : vacuousExtras.Whole :=
  vacuous_extras_whole belonging

/-- Door 7. Twelve pairings. Finite owed lock. Not their variety. -/
example : ¬ theirProjectiveVarietyIsTheObject :=
  not_their_variety

example : lockPairings.length = 12 :=
  twelve_pairings_stay

example : thisLock.Whole :=
  this_lock_is_whole

example : thisLock.belong.length = 12 :=
  this_lock_is_finite

/-- Door 8. Seeming-belonging is present or a Hole. Whole iff Hodge-named is algebraic-named. -/
example : ¬ cohomologyInstalled :=
  refuse_cohomology

example : AlgebraicNamed full sixth ∨ full.Hole sixth :=
  seeming_belonging_is_present_or_hole full sixth (by decide)

example : dropSixth.Hole sixth :=
  drop_is_hole full sixth (by decide)

example : full.Whole ↔ ∀ c, HodgeNamed full c → AlgebraicNamed full c :=
  whole_iff_hodge_named_algebraic full

example : joined.present = oneSixth.present ++ oneLast.present :=
  q_linear_combination_is_join oneSixth oneLast

/-- Door 9. A class-name that is not present is a Hole. Prestige class is not the object. -/
example : ¬ prestigeClassIsTheObject :=
  not_prestige_class

example : dropSixth.Hole sixth :=
  class_name_not_present_is_hole dropSixth sixth (by decide) (by decide)

/-- Door 10. Belong grows under join. A one-cycle whole raises the sitting count. -/
example : full.rank = full.seated.length :=
  rank_is_seated_count full

example : (full.join oneLast).belong.length = full.belong.length + 1 :=
  belong_grows_under_join full oneLast

example : (full.join oneLast).present.length = full.present.length + 1 :=
  join_one_cycle_raises_sitting full last

/-- Same owed pairings, present in a different order: still whole. -/
example : shuffled.Whole := by
  intro c hb
  exact List.mem_reverse.mpr hb

/-- Drop sixth: sixth is a hole AND first is still sitting. -/
example : dropSixth.Hole sixth ∧ ¬ dropSixth.Hole first := by
  refine ⟨drop_is_hole full sixth (by decide), ?_⟩
  intro h
  exact h.2 (by decide)

/-- Two drops: sixth is a hole. -/
example : dropSixthLast.Hole sixth := by
  constructor
  · decide
  · decide

/-- Two drops: last is a hole. -/
example : dropSixthLast.Hole last := by
  constructor
  · decide
  · decide

/-- Two drops: first is not a hole. -/
example : ¬ dropSixthLast.Hole first := by
  intro h
  exact h.2 (by decide)

/-- Unique hole after take-11: last is a hole. -/
example : eleven.Hole last := by
  constructor
  · decide
  · decide

/-- Unique hole after take-11: no other belonging cycle is a hole. -/
example : ∀ c, eleven.Hole c → c = last :=
  unique_belonging_hole eleven last (by decide)

/-- Seat the last, drop the sixth: last is sitting. -/
example : ¬ moved.Hole last := by
  intro h
  exact h.2 (by decide)

/-- Seat the last, drop the sixth: sixth is the hole. -/
example : moved.Hole sixth :=
  drop_is_hole seatedLast sixth (by decide)

/-- Restore only one of two holes: still not whole. -/
example : ¬ restoreOne.Whole := by
  intro hw
  have h : restoreOne.Hole last := by
    constructor
    · decide
    · decide
  exact h.2 (hw last h.1)

/-- Owes sixth and last, present has only sixth: last is the hole. -/
example : owesTwoHasSixth.Hole last := by
  constructor
  · decide
  · decide

/-- Owes sixth and last, present has only sixth: sixth is not a hole. -/
example : ¬ owesTwoHasSixth.Hole sixth := by
  intro h
  exact h.2 (by decide)

/-- Finite seating check. This is the run, not a second harness. -/
def seated (s : Shape) : Bool :=
  s.belong.all (fun c => s.present.contains c)

def hole (s : Shape) (c : Cycle) : Bool :=
  s.belong.contains c && !s.present.contains c

def run : IO Unit := do
  let put (n : Nat) (q : String) (b : Bool) : IO Unit :=
    IO.println s!"{n}. {q}  {b}"
  IO.println "hodge"
  put 1 "lock is belong — same list?" (decide (full.lock = full.belong))
  put 2 "sixth sitting on full — a hole?" (hole full sixth)
  put 3 "three-pairing lock — whole?" (seated smallLock)
  put 4 "three-pairing lock — small?" (decide (smallLock.belong.length < 4))
  put 5 "four-pairing lock — whole?" (seated fourWhole)
  put 6 "four-pairing lock, drop last — whole?" (seated fourHoled)
  put 7 "join of two one-cycle wholes — whole?" (seated joined)
  put 8 "drop stranger — still whole?" (seated dropStranger)
  put 9 "drop stranger — stranger is a hole?" (hole dropStranger stranger)
  put 10 "owes nothing, extras sitting — whole?" (seated vacuousExtras)
  put 11 "twelve pairings stay?" (decide (lockPairings.length = 12))
  put 12 "this lock — whole?" (seated thisLock)
  put 13 "drop sixth — sixth a hole (class-name missing)?" (hole dropSixth sixth)
  put 14 "join one-cycle to full — belong grew by one?"
    (decide ((full.join oneLast).belong.length = full.belong.length + 1))
  put 15 "join one-cycle to full — sitting grew by one?"
    (decide ((full.join oneLast).present.length = full.present.length + 1))
  put 16 "same pairings, reverse order — whole?" (seated shuffled)
  put 17 "drop sixth — sixth a hole and first sitting?"
    (hole dropSixth sixth && !hole dropSixth first)
  put 18 "take eleven — last is a hole?" (hole eleven last)
  put 19 "restore only sixth of two holes — whole?" (seated restoreOne)

#eval run
