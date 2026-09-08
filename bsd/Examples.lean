import bsd.Proof

/-
  Hostile problems from the Birch and Swinnerton-Dyer seating.
  Score any door wrong and the example fails. Twelve pairings stay the lock.
-/

def full : Shape := thisLock

def sixth : Cycle := ⟨6, 13⟩
def holed : Shape := full.drop sixth

def halfBelong : List Cycle :=
  [ ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 5⟩, ⟨4, 7⟩, ⟨5, 11⟩, ⟨6, 13⟩ ]

def half : Shape where
  belong := halfBelong
  present := halfBelong

def empty : Shape where
  belong := []
  present := []

def otherBelong : List Cycle :=
  [ ⟨20, 21⟩, ⟨21, 22⟩ ]

def otherWhole : Shape where
  belong := otherBelong
  present := otherBelong

def otherDropped : Cycle := ⟨20, 21⟩
def otherHoled : Shape := otherWhole.drop otherDropped

/-- Door 1. Pairings on a lock, not their curve. -/
example : ¬ theirCubicCurveIsTheObject := id

example : ∀ c ∈ full.belong, c = ⟨c.left, c.right⟩ := by
  intro c _; rfl

/-- Door 2. Rank is owed cycles sitting. Score 12 on the holed lock and you lied. -/
example : full.rank = 12 := by native_decide
example : holed.rank = 11 := by native_decide

/-- Door 3. Experimental count is a reading of present pairings. -/
example : full.presentReading = 12 := by native_decide
example : holed.presentReading = 11 := by native_decide

/-- Door 4. Origin reading: order is owed holes. Score 0 on the holed lock and you lied. -/
example : full.order = 0 := by native_decide
example : holed.order = 1 := by native_decide

/-- Door 5. Origin hole ⇒ not Whole. Score the holed lock whole and you lied. -/
example : holed.Hole sixth :=
  drop_is_hole full sixth (by decide)

example : ¬ holed.Whole :=
  drop_not_whole full sixth (by decide)

example : sixth ∈ holed.holes := by native_decide

/-- Door 6. Origin not a hole ⇒ Whole, finite lock. -/
example : full.Whole :=
  present_eq_belong_whole full rfl

example : full.order = 0 ∧ full.rank = 12 := by native_decide

example : empty.Whole :=
  present_eq_belong_whole empty rfl

example : empty.rank = 0 ∧ empty.order = 0 := by native_decide

/-- Door 7. Two names for one belonging. -/
example : ¬ full.Hole sixth := by
  intro h
  exact h.2 (by decide)

example : holed.rank + holed.order = 12 := by native_decide

/-- Door 8. Their continuation and their equation: refuse. Install either and you lied. -/
example : ¬ analyticContinuationInstalled := id
example : ¬ functionalEquationInstalled := id
example : ¬ holomorphicContinuationInstalled := id
example : ¬ eulerProductInstalled := id

/-- Door 9. Their letters are not objects. Join of wholes is whole; ranks add. -/
example : ¬ leadingCoefficientIsTheObject := id
example : ¬ shaIsTheObject := id
example : ¬ regulatorIsTheObject := id
example : ¬ periodIsTheObject := id
example : ¬ tamagawaIsTheObject := id
example : ¬ torsionIsTheObject := id

example : half.Whole :=
  present_eq_belong_whole half rfl

example : (half.join half).Whole :=
  present_eq_belong_whole (half.join half) rfl

example : (half.join half).rank = 12 := by native_decide
example : (half.join half).rank = half.rank + half.rank := by native_decide

example : otherWhole.Whole :=
  present_eq_belong_whole otherWhole rfl

example : ¬ otherHoled.Whole :=
  drop_not_whole otherWhole otherDropped (by decide)

example : ¬ (full.join otherHoled).Whole :=
  drop_not_whole (full.join otherWhole) otherDropped (by native_decide)

/-- Door 10. The object is the Shape. Their group and their group law are not. -/
example : ¬ theirAbelianVarietyIsTheObject := id
example : ¬ theirRationalPointGroupIsTheObject := id
example : ¬ theirGroupLawInstalled := id

example : full.Whole ↔ ∀ c : Cycle, c ∈ full.belong → c ∈ full.present :=
  whole_iff_every_belonging_present full

/-- Door 11. No general method. This lock is seated. File a general solver and you lied. -/
example : ¬ generalMethodForEveryLock := id

example : present_eq_belong_whole full rfl = present_eq_belong_whole full rfl :=
  rfl

/-- Door 12. Twelve pairings stay the lock. Count eleven and you lied. -/
example : lockPairings.length = 12 := rfl
example : full.belong = lockPairings := rfl

/-- Origin meeting: complete is the dent, not the world. A missing origin seat is not closed. -/
example : originMeeting.Closed :=
  closed_of_dent_eq_lock originMeeting rfl (by decide)

example : workingShape originMeeting
    (closed_of_dent_eq_lock originMeeting rfl (by decide)) = Sphere.dent :=
  complete_meeting_is_the_sphere _ _

example : ¬ (workingShape originMeeting
    (closed_of_dent_eq_lock originMeeting rfl (by decide))).asWorld :=
  sphere_is_not_the_world _ _

example : ¬ originMissing.Closed :=
  missing_not_closed originMissing origin_missing_has_hole

example : ¬ originMissing.Whole :=
  missing_not_whole originMissing origin_missing_has_hole

/-- Wiles extras: their other rooms and their how stay off. Score any installed and you lied. -/
example : ¬ theirOtherRoomsInstalled := id
example : ¬ theirHowInstalled := id
example : ¬ theirSpecialValueElaborationsInstalled := id
example : ¬ theirFunctionFieldAnalogInstalled := id
example : ¬ theirHigherDimensionalHuntInstalled := id
example : ¬ theirSpecialFamilyTestInstalled := id
example : ¬ effectiveGeneratorMethodInstalled := id

def run : String :=
  if full.rank == 12 && full.order == 0 && holed.rank == 11 && holed.order == 1
      && lockPairings.length == 12 && (half.join half).rank == 12
  then "ok" else "fail"

#eval run
