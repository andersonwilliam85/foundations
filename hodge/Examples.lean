import hodge.Proof

/-
  Shape seating plus leftover / cl / inverse.
  ProjectiveNonsingularVariety produces a seating. AlgebraicCycle is Cut.
  FromMathlib is furniture. OfficialHodge sits on Proof.
  `#eval run` is Bool.
-/

def sixth : Placed := here ⟨6, 13⟩
def first : Placed := here ⟨1, 2⟩
def last : Placed := here ⟨12, 37⟩
def stranger : Placed := here ⟨0, 0⟩

def full : Shape := thisLock
def dropSixth : Shape := full.drop sixth

def emptyWhole : Shape := ⟨[], []⟩
def oneLast : Shape := ⟨[last], [last]⟩
def oneSixth : Shape := ⟨[sixth], [sixth]⟩

def dressedHoled : Dressed :=
  { shape := dropSixth, costume := Costume.full }

def dressedWhole : Dressed :=
  { shape := thisLock, costume := Costume.none }

/-- Drop sixth: owed-absent hole. Not a third kind. -/
example : dropSixth.Hole sixth ∧ ¬ dropSixth.Whole :=
  ⟨drop_is_hole full sixth (by decide), drop_not_whole full sixth (by decide)⟩

example (h : dropSixth.Whole) : False :=
  drop_not_whole full sixth (by decide) h

/-- Join does not cancel a piece hole. -/
example : (full.join dropSixth).Hole (tagRight sixth) :=
  join_hole_of_right full dropSixth sixth (drop_is_hole full sixth (by decide))

example : (full.join dropSixth).HasHole :=
  join_hasHole_of_right full dropSixth ⟨sixth, drop_is_hole full sixth (by decide)⟩

example (h : ¬ (full.join dropSixth).HasHole) : False :=
  h (join_hasHole_of_right full dropSixth ⟨sixth, drop_is_hole full sixth (by decide)⟩)

example : (emptyWhole.join dropSixth).HasHole :=
  join_hasHole_of_right emptyWhole dropSixth ⟨sixth, drop_is_hole full sixth (by decide)⟩

example : ¬ (emptyWhole.join dropSixth).Whole := by
  intro hw
  exact (whole_iff_no_hasHole (emptyWhole.join dropSixth)).mp hw
    (join_hasHole_of_right emptyWhole dropSixth
      ⟨sixth, drop_is_hole full sixth (by decide)⟩)

example : (oneSixth.join oneLast).Whole :=
  join_whole_of_whole oneSixth oneLast
    (present_eq_belong_whole oneSixth rfl)
    (present_eq_belong_whole oneLast rfl)

example : ¬ dropSixth.Hole first :=
  fun h => h.2 (by decide)

example : ¬ dropSixth.Hole stranger :=
  fun h => (by decide : stranger ∉ dropSixth.belong) h.1

/-- Clothes on a hole: still holed. Clothes are not the prize. -/
example : dressedHoled.costume = Costume.full ∧
    dressedHoled.shape.Hole sixth ∧ ¬ dressedHoled.shape.Whole :=
  ⟨rfl, full_costume_still_holed full sixth (by decide)⟩

example : dressedWhole.costume = Costume.none ∧ dressedWhole.shape.Whole :=
  ⟨rfl, no_costume_still_whole⟩

example : ({ shape := thisLock, costume := Costume.full } : Dressed).shape.Whole :=
  this_lock_is_whole

example : ¬ ({ shape := dropSixth, costume := Costume.none } : Dressed).shape.Whole :=
  drop_not_whole full sixth (by decide)

example : leftoverSix.slot = (leftoverSix.p, leftoverSix.p) :=
  leftover_slot_is_pp leftoverSix

example : leftoverSix.slot = (lockP, lockP) :=
  rfl

example : thisVariety.produces = thisLock :=
  thisVariety_produces_lock

example : thisVariety.leftover = thisLock.belong.map leftoverOf :=
  rfl

example : algebraicCycleOf thisVariety = Cut :=
  algebraicCycleOf_is_cut thisVariety

example : AlgebraicCycle = Cut :=
  algebraicCycle_is_cut

example (α : HodgeClass) (hα : α ∈ thisVariety.leftover) :
    isSpanOfCl α thisVariety.produces.present :=
  OfficialHodge thisVariety α hα

example : OfficialHodgeOn thisVariety.produces :=
  OfficialHodgeOn_thisVariety

example : OfficialHodgeOn thisLock :=
  OfficialHodgeOn_thisLock

example : ¬ OfficialHodgeOn dropSixth :=
  not_OfficialHodgeOn_drop

example : ¬ OfficialHodgeOn (thisVariety.produces.drop sixth) :=
  not_OfficialHodgeOn_drop

example : leftoverSix ∈ dropSixth.belong.map leftoverOf ∧
    ¬ isSpanOfCl leftoverSix dropSixth.present :=
  leftover_six_not_span_after_drop

example : dropSixth.present.length = 11 :=
  drop_count_12_to_11.2

def run : Bool :=
  decide thisLock.Whole &&
  decide (¬ dropSixth.Whole) &&
  decide (dropSixth.Hole sixth) &&
  decide (full.join dropSixth).HasHole &&
  decide (¬ (emptyWhole.join dropSixth).Whole) &&
  decide (oneSixth.join oneLast).Whole &&
  decide dressedHoled.shape.HasHole &&
  decide dressedWhole.shape.Whole &&
  decide (leftoverSix.slot = (lockP, lockP)) &&
  decide (OfficialHodgeOn thisVariety.produces) &&
  decide (OfficialHodgeOn thisLock) &&
  decide (¬ OfficialHodgeOn dropSixth) &&
  decide (¬ OfficialHodgeOn (thisVariety.produces.drop sixth)) &&
  decide (¬ isSpanOfCl leftoverSix dropSixth.present) &&
  decide (thisLock.present.length = 12) &&
  decide (dropSixth.present.length = 11)

#eval run
