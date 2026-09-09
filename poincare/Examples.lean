import poincare.Proof
import poincare.FromMathlib

noncomputable section

open scoped Manifold ContDiff

/-
  Two worlds and a map that computes.
  OfficialPoincare is the Clay sentence as leftover Homeomorph.
  Official M is compact, simply-connected, dimension 3. Those
  words gate the sit. Type of M is not Leftover.
  M produces leftover and a seating. Leftover is seated R.
  Homeomorph M S³ is cl/inverse of that seating.
  seatingSits is leftover sitting. Not seating = thisLock.
  Doughnut and circle fail the gates. Missing R.
  Identity on Sphere3 computes. It is not the ∀-prize witness.
  Furniture: charts, doughnut fail, circle fail.
  `#eval run` is Bool.
-/

def sixth : Placed := here ⟨6, 13⟩
def first : Placed := here ⟨1, 2⟩
def last : Placed := here ⟨12, 37⟩
def stranger : Placed := here ⟨0, 0⟩

def full : Shape := thisLock
def dropSixth : Shape := full.drop sixth

/-- Drop sixth: owed-absent hole. Missing R. -/
example : dropSixth.Hole sixth ∧ ¬ dropSixth.Whole :=
  ⟨drop_is_hole full sixth (by decide), drop_not_whole full sixth (by decide)⟩

example (h : dropSixth.Whole) : False :=
  drop_not_whole full sixth (by decide) h

example : ¬ dropSixth.Hole first :=
  fun h => h.2 (by decide)

example : ¬ dropSixth.Hole stranger :=
  fun h => (by decide : stranger ∉ dropSixth.belong) h.1

example : OfficialPoincareOn thisLock :=
  OfficialPoincareOn_thisLock

example : sphere3M.such :=
  sphere3M_such

example : lockM.such :=
  lockM_such

example : leftover sphere3M = lockPairings.map leftoverOf :=
  leftover_of_such sphere3M sphere3M_such

example : sphere3M.seatingSits :=
  seatingSits_of_such sphere3M sphere3M_such

/-- OfficialPoincare: leftover 6 pairs with cut 13. The pairing computes. -/
example : inverse thisLock.present ⟨6⟩ = some ⟨13⟩ ∧
    cl thisLock.present ⟨13⟩ = some ⟨6⟩ := by
  decide

example : sphere3M.Homeomorph :=
  OfficialPoincare_Homeomorph sphere3M sphere3M_such

example (M : OfficialManifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.Homeomorph M.seating :=
  OfficialPoincare M h α hα

example : ¬ OfficialPoincareOn dropSixth :=
  not_OfficialPoincareOn_drop

example : dropSixth.present.length = 11 :=
  drop_count_12_to_11.2

/-- Doughnut: not such M. Not simply connected. Missing R. -/
example : doughnutShape.Hole doughnutPairing ∧
    ¬ SimplyConnectedSpace Doughnut ∧
    ¬ OfficialPoincareOn doughnutShape ∧
    ¬ doughnut.such :=
  doughnut_missing_R

/-- Circle: not such M. Not simply connected. Not a 3-manifold. Missing R. -/
example : circleShape.Hole circlePairing ∧
    ¬ SimplyConnectedSpace Circle ∧
    ¬ OfficialPoincareOn circleShape ∧
    ¬ circle.such :=
  circle_missing_R

/-- Doughnut fails because it is not simply connected. Not because seating = thisLock. -/
example : ¬ doughnut.such ∧
    doughnut.simplyConnected = false ∧
    ¬ doughnut.seatingSits ∧
    ¬ doughnut.Homeomorph ∧
    leftover doughnut = [] ∧
    ¬ OfficialPoincareOn doughnut.seating ∧
    ¬ SimplyConnectedSpace Doughnut :=
  ⟨doughnut_not_such, doughnut_fails_because_not_simply_connected.1,
    by decide, by decide, doughnut_produces_no_leftover,
    not_OfficialPoincareOn_doughnut, doughnut_fails_simply_connected⟩

/-- Circle fails because it is not such M. Not a 3-manifold. Not simply connected. -/
example : ¬ circle.such ∧
    circle.dimension ≠ 3 ∧
    ¬ circle.seatingSits ∧
    ¬ circle.Homeomorph ∧
    leftover circle = [] ∧
    ¬ OfficialPoincareOn circle.seating ∧
    ¬ SimplyConnectedSpace Circle :=
  ⟨circle_not_such, circle_fails_because_not_such_M.2,
    by decide, by decide, circle_produces_no_leftover,
    not_OfficialPoincareOn_circle, circle_fails_simply_connected⟩

/-- The 3-sphere is a closed 3-manifold: compact, Hausdorff, charted on ℝ³. -/
example : CompactSpace Sphere3 := inferInstance

example : T2Space Sphere3 := inferInstance

example : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Sphere3 := inferInstance

example : IsManifold (𝓡 3) ω Sphere3 := inferInstance

example : PathConnectedSpace Sphere3 := inferInstance

/-- The identity homeomorphism of the 3-sphere inverts both ways. It computes. -/
example : sphere3_homeomorph_self.symm ∘ sphere3_homeomorph_self = id := by
  funext x
  exact sphere3_homeomorph_self_left_inv x

example : sphere3_homeomorph_self ∘ sphere3_homeomorph_self.symm = id := by
  funext y
  exact sphere3_homeomorph_self_right_inv y

example : Nonempty (Sphere3 ≃ₜ Sphere3) :=
  nonempty_sphere3_homeomorph_self

/-- Identity on Sphere3 computes. It is not OfficialPoincare. Not ∀ such M. -/
example : Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
    ¬ OfficialPoincareOn circleShape ∧
    ¬ doughnut.such ∧
    ¬ circle.such ∧
    ¬ doughnut.seatingSits ∧
    ¬ circle.seatingSits ∧
    leftover doughnut = [] ∧
    leftover circle = [] :=
  identity_computes_not_prize

/-- Simply connected transfers along a homeomorphism. Furniture. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [SimplyConnectedSpace Y] : SimplyConnectedSpace X :=
  simplyConnected_of_homeomorph e

/-- Euclidean 3-space is a 3-manifold and is not compact. Not closed. -/
example : ChartedSpace Euclidean3 Euclidean3 := inferInstance

example : NoncompactSpace Euclidean3 := inferInstance

/-- The 2-sphere is a closed 2-manifold. Not a 3-manifold. -/
example : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Sphere2 := inferInstance

example : CompactSpace Sphere2 := inferInstance

/-- The circle is a closed 1-manifold. Not a 3-manifold. -/
example : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := inferInstance

example : CompactSpace Circle := inferInstance

/-- Thin miss: the doughnut fails simply connected. Missing R. -/
example : ¬ SimplyConnectedSpace Doughnut :=
  doughnut_fails_simply_connected

example : CompactSpace Doughnut := inferInstance

example : T2Space Doughnut := inferInstance

example : ¬ SimplyConnectedSpace Circle :=
  circle_fails_simply_connected

def run : Bool :=
  decide thisLock.Whole &&
  decide (¬ dropSixth.Whole) &&
  decide (dropSixth.Hole sixth) &&
  decide (OfficialPoincareOn thisLock) &&
  decide sphere3M.such &&
  decide sphere3M.seatingSits &&
  decide sphere3M.Homeomorph &&
  decide (¬ OfficialPoincareOn dropSixth) &&
  decide (doughnutShape.Hole doughnutPairing) &&
  decide (¬ OfficialPoincareOn doughnutShape) &&
  decide (¬ doughnut.such) &&
  decide (¬ doughnut.seatingSits) &&
  decide (¬ doughnut.Homeomorph) &&
  decide (leftover doughnut = []) &&
  decide (circleShape.Hole circlePairing) &&
  decide (¬ OfficialPoincareOn circleShape) &&
  decide (¬ circle.such) &&
  decide (¬ circle.seatingSits) &&
  decide (¬ circle.Homeomorph) &&
  decide (leftover circle = []) &&
  decide (thisLock.present.length = 12) &&
  decide (dropSixth.present.length = 11) &&
  decide (doughnut.simplyConnected = false) &&
  decide (circle.dimension ≠ 3)

#eval run
