import poincare.Proof
import poincare.FromMathlib

noncomputable section

open scoped Manifold ContDiff

/-
  Leftover is produced from M. Official words are leftover readings.
  No Bool clothes. No if-then-thisLock.
  Doughnut is the drop. Missing R. Circle is not a 3-pairing.
  Identity on Sphere3 computes. It is not the ∀-prize witness.
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

example : leftover sphere3M = lockPairings.map leftoverOf :=
  leftover_of_such sphere3M sphere3M_such

example : leftover sphere3M = sphere3M.seating.seated.map leftoverOf :=
  leftover_is_seated_R sphere3M

example : sphere3M.seatingSits :=
  seatingSits_of_such sphere3M sphere3M_such

/-- OfficialPoincare: leftover 6 pairs with cut 13. The pairing computes. -/
example : inverse thisLock.present ⟨6⟩ = some ⟨13⟩ ∧
    cl thisLock.present ⟨13⟩ = some ⟨6⟩ := by
  decide

example : sphere3M.Homeomorph :=
  OfficialPoincare_Homeomorph sphere3M sphere3M_such

example (M : CompactSimplyConnected3Manifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.Homeomorph M.seating :=
  OfficialPoincare M h α hα

example : ¬ OfficialPoincareOn dropSixth :=
  not_OfficialPoincareOn_drop

example : dropSixth.present.length = 11 :=
  drop_count_12_to_11.2

/-- Doughnut is the drop. Missing R. Not simply connected. Leftover stays. -/
example : doughnut.seating = thisLock.drop droppedR :=
  rfl

example : doughnutShape.Hole doughnutPairing ∧
    ¬ doughnut.simplyConnected ∧
    doughnut.compact ∧
    doughnut.dimension3 ∧
    ¬ SimplyConnectedSpace Doughnut ∧
    ¬ OfficialPoincareOn doughnutShape ∧
    ¬ doughnut.such :=
  doughnut_missing_R

/-- Circle is not a 3-pairing. Not a 3-manifold. -/
example : circleShape.Hole circlePairing ∧
    ¬ circle.dimension3 ∧
    ¬ circle.compact ∧
    ¬ SimplyConnectedSpace Circle ∧
    ¬ OfficialPoincareOn circleShape ∧
    ¬ circle.such :=
  circle_missing_R

example : ¬ doughnut.such ∧
    ¬ doughnut.simplyConnected ∧
    doughnut.compact ∧
    doughnut.dimension3 ∧
    ¬ doughnut.seatingSits ∧
    ¬ doughnut.Homeomorph ∧
    (leftover doughnut).length = 11 ∧
    ¬ OfficialPoincareOn doughnut.seating ∧
    ¬ SimplyConnectedSpace Doughnut :=
  doughnut_not_such_M

example : ¬ circle.such ∧
    ¬ circle.dimension3 ∧
    ¬ circle.seatingSits ∧
    ¬ circle.Homeomorph ∧
    leftover circle = [] ∧
    ¬ OfficialPoincareOn circle.seating ∧
    ¬ SimplyConnectedSpace Circle :=
  circle_not_such_M

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
    ¬ doughnut.simplyConnected ∧
    ¬ circle.dimension3 ∧
    ¬ doughnut.seatingSits ∧
    ¬ circle.seatingSits :=
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
  decide (¬ doughnut.simplyConnected) &&
  decide doughnut.compact &&
  decide doughnut.dimension3 &&
  decide (¬ OfficialPoincareOn doughnutShape) &&
  decide (¬ doughnut.such) &&
  decide (¬ doughnut.seatingSits) &&
  decide (¬ doughnut.Homeomorph) &&
  decide ((leftover doughnut).length = 11) &&
  decide (circleShape.Hole circlePairing) &&
  decide (¬ circle.dimension3) &&
  decide (¬ OfficialPoincareOn circleShape) &&
  decide (¬ circle.such) &&
  decide (¬ circle.seatingSits) &&
  decide (¬ circle.Homeomorph) &&
  decide (leftover circle = []) &&
  decide (thisLock.present.length = 12) &&
  decide (dropSixth.present.length = 11)

#eval run
