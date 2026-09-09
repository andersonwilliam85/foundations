import poincare.Proof
import poincare.FromMathlib

noncomputable section

open scoped Manifold ContDiff

/-
  Two worlds and a map that computes.
  OfficialPoincare is the Clay sentence as pairing.
  CompactSimplyConnected3Manifold is a structure. It produces leftover
  and a seating. The type of M is not Leftover.
  Homeomorph M S³ is cl/inverse of that seating.
  OfficialPoincareOn sits on leftover / cl / inverse.
  Doughnut and circle: not such M. Missing R. OfficialPoincareOn fails.
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

example : lockM.seating = thisLock :=
  lockM_seating_is_thisLock

example : lockM.seatingSits := by
  decide

/-- OfficialPoincare: leftover 6 pairs with cut 13. The pairing computes. -/
example : inverse thisLock.present ⟨6⟩ = some ⟨13⟩ ∧
    cl thisLock.present ⟨13⟩ = some ⟨6⟩ := by
  decide

example : lockM.Homeomorph := by
  decide

example (M : CompactSimplyConnected3Manifold)
    (hSit : M.seatingSits) :
    M.Homeomorph :=
  OfficialPoincare M hSit

example : ¬ OfficialPoincareOn dropSixth :=
  not_OfficialPoincareOn_drop

example : dropSixth.present.length = 11 :=
  drop_count_12_to_11.2

/-- Doughnut: missing R. Pairing does not sit. OfficialPoincareOn fails. -/
example : doughnutShape.Hole doughnutPairing ∧
    ¬ SimplyConnectedSpace Doughnut ∧
    ¬ OfficialPoincareOn doughnutShape :=
  doughnut_missing_R

/-- Circle: missing R. OfficialPoincareOn fails. -/
example : circleShape.Hole circlePairing ∧
    ¬ SimplyConnectedSpace Circle ∧
    ¬ OfficialPoincareOn circleShape :=
  circle_missing_R

/-- Doughnut is not such an M. -/
example : ¬ doughnutM.seatingSits ∧
    ¬ doughnutM.Homeomorph ∧
    ¬ OfficialPoincareOn doughnutM.seating ∧
    ¬ SimplyConnectedSpace Doughnut :=
  doughnut_not_such_M

/-- Circle is not such an M. -/
example : ¬ circleM.seatingSits ∧
    ¬ circleM.Homeomorph ∧
    ¬ OfficialPoincareOn circleM.seating ∧
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
    ¬ doughnutM.seatingSits ∧
    ¬ circleM.seatingSits ∧
    ¬ doughnutLeftover.seatedOn thisLock ∧
    ¬ circleLeftover.seatedOn thisLock :=
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
  decide (lockM.seating = thisLock) &&
  decide lockM.seatingSits &&
  decide lockM.Homeomorph &&
  decide (¬ OfficialPoincareOn dropSixth) &&
  decide (doughnutShape.Hole doughnutPairing) &&
  decide (¬ OfficialPoincareOn doughnutShape) &&
  decide (¬ doughnutM.seatingSits) &&
  decide (¬ doughnutM.Homeomorph) &&
  decide (circleShape.Hole circlePairing) &&
  decide (¬ OfficialPoincareOn circleShape) &&
  decide (¬ circleM.seatingSits) &&
  decide (¬ circleM.Homeomorph) &&
  decide (thisLock.present.length = 12) &&
  decide (dropSixth.present.length = 11)

#eval run
