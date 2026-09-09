import poincare.Proof
import poincare.FromMathlib

noncomputable section

open scoped Manifold ContDiff

/-
  Leftover is produced from M. thisLock is one production.
  leftoverSixM is such and is not thisLock.
  Doughnut is missing R. Circle is not a 3-pairing.
  `#eval run` is Bool.
-/

def sixth : Placed := here ⟨6, 13⟩
def first : Placed := here ⟨1, 2⟩
def last : Placed := here ⟨12, 37⟩
def stranger : Placed := here ⟨0, 0⟩

def full : Shape := thisLock
def dropSixth : Shape := full.drop sixth

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

example : sphere3M.seating = thisLock :=
  sphere3M_produces_thisLock

example : leftoverSixM.such :=
  leftoverSixM_such

example : leftoverSixM.seating ≠ thisLock :=
  leftoverSixM_seating_ne_thisLock

example : leftoverSixM.compact :=
  leftoverSixM_compact

example : sphere3M.compact :=
  sphere3M_compact

example : circle.compact :=
  circle_compact

example (M : CompactSimplyConnected3Manifold) : M.compact :=
  compact_of_leftover M

example : leftoverSixM.Homeomorph :=
  leftoverSixM_Homeomorph

example : leftover sphere3M = sphere3M.seating.seated.map leftoverOf :=
  leftover_is_seated_R sphere3M

example : sphere3M.seatingSits :=
  seatingSits_of_such sphere3M sphere3M_such

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

example : doughnutShape.Hole doughnutPairing ∧
    ¬ doughnut.simplyConnected ∧
    doughnut.compact ∧
    doughnut.dimension3 ∧
    ¬ SimplyConnectedSpace Doughnut ∧
    ¬ OfficialPoincareOn doughnutShape ∧
    ¬ doughnut.such :=
  doughnut_missing_R

example : pairingOf ⟨100⟩ = none ∧
    ¬ circle.dimension3 ∧
    ¬ SimplyConnectedSpace Circle ∧
    leftover circle = [] ∧
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
    pairingOf ⟨100⟩ = none ∧
    leftover circle = [] ∧
    ¬ circle.seatingSits ∧
    ¬ SimplyConnectedSpace Circle :=
  circle_not_such_M

example : CompactSpace Sphere3 := inferInstance

example : T2Space Sphere3 := inferInstance

example : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Sphere3 := inferInstance

example : IsManifold (𝓡 3) ω Sphere3 := inferInstance

example : PathConnectedSpace Sphere3 := inferInstance

example : sphere3_homeomorph_self.symm ∘ sphere3_homeomorph_self = id := by
  funext x
  exact sphere3_homeomorph_self_left_inv x

example : sphere3_homeomorph_self ∘ sphere3_homeomorph_self.symm = id := by
  funext y
  exact sphere3_homeomorph_self_right_inv y

example : Nonempty (Sphere3 ≃ₜ Sphere3) :=
  nonempty_sphere3_homeomorph_self

example : Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
    ¬ doughnut.such ∧
    ¬ circle.such ∧
    leftoverSixM.such ∧
    leftoverSixM.seating ≠ thisLock ∧
    pairingOf ⟨100⟩ = none ∧
    ¬ doughnut.simplyConnected ∧
    ¬ circle.dimension3 :=
  identity_computes_not_prize

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [SimplyConnectedSpace Y] : SimplyConnectedSpace X :=
  simplyConnected_of_homeomorph e

example : ChartedSpace Euclidean3 Euclidean3 := inferInstance

example : NoncompactSpace Euclidean3 := inferInstance

example : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Sphere2 := inferInstance

example : CompactSpace Sphere2 := inferInstance

example : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := inferInstance

example : CompactSpace Circle := inferInstance

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
  decide (sphere3M.seating = thisLock) &&
  decide leftoverSixM.such &&
  decide leftoverSixM.compact &&
  decide sphere3M.compact &&
  decide circle.compact &&
  decide (leftoverSixM.seating ≠ thisLock) &&
  decide leftoverSixM.Homeomorph &&
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
  decide (pairingOf ⟨100⟩ = none) &&
  decide (¬ circle.dimension3) &&
  decide (¬ circle.such) &&
  decide (¬ circle.seatingSits) &&
  decide (leftover circle = []) &&
  decide (thisLock.present.length = 12) &&
  decide (dropSixth.present.length = 11)

#eval run
