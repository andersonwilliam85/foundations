/-
  Leftovers from mathlib as it sits (v4.33.1).
  Manifolds, the 3-sphere, simply connected, homeomorph.
  Quote the modules. Do not inhabit the prize.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples

noncomputable section

open Metric Module
open scoped Manifold

/--
  Unit sphere in Euclidean 4-space.
  Quoted from `Metric.sphere` and
  `Geometry.Manifold.Instances.Sphere`:
  `ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)`.
  For `n = 3` this is a 3-manifold. Compact by `Metric.sphere.compactSpace`
  (`ProperSpace` of a finite-dimensional real normed space).
-/
abbrev Sphere3 : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/--
  Unit sphere in Euclidean 3-space. Charted on `EuclideanSpace ℝ (Fin 2)`.
  A 2-manifold. Not a 3-manifold.
-/
abbrev Sphere2 : Type := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/--
  Unit sphere in Euclidean 2-space. Charted on `EuclideanSpace ℝ (Fin 1)`.
  Same model as `Circle`.
-/
abbrev Sphere1 : Type := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/--
  Euclidean 3-space as a charted space on itself
  (`ChartedSpace.chartedSpaceSelf`). Not compact.
-/
abbrev Euclidean3 : Type := EuclideanSpace ℝ (Fin 3)

/--
  Simply connected: fundamental groupoid equivalent to `Discrete Unit`.
  Quoted from `SimplyConnectedSpace`
  (`AlgebraicTopology.FundamentalGroupoid.SimplyConnected`).
-/
abbrev IsSimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop :=
  SimplyConnectedSpace X

/--
  Fundamental group at a basepoint.
  Quoted from `FundamentalGroup`
  (`AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`):
  `abbrev FundamentalGroup (x : X) := End (FundamentalGroupoid.mk x)`.
-/
abbrev Pi1 (X : Type*) [TopologicalSpace X] (x : X) :=
  FundamentalGroup X x

/-- Homeomorphism. Quoted from `Homeomorph`, notation `≃ₜ`. -/
abbrev Homeo (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  X ≃ₜ Y

/-- A homeomorphism is a homotopy equivalence. Quoted: `Homeomorph.toHomotopyEquiv`. -/
def homeomorph_toHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ContinuousMap.HomotopyEquiv X Y :=
  h.toHomotopyEquiv

/-- Simply connected transfers along a homeomorphism. -/
theorem simplyConnected_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [SimplyConnectedSpace Y] : SimplyConnectedSpace X :=
  e.toHomotopyEquiv.simplyConnectedSpace

theorem simplyConnected_iff_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : SimplyConnectedSpace X ↔ SimplyConnectedSpace Y :=
  e.toHomotopyEquiv.simplyConnectedSpace_iff

/-- Identity homeomorphism. Quoted: `Homeomorph.refl`. -/
def homeomorph_refl (X : Type*) [TopologicalSpace X] : X ≃ₜ X :=
  Homeomorph.refl X

/-- Inverse of a homeomorphism. Quoted: `Homeomorph.symm`. -/
def homeomorph_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Y ≃ₜ X :=
  h.symm

/-- Composition of homeomorphisms. Quoted: `Homeomorph.trans`. -/
def homeomorph_trans {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (h : X ≃ₜ Y) (g : Y ≃ₜ Z) : X ≃ₜ Z :=
  h.trans g

theorem one_lt_rank_euclideanSpace_four :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 :=
    finrank_euclideanSpace_fin
  have : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 4)) := inferInstance
  rw [← finrank_eq_rank', hfin]
  exact_mod_cast (by decide : (1 : ℕ) < 4)

/-- The 3-sphere is path-connected. Quoted: `isPathConnected_sphere` at rank `> 1`. -/
instance : PathConnectedSpace Sphere3 :=
  (isPathConnected_iff_pathConnectedSpace
      (F := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)).mp
    (isPathConnected_sphere one_lt_rank_euclideanSpace_four 0 (by norm_num : (0 : ℝ) ≤ 1))

open scoped unitInterval
open AddCircle

/--
  The loop that goes once around `AddCircle p`.
  At time 1 it is the period, which is `0` on the circle.
-/
def addCircle_once (p : ℝ) : Path (0 : AddCircle p) 0 where
  toFun t := (t.val * p : ℝ)
  source' := by simp
  target' := by
    change ((1 : ℝ) * p : AddCircle p) = 0
    simp [AddCircle.coe_period]

/-- The straight lift of that loop to `ℝ` ends at the period. -/
def addCircle_once_lift (p : ℝ) : C(I, ℝ) :=
  ⟨fun t => t.val * p, by fun_prop⟩

theorem addCircle_once_lift_zero (p : ℝ) : addCircle_once_lift p 0 = 0 := by
  simp [addCircle_once_lift]

theorem addCircle_once_lift_one (p : ℝ) : addCircle_once_lift p 1 = p := by
  simp [addCircle_once_lift]

theorem addCircle_once_lift_covers (p : ℝ) :
    ((↑) : ℝ → AddCircle p) ∘ addCircle_once_lift p = addCircle_once p := by
  funext t
  rfl

/--
  Covering `ℝ → AddCircle p` plus unique path lifting.
  The once-around loop is not null-homotopic: its lift ends at `p ≠ 0`.
-/
theorem not_simplyConnected_addCircle {p : ℝ} (hp : p ≠ 0) :
    ¬ SimplyConnectedSpace (AddCircle p) := by
  intro hsc
  let cov : IsCoveringMap ((↑) : ℝ → AddCircle p) := isCoveringMap_coe p
  let γ := addCircle_once p
  have hγ0 : (γ : C(I, AddCircle p)) 0 = ((↑) : ℝ → AddCircle p) 0 := by
    simp [γ, addCircle_once]
  have hlift :
      cov.liftPath (γ : C(I, AddCircle p)) 0 hγ0 = addCircle_once_lift p := by
    refine ((cov.eq_liftPath_iff' (γ := (γ : C(I, AddCircle p))) (e := (0 : ℝ))
        (γ_0 := hγ0)).mpr ?_).symm
    exact ⟨addCircle_once_lift_covers p, addCircle_once_lift_zero p⟩
  have hconst :
      cov.liftPath (Path.refl (0 : AddCircle p)).toContinuousMap 0
        (by simp [Path.refl]) =
        ContinuousMap.const I (0 : ℝ) :=
    cov.liftPath_const (x := (0 : AddCircle p)) (e := (0 : ℝ)) (by simp)
  have hhom : (γ : C(I, AddCircle p)).HomotopicRel
      (Path.refl (0 : AddCircle p)).toContinuousMap {0, 1} :=
    SimplyConnectedSpace.paths_homotopic γ (Path.refl 0)
  have hends :=
    cov.liftPath_apply_one_eq_of_homotopicRel hhom (0 : ℝ) hγ0
      (by simp [Path.refl])
  have : p = 0 := by
    calc
      p = addCircle_once_lift p 1 := (addCircle_once_lift_one p).symm
      _ = cov.liftPath (γ : C(I, AddCircle p)) 0 hγ0 1 := by rw [hlift]
      _ = cov.liftPath (Path.refl (0 : AddCircle p)).toContinuousMap 0
            (by simp [Path.refl]) 1 := hends
      _ = (0 : ℝ) := by rw [hconst]; rfl
  exact hp this

/-- The circle is not simply connected. Quoted covering + `homeomorphCircle'`. -/
theorem not_simplyConnected_circle : ¬ SimplyConnectedSpace Circle := by
  intro h
  let : SimplyConnectedSpace Circle := h
  exact not_simplyConnected_addCircle (by positivity)
    (homeomorphCircle').toHomotopyEquiv.simplyConnectedSpace

/-- A point of the 2-sphere. -/
def sphere2_pt : Sphere2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

/--
  A retract of a simply-connected space is simply connected.
  Used for the doughnut: the circle is a retract of `Circle × Sphere2`.
-/
theorem simplyConnected_of_retract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (i : X → Y) (r : Y → X)
    (hi : Continuous i) (hr : Continuous r) (hri : ∀ x, r (i x) = x) :
    SimplyConnectedSpace X := by
  have : PathConnectedSpace Y := inferInstance
  have : Nonempty X := (inferInstance : Nonempty Y).map r
  have : PathConnectedSpace X :=
    { nonempty := this
      joined := fun x y =>
        (hri x) ▸ (hri y) ▸ (PathConnectedSpace.joined (i x) (i y)).map hr }
  refine (simply_connected_iff_loops_nullhomotopic (Y := X)).mpr ⟨this, ?_⟩
  intro x γ
  have hY : Path.Homotopic (γ.map hi) (Path.refl (i x)) :=
    SimplyConnectedSpace.paths_homotopic (γ.map hi) (Path.refl (i x))
  have hX : Path.Homotopic ((γ.map hi).map hr) ((Path.refl (i x)).map hr) :=
    Path.Homotopic.map hY ⟨r, hr⟩
  have hX' : Path.Homotopic
      (((γ.map hi).map hr).cast (hri x).symm (hri x).symm)
      (((Path.refl (i x)).map hr).cast (hri x).symm (hri x).symm) :=
    Path.Homotopic.pathCast hX (hri x).symm (hri x).symm
  have heq : ((γ.map hi).map hr).cast (hri x).symm (hri x).symm = γ := by
    ext t
    simp [Path.cast, Path.map_coe, hri]
  have hrefl : ((Path.refl (i x)).map hr).cast (hri x).symm (hri x).symm = Path.refl x := by
    ext t
    simp [Path.cast, Path.map_coe, Path.refl]
    exact hri x
  exact heq ▸ hrefl ▸ hX'

/-- The doughnut `Circle × Sphere2` is a compact 3-manifold model. Not simply connected. -/
abbrev Doughnut : Type := Circle × Sphere2

theorem not_simplyConnected_doughnut : ¬ SimplyConnectedSpace Doughnut := by
  intro h
  let : SimplyConnectedSpace Doughnut := h
  have : SimplyConnectedSpace Circle :=
    simplyConnected_of_retract (fun x : Circle => (x, sphere2_pt)) Prod.fst
      (by fun_prop) continuous_fst (fun _ => rfl)
  exact not_simplyConnected_circle this

/--
  Sitting constructor: continuous inverses give a homeomorphism.
  This is `Homeomorph.mk`. It does not prove OfficialPoincareOn.
-/
def homeomorph_of_continuous_inverses {M : Type} [TopologicalSpace M]
    (send : M → Sphere3) (inv : Sphere3 → M)
    (hleft : Function.LeftInverse inv send)
    (hright : Function.RightInverse inv send)
    (hs : Continuous send) (hi : Continuous inv) : M ≃ₜ Sphere3 where
  toFun := send
  invFun := inv
  left_inv := hleft
  right_inv := hright
  continuous_toFun := hs
  continuous_invFun := hi

open scoped Manifold ContDiff

/-- The 3-sphere is Hausdorff. -/
instance : T2Space Sphere3 := inferInstance

/-- The 3-sphere is compact. -/
instance : CompactSpace Sphere3 := inferInstance

/-- The 3-sphere is charted on Euclidean 3-space. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Sphere3 := inferInstance

/-- The 3-sphere is an analytic 3-manifold. -/
instance : IsManifold (𝓡 3) ω Sphere3 := inferInstance

/-- The identity is a homeomorphism of the 3-sphere to itself. It computes. -/
def sphere3_homeomorph_self : Sphere3 ≃ₜ Sphere3 :=
  Homeomorph.refl Sphere3

theorem sphere3_homeomorph_self_left_inv (x : Sphere3) :
    sphere3_homeomorph_self.symm (sphere3_homeomorph_self x) = x :=
  Homeomorph.symm_apply_apply sphere3_homeomorph_self x

theorem sphere3_homeomorph_self_right_inv (y : Sphere3) :
    sphere3_homeomorph_self (sphere3_homeomorph_self.symm y) = y :=
  Homeomorph.apply_symm_apply sphere3_homeomorph_self y

theorem nonempty_sphere3_homeomorph_self : Nonempty (Sphere3 ≃ₜ Sphere3) :=
  ⟨sphere3_homeomorph_self⟩

/-- Euclidean 3-space is charted on itself. It is not compact. -/
instance : ChartedSpace Euclidean3 Euclidean3 := inferInstance

instance : T2Space Euclidean3 := inferInstance

instance : NoncompactSpace Euclidean3 := inferInstance

/-- The 2-sphere is charted on Euclidean 2-space. Not a 3-manifold. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Sphere2 := inferInstance

instance : CompactSpace Sphere2 := inferInstance

/-- The circle is charted on Euclidean 1-space. Not a 3-manifold. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := inferInstance

instance : CompactSpace Circle := inferInstance

/-- The doughnut is compact and Hausdorff. It is a 3-manifold on the product model. -/
instance : CompactSpace Doughnut := inferInstance

instance : T2Space Doughnut := inferInstance

instance : ChartedSpace
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 2))) Doughnut :=
  inferInstance

/--
  Thin miss: the doughnut is not simply connected.
  Missing R. OfficialPoincareOn fails on doughnutShape.
-/
theorem doughnut_fails_simply_connected : ¬ SimplyConnectedSpace Doughnut :=
  not_simplyConnected_doughnut

/-- The circle fails simply connected. Not a 3-manifold. Missing R. -/
theorem circle_fails_simply_connected : ¬ SimplyConnectedSpace Circle :=
  not_simplyConnected_circle
