/-
  Leftovers from mathlib as it sits (v4.33.1) for the 3D incompressible
  Navier–Stokes problem. Survey, then constructors the pin does not name.
  The prize seating is leftover / cl / inverse in navierstokes.Proof.
  Clothes are lifespan and continuation.

  Present:
  * `EuclideanSpace` — `Mathlib.Analysis.InnerProductSpace.PiL2`
  * `ContDiff` — `Mathlib.Analysis.Calculus.ContDiff.Defs`
  * `gradient` / `∇` — `Mathlib.Analysis.Calculus.Gradient.Basic`
  * `laplacian` / `Δ` — `Mathlib.Analysis.InnerProductSpace.Laplacian`
  * `VectorField` — Lie bracket and pullback; no divergence
  * `SchwartzMap` / `𝓢(E, F)` — `Mathlib.Analysis.Distribution.SchwartzSpace.Basic`
  * `TemperedDistribution.MemSobolev` — Bessel potential / Sobolev
  * `extDeriv` — `Mathlib.Analysis.Calculus.DifferentialForm.Basic`
  * Divergence Theorem formula — `Mathlib.Analysis.BoxIntegral.DivergenceTheorem`

  Absent at this pin: any `Mathlib.Analysis.PDE` or Navier–Stokes module.
  Absent: a named `divergence`. Absent: Laplacian on `AddCircle`³ (the
  3-torus is not an inner-product vector space). Periodic seating is
  lattice-periodic maps on `Place`.

  Official smoothness is `ContDiff ℝ ∞` plus Schwartz decay.
  Sobolev is a weaker ambient. It is not the seating.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.Topology.Order.DenselyOrdered

open scoped Laplacian Gradient ContDiff SchwartzMap InnerProductSpace

noncomputable section

/--
  Place in ℝ³.
  Quoted from `EuclideanSpace`:
  `abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ := PiLp 2 fun _ : n => 𝕜`.
-/
abbrev Place : Type := EuclideanSpace ℝ (Fin 3)

/-- Time. -/
abbrev Time : Type := ℝ

/-- Place and time. Velocity and pressure sit here. -/
abbrev Instant : Type := Time × Place

/--
  Schwartz map `E → F`.
  Quoted from `SchwartzMap`:
  `structure SchwartzMap` with `toFun : E → F`, `smooth' : ContDiff ℝ ∞ toFun`,
  and `decay'` faster than any power of `‖x‖`.
  Notation `𝓢(E, F)`.
-/
abbrev Schwartz (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  𝓢(E, F)

/--
  Sobolev membership of a tempered distribution.
  Quoted from `TemperedDistribution.MemSobolev`:
  `def MemSobolev (s : ℝ) (p : ℝ≥0∞) ... (f : 𝓢'(E, F)) : Prop`.
  Bessel potential `(1 + ‖x‖ ^ 2) ^ (s / 2)`. Weaker than Schwartz.
-/
abbrev memSobolev {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (s : ℝ) (p : ENNReal) [Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  TemperedDistribution.MemSobolev s p f

/--
  Exterior derivative of a differential form on a normed space.
  Quoted from `extDeriv`:
  `noncomputable def extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E)`.
  Mathlib analysis, not a house complex.
-/
abbrev exteriorDeriv {𝕜 E F : Type*} {n : ℕ}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (form : E → E [⋀^Fin n]→L[𝕜] F) (x : E) :=
  extDeriv form x

/-- Spatial slice of a spacetime field. -/
def spatial (u : Instant → Place) (t : Time) : Place → Place :=
  fun x => u (t, x)

/-- Spatial slice of pressure. -/
def pressureSlice (p : Instant → ℝ) (t : Time) : Place → ℝ :=
  fun x => p (t, x)

/--
  ∂t of a spacetime velocity field.
  `deriv` from `Mathlib.Analysis.Calculus.Deriv.Basic`.
-/
def timeDeriv (u : Instant → Place) (t : Time) (x : Place) : Place :=
  deriv (fun τ : Time => u (τ, x)) t

/--
  ∇p at a place, fixed time.
  Quoted: `def gradient (f : F → 𝕜) (x : F) : F`, notation `∇`.
-/
def gradPressure (p : Instant → ℝ) (t : Time) (x : Place) : Place :=
  ∇ (pressureSlice p t) x

/--
  Δu at a place, fixed time.
  Quoted: `Laplacian.laplacian`, notation `Δ`,
  `instLaplacian` on `E → F` via the canonical covariant tensor.
-/
def viscousLap (u : Instant → Place) (t : Time) (x : Place) : Place :=
  Δ (spatial u t) x

/--
  (u · ∇)u. The Fréchet derivative of the spatial field applied to the
  velocity. No convective constructor in mathlib; built from `fderiv`.
-/
def convective (u : Place → Place) (x : Place) : Place :=
  fderiv ℝ u x (u x)

/-- Convective term of a spacetime field at an instant. -/
def convectiveAt (u : Instant → Place) (t : Time) (x : Place) : Place :=
  convective (spatial u t) x

/--
  ∇ · u.
  mathlib has no `divergence`. The Divergence Theorem writes the integrand
  as `∑ k, f' x eₖ k` (`Mathlib.Analysis.BoxIntegral.DivergenceTheorem`).
  This is that sum on `Place`.
-/
def divergence (u : Place → Place) (x : Place) : ℝ :=
  ∑ i : Fin 3,
    EuclideanSpace.proj i (fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)))

/-- Divergence of a spacetime field at an instant. -/
def divergenceAt (u : Instant → Place) (t : Time) (x : Place) : ℝ :=
  divergence (spatial u t) x

/--
  Spatial Schwartz decay at a fixed time.
  The slice equals a `SchwartzMap`.
-/
def SpatialSchwartz (u : Place → Place) : Prop :=
  ∃ φ : 𝓢(Place, Place), ∀ x, φ x = u x

/-- Spatial Schwartz decay of a scalar (pressure). -/
def SpatialSchwartzScalar (p : Place → ℝ) : Prop :=
  ∃ φ : 𝓢(Place, ℝ), ∀ x, φ x = p x

/--
  Lattice-periodic on ℝ³.
  `AddCircle` is S¹; the 3-torus is not an inner-product space, so Δ
  does not sit there. Periodicity is invariance under ℤ³ translations.
-/
def latticeShift (n : Fin 3 → ℤ) (x : Place) : Place :=
  x + ∑ i : Fin 3, (n i : ℝ) • EuclideanSpace.single i (1 : ℝ)

def SpatialPeriodic (u : Place → Place) : Prop :=
  ∀ (x : Place) (n : Fin 3 → ℤ), u (latticeShift n x) = u x

def SpatialPeriodicScalar (p : Place → ℝ) : Prop :=
  ∀ (x : Place) (n : Fin 3 → ℤ), p (latticeShift n x) = p x

/-- Left side: ∂t u + (u · ∇)u. -/
def nseLeft (u : Instant → Place) (t : Time) (x : Place) : Place :=
  timeDeriv u t x + convectiveAt u t x

/-- Right side: ν Δu − ∇p + f. -/
def nseRight (u : Instant → Place) (p : Instant → ℝ) (f : Instant → Place)
    (nu : ℝ) (t : Time) (x : Place) : Place :=
  nu • viscousLap u t x - gradPressure p t x + f (t, x)

theorem timeDeriv_const (c : Place) (t : Time) (x : Place) :
    timeDeriv (fun _ => c) t x = 0 := by
  simp [timeDeriv, deriv_const]

theorem convective_const (c : Place) (x : Place) :
    convective (fun _ => c) x = 0 := by
  simp [convective, fderiv_fun_const]

theorem divergence_const (c : Place) (x : Place) :
    divergence (fun _ => c) x = 0 := by
  simp [divergence, fderiv_fun_const]

theorem viscousLap_const (c : Place) (t : Time) (x : Place) :
    viscousLap (fun _ => c) t x = 0 := by
  simp [viscousLap]
  exact congrFun (InnerProductSpace.laplacian_const (c := c)) x

theorem gradPressure_const (c : ℝ) (t : Time) (x : Place) :
    gradPressure (fun _ => c) t x = 0 := by
  unfold gradPressure pressureSlice
  exact gradient_fun_const (F := Place) (𝕜 := ℝ) x c

/-- A nonzero constant does not decay. The zero field is Schwartz. -/
theorem spatialSchwartz_zero : SpatialSchwartz (fun _ => (0 : Place)) :=
  ⟨0, fun _ => rfl⟩

theorem spatialSchwartzScalar_zero : SpatialSchwartzScalar (fun _ => (0 : ℝ)) :=
  ⟨0, fun _ => rfl⟩

theorem spatialPeriodic_const (c : Place) : SpatialPeriodic (fun _ => c) := by
  intro x n
  rfl

theorem spatialPeriodicScalar_const (c : ℝ) : SpatialPeriodicScalar (fun _ => c) := by
  intro x n
  rfl

end
