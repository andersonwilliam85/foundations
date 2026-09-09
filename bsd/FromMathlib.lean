/-
  Leftovers from mathlib as it sits (v4.33.1).
  WeierstrassCurve, Affine.Point, LFunction, LSeries, localEulerFactor.
  AddGroup.FG of Affine.Point does not sit.
  AnalyticAt of LSeries at 1 does not sit
  (LSeries.analyticOnNhd only for Re s > abscissaOfAbsConv).
  Do not sorry.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.NormNum

open WeierstrassCurve NumberField

/--
  A Weierstrass model. Quoted from `WeierstrassCurve`:
  `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆`.
  Over a field this is an elliptic curve when `IsElliptic` (unit discriminant).
-/
abbrev Curve (K : Type) :=
  WeierstrassCurve K

/--
  Nonsingular points in affine coordinates, with the point at infinity.
  Quoted from `WeierstrassCurve.Affine.Point`.
  Over a field this is an `AddCommGroup`.
  `AddGroup.FG` of this group over `ℚ` is not in mathlib.
-/
abbrev MordellWeil (K : Type) [Field K] (W : WeierstrassCurve K) :=
  W.toAffine.Point

/--
  Formal Dirichlet series of the curve over a number field.
  Quoted: `WeierstrassCurve.LFunction : ArithmeticFunction ℤ`.
  Euler product of the local factors `localEulerFactor`.
-/
noncomputable abbrev LFunction (K : Type) [Field K] [NumberField K]
    (W : WeierstrassCurve K) : ArithmeticFunction ℤ :=
  W.LFunction

/--
  The L-series as a function of `s`.
  Quoted: `WeierstrassCurve.LSeries`.
  The sum of the Dirichlet series if it exists, else `0`.
  Not an analytic continuation through `s = 1`.
-/
noncomputable abbrev Lseries (K : Type) [Field K] [NumberField K]
    (W : WeierstrassCurve K) : ℂ → ℂ :=
  W.LSeries

/--
  Rank of the point group as a `ℤ`-module.
  Quoted: `Module.rank`. A `Cardinal`.
  Finite generation is not assumed. This is not `AddGroup.rank`
  (minimum generators; that needs `AddGroup.FG`).
-/
noncomputable abbrev moduleRank (K : Type) [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) : Cardinal :=
  Module.rank ℤ W.toAffine.Point

/--
  Rank as a natural number.
  Quoted: `Module.finrank`. Junk `0` if the cardinal rank is infinite.
-/
noncomputable abbrev moduleFinrank (K : Type) [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) : ℕ :=
  Module.finrank ℤ W.toAffine.Point

/-- Local Euler factor of the curve at a discrete valuation ring. Quoted. -/
noncomputable abbrev localEulerFactor (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : ArithmeticFunction ℤ :=
  W.localEulerFactor R

/-- `Y² = X³ + 1` over `ℚ`. Discriminant `-432`, a unit. -/
def sampleCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 1

lemma sampleCurve_Δ : sampleCurve.Δ = -432 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, sampleCurve]
  norm_num

instance sampleCurve.instIsElliptic : sampleCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [sampleCurve_Δ]; norm_num)⟩

lemma sampleCurve_equation_zero_one : sampleCurve.toAffine.Equation (0 : ℚ) 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [sampleCurve]

lemma sampleCurve_nonsingular_zero_one : sampleCurve.toAffine.Nonsingular (0 : ℚ) 1 :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular (W := sampleCurve.toAffine)).mp
    sampleCurve_equation_zero_one

/-- A non-origin rational point on `Y² = X³ + 1`. -/
def samplePoint : sampleCurve.toAffine.Point :=
  .some 0 1 sampleCurve_nonsingular_zero_one

theorem samplePoint_ne_zero : samplePoint ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero sampleCurve_nonsingular_zero_one

/-- Origin of the point group. -/
example : (0 : MordellWeil ℚ sampleCurve) = WeierstrassCurve.Affine.Point.zero :=
  rfl

/-- The L-series of the sample curve. Furniture, not the prize. -/
noncomputable def thisLSeries : ℂ → ℂ :=
  sampleCurve.LSeries

theorem thisLSeries_eq : thisLSeries = sampleCurve.LSeries :=
  rfl

lemma sampleCurve_negY (x y : ℚ) : sampleCurve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, sampleCurve]

lemma samplePoint_Y_ne_negY : (1 : ℚ) ≠ sampleCurve.toAffine.negY 0 1 := by
  simp [WeierstrassCurve.Affine.negY, sampleCurve]
  norm_num

lemma sampleCurve_slope_double :
    sampleCurve.toAffine.slope 0 0 1 1 = 0 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl samplePoint_Y_ne_negY]
  simp [sampleCurve]

lemma sampleCurve_addX_double :
    sampleCurve.toAffine.addX 0 0 (sampleCurve.toAffine.slope 0 0 1 1) = 0 := by
  rw [sampleCurve_slope_double]
  simp [sampleCurve]

lemma sampleCurve_addY_double :
    sampleCurve.toAffine.addY 0 0 1 (sampleCurve.toAffine.slope 0 0 1 1) = -1 := by
  rw [sampleCurve_slope_double]
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, sampleCurve]

theorem two_nsmul_samplePoint : 2 • samplePoint = -samplePoint := by
  rw [two_nsmul]
  unfold samplePoint
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne samplePoint_Y_ne_negY,
    WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨sampleCurve_addX_double, sampleCurve_addY_double.trans (sampleCurve_negY 0 1).symm⟩

theorem three_nsmul_samplePoint : 3 • samplePoint = 0 := by
  rw [succ_nsmul, two_nsmul_samplePoint]
  exact neg_add_cancel samplePoint

/-
  Names that still do not sit:

  1. AddGroup.FG sampleCurve.toAffine.Point
     failed to synthesize. AddGroup.fg_of_descent needs a height
     and finite G/2G. Height/EllipticCurve does not define the
     naïve height.

  2. LSeries.abscissaOfAbsConv (Int.cast ∘ W.LFunction) < (1 : ℂ).re
     does not reduce. LSeries_analyticOnNhd therefore does not
     give AnalyticAt ℂ W.LSeries 1.

  Neighbors that exist and are not this:

  AddGroup.rank needs AddGroup.FG and counts generators, not the
  free rank of the point group.
  Height/EllipticCurve is a stub for naïve height; no descent.
  meromorphicOrderAt is the meromorphic cousin of analyticOrderAt.
  Module.finrank junks 0 if the cardinal is infinite.
  analyticOrderAt junks 0 if not AnalyticAt.
-/
