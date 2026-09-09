/-
  What sits from mathlib v4.33.1, plus the algebraic de Rham
  complex written in hodge.DeRham.
  Furniture. Not the prize.
  The prize is leftover / cl / inverse / drop in hodge.Proof.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Extension.Cotangent.Basic
import hodge.DeRham
import hodge.OmegaSheaf

open AlgebraicGeometry AlgebraicTopology CategoryTheory

universe u

/--
  ℓ-adic cohomology in degree `n`.
  Quoted from `Scheme.EllAdicCohomology`:
  `((sheafCompose _ AddCommGrpCat.uliftFunctor).obj <| X.ellAdicSheaf ℓ).H n`.
  Real `AddCommGroup`. No Hodge type on this group.
-/
abbrev ellAdicH (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] : Type (u + 1) :=
  X.EllAdicCohomology ℓ n

/--
  Singular homology of the Zariski space.
  `singularHomologyFunctor` is `C ⥤ TopCat ⥤ C`.
  The Scheme–TopCat bridge is `Scheme.forgetToTop` (Zariski carrier).
  This meets a scheme. It is not Betti homology of an analytification.
-/
noncomputable abbrev zariskiSingularHomology (X : Scheme.{0}) (n : ℕ) :=
  ((singularHomologyFunctor Ab n).obj (.of ℤ)).obj (Scheme.forgetToTop.obj X)

/--
  Kähler differentials of an affine.
  Quoted from `KaehlerDifferential`:
  `def KaehlerDifferential : Type v := (KaehlerDifferential.ideal R S).Cotangent`
  with `ideal` the kernel of `S ⊗[R] S →ₐ[R] S`.
  Notation `Ω[S⁄R]`. A module of differentials. Not `H^{p,q}`.
-/
abbrev kaehlerDiff (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :=
  Ω[S⁄R]

/--
  Universal derivation into `Ω[S⁄R]`.
  Quoted: `KaehlerDifferential.D : Derivation R S Ω[S⁄R]`.
  A derivation `S → Ω`. Not an exterior derivative on `⋀ Ω`.
-/
noncomputable abbrev kaehlerD (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :=
  KaehlerDifferential.D R S

/--
  Exterior algebra of `Ω[S⁄R]`.
  Quoted from `ExteriorAlgebra`:
  `abbrev ExteriorAlgebra := CliffordAlgebra (0 : QuadraticForm R M)`.
  An `S`-algebra. Not a `HomologicalComplex`. Not a bigraded split.
-/
abbrev exteriorKaehler (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :=
  ExteriorAlgebra S (Ω[S⁄R])

/--
  The `n`th exterior power of `Ω[S⁄R]`.
  Quoted: `abbrev exteriorPower := LinearMap.range (ι R) ^ n`,
  notation `⋀[R]^n M`.
  An `S`-submodule of `ExteriorAlgebra S Ω`. Degree is one `ℕ`, not `(p,q)`.
-/
noncomputable abbrev exteriorPowerKaehler (R S : Type*)
    [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :=
  ⋀[S]^n (Ω[S⁄R])

/--
  First homology of the naive cotangent complex.
  Quoted from `Algebra.Extension`:
  `protected def H1Cotangent := LinearMap.ker P.cotangentComplex`
  and `abbrev H1Cotangent := (Generators.self R S).toExtension.H1Cotangent`.
  The map is `I/I² → ⨁ᵢ S dxᵢ` (André–Quillen). Not de Rham. Not `(p,q)`.
-/
abbrev h1Cotangent (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :=
  Algebra.H1Cotangent R S

/--
  An algebraic cycle with rational coefficients.
  Quoted from `AlgebraicCycle`: `Function.locallyFinsupp X R`.
  `AddCommGroup` when `R = ℚ`. `SMul ℤ` sits. No `Module ℚ` instance
  on `locallyFinsupp`. Not a class in cohomology.
-/
abbrev rationalCycle (X : Scheme.{u}) :=
  AlgebraicCycle X ℚ

/-- Smooth is a morphism property. Quoted: Γ-maps of affines are smooth. -/
abbrev SmoothHom (X Y : Scheme.{u}) :=
  { f : X ⟶ Y // Smooth f }

/-- Proj of an ℕ-graded ring is a scheme. Quoted: `AlgebraicGeometry.«Proj»`. -/
noncomputable abbrev projScheme {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Scheme :=
  «Proj» 𝒜

/--
  Degree `2p` on the two real cohomology groups we have.
  Neither carries a `(p,p)` summand, so their intersection with `H^{p,p}`
  is not a type.
-/
noncomputable abbrev ellAdicH2p (X : Scheme.{u}) (ℓ p : ℕ) [Fact ℓ.Prime] : Type (u + 1) :=
  ellAdicH X ℓ (2 * p)

noncomputable abbrev zariskiH2p (X : Scheme.{0}) (p : ℕ) :=
  zariskiSingularHomology X (2 * p)

/--
  Algebraic de Rham complex of `S` over `R`.
  Written in `hodge.DeRham`. Terms `⋀[S]^n (Ω[S⁄R])`.
  `d` is the exterior derivative of `KaehlerDifferential.D`.
  `d ∘ d = 0` is proved. Not the zero map. Not ell-adic. Not Zariski.
-/
noncomputable abbrev deRhamComplex (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  KaehlerDifferential.DeRhamComplex R S

/-- Total algebraic de Rham cohomology. One `ℕ` degree. Not `(p,q)`. -/
noncomputable abbrev deRhamH (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :=
  KaehlerDifferential.deRhamCohomology R S n

/--
  Stupid truncation `σ≥p` of the de Rham complex.
  Hodge filtration on the complex.
-/
noncomputable abbrev deRhamHodgeFiltration
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) :=
  KaehlerDifferential.deRhamHodgeFiltration R S p

/--
  `F^p H_dR^n := im(H^n(σ≥p) → H_dR^n)`.
  A submodule of total `deRhamH n`. Not `H^{p,q}`.
-/
noncomputable abbrev deRhamHodgeFiltered
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p n : ℕ) :=
  KaehlerDifferential.deRhamHodgeFiltered R S p n

/--
  Sheaf of algebraic `p`-forms on `Spec S`.
  Quoted construction: `AlgebraicGeometry.tilde` of `⋀[S]^p (Ω[S⁄R])`.
  mathlib v4.33.1 has no sheaf `Ω^p` on a general `Scheme`.
  Not `H^{p,q}`. Not a subspace of `H_dR`.
-/
noncomputable abbrev omegaPSheaf
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) :=
  KaehlerDifferential.OmegaPSheaf R S p

/--
  Global sections of affine `Ω^p`. Identified with `⋀[S]^p (Ω[S⁄R])`
  by `tilde.isoTop`. `H^0(Spec S, Ω^p)`, not a subspace of `H_dR^p`.
-/
noncomputable abbrev omegaPGlobal
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : ℕ) :=
  KaehlerDifferential.omegaPGlobal R S p

/-- Associated graded `F^p / (F^p ∩ F^{p+1})`. Not `H^{p,q}`. -/
noncomputable abbrev deRhamHodgeAssociatedGraded
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p n : ℕ) :=
  KaehlerDifferential.deRhamHodgeAssociatedGraded R S p n

/-- Same-filtration meet `F^p ∩ F^q`. Not conjugate meet. Not `H^{p,p}`. -/
noncomputable abbrev deRhamHodgeFilteredInf
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p q n : ℕ) :=
  KaehlerDifferential.deRhamHodgeFilteredInf R S p q n

noncomputable instance : DecidableEq (Spec (.of ℚ)) :=
  Classical.decEq _

/-- Cycle of coefficient `1` at the unique point of `Spec ℚ`. Furniture. -/
noncomputable def unitCycle : AlgebraicCycle (Spec (.of ℚ)) ℚ :=
  Function.locallyFinsuppWithin.single default 1

/--
  Span of a set of vectors, as a submodule.
  Quoted from `Submodule.span`: smallest submodule containing `s`.
  Needs `[Module R M]`. `AlgebraicCycle X ℚ` is not a `Module ℚ`.
-/
abbrev moduleSpan (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Set M) : Submodule R M :=
  Submodule.span R s

/-- Finite sum of algebraic cycles. Quoted `locallyFinsuppWithin.coe_sum`. -/
example (X : Scheme.{u}) {ι : Type*} (s : Finset ι)
    (F : ι → AlgebraicCycle X ℚ) :
    ((∑ n ∈ s, F n : AlgebraicCycle X ℚ) : X → ℚ) = ∑ n ∈ s, (F n : X → ℚ) :=
  Function.locallyFinsuppWithin.coe_sum

/-- ℤ-scalar on an algebraic cycle. Quoted `locallyFinsuppWithin.coe_zsmul`. -/
example (X : Scheme.{u}) (Z : AlgebraicCycle X ℚ) (n : ℤ) :
    ((n • Z : AlgebraicCycle X ℚ) : X → ℚ) = n • (Z : X → ℚ) :=
  Function.locallyFinsuppWithin.coe_zsmul Z n

/-
  Furniture stays. The prize is leftover / cl / inverse in hodge.Proof.
  HodgeClass and cl sit there as leftover and lookup. Slot (p,p) is leftover.slot.
  ProjectiveNonsingularVariety is Ground + Embedding + Regularity there.
  Leftover is computed. AlgebraicCycle is Cut there.
  mathlib AlgebraicCycle X ℚ is furniture, not that Cut.
  H^{p,p} is not a type here. Cycle class of a variety is not a type here.
  Unique F is the filtration furniture already sitting. Do not remint.

  Homology is total H_dR^n with one ℕ degree.
  deRhamHodgeFiltration p sits as σ≥p on the complex.
  ιStupidTrunc and ιStupidTruncLE sit.
  deRhamHodgeAssociatedGraded p n is F^p / (F^p ∩ F^{p+1}).
  Affine Ω^p sits as tilde of ⋀[S]^p (Ω[S⁄R]) on Spec S.

  Names that do not sit:

  1. H^{p,q} as a summand of Betti or de Rham cohomology.

  2. Conjugate filtration.

  3. hodgeToDeRhamSpectralSequence_degenerates_at_E1 — sheafy
     hypercohomology RΓ(X, Ω^•) of a smooth proper scheme.
     Not in mathlib. Affine E_1 degeneracy would force d = 0.

  4. deRhamCohomology.star — a ℂ-antilinear involution on these
     groups. Without it, conjugate F^q does not form.

  5. Scheme.analytification / Scheme.bettiCohomology. Not in
     mathlib. Scheme.forgetToTop is Zariski.

  6. Scheme.OmegaP / Scheme.kahlerDifferentials — glue of affine
     tilde (⋀^p Ω) along X.affineCover into X.Modules.

  Neighbors that exist and are not this:

  Algebra.Extension.cotangentComplex / H1Cotangent is André–Quillen.
  BDeRham / BDeRhamPlus are Fontaine period rings.
-/
