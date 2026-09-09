/-
  Sheaf of algebraic p-forms on Spec S, relative to R.
  mathlib v4.33.1 has no sheaf Ω^p on a Scheme.
  This is `tilde` of the S-module ⋀[S]^p (Ω[S⁄R]).
  Same cut as DeRhamComplex: affine module, then the sitting language.
  Not H^{p,q}. Not a subspace of H_dR.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

open AlgebraicGeometry CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

namespace KaehlerDifferential

/-- The S-module of algebraic `p`-forms. One `ℕ` degree. Not `(p,q)`. -/
noncomputable abbrev omegaPModule (p : ℕ) : ModuleCat (CommRingCat.of S) :=
  ModuleCat.of (CommRingCat.of S) (⋀[S]^p (Ω[S⁄R]))

/--
  Sheaf of algebraic `p`-forms on `Spec S`, relative to `R`.
  Quoted construction: `AlgebraicGeometry.tilde` of `⋀[S]^p (Ω[S⁄R])`.
  An object of `(Spec S).Modules`. Quasi-coherent.
  Not a sheaf on a general `Scheme`. Not `H^{p,q}`.
-/
noncomputable def OmegaPSheaf (p : ℕ) : (Spec (.of S)).Modules :=
  tilde (omegaPModule R S p)

/--
  Global sections of `Ω^p` on `Spec S`.
  `tilde.isoTop` identifies this with `⋀[S]^p (Ω[S⁄R])`.
  This is `H^0(Spec S, Ω^p)`, a module of forms. Not a subspace of `H_dR^p`.
-/
noncomputable def omegaPGlobal (p : ℕ) : ModuleCat (CommRingCat.of S) :=
  (modulesSpecToSheaf.obj (OmegaPSheaf R S p)).presheaf.obj (.op ⊤)

/-- Global sections of the affine sheaf recover the module of `p`-forms. -/
noncomputable def omegaPGlobalIso (p : ℕ) :
    omegaPModule R S p ≅ omegaPGlobal R S p :=
  tilde.isoTop (omegaPModule R S p)

end KaehlerDifferential
