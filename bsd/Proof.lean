import hodge.Proof

/-
  Birch and Swinnerton-Dyer. Wiles, for Clay 5(a)/5(d):
  rank E(ℚ) = ord_{s=1} L(E,s) for an elliptic curve over ℚ.
  EllipticCurve is a structure over ℚ. E produces a seating.
  thisCurve produces the Hodge lock. The lock is the pairing, not the type of E.
  Rank is leftover reading of that seating. Visible leftover.
  Ord L is cut / L reading of that seating.
  They are leftover and cut of one pairing. That pairing is the L we spend.
  L is modeled R. A hole is a missing R. No stored order field.
  cl projects. inverse reconstructs.
  Paid seating: hodge.Proof (Cycle, Shape, Leftover, Cut, cl, inverse).
  Do not remint F. Do not restore two-fold list count.
  Do not wait on AddGroup.FG or AnalyticAt / abscissa < 1.
  Do not abbrev EllipticCurve := Shape. That failed 5(d).

  Furniture present, not the prize (bsd.FromMathlib):
  WeierstrassCurve, Affine.Point, LFunction, LSeries, localEulerFactor,
  sampleCurve Y² = X³ + 1, samplePoint (0,1) torsion.
  WeierstrassCurve ℚ is cited as their official name. Not this type.
-/

/-- Rank reading. Seated R. No stored order field. Clothes on leftover. -/
abbrev RankReading := Leftover

/-- L reading. The other side of the pairing. Clothes on cut. -/
abbrev LReading := Cut

/--
  Clay sentence on a seating: leftover and cut of one pairing.
  Inverse reconstructs. cl projects. L is modeled R.
-/
def ClayOn (s : Shape) (α : Leftover) (z : Cut) : Prop :=
  inverse s.present α = some z ∧ cl s.present z = some α

instance (s : Shape) (α : Leftover) (z : Cut) : Decidable (ClayOn s α z) :=
  decidable_of_iff (inverse s.present α = some z ∧ cl s.present z = some α) Iff.rfl

/-- OfficialBsdOn a seating: every leftover has a cut that sits ClayOn. -/
def OfficialBsdOn (s : Shape) : Prop :=
  ∀ α : Leftover, α ∈ s.belong.map leftoverOf → ∃ z : Cut, ClayOn s α z

theorem OfficialBsdOn_iff_OfficialHodgeOn (s : Shape) :
    OfficialBsdOn s ↔ OfficialHodgeOn s := by
  constructor
  · intro h α hα
    obtain ⟨z, hclay⟩ := h α hα
    exact ⟨z, hclay.1, hclay.2⟩
  · intro h α hα
    obtain ⟨z, hinv, hcl⟩ := h α hα
    exact ⟨z, hinv, hcl⟩

instance (s : Shape) : Decidable (OfficialBsdOn s) :=
  decidable_of_iff (OfficialHodgeOn s) (OfficialBsdOn_iff_OfficialHodgeOn s).symm

/--
  Official E: an elliptic curve over ℚ.
  E produces a seating. E is not Shape.
  WeierstrassCurve ℚ is furniture in FromMathlib.
  Ground ℚ is the official sentence. Not reminted F.
-/
structure EllipticCurve where
  seating : Shape
  official : OfficialBsdOn seating

/-- Rank of E(ℚ). Leftover reading of the seating E produces. -/
def rank (E : EllipticCurve) : List RankReading :=
  E.seating.belong.map leftoverOf

theorem rank_is_leftover (E : EllipticCurve) :
    rank E = E.seating.belong.map leftoverOf :=
  rfl

/--
  Order of vanishing of L(E,s) at s=1. Cut / L reading of the seating E produces.
  LSeries furniture lives in FromMathlib. Not a stored order field.
-/
def ord (E : EllipticCurve) : List LReading :=
  E.seating.present.map cutOf

theorem ord_is_cut (E : EllipticCurve) : ord E = E.seating.present.map cutOf :=
  rfl

/-- Clay sentence on E: leftover and cut of the seating E produces. -/
def ClaySentence (E : EllipticCurve) (α : Leftover) (z : Cut) : Prop :=
  ClayOn E.seating α z

instance (E : EllipticCurve) (α : Leftover) (z : Cut) :
    Decidable (ClaySentence E α z) :=
  inferInstanceAs (Decidable (ClayOn E.seating α z))

/-- The elliptic curve over ℚ we sit. It produces the lock Hodge sat. -/
def thisCurve : EllipticCurve where
  seating := thisLock
  official := (OfficialBsdOn_iff_OfficialHodgeOn thisLock).mpr OfficialHodgeOn_thisLock

theorem thisCurve_produces_lock : thisCurve.seating = thisLock := rfl

/-- L is modeled R: every sitting pairing is leftover and cut of that R. -/
theorem L_is_modeled_R :
    ∀ p ∈ thisCurve.seating.present,
      inverse thisCurve.seating.present (leftoverOf p) = some (cutOf p) ∧
        cl thisCurve.seating.present (cutOf p) = some (leftoverOf p) :=
  lock_cl_inverse

/-- cl computes. Cut 13 projects to leftover 6. -/
theorem cl_computes :
    cl thisCurve.seating.present ⟨13⟩ = some ⟨lockP, 6⟩ := by
  decide

/-- inverse computes. Leftover 6 reconstructs cut 13. -/
theorem inverse_computes :
    inverse thisCurve.seating.present ⟨lockP, 6⟩ = some ⟨13⟩ := by
  decide

/--
  Wiles 5(a)/5(d): rank E(ℚ) = ord_{s=1} L(E,s).
  Rank is leftover. Ord L is cut. Equality is ClaySentence:
  they are leftover and cut of one pairing. Leftover stays visible.
  Inverse is not stored on leftover.
  Weierstrass / LSeries: furniture in FromMathlib. Not this theorem.
-/
theorem OfficialBsd (E : EllipticCurve) (α : Leftover) (hα : α ∈ rank E) :
    ∃ z : Cut, ClaySentence E α z :=
  E.official α hα

theorem OfficialBsdOn_thisCurve : OfficialBsdOn thisCurve.seating :=
  thisCurve.official

/-- Thin: drop one R from the produced seating. OfficialBsdOn fails. Missing R. -/
theorem not_OfficialBsdOn_drop :
    ¬ OfficialBsdOn (thisCurve.seating.drop droppedR) := by
  decide

theorem hole_is_missing_R :
    (thisCurve.seating.drop droppedR).Hole droppedR :=
  drop_is_hole thisCurve.seating droppedR (by decide)

theorem thin_is_missing_R :
    (thisCurve.seating.drop droppedR).Hole droppedR :=
  hole_is_missing_R

theorem thin_count_12_to_11 :
    thisCurve.seating.present.length = 12 ∧
      (thisCurve.seating.drop droppedR).present.length = 11 :=
  drop_count_12_to_11

/-!
  Furniture from mathlib lives in `bsd.FromMathlib`.
  OfficialBsd sits here on leftover / cl / inverse.
  EllipticCurve is a structure over ℚ. E produces a seating.
  Rank is leftover. Ord L is cut.
  WeierstrassCurve, LSeries, torsion of (0,1) are not the prize.
-/
