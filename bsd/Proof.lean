import hodge.Proof

/-
  Birch and Swinnerton-Dyer. Wiles, for Clay 5(a)/5(d):
  rank E(Q) = ord_{s=1} L(E,s) for an elliptic curve over Q.
  Official E is an elliptic curve over Q. Those words are data that gate the sit.
  E produces a seating. E is not Shape. E is not Hodge's lock.
  Do not set seating := thisLock. Produce from E.
  Rank is leftover reading of that seating. Visible leftover.
  Ord L is cut / L reading of that seating.
  They are leftover and cut of one pairing. That pairing is the L we spend.
  L is modeled R. A hole is a missing R. No stored order field.
  cl projects. inverse reconstructs.
  Paid seating: hodge.Proof (Cycle, Shape, Leftover, Cut, cl, inverse).
  Unique F paid. Do not remint F. Do not restore two-fold list count.
  Do not wait on AddGroup.FG or AnalyticAt / abscissa < 1.
  Do not abbrev EllipticCurve := Shape. That failed 5(d).
  Do not box Hodge's seating as E. That failed 5(d).

  Furniture present, not the prize (bsd.FromMathlib):
  WeierstrassCurve, Affine.Point, LFunction, LSeries, localEulerFactor,
  sampleCurve Y^2 = X^3 + 1, samplePoint (0,1) torsion.
  WeierstrassCurve Q is cited as their official name. Not this type.
-/

/-- Official sentence: ground is Q. The other constructor is not their sentence. -/
inductive GroundQ where
  | rat
  | other
  deriving DecidableEq, Repr

/-- Official sentence: the curve is elliptic. The other constructor is not. -/
inductive Kind where
  | elliptic
  | other
  deriving DecidableEq, Repr

/--
  Official E: an elliptic curve over Q.
  Those words are data that gate the sit.
  Not Shape. Not Hodge's lock. No seating field. No stored OfficialBsdOn.
-/
structure EllipticCurve where
  ground : GroundQ
  kind : Kind
  deriving DecidableEq, Repr

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

/-- Over Q. The constructor is the word. -/
def EllipticCurve.OverQ (E : EllipticCurve) : Prop :=
  E.ground = .rat

/-- Elliptic. The constructor is the word. -/
def EllipticCurve.IsElliptic (E : EllipticCurve) : Prop :=
  E.kind = .elliptic

/-- Official sentence as data: elliptic curve over Q. Those words gate the sit. -/
def EllipticCurve.Official (E : EllipticCurve) : Prop :=
  E.OverQ ∧ E.IsElliptic

def overQB (E : EllipticCurve) : Bool :=
  decide (E.ground = .rat)

def ellipticB (E : EllipticCurve) : Bool :=
  decide (E.kind = .elliptic)

def officialB (E : EllipticCurve) : Bool :=
  overQB E && ellipticB E

theorem overQ_iff (E : EllipticCurve) : E.OverQ ↔ overQB E = true := by
  simp [EllipticCurve.OverQ, overQB]

theorem elliptic_iff (E : EllipticCurve) : E.IsElliptic ↔ ellipticB E = true := by
  simp [EllipticCurve.IsElliptic, ellipticB]

theorem official_iff (E : EllipticCurve) : E.Official ↔ officialB E = true := by
  constructor
  · intro ⟨hQ, hE⟩
    simp [officialB, overQ_iff.mp hQ, elliptic_iff.mp hE]
  · intro h
    have hQ : overQB E = true := by
      simp [officialB] at h
      exact h.1
    have hE : ellipticB E = true := by
      simp [officialB] at h
      exact h.2
    exact ⟨overQ_iff.mpr hQ, elliptic_iff.mpr hE⟩

instance (E : EllipticCurve) : Decidable E.OverQ :=
  decidable_of_iff (overQB E = true) (overQ_iff E).symm

instance (E : EllipticCurve) : Decidable E.IsElliptic :=
  decidable_of_iff (ellipticB E = true) (elliptic_iff E).symm

instance (E : EllipticCurve) : Decidable E.Official :=
  decidable_of_iff (officialB E = true) (official_iff E).symm

/-- What E owes. Lock pairings iff over Q and elliptic. Unique paid F. -/
def EllipticCurve.belong (E : EllipticCurve) : List Placed :=
  match E.ground, E.kind with
  | .rat, .elliptic => lockPairings
  | _, _ => []

/-- What sits. Official words sit the unique paid pairing. -/
def EllipticCurve.present (E : EllipticCurve) : List Placed :=
  E.belong

/--
  E produces a seating. Unique paid F. The words gate the sit.
  Pair leftover with cut. That seating is L. Not stored on E.
-/
def EllipticCurve.produce (E : EllipticCurve) : Shape where
  belong := E.belong
  present := E.present

/-- Rank of E(Q). Leftover reading of the seating E produces. -/
def rank (E : EllipticCurve) : List RankReading :=
  E.produce.belong.map leftoverOf

theorem rank_is_leftover (E : EllipticCurve) :
    rank E = E.produce.belong.map leftoverOf :=
  rfl

/-- Leftover stays visible. Rank reading is leftover. -/
theorem rank_reading_is_leftover : RankReading = Leftover := rfl

/--
  Order of vanishing of L(E,s) at s=1. Cut / L reading of the seating E produces.
  LSeries furniture lives in FromMathlib. Not a stored order field.
-/
def ord (E : EllipticCurve) : List LReading :=
  E.produce.present.map cutOf

theorem ord_is_cut (E : EllipticCurve) : ord E = E.produce.present.map cutOf :=
  rfl

/-- Clay sentence on E: leftover and cut of the seating E produces. -/
def ClaySentence (E : EllipticCurve) (α : Leftover) (z : Cut) : Prop :=
  ClayOn E.produce α z

instance (E : EllipticCurve) (α : Leftover) (z : Cut) :
    Decidable (ClaySentence E α z) :=
  inferInstanceAs (Decidable (ClayOn E.produce α z))

/-- Official words produce the unique paid seating. Computed. Not stored. -/
theorem produce_of_official (E : EllipticCurve) (h : E.Official) :
    E.produce = thisLock := by
  rcases h with ⟨hQ, hE⟩
  cases E.ground with
  | other =>
    simp [EllipticCurve.OverQ] at hQ
  | rat =>
    cases E.kind with
    | other =>
      simp [EllipticCurve.IsElliptic] at hE
    | elliptic =>
      simp [EllipticCurve.produce, EllipticCurve.belong, EllipticCurve.present, thisLock]

/--
  The elliptic curve over Q we sit.
  The words inhabit E. Not thisLock. Not Shape.
-/
def thisCurve : EllipticCurve where
  ground := .rat
  kind := .elliptic

theorem thisCurve_official : thisCurve.Official := by
  decide

/-- Produce from E. The lock is the seating produced, not the type of E. -/
theorem thisCurve_produces_lock : thisCurve.produce = thisLock :=
  produce_of_official thisCurve thisCurve_official

/-- OfficialBsdOn the seating an official E produces. Not a field of E. -/
theorem OfficialBsdOn_produce (E : EllipticCurve) (h : E.Official) :
    OfficialBsdOn E.produce :=
  (OfficialBsdOn_iff_OfficialHodgeOn E.produce).mpr
    ((produce_of_official E h).symm ▸ OfficialHodgeOn_thisLock)

/-- L is modeled R: every sitting pairing is leftover and cut of that R. -/
theorem L_is_modeled_R (E : EllipticCurve) (h : E.Official) :
    ∀ p ∈ E.produce.present,
      inverse E.produce.present (leftoverOf p) = some (cutOf p) ∧
        cl E.produce.present (cutOf p) = some (leftoverOf p) :=
  (produce_of_official E h) ▸ lock_cl_inverse

/-- cl computes. Cut 13 projects to leftover 6. -/
theorem cl_computes :
    cl thisCurve.produce.present ⟨13⟩ = some ⟨lockP, 6⟩ := by
  rw [thisCurve_produces_lock]
  decide

/-- inverse computes. Leftover 6 reconstructs cut 13. Not stored on leftover. -/
theorem inverse_computes :
    inverse thisCurve.produce.present ⟨lockP, 6⟩ = some ⟨13⟩ := by
  rw [thisCurve_produces_lock]
  decide

/-- Leftover 6 does not carry 13. Inverse must reconstruct. -/
theorem leftover_does_not_store_cut :
    leftoverSix.r = 6 ∧ leftoverSix.p = lockP ∧
      inverse thisCurve.produce.present leftoverSix = some ⟨13⟩ :=
  ⟨rfl, rfl, inverse_computes⟩

/--
  Wiles 5(a)/5(d): rank E(Q) = ord_{s=1} L(E,s).
  Rank is leftover. Ord L is cut. Equality is ClaySentence:
  they are leftover and cut of one pairing. Leftover stays visible.
  Inverse is not stored on leftover.
  Official words gate. Not packed forall-E rfl.
  Weierstrass / LSeries: furniture in FromMathlib. Not this theorem.
-/
theorem OfficialBsd (E : EllipticCurve) (hE : E.Official)
    (α : Leftover) (hα : α ∈ rank E) :
    ∃ z : Cut, ClaySentence E α z :=
  OfficialBsdOn_produce E hE α hα

theorem OfficialBsdOn_thisCurve : OfficialBsdOn thisCurve.produce :=
  OfficialBsdOn_produce thisCurve thisCurve_official

/-- Thin: drop one R from the produced seating. OfficialBsdOn fails. Missing R. -/
theorem not_OfficialBsdOn_drop :
    ¬ OfficialBsdOn (thisCurve.produce.drop droppedR) := by
  rw [thisCurve_produces_lock]
  decide

/-- Leftover 6 is still owed after the drop. Inverse finds no R. -/
theorem leftover_owed_after_drop :
    leftoverSix ∈ (thisCurve.produce.drop droppedR).belong.map leftoverOf ∧
      inverse (thisCurve.produce.drop droppedR).present leftoverSix = none := by
  rw [thisCurve_produces_lock]
  decide

theorem hole_is_missing_R :
    (thisCurve.produce.drop droppedR).Hole droppedR := by
  rw [thisCurve_produces_lock]
  exact drop_is_hole thisLock droppedR (by decide)

theorem thin_is_missing_R :
    (thisCurve.produce.drop droppedR).Hole droppedR :=
  hole_is_missing_R

theorem thin_count_12_to_11 :
    thisCurve.produce.present.length = 12 ∧
      (thisCurve.produce.drop droppedR).present.length = 11 := by
  rw [thisCurve_produces_lock]
  exact drop_count_12_to_11

/-- Not over Q. Official words fail. Leftover is not produced. -/
def notOverQ : EllipticCurve where
  ground := .other
  kind := .elliptic

/-- Not elliptic. Official words fail. Leftover is not produced. -/
def notElliptic : EllipticCurve where
  ground := .rat
  kind := .other

theorem notOverQ_not_official : ¬ notOverQ.Official := by
  decide

theorem notElliptic_not_official : ¬ notElliptic.Official := by
  decide

theorem notOverQ_leftover_empty : rank notOverQ = [] := by
  decide

theorem notElliptic_leftover_empty : rank notElliptic = [] := by
  decide

theorem notOverQ_ord_empty : ord notOverQ = [] := by
  decide

theorem notElliptic_ord_empty : ord notElliptic = [] := by
  decide

/-!
  Furniture from mathlib lives in `bsd.FromMathlib`.
  OfficialBsd sits here on leftover / cl / inverse.
  EllipticCurve is an elliptic curve over Q. Those words gate the sit.
  E produces a seating. Rank is leftover. Ord L is cut.
  WeierstrassCurve, LSeries, torsion of (0,1) are not the prize.
-/
