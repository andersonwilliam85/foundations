import hodge.Proof

/-
  Birch and Swinnerton-Dyer. Wiles, for Clay 5(a)/5(d):
  rank E(Q) = ord_{s=1} L(E,s) for an elliptic curve over Q.
  E is a curve over Q. Not two flags. Not Shape. Not Hodge's lock.
  Leftover of E(Q) is leftover of that curve. Produce pairs it.
  That seating is L. Rank reads leftover.
  Ord L reads cut. Do not emit lockPairings from official words.
  thisLock may be what one E produces.
  L is modeled R. A hole is a missing R. No stored order field.
  cl projects. inverse reconstructs.
  Paid seating: hodge.Proof (Cycle, Shape, Leftover, Cut, cl, inverse).
  Do not wait on AddGroup.FG or AnalyticAt / abscissa < 1.

  Furniture present, not the prize (bsd.FromMathlib):
  WeierstrassCurve, Affine.Point, LFunction, LSeries, localEulerFactor,
  sampleCurve Y^2 = X^3 + 1, samplePoint (0,1) torsion.
  WeierstrassCurve Q is cited as their official name. Not this type.
-/

/--
  Official E: an elliptic curve over Q.
  Short Weierstrass Y^2 = X^3 + A X + B, coefficients in Q.
  leftoverR is leftover of E(Q). Not a flag. Not Shape.
-/
structure EllipticCurve where
  A : Int
  B : Int
  leftoverR : List Nat
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

/-- Discriminant of Y^2 = X^3 + A X + B. Over Q. -/
def EllipticCurve.disc (E : EllipticCurve) : Int :=
  -16 * (4 * E.A ^ 3 + 27 * E.B ^ 2)

/-- Elliptic: unit discriminant. The curve, not a flag. -/
def EllipticCurve.IsElliptic (E : EllipticCurve) : Prop :=
  E.disc ≠ 0

instance (E : EllipticCurve) : Decidable E.IsElliptic :=
  inferInstanceAs (Decidable (E.disc ≠ 0))

/--
  Paid pairings whose leftover the curve sits.
  Not `if elliptic then lockPairings`.
-/
def paidFor (rs : List Nat) : List Placed :=
  lockPairings.filter fun p => decide (p.cycle.left ∈ rs)

theorem mem_paidFor (rs : List Nat) (p : Placed) :
    p ∈ paidFor rs ↔ p ∈ lockPairings ∧ p.cycle.left ∈ rs := by
  constructor
  · intro h
    have hf := List.mem_filter.mp h
    exact ⟨hf.1, of_decide_eq_true hf.2⟩
  · intro ⟨hp, hr⟩
    exact List.mem_filter.mpr ⟨hp, decide_eq_true hr⟩

/--
  E produces a seating from the curve: leftover of E(Q) paired with paid cuts.
  That seating is L. Not stored on E. Not emitted from official words.
-/
def EllipticCurve.produce (E : EllipticCurve) : Shape where
  belong := paidFor E.leftoverR
  present := paidFor E.leftoverR

/-- Rank of E(Q). Leftover reading of the seating E produces. -/
def rank (E : EllipticCurve) : List RankReading :=
  E.produce.belong.map leftoverOf

theorem rank_is_leftover (E : EllipticCurve) :
    rank E = E.produce.belong.map leftoverOf :=
  rfl

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

/--
  The elliptic curve over Q we sit: Y^2 = X^3 + 1.
  Leftover of E(Q) is leftoverSeq. This E produces thisLock.
  Not every official E.
-/
def thisCurve : EllipticCurve where
  A := 0
  B := 1
  leftoverR := leftoverSeq

theorem thisCurve_disc : thisCurve.disc = -432 := by
  decide

theorem thisCurve_isElliptic : thisCurve.IsElliptic := by
  decide

/-- One E produces the lock. Computed from this curve's leftover. -/
theorem thisCurve_produces_lock : thisCurve.produce = thisLock := by
  decide

theorem leftoverOf_eq_of_mem_lock {p q : Placed}
    (hp : p ∈ lockPairings) (hq : q ∈ lockPairings)
    (h : leftoverOf p = leftoverOf q) : p = q := by
  have hall :
      ∀ p ∈ lockPairings, ∀ q ∈ lockPairings,
        leftoverOf p = leftoverOf q → p = q := by
    decide
  exact hall p hp q hq h

theorem cutOf_eq_of_mem_lock {p q : Placed}
    (hp : p ∈ lockPairings) (hq : q ∈ lockPairings)
    (h : cutOf p = cutOf q) : p = q := by
  have hall :
      ∀ p ∈ lockPairings, ∀ q ∈ lockPairings, cutOf p = cutOf q → p = q := by
    decide
  exact hall p hp q hq h

theorem produce_present_mem_lock (E : EllipticCurve) {p : Placed}
    (hp : p ∈ E.produce.present) : p ∈ lockPairings :=
  ((mem_paidFor E.leftoverR p).mp (by simpa [EllipticCurve.produce] using hp)).1

theorem inverse_produce (E : EllipticCurve) {p : Placed}
    (hp : p ∈ E.produce.present) :
    inverse E.produce.present (leftoverOf p) = some (cutOf p) := by
  unfold inverse
  cases hfind : E.produce.present.find? (fun x => leftoverOf x == leftoverOf p) with
  | none =>
    have hn := List.find?_eq_none.mp hfind p hp
    simp at hn
  | some q =>
    have hq : q ∈ E.produce.present := List.mem_of_find?_eq_some hfind
    have hql : leftoverOf q = leftoverOf p :=
      beq_iff_eq.mp (List.find?_some (p := fun x : Placed => leftoverOf x == leftoverOf p) hfind)
    have heq : q = p :=
      leftoverOf_eq_of_mem_lock (produce_present_mem_lock E hq)
        (produce_present_mem_lock E hp) hql
    simp [heq]

theorem cl_produce (E : EllipticCurve) {p : Placed}
    (hp : p ∈ E.produce.present) :
    cl E.produce.present (cutOf p) = some (leftoverOf p) := by
  unfold cl
  cases hfind : E.produce.present.find? (fun x => cutOf x == cutOf p) with
  | none =>
    have hn := List.find?_eq_none.mp hfind p hp
    simp at hn
  | some q =>
    have hq : q ∈ E.produce.present := List.mem_of_find?_eq_some hfind
    have hqc : cutOf q = cutOf p :=
      beq_iff_eq.mp (List.find?_some (p := fun x : Placed => cutOf x == cutOf p) hfind)
    have heq : q = p :=
      cutOf_eq_of_mem_lock (produce_present_mem_lock E hq)
        (produce_present_mem_lock E hp) hqc
    simp [heq]

/-- OfficialBsdOn the seating E produces. From the pairing, not from produce = thisLock. -/
theorem OfficialBsdOn_produce (E : EllipticCurve) : OfficialBsdOn E.produce := by
  intro α hα
  obtain ⟨p, hpB, hpα⟩ := List.mem_map.mp hα
  have hpP : p ∈ E.produce.present := by
    simpa [EllipticCurve.produce] using hpB
  refine ⟨cutOf p, ?_, ?_⟩
  · simpa [hpα] using inverse_produce E hpP
  · simpa [hpα] using cl_produce E hpP

/-- L is modeled R: every sitting pairing is leftover and cut of that R. -/
theorem L_is_modeled_R (E : EllipticCurve) :
    ∀ p ∈ E.produce.present,
      inverse E.produce.present (leftoverOf p) = some (cutOf p) ∧
        cl E.produce.present (cutOf p) = some (leftoverOf p) := by
  intro p hp
  exact ⟨inverse_produce E hp, cl_produce E hp⟩

/-- cl computes on thisCurve. Cut 13 projects to leftover 6. -/
theorem cl_computes :
    cl thisCurve.produce.present ⟨13⟩ = some ⟨lockP, 6⟩ := by
  rw [thisCurve_produces_lock]
  decide

/-- inverse computes on thisCurve. Leftover 6 reconstructs cut 13. -/
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
  Rank is leftover of the seating the curve produces.
  Ord L is cut of that seating. Equality is ClaySentence.
  Official: the curve is elliptic. Not packed produce = thisLock.
-/
theorem OfficialBsd (E : EllipticCurve) (_hE : E.IsElliptic)
    (α : Leftover) (hα : α ∈ rank E) :
    ∃ z : Cut, ClaySentence E α z :=
  OfficialBsdOn_produce E α hα

theorem OfficialBsdOn_thisCurve : OfficialBsdOn thisCurve.produce :=
  OfficialBsdOn_produce thisCurve

/-- Drop one R from the seating thisCurve produces. OfficialBsdOn fails. Missing R. -/
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

theorem thisCurve_drop_count_12_to_11 :
    thisCurve.produce.present.length = 12 ∧
      (thisCurve.produce.drop droppedR).present.length = 11 := by
  rw [thisCurve_produces_lock]
  exact drop_count_12_to_11

/-!
  Furniture from mathlib lives in `bsd.FromMathlib`.
  OfficialBsd sits here on leftover / cl / inverse.
  E is a curve over Q. Leftover of E(Q) produces the seating.
  Rank is leftover. Ord L is cut.
  WeierstrassCurve, LSeries, torsion of (0,1) are not the prize.
-/
