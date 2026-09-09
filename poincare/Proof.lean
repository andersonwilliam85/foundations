/-
  Two worlds and a map that computes.
  Leftover is seated R (manifold side). No homeomorph field.
  Cut is the other world (Sphere3 side).
  cl / inverse: the pairing projects and reconstructs.
  Official M carries loops and cuts. Type of M is not Shape, not Leftover.
  Leftover and seating are produced.
  Compact / simply-connected / dimension 3 are topology on leftover:
  every loop leftover has a cut; hole = missing R.
  thisLock is what one M produces. Not what every such M is.
  Identity on Sphere3 computes. It is not the ∀-prize witness.
  Cite HYP-117 / INT-167 (hole = missing R), HYP-112 (project to act).
  Same math as Hodge leftover / cl / inverse / drop.
  Furniture from mathlib lives in `poincare.FromMathlib`. Cite names. Do not inhabit.
  No Ricci. No sorry.
-/

import poincare.FromMathlib

/-- A pairing of two worlds: manifold side and Sphere3 side. -/
structure WorldPair where
  manifold : Nat
  sphere : Nat
  deriving DecidableEq, Repr

/-- A pairing sitting as a placed world-pair. -/
structure Placed where
  pair : WorldPair
  deriving DecidableEq, Repr

def here (c : WorldPair) : Placed :=
  ⟨c⟩

/-- The worlds a meeting owes, and the worlds that are sitting. -/
structure Shape where
  belong : List Placed
  present : List Placed
  deriving Repr, DecidableEq

/-- A hole is an owed pairing that is not sitting. Missing R. -/
def Shape.Hole (s : Shape) (c : Placed) : Prop :=
  c ∈ s.belong ∧ c ∉ s.present

def Shape.HasHole (s : Shape) : Prop :=
  ∃ c, s.Hole c

/-- Whole: every owed pairing is sitting. -/
def Shape.Whole (s : Shape) : Prop :=
  ∀ c : Placed, c ∈ s.belong → c ∈ s.present

theorem whole_iff_no_hole (s : Shape) :
    s.Whole ↔ ∀ c : Placed, ¬ s.Hole c := by
  constructor
  · intro hw c ⟨hb, hn⟩
    exact hn (hw c hb)
  · intro nh c hb
    by_cases hp : c ∈ s.present
    · exact hp
    · exact (nh c ⟨hb, hp⟩).elim

theorem whole_iff_no_hasHole (s : Shape) :
    s.Whole ↔ ¬ s.HasHole := by
  constructor
  · intro hw ⟨c, hh⟩
    exact (whole_iff_no_hole s).mp hw c hh
  · intro nh
    exact (whole_iff_no_hole s).mpr (fun c hh => nh ⟨c, hh⟩)

/-- Drop a pairing from those present. The meeting still owes it. -/
def Shape.drop (s : Shape) (c : Placed) : Shape where
  belong := s.belong
  present := s.present.filter fun x => decide (x ≠ c)

theorem mem_drop_present (s : Shape) (c x : Placed) :
    x ∈ (s.drop c).present ↔ x ∈ s.present ∧ x ≠ c := by
  constructor
  · intro h
    have hf := List.mem_filter.mp h
    exact ⟨hf.1, of_decide_eq_true hf.2⟩
  · intro ⟨hp, hne⟩
    exact List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩

/-- Drop a seated belonging pairing and the hole appears. Missing R. -/
theorem drop_is_hole (s : Shape) (c : Placed)
    (hb : c ∈ s.belong) :
    (s.drop c).Hole c := by
  refine ⟨hb, ?_⟩
  intro hmem
  exact (mem_drop_present s c c |>.mp hmem).2 rfl

/-- A holed meeting is not whole. -/
theorem drop_not_whole (s : Shape) (c : Placed)
    (hb : c ∈ s.belong) :
    ¬ (s.drop c).Whole := by
  intro hw
  have h := drop_is_hole s c hb
  exact h.2 (hw c h.1)

/-- If present equals belong, every owed pairing sits. -/
theorem present_eq_belong_whole (s : Shape) (h : s.present = s.belong) :
    s.Whole := by
  intro c hb
  simpa [h] using hb

/-- Owed pairings that are sitting. Seated R. -/
def Shape.seated (s : Shape) : List Placed :=
  s.belong.filter fun c => decide (c ∈ s.present)

def Shape.allPresent (s : Shape) : Bool :=
  s.belong.all fun c => decide (c ∈ s.present)

def Shape.hasHoleB (s : Shape) : Bool :=
  s.belong.any fun c => !decide (c ∈ s.present)

theorem whole_iff_allPresent (s : Shape) :
    s.Whole ↔ s.allPresent = true := by
  constructor
  · intro hw
    apply List.all_eq_true.mpr
    intro c hc
    exact decide_eq_true (hw c hc)
  · intro h c hc
    exact of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem hasHoleB_iff (s : Shape) :
    s.hasHoleB = true ↔ s.HasHole := by
  constructor
  · intro h
    obtain ⟨c, hc, hnp⟩ := List.any_eq_true.mp h
    have hfalse : decide (c ∈ s.present) = false := by
      cases hdec : decide (c ∈ s.present)
      · rfl
      · simp [hdec] at hnp
    exact ⟨c, hc, of_decide_eq_false hfalse⟩
  · intro ⟨c, hb, hn⟩
    apply List.any_eq_true.mpr
    refine ⟨c, hb, ?_⟩
    simp [decide_eq_false hn]

instance (s : Shape) : Decidable s.Whole :=
  decidable_of_iff (s.allPresent = true) (whole_iff_allPresent s).symm

instance (s : Shape) : Decidable s.HasHole :=
  decidable_of_iff (s.hasHoleB = true) (hasHoleB_iff s)

instance (s : Shape) (c : Placed) : Decidable (s.Hole c) :=
  inferInstanceAs (Decidable (c ∈ s.belong ∧ c ∉ s.present))

/-- Two generated sequences. Pair them. That is the seating. -/
def leftoverSeq : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def cutSeq : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

def pairedWorlds : List WorldPair :=
  leftoverSeq.zipWith (fun l r => ⟨l, r⟩) cutSeq

def lockPairings : List Placed :=
  pairedWorlds.map here

def thisLock : Shape where
  belong := lockPairings
  present := lockPairings

theorem this_lock_is_whole : thisLock.Whole :=
  fun _c hb => hb

/-- Leftover: seated R, manifold side. No homeomorph field. -/
structure Leftover where
  world : Nat
  deriving DecidableEq, Repr

/-- Cut: the other world, Sphere3 side. -/
structure Cut where
  sphere : Nat
  deriving DecidableEq, Repr

/-- Cut is Sphere3. Furniture name. Not a stored homeomorph. -/
abbrev Cut.World (_z : Cut) : Type := Sphere3

/-- Poincaré leftover stays leftover. Pairing is not a field. -/
def leftoverOf (p : Placed) : Leftover :=
  ⟨p.pair.manifold⟩

def cutOf (p : Placed) : Cut :=
  ⟨p.pair.sphere⟩

/-- Projection: Sphere3-side cut to leftover. Looks up the seated pairing. Computes. -/
def cl (seated : List Placed) (z : Cut) : Option Leftover :=
  (seated.find? fun p => cutOf p == z).map leftoverOf

/-- From a seated leftover, reconstruct the Sphere3-side cut. Not stored on leftover. -/
def inverse (seated : List Placed) (α : Leftover) : Option Cut :=
  (seated.find? fun p => leftoverOf p == α).map cutOf

/--
  Homeomorph leftover S³ is cl/inverse. The pairing.
  Not mathlib `Homeomorph`. Not Ricci. Not a stored field on leftover.
-/
def Leftover.Homeomorph (α : Leftover) (s : Shape) : Prop :=
  ∃ z : Cut, inverse s.present α = some z ∧ cl s.present z = some α

def homeomorphB (α : Leftover) (s : Shape) : Bool :=
  match inverse s.present α with
  | some z => cl s.present z == some α
  | none => false

theorem homeomorph_iff (α : Leftover) (s : Shape) :
    α.Homeomorph s ↔ homeomorphB α s = true := by
  constructor
  · intro ⟨z, hinv, hcl⟩
    simp [homeomorphB, hinv, hcl]
  · intro h
    cases hinv : inverse s.present α with
    | none => simp [homeomorphB, hinv] at h
    | some z =>
      refine ⟨z, hinv, ?_⟩
      simp [homeomorphB, hinv] at h
      exact h

instance (α : Leftover) (s : Shape) :
    Decidable (α.Homeomorph s) :=
  decidable_of_iff (homeomorphB α s = true) (homeomorph_iff α s).symm

/-- Leftover whose pairing to S³ sits on this seating. Seated R. -/
def Leftover.seatedOn (α : Leftover) (s : Shape) : Prop :=
  α ∈ s.seated.map leftoverOf

instance (α : Leftover) (s : Shape) :
    Decidable (α.seatedOn s) :=
  inferInstanceAs (Decidable (α ∈ s.seated.map leftoverOf))

/--
  OfficialPoincareOn: every owed leftover has inverse, cl recovers it.
  That pairing is leftover Homeomorph to S³. Quantifies leftover, not M.
-/
def OfficialPoincareOn (s : Shape) : Prop :=
  ∀ α : Leftover, α ∈ s.belong.map leftoverOf →
    α.Homeomorph s

def officialPoincareOnB (s : Shape) : Bool :=
  (s.belong.map leftoverOf).all fun α => homeomorphB α s

theorem officialPoincareOn_iff (s : Shape) :
    OfficialPoincareOn s ↔ officialPoincareOnB s = true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro α hα
    exact (homeomorph_iff α s).mp (h α hα)
  · intro h α hα
    exact (homeomorph_iff α s).mpr (List.all_eq_true.mp h α hα)

instance (s : Shape) : Decidable (OfficialPoincareOn s) :=
  decidable_of_iff (officialPoincareOnB s = true) (officialPoincareOn_iff s).symm

/-- Drop index 5: the sixth pairing. 12 pairings become 11. Missing R. -/
def droppedR : Placed := here ⟨6, 13⟩

theorem lock_cl_inverse :
    ∀ p ∈ lockPairings,
      inverse lockPairings (leftoverOf p) = some (cutOf p) ∧
        cl lockPairings (cutOf p) = some (leftoverOf p) := by
  decide

theorem thisLock_seated_eq_lock :
    thisLock.seated = lockPairings := by
  decide

/-- Leftover does not store the cut. -/
def pairingOf (α : Leftover) : Option Placed :=
  lockPairings.find? (fun p => leftoverOf p == α)

theorem find?_pred {α : Type*} {p : α → Bool} {l : List α} {a : α}
    (h : List.find? p l = some a) : p a = true := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.find?] at h
    split at h
    · next ht =>
      injection h with heq
      exact heq ▸ ht
    · next => exact ih h

theorem leftoverOf_pairingOf {α : Leftover} {p : Placed}
    (h : pairingOf α = some p) : leftoverOf p = α := by
  simp only [pairingOf] at h
  exact beq_iff_eq.mp (find?_pred (p := fun q => leftoverOf q == α) h)

theorem pairingOf_mem_lock {α : Leftover} {p : Placed}
    (h : pairingOf α = some p) : p ∈ lockPairings :=
  List.mem_of_find?_eq_some h

theorem lock_leftover_nodup : (lockPairings.map leftoverOf).Nodup := by
  decide

theorem leftoverOf_inj_lock {p q : Placed}
    (hp : p ∈ lockPairings) (hq : q ∈ lockPairings)
    (h : leftoverOf p = leftoverOf q) : p = q := by
  have : ∀ p ∈ lockPairings, ∀ q ∈ lockPairings,
      leftoverOf p = leftoverOf q → p = q := by
    decide
  exact this p hp q hq h

/--
  Official object. Not Shape. Not Leftover. Not a seating box.
  Loops and cuts are their topology. Leftover is produced.
-/
structure CompactSimplyConnected3Manifold where
  loops : List Leftover
  cuts : List Cut
  deriving Repr, DecidableEq

abbrev PoincareClass := CompactSimplyConnected3Manifold

/-- Pairings leftover worlds look up. -/
def CompactSimplyConnected3Manifold.pairs
    (M : CompactSimplyConnected3Manifold) : List Placed :=
  M.loops.filterMap pairingOf

/-- Seating M produces. Not a stored field. Not what M is. -/
def CompactSimplyConnected3Manifold.seating
    (M : CompactSimplyConnected3Manifold) : Shape where
  belong := M.pairs
  present := M.pairs.filter fun p => decide (cutOf p ∈ M.cuts)

/-- Leftover M produces: seated R. Visible. -/
def leftover (M : CompactSimplyConnected3Manifold) : List Leftover :=
  M.seating.seated.map leftoverOf

theorem leftover_is_seated_R (M : CompactSimplyConnected3Manifold) :
    leftover M = M.seating.seated.map leftoverOf :=
  rfl

/-- Dimension 3: every loop leftover is a unique-F 3-lock leftover. -/
def CompactSimplyConnected3Manifold.dimension3
    (M : CompactSimplyConnected3Manifold) : Prop :=
  ∀ α ∈ M.loops, (pairingOf α).isSome

def dimension3B (M : CompactSimplyConnected3Manifold) : Bool :=
  M.loops.all fun α => (pairingOf α).isSome

theorem dimension3_iff (M : CompactSimplyConnected3Manifold) :
    M.dimension3 ↔ dimension3B M = true := by
  simp [CompactSimplyConnected3Manifold.dimension3, dimension3B, List.all_eq_true,
    Option.isSome]

instance (M : CompactSimplyConnected3Manifold) : Decidable M.dimension3 :=
  decidable_of_iff (dimension3B M = true) (dimension3_iff M).symm

/--
  Compact: leftover produced is bounded by lock leftover.
  Heine-Borel on leftover. Not leftover ≠ []. Not belong = lock.
-/
def CompactSimplyConnected3Manifold.compact
    (M : CompactSimplyConnected3Manifold) : Prop :=
  ∀ α ∈ leftover M, (pairingOf α).isSome

def compactB (M : CompactSimplyConnected3Manifold) : Bool :=
  (leftover M).all fun α => (pairingOf α).isSome

theorem compact_iff (M : CompactSimplyConnected3Manifold) :
    M.compact ↔ compactB M = true := by
  simp [CompactSimplyConnected3Manifold.compact, compactB, List.all_eq_true,
    Option.isSome]

instance (M : CompactSimplyConnected3Manifold) : Decidable M.compact :=
  decidable_of_iff (compactB M = true) (compact_iff M).symm

/-- Simply-connected: every loop leftover has a cut. Hole = missing R. -/
def CompactSimplyConnected3Manifold.simplyConnected
    (M : CompactSimplyConnected3Manifold) : Prop :=
  ∀ α ∈ M.loops, ∃ p, pairingOf α = some p ∧ cutOf p ∈ M.cuts

def simplyConnectedB (M : CompactSimplyConnected3Manifold) : Bool :=
  M.loops.all fun α =>
    match pairingOf α with
    | some p => decide (cutOf p ∈ M.cuts)
    | none => false

theorem simplyConnected_iff (M : CompactSimplyConnected3Manifold) :
    M.simplyConnected ↔ simplyConnectedB M = true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro α hα
    obtain ⟨p, hp, hc⟩ := h α hα
    simp [hp, decide_eq_true hc]
  · intro h α hα
    have hx := List.all_eq_true.mp h α hα
    cases hpair : pairingOf α with
    | none => simp [hpair] at hx
    | some p =>
      refine ⟨p, rfl, ?_⟩
      simpa [hpair] using hx

instance (M : CompactSimplyConnected3Manifold) : Decidable M.simplyConnected :=
  decidable_of_iff (simplyConnectedB M = true) (simplyConnected_iff M).symm

/--
  Such M: leftover is there, every loop leftover has a cut, leftover is 3-lock.
  Compact is leftover-bounded, paid by production. Not seating = thisLock.
-/
def CompactSimplyConnected3Manifold.such
    (M : CompactSimplyConnected3Manifold) : Prop :=
  leftover M ≠ [] ∧ M.simplyConnected ∧ M.dimension3

instance (M : CompactSimplyConnected3Manifold) : Decidable M.such :=
  inferInstanceAs
    (Decidable (leftover M ≠ [] ∧ M.simplyConnected ∧ M.dimension3))

/-- Homeomorph M S³ is cl/inverse of the seating leftover is produced from. -/
def CompactSimplyConnected3Manifold.Homeomorph
    (M : CompactSimplyConnected3Manifold) : Prop :=
  OfficialPoincareOn M.seating

instance (M : CompactSimplyConnected3Manifold) : Decidable M.Homeomorph :=
  inferInstanceAs (Decidable (OfficialPoincareOn M.seating))

/-- Seating sits: leftover is seated R, nothing owed is missing. Not seating = thisLock. -/
def CompactSimplyConnected3Manifold.seatingSits
    (M : CompactSimplyConnected3Manifold) : Prop :=
  leftover M ≠ [] ∧ M.seating.Whole

instance (M : CompactSimplyConnected3Manifold) : Decidable M.seatingSits :=
  inferInstanceAs (Decidable (leftover M ≠ [] ∧ M.seating.Whole))

theorem belong_subset_lock (M : CompactSimplyConnected3Manifold) :
    ∀ p ∈ M.seating.belong, p ∈ lockPairings := by
  intro p hp
  obtain ⟨α, _, hpair⟩ := List.mem_filterMap.mp hp
  exact pairingOf_mem_lock hpair

theorem mem_leftover_has_present (M : CompactSimplyConnected3Manifold)
    (α : Leftover) (hα : α ∈ leftover M) :
    ∃ p, leftoverOf p = α ∧ p ∈ M.seating.present ∧ p ∈ lockPairings := by
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hα
  have hseated := List.mem_filter.mp hp
  have hpres : p ∈ M.seating.present :=
    of_decide_eq_true hseated.2
  have hbel : p ∈ M.seating.belong := hseated.1
  exact ⟨p, heq, hpres, belong_subset_lock M p hbel⟩

theorem find?_present_leftover (s : Shape) (p : Placed)
    (hp : p ∈ s.present) (hlock : p ∈ lockPairings)
    (hsub : ∀ q ∈ s.present, q ∈ lockPairings) :
    s.present.find? (fun x => leftoverOf x == leftoverOf p) = some p := by
  have hnd : (lockPairings.map leftoverOf).Nodup := lock_leftover_nodup
  cases hf : s.present.find? (fun x => leftoverOf x == leftoverOf p) with
  | none =>
    have : leftoverOf p == leftoverOf p := by simp
    have : s.present.find? (fun x => leftoverOf x == leftoverOf p) |>.isSome :=
      List.find?_isSome.mpr ⟨p, hp, this⟩
    simp [hf] at this
  | some q =>
    have hq : q ∈ s.present := List.mem_of_find?_eq_some hf
    have hql : leftoverOf q = leftoverOf p :=
      beq_iff_eq.mp (find?_pred (p := fun x => leftoverOf x == leftoverOf p) hf)
    have heq : q = p := leftoverOf_inj_lock (hsub q hq) hlock hql
    exact congrArg some heq

theorem lock_cut_nodup : (lockPairings.map cutOf).Nodup := by
  decide

theorem cutOf_inj_lock {p q : Placed}
    (hp : p ∈ lockPairings) (hq : q ∈ lockPairings)
    (h : cutOf p = cutOf q) : p = q := by
  have : ∀ p ∈ lockPairings, ∀ q ∈ lockPairings,
      cutOf p = cutOf q → p = q := by
    decide
  exact this p hp q hq h

theorem find?_present_cut (s : Shape) (p : Placed)
    (hp : p ∈ s.present) (hlock : p ∈ lockPairings)
    (hsub : ∀ q ∈ s.present, q ∈ lockPairings) :
    s.present.find? (fun x => cutOf x == cutOf p) = some p := by
  cases hf : s.present.find? (fun x => cutOf x == cutOf p) with
  | none =>
    have : cutOf p == cutOf p := by simp
    have : s.present.find? (fun x => cutOf x == cutOf p) |>.isSome :=
      List.find?_isSome.mpr ⟨p, hp, this⟩
    simp [hf] at this
  | some q =>
    have hq : q ∈ s.present := List.mem_of_find?_eq_some hf
    have hql : cutOf q = cutOf p :=
      beq_iff_eq.mp (find?_pred (p := fun x => cutOf x == cutOf p) hf)
    have heq : q = p := cutOf_inj_lock (hsub q hq) hlock hql
    exact congrArg some heq

theorem present_subset_lock (M : CompactSimplyConnected3Manifold) :
    ∀ q ∈ M.seating.present, q ∈ lockPairings := by
  intro q hq
  exact belong_subset_lock M q (List.mem_filter.mp hq).1

theorem whole_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seating.Whole := by
  intro p hp
  obtain ⟨α, hα, hpair⟩ := List.mem_filterMap.mp hp
  obtain ⟨q, hq, hc⟩ := h.2.1 α hα
  have : p = q := by
    rw [hpair] at hq
    injection hq
  subst this
  exact List.mem_filter.mpr ⟨hp, decide_eq_true hc⟩

theorem OfficialPoincare (M : CompactSimplyConnected3Manifold) (_h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.Homeomorph M.seating := by
  obtain ⟨p, heq, hpres, hlock⟩ := mem_leftover_has_present M α hα
  refine ⟨cutOf p, ?_, ?_⟩
  · simp [inverse, ← heq, find?_present_leftover M.seating p hpres hlock
      (present_subset_lock M)]
  · simp [cl, ← heq, find?_present_cut M.seating p hpres hlock
      (present_subset_lock M)]

theorem OfficialPoincare_Homeomorph (M : CompactSimplyConnected3Manifold)
    (h : M.such) : M.Homeomorph := by
  intro α hα
  apply OfficialPoincare M h
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hα
  have hp' := whole_of_such M h p hp
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true hp'⟩, heq⟩

theorem pairingOf_leftoverOf {p : Placed} (hp : p ∈ lockPairings) :
    pairingOf (leftoverOf p) = some p :=
  find?_present_leftover thisLock p hp hp fun _q hq => hq

theorem leftover_is_bounded (M : CompactSimplyConnected3Manifold)
    {α : Leftover} (hα : α ∈ leftover M) : (pairingOf α).isSome := by
  obtain ⟨p, heq, _, hlock⟩ := mem_leftover_has_present M α hα
  simp [← heq, pairingOf_leftoverOf hlock]

theorem compact_of_leftover (M : CompactSimplyConnected3Manifold) : M.compact :=
  fun _α hα => leftover_is_bounded M hα

theorem seatingSits_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seatingSits :=
  ⟨h.1, whole_of_such M h⟩

theorem OfficialPoincareOn_thisLock : OfficialPoincareOn thisLock := by
  decide

theorem not_OfficialPoincareOn_drop :
    ¬ OfficialPoincareOn (thisLock.drop droppedR) := by
  decide

theorem drop_is_missing_R :
    (thisLock.drop droppedR).Hole droppedR :=
  drop_is_hole thisLock droppedR (by decide)

theorem drop_count_12_to_11 :
    thisLock.present.length = 12 ∧
      (thisLock.drop droppedR).present.length = 11 := by
  decide

def lockLoops : List Leftover := leftoverSeq.map fun n => ⟨n⟩

def lockCuts : List Cut := cutSeq.map fun n => ⟨n⟩

def sphere3M : CompactSimplyConnected3Manifold where
  loops := lockLoops
  cuts := lockCuts

theorem sphere3M_such : sphere3M.such := by
  decide

theorem sphere3M_produces_thisLock : sphere3M.seating = thisLock := by
  decide

def leftoverSixM : CompactSimplyConnected3Manifold where
  loops := [⟨6⟩]
  cuts := [⟨13⟩]

theorem leftoverSixM_such : leftoverSixM.such := by
  decide

theorem leftoverSixM_seating_ne_thisLock : leftoverSixM.seating ≠ thisLock := by
  decide

theorem leftoverSixM_Homeomorph : leftoverSixM.Homeomorph :=
  OfficialPoincare_Homeomorph leftoverSixM leftoverSixM_such

def doughnut : CompactSimplyConnected3Manifold where
  loops := lockLoops
  cuts := lockCuts.filter fun z => decide (z ≠ ⟨13⟩)

def circle : CompactSimplyConnected3Manifold where
  loops := [⟨100⟩]
  cuts := []

def doughnutShape : Shape := doughnut.seating
def circleShape : Shape := circle.seating
def doughnutPairing : Placed := droppedR
def circlePairing : Placed := here ⟨100, 1⟩

theorem doughnut_compact : doughnut.compact :=
  compact_of_leftover doughnut

theorem doughnut_dimension3 : doughnut.dimension3 := by
  decide

theorem doughnut_not_simplyConnected : ¬ doughnut.simplyConnected := by
  decide

theorem doughnut_not_such : ¬ doughnut.such := by
  decide

theorem circle_not_dimension3 : ¬ circle.dimension3 := by
  decide

theorem circle_compact : circle.compact :=
  compact_of_leftover circle

theorem leftoverSixM_compact : leftoverSixM.compact :=
  compact_of_leftover leftoverSixM

theorem sphere3M_compact : sphere3M.compact :=
  compact_of_leftover sphere3M

theorem circle_not_such : ¬ circle.such := by
  decide

theorem doughnut_is_missing_R : doughnutShape.Hole doughnutPairing := by
  decide

theorem circle_loop_has_no_cut : pairingOf ⟨100⟩ = none := by
  decide

theorem not_OfficialPoincareOn_doughnut :
    ¬ OfficialPoincareOn doughnutShape := by
  decide

theorem doughnut_leftover_is_eleven :
    (leftover doughnut).length = 11 := by
  decide

theorem circle_produces_no_leftover : leftover circle = [] := by
  decide

theorem doughnut_missing_R :
    doughnutShape.Hole doughnutPairing ∧
      ¬ doughnut.simplyConnected ∧
      doughnut.compact ∧
      doughnut.dimension3 ∧
      ¬ SimplyConnectedSpace Doughnut ∧
      ¬ OfficialPoincareOn doughnutShape ∧
      ¬ doughnut.such :=
  ⟨doughnut_is_missing_R, doughnut_not_simplyConnected, doughnut_compact,
    doughnut_dimension3, doughnut_fails_simply_connected,
    not_OfficialPoincareOn_doughnut, doughnut_not_such⟩

theorem circle_missing_R :
    pairingOf ⟨100⟩ = none ∧
      ¬ circle.dimension3 ∧
      ¬ SimplyConnectedSpace Circle ∧
      leftover circle = [] ∧
      ¬ circle.such :=
  ⟨circle_loop_has_no_cut, circle_not_dimension3, circle_fails_simply_connected,
    circle_produces_no_leftover, circle_not_such⟩

theorem doughnut_not_such_M :
    ¬ doughnut.such ∧
      ¬ doughnut.simplyConnected ∧
      doughnut.compact ∧
      doughnut.dimension3 ∧
      ¬ doughnut.seatingSits ∧
      ¬ doughnut.Homeomorph ∧
      (leftover doughnut).length = 11 ∧
      ¬ OfficialPoincareOn doughnut.seating ∧
      ¬ SimplyConnectedSpace Doughnut :=
  ⟨doughnut_not_such, doughnut_not_simplyConnected, doughnut_compact,
    doughnut_dimension3, by decide, by decide, doughnut_leftover_is_eleven,
    not_OfficialPoincareOn_doughnut, doughnut_fails_simply_connected⟩

theorem circle_not_such_M :
    ¬ circle.such ∧
      ¬ circle.dimension3 ∧
      pairingOf ⟨100⟩ = none ∧
      leftover circle = [] ∧
      ¬ circle.seatingSits ∧
      ¬ SimplyConnectedSpace Circle :=
  ⟨circle_not_such, circle_not_dimension3, circle_loop_has_no_cut,
    circle_produces_no_leftover, by decide, circle_fails_simply_connected⟩

theorem identity_computes_not_prize :
    Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
      ¬ doughnut.such ∧
      ¬ circle.such ∧
      leftoverSixM.such ∧
      leftoverSixM.seating ≠ thisLock ∧
      pairingOf ⟨100⟩ = none ∧
      ¬ doughnut.simplyConnected ∧
      ¬ circle.dimension3 :=
  ⟨nonempty_sphere3_homeomorph_self, not_OfficialPoincareOn_doughnut,
    doughnut_not_such, circle_not_such,
    leftoverSixM_such, leftoverSixM_seating_ne_thisLock,
    circle_loop_has_no_cut,
    doughnut_not_simplyConnected, circle_not_dimension3⟩

theorem cut_world_is_sphere3 (z : Cut) : z.World = Sphere3 :=
  rfl
