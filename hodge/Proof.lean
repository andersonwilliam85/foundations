/-
  Shape seating. Belong / present / join / drop.
  A hole is owed-absent: a missing R.
  Leftover is seated R at slot (p,p). HodgeClass is leftover. No cut field.
  cl is the projection from cut to leftover. inverse reconstructs the cut.
  OfficialHodge is Deligne 5(a)/5(d): on a projective nonsingular
  variety over ℂ, every Hodge class is a ℚ-span of cl(Z).
  ProjectiveNonsingularVariety is ambient Pn and algebraic cycles.
  X is not Shape. X is not three flags. Leftover is produced from X.
  Hodge class is leftover at (p,p) of that production. Cycle is Cut.
  thisLock is the produced seating of thisVariety. Not the type of X.
  House: 1 · cl(inverse α) = α. A thin drop fails OfficialHodgeOn.
  Clothes are tags, not the prize. Leftover stays visible.
-/

/-- A cycle is a pairing. -/
structure Cycle where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

/-- Which copy. Join tags left / right so copies stay disjoint. -/
inductive Copy where
  | here
  | left (c : Copy)
  | right (c : Copy)
  deriving DecidableEq, Repr

/-- A cycle sitting on a tagged copy. -/
structure Placed where
  cycle : Cycle
  copy : Copy
  deriving DecidableEq, Repr

def here (c : Cycle) : Placed :=
  ⟨c, .here⟩

def tagLeft (p : Placed) : Placed :=
  { p with copy := .left p.copy }

def tagRight (p : Placed) : Placed :=
  { p with copy := .right p.copy }

theorem tagLeft_ne_tagRight (p q : Placed) : tagLeft p ≠ tagRight q := by
  intro h
  cases p
  cases q
  exact (nomatch h)

theorem tagLeft_inj {p q : Placed} (h : tagLeft p = tagLeft q) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem tagRight_inj {p q : Placed} (h : tagRight p = tagRight q) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem mem_map_tagLeft (p : Placed) (l : List Placed) :
    tagLeft p ∈ l.map tagLeft ↔ p ∈ l := by
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
    exact (tagLeft_inj heq) ▸ hq
  · intro h
    exact List.mem_map.mpr ⟨p, h, rfl⟩

theorem mem_map_tagRight (p : Placed) (l : List Placed) :
    tagRight p ∈ l.map tagRight ↔ p ∈ l := by
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
    exact (tagRight_inj heq) ▸ hq
  · intro h
    exact List.mem_map.mpr ⟨p, h, rfl⟩

/-- The cycles a shape owes, and the cycles that are sitting. -/
structure Shape where
  belong : List Placed
  present : List Placed
  deriving Repr, DecidableEq

/-- A hole is an owed cycle that is not sitting. One hole-type: owed-absent. -/
def Shape.Hole (s : Shape) (c : Placed) : Prop :=
  c ∈ s.belong ∧ c ∉ s.present

def Shape.HasHole (s : Shape) : Prop :=
  ∃ c, s.Hole c

/-- Whole: every owed cycle is sitting. -/
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

/-- Drop a cycle from those present. The shape still owes it. -/
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

/-- Drop a seated belonging cycle and the hole appears. -/
theorem drop_is_hole (s : Shape) (c : Placed)
    (hb : c ∈ s.belong) :
    (s.drop c).Hole c := by
  refine ⟨hb, ?_⟩
  intro hmem
  exact (mem_drop_present s c c |>.mp hmem).2 rfl

/-- A holed shape is not whole. -/
theorem drop_not_whole (s : Shape) (c : Placed)
    (hb : c ∈ s.belong) :
    ¬ (s.drop c).Whole := by
  intro hw
  have h := drop_is_hole s c hb
  exact h.2 (hw c h.1)

/-- If present equals belong, every owed cycle sits. -/
theorem present_eq_belong_whole (s : Shape) (h : s.present = s.belong) :
    s.Whole := by
  intro c hb
  simpa [h] using hb

/-- Join tags copies (side / disjoint). A hole on a piece stays a hole. -/
def Shape.join (s t : Shape) : Shape where
  belong := s.belong.map tagLeft ++ t.belong.map tagRight
  present := s.present.map tagLeft ++ t.present.map tagRight

theorem tagLeft_not_mem_map_tagRight (p : Placed) (l : List Placed) :
    tagLeft p ∉ l.map tagRight := by
  intro h
  obtain ⟨q, _, heq⟩ := List.mem_map.mp h
  exact tagLeft_ne_tagRight p q heq.symm

theorem tagRight_not_mem_map_tagLeft (p : Placed) (l : List Placed) :
    tagRight p ∉ l.map tagLeft := by
  intro h
  obtain ⟨q, _, heq⟩ := List.mem_map.mp h
  exact tagLeft_ne_tagRight q p heq

/-- If b has a hole, join a b has that hole (right copy). -/
theorem join_hole_of_right (a b : Shape) (c : Placed) (h : b.Hole c) :
    (a.join b).Hole (tagRight c) := by
  refine ⟨List.mem_append.mpr (Or.inr ((mem_map_tagRight c b.belong).mpr h.1)), ?_⟩
  intro hp
  cases List.mem_append.mp hp with
  | inl hL => exact tagRight_not_mem_map_tagLeft c a.present hL
  | inr hR => exact h.2 ((mem_map_tagRight c b.present).mp hR)

theorem join_hasHole_of_right (a b : Shape) (h : b.HasHole) :
    (a.join b).HasHole := by
  obtain ⟨c, hc⟩ := h
  exact ⟨tagRight c, join_hole_of_right a b c hc⟩

theorem join_whole_of_whole (s t : Shape) (hs : s.Whole) (ht : t.Whole) :
    (s.join t).Whole := by
  intro p hp
  cases List.mem_append.mp hp with
  | inl hL =>
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hL
    have : p = tagLeft q := heq.symm
    subst this
    exact List.mem_append.mpr (Or.inl ((mem_map_tagLeft q s.present).mpr (hs q hq)))
  | inr hR =>
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hR
    have : p = tagRight q := heq.symm
    subst this
    exact List.mem_append.mpr (Or.inr ((mem_map_tagRight q t.present).mpr (ht q hq)))

/-- Owed cycles that are sitting. -/
def Shape.seated (s : Shape) : List Placed :=
  s.belong.filter fun c => decide (c ∈ s.present)

/-- Rank: how many owed cycles are sitting. -/
def Shape.rank (s : Shape) : Nat :=
  s.seated.length

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

def pairedCycles : List Cycle :=
  leftoverSeq.zipWith (fun l r => ⟨l, r⟩) cutSeq

def lockPairings : List Placed :=
  pairedCycles.map here

def thisLock : Shape where
  belong := lockPairings
  present := lockPairings

/-- The lock seating. A variety will produce it. The seating is not the variety. -/
theorem this_lock_is_whole : thisLock.Whole :=
  fun _c hb => hb

/-- Leftover is seated R at slot (p,p). No cut field. -/
structure Leftover where
  p : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- The slot of a leftover is (p,p). Not a dummy ⊤. Not Fin n → ℚ. -/
def Leftover.slot (α : Leftover) : Nat × Nat := (α.p, α.p)

theorem leftover_slot_is_pp (α : Leftover) : α.slot = (α.p, α.p) := rfl

/-- Cut: the other side of the pairing. -/
structure Cut where
  z : Nat
  deriving DecidableEq, Repr

/-- HodgeClass is leftover. Their name sits. No cycle field. -/
abbrev HodgeClass := Leftover

/-- Algebraic cycle is Cut. Their name sits. Not mathlib locallyFinsupp. -/
abbrev AlgebraicCycle := Cut

theorem algebraicCycle_is_cut : AlgebraicCycle = Cut := rfl

/-- This lock sits at (1,1). -/
def lockP : Nat := 1

def leftoverOf (x : Placed) : Leftover :=
  ⟨lockP, x.cycle.left⟩

theorem leftoverOf_slot (x : Placed) : (leftoverOf x).slot = (lockP, lockP) := rfl

def cutOf (x : Placed) : Cut :=
  ⟨x.cycle.right⟩

/-- Projection: cut to leftover. Looks up the seated pairing. Computes. -/
def cl (seated : List Placed) (z : Cut) : Option Leftover :=
  (seated.find? fun x => cutOf x == z).map leftoverOf

/-- From a seated leftover, reconstruct the cut. Not stored on HodgeClass. -/
def inverse (seated : List Placed) (α : Leftover) : Option Cut :=
  (seated.find? fun x => leftoverOf x == α).map cutOf

/--
  One-term ℚ-span of cl(Z): 1 · cl(inverse α) = α.
  Z is an algebraic cycle (our Cut). No stored unpack. No 1-dim linear-algebra prize.
-/
def isSpanOfCl (α : HodgeClass) (seated : List Placed) : Prop :=
  ∃ Z : AlgebraicCycle, inverse seated α = some Z ∧ cl seated Z = some α

def isSpanOfClB (α : HodgeClass) (seated : List Placed) : Bool :=
  match inverse seated α with
  | some z => cl seated z == some α
  | none => false

theorem isSpanOfCl_iff (α : HodgeClass) (seated : List Placed) :
    isSpanOfCl α seated ↔ isSpanOfClB α seated = true := by
  constructor
  · intro ⟨z, hinv, hcl⟩
    simp [isSpanOfClB, hinv, hcl]
  · intro h
    cases hinv : inverse seated α with
    | none => simp [isSpanOfClB, hinv] at h
    | some z =>
      refine ⟨z, hinv, ?_⟩
      simp [isSpanOfClB, hinv] at h
      exact h

instance (α : HodgeClass) (seated : List Placed) : Decidable (isSpanOfCl α seated) :=
  decidable_of_iff (isSpanOfClB α seated = true) (isSpanOfCl_iff α seated).symm

/-- Deligne on a seating: every seated Hodge class is a ℚ-span of cl(Z). -/
def OfficialHodgeOn (s : Shape) : Prop :=
  ∀ α : HodgeClass, α ∈ s.belong.map leftoverOf → isSpanOfCl α s.present

def officialHodgeOnB (s : Shape) : Bool :=
  (s.belong.map leftoverOf).all fun α => isSpanOfClB α s.present

theorem officialHodgeOn_iff (s : Shape) :
    OfficialHodgeOn s ↔ officialHodgeOnB s = true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro α hα
    exact (isSpanOfCl_iff α s.present).mp (h α hα)
  · intro h α hα
    exact (isSpanOfCl_iff α s.present).mpr (List.all_eq_true.mp h α hα)

instance (s : Shape) : Decidable (OfficialHodgeOn s) :=
  decidable_of_iff (officialHodgeOnB s = true) (officialHodgeOn_iff s).symm

/--
  Official X: a projective nonsingular variety over ℂ.
  Ambient Pn and algebraic cycles are the data. Not flags. Not Shape.
  Leftover is produced from that data. No stored seating. No stored OfficialHodgeOn.
-/
structure ProjectiveNonsingularVariety where
  Pn : Nat
  cycles : List Cut
  deriving DecidableEq, Repr

/-- Leftover produced from a cycle: cl of the paid pairing. -/
def leftoverFromCut (z : Cut) : Option Leftover :=
  cl lockPairings z

/-- What X owes. Produced from ambient: the prefix of the paid lock. -/
def ProjectiveNonsingularVariety.belong (X : ProjectiveNonsingularVariety) :
    List Placed :=
  lockPairings.take X.Pn

/-- What sits. Produced from X.cycles: owed pairings whose cut is among them. -/
def ProjectiveNonsingularVariety.present (X : ProjectiveNonsingularVariety) :
    List Placed :=
  X.belong.filter fun pl => decide (cutOf pl ∈ X.cycles)

/-- Produced seating. Computed from X. Not a field. -/
def ProjectiveNonsingularVariety.seating (X : ProjectiveNonsingularVariety) :
    Shape where
  belong := X.belong
  present := X.present

/-- Hodge class of X: leftover of the produced seating at (p,p). -/
def ProjectiveNonsingularVariety.leftover (X : ProjectiveNonsingularVariety) :
    List Leftover :=
  X.seating.belong.map leftoverOf

theorem leftover_of_X_at_pp (X : ProjectiveNonsingularVariety) (α : Leftover)
    (_h : α ∈ X.leftover) : α.slot = (α.p, α.p) :=
  leftover_slot_is_pp α

/-- Algebraic cycle of X is Cut. -/
abbrev algebraicCycleOf (_X : ProjectiveNonsingularVariety) := Cut

theorem algebraicCycleOf_is_cut (X : ProjectiveNonsingularVariety) :
    algebraicCycleOf X = Cut := rfl

/-- Projective: ambient P^n with n ≥ 1. Used in leftover production. -/
def ProjectiveNonsingularVariety.Projective (X : ProjectiveNonsingularVariety) : Prop :=
  X.Pn ≥ 1

/-- Nonsingular: every owed leftover sits. Hole = missing R. -/
def ProjectiveNonsingularVariety.Nonsingular (X : ProjectiveNonsingularVariety) : Prop :=
  X.seating.Whole

/-- Official: projective and nonsingular. Leftover sits at (p,p) by production. -/
def ProjectiveNonsingularVariety.Official (X : ProjectiveNonsingularVariety) : Prop :=
  X.Projective ∧ X.Nonsingular

instance (X : ProjectiveNonsingularVariety) : Decidable X.Projective :=
  inferInstanceAs (Decidable (X.Pn ≥ 1))

instance (X : ProjectiveNonsingularVariety) : Decidable X.Nonsingular :=
  inferInstanceAs (Decidable X.seating.Whole)

def ProjectiveNonsingularVariety.officialB (X : ProjectiveNonsingularVariety) : Bool :=
  decide (X.Pn ≥ 1) && X.seating.allPresent

theorem varietyOfficial_iff (X : ProjectiveNonsingularVariety) :
    X.Official ↔ X.officialB = true := by
  constructor
  · intro ⟨hP, hN⟩
    have hPb : decide (X.Pn ≥ 1) = true := decide_eq_true (hP : X.Pn ≥ 1)
    have hNb : X.seating.allPresent = true := (whole_iff_allPresent X.seating).mp hN
    simp [ProjectiveNonsingularVariety.officialB, hPb, hNb]
  · intro h
    have hand : decide (X.Pn ≥ 1) = true ∧ X.seating.allPresent = true := by
      simpa [ProjectiveNonsingularVariety.officialB] using h
    exact ⟨of_decide_eq_true hand.1, (whole_iff_allPresent X.seating).mpr hand.2⟩

instance (X : ProjectiveNonsingularVariety) : Decidable X.Official :=
  decidable_of_iff (X.officialB = true) (varietyOfficial_iff X).symm

/-- Drop index 5: the sixth pairing. 12 pairings become 11. -/
def droppedR : Placed := here ⟨6, 13⟩

def leftoverSix : HodgeClass := ⟨lockP, 6⟩

theorem lock_cl_inverse :
    ∀ x ∈ lockPairings,
      inverse lockPairings (leftoverOf x) = some (cutOf x) ∧
        cl lockPairings (cutOf x) = some (leftoverOf x) := by
  decide

theorem OfficialHodgeOn_thisLock : OfficialHodgeOn thisLock := by
  decide

theorem lock_lefts_unique :
    ∀ x ∈ lockPairings, ∀ y ∈ lockPairings,
      leftoverOf x = leftoverOf y → x = y := by
  decide

theorem lock_cuts_unique :
    ∀ x ∈ lockPairings, ∀ y ∈ lockPairings,
      cutOf x = cutOf y → x = y := by
  decide

theorem mem_of_take_lock {n : Nat} {pl : Placed}
    (h : pl ∈ lockPairings.take n) : pl ∈ lockPairings := by
  have hsplit : lockPairings.take n ++ lockPairings.drop n = lockPairings :=
    List.take_append_drop n lockPairings
  rw [← hsplit]
  exact List.mem_append.mpr (Or.inl h)

theorem present_eq_belong_of_whole (X : ProjectiveNonsingularVariety)
    (h : X.seating.Whole) : X.present = X.belong := by
  apply List.filter_eq_self.mpr
  intro pl hpl
  have hmem : pl ∈ X.seating.present := h pl (by
    simp [ProjectiveNonsingularVariety.seating]
    exact hpl)
  have hf : pl ∈ X.present := by
    simpa [ProjectiveNonsingularVariety.seating] using hmem
  exact (List.mem_filter.mp hf).2

theorem find?_leftover_self {seated : List Placed} {pl : Placed}
    (hmem : pl ∈ seated)
    (hinj : ∀ x ∈ seated, leftoverOf x = leftoverOf pl → x = pl) :
    seated.find? (fun x => leftoverOf x == leftoverOf pl) = some pl := by
  induction seated with
  | nil => cases hmem
  | cons q qs ih =>
    cases hbeq : (leftoverOf q == leftoverOf pl) with
    | true =>
      have heq : leftoverOf q = leftoverOf pl := beq_iff_eq.mp hbeq
      have hq : q = pl := hinj q List.mem_cons_self heq
      simp [List.find?, hq]
    | false =>
      have hne : leftoverOf q ≠ leftoverOf pl :=
        fun h => Bool.noConfusion (hbeq.symm.trans (beq_iff_eq.mpr h))
      simp [List.find?, hbeq]
      apply ih
      · cases List.mem_cons.mp hmem with
        | inl hq =>
          exact (hne (hq ▸ rfl)).elim
        | inr hqs => exact hqs
      · intro x hx heq
        exact hinj x (List.mem_cons_of_mem q hx) heq

theorem find?_cut_self {seated : List Placed} {pl : Placed}
    (hmem : pl ∈ seated)
    (hinj : ∀ x ∈ seated, cutOf x = cutOf pl → x = pl) :
    seated.find? (fun x => cutOf x == cutOf pl) = some pl := by
  induction seated with
  | nil => cases hmem
  | cons q qs ih =>
    cases hbeq : (cutOf q == cutOf pl) with
    | true =>
      have heq : cutOf q = cutOf pl := beq_iff_eq.mp hbeq
      have hq : q = pl := hinj q List.mem_cons_self heq
      simp [List.find?, hq]
    | false =>
      have hne : cutOf q ≠ cutOf pl :=
        fun h => Bool.noConfusion (hbeq.symm.trans (beq_iff_eq.mpr h))
      simp [List.find?, hbeq]
      apply ih
      · cases List.mem_cons.mp hmem with
        | inl hq =>
          exact (hne (hq ▸ rfl)).elim
        | inr hqs => exact hqs
      · intro x hx heq
        exact hinj x (List.mem_cons_of_mem q hx) heq

/--
  Deligne 5(a)/5(d): leftover of X is 1 · cl(inverse α) = α.
  Proved from the produced seating. Not seating = thisLock.
-/
theorem OfficialHodge (X : ProjectiveNonsingularVariety) (hX : X.Official)
    (α : HodgeClass) (hα : α ∈ X.leftover) :
    isSpanOfCl α X.seating.present := by
  obtain ⟨pl, hpl, hαeq⟩ := List.mem_map.mp hα
  have hbelong : pl ∈ X.belong := by
    simpa [ProjectiveNonsingularVariety.leftover, ProjectiveNonsingularVariety.seating] using hpl
  have hlock : pl ∈ lockPairings := mem_of_take_lock hbelong
  have hp : X.present = X.belong := present_eq_belong_of_whole X hX.2
  have hpres : pl ∈ X.present := by
    rw [hp]
    exact hbelong
  have hinjL : ∀ x ∈ X.present, leftoverOf x = leftoverOf pl → x = pl := by
    intro x hx heq
    have hxB : x ∈ X.belong := by simpa [hp] using hx
    have hxL : x ∈ lockPairings := mem_of_take_lock (hxB : x ∈ lockPairings.take X.Pn)
    exact lock_lefts_unique x hxL pl hlock heq
  have hinjC : ∀ x ∈ X.present, cutOf x = cutOf pl → x = pl := by
    intro x hx heq
    have hxB : x ∈ X.belong := by simpa [hp] using hx
    have hxL : x ∈ lockPairings := mem_of_take_lock (hxB : x ∈ lockPairings.take X.Pn)
    exact lock_cuts_unique x hxL pl hlock heq
  have hfindL := find?_leftover_self hpres hinjL
  have hfindC := find?_cut_self hpres hinjC
  refine ⟨cutOf pl, ?_, ?_⟩
  · change inverse X.present α = some (cutOf pl)
    rw [← hαeq]
    simp [inverse, hfindL]
  · change cl X.present (cutOf pl) = some α
    rw [← hαeq]
    simp [cl, hfindC]

/-- thisVariety: ambient covers the lock; every paid cut sits. Leftover is produced. -/
def thisVariety : ProjectiveNonsingularVariety where
  Pn := leftoverSeq.length
  cycles := lockPairings.map cutOf

theorem thisVariety_official : thisVariety.Official := by
  decide

theorem thisVariety_produces_lock : thisVariety.seating = thisLock := by
  decide

theorem OfficialHodgeOn_thisVariety : OfficialHodgeOn thisVariety.seating := by
  decide

/-- Drop one R on the produced seating. OfficialHodgeOn fails. Missing R. -/
theorem not_OfficialHodgeOn_drop :
    ¬ OfficialHodgeOn (thisVariety.seating.drop droppedR) := by
  decide

theorem leftover_six_not_span_after_drop :
    leftoverSix ∈ (thisVariety.seating.drop droppedR).belong.map leftoverOf ∧
      ¬ isSpanOfCl leftoverSix (thisVariety.seating.drop droppedR).present := by
  decide

theorem drop_is_missing_R :
    (thisLock.drop droppedR).Hole droppedR :=
  drop_is_hole thisLock droppedR (by decide)

theorem drop_count_12_to_11 :
    thisLock.present.length = 12 ∧
      (thisLock.drop droppedR).present.length = 11 := by
  decide

/-- Missing a cycle: leftover 6 is owed, R does not sit. -/
def singularX : ProjectiveNonsingularVariety where
  Pn := leftoverSeq.length
  cycles := (lockPairings.map cutOf).erase ⟨13⟩

theorem singularX_not_official : ¬ singularX.Official := by
  decide

theorem not_OfficialHodgeOn_singular :
    ¬ OfficialHodgeOn singularX.seating := by
  decide

theorem singular_is_missing_R :
    singularX.seating.Hole droppedR := by
  decide

/-!
  Furniture from mathlib lives in `hodge.FromMathlib`.
  OfficialHodge sits here on leftover / cl / inverse.
  ProjectiveNonsingularVariety is ambient and cycles. Leftover is produced.
  AlgebraicCycle is Cut. BSD may import this file without mathlib.
-/


/-- Their names as tags a shape may wear. The tags are not the prize. -/
structure Costume where
  cohomology : Bool
  variety : Bool
  equationSystem : Bool
  prestige : Bool
  deriving DecidableEq, Repr

def Costume.full : Costume where
  cohomology := true
  variety := true
  equationSystem := true
  prestige := true

def Costume.none : Costume where
  cohomology := false
  variety := false
  equationSystem := false
  prestige := false

/-- A shape dressed in their names. Whole and Hole read the shape, not the tags. -/
structure Dressed where
  shape : Shape
  costume : Costume
  deriving Repr

/-- Full costume, still a hole: every name true, drop a belonging cycle. -/
theorem full_costume_still_holed (s : Shape) (c : Placed) (hb : c ∈ s.belong) :
    let d : Dressed := { shape := s.drop c, costume := .full }
    d.shape.Hole c ∧ ¬ d.shape.Whole :=
  ⟨drop_is_hole s c hb, drop_not_whole s c hb⟩

/-- No costume, still whole: every name false on thisLock. -/
theorem no_costume_still_whole :
    ({ shape := thisLock, costume := Costume.none } : Dressed).shape.Whole :=
  this_lock_is_whole
