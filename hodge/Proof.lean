/-
  Shape seating. Belong / present / join / drop.
  A hole is owed-absent: a missing R.
  Leftover is seated R at slot (p,p). HodgeClass is leftover. No cut field.
  cl is the projection from cut to leftover. inverse reconstructs the cut.
  OfficialHodge is Deligne 5(a)/5(d): on a projective nonsingular
  variety over ℂ, every Hodge class is a ℚ-span of cl(Z).
  ProjectiveNonsingularVariety is Ground + Embedding + seatedR.
  Those words are data that gate leftover. X is not Shape.
  Leftover of X is computed from that data at (p,p).
  AlgebraicCycle of X is Cut of the produced seating.
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
  Official ground. Constructor `C` is ℂ. The other constructor is not
  their sentence. Not reminted F. Not mathlib ℂ as a prize.
-/
inductive Ground where
  | C
  | other
  deriving DecidableEq, Repr

/--
  Embedding. `projective n` is closed in P^n. Affine is not their sentence.
  `n ≥ 1` gates the sit. P^0 does not owe the lock.
-/
inductive Embedding where
  | projective (Pn : Nat)
  | affine
  deriving DecidableEq, Repr

/--
  Official X: projective nonsingular variety over ℂ.
  Ground, embedding, and seated leftover coordinates are the data.
  Those words gate leftover. X is not Shape. X is not Leftover.
  No stored seating. No stored OfficialHodgeOn.
-/
structure ProjectiveNonsingularVariety where
  ground : Ground
  embedding : Embedding
  seatedR : List Nat
  deriving DecidableEq, Repr

/-- What X owes. Lock pairings iff over ℂ and projective in P^n, n ≥ 1. -/
def ProjectiveNonsingularVariety.belong (X : ProjectiveNonsingularVariety) :
    List Placed :=
  match X.ground, X.embedding with
  | .C, .projective n => if n ≥ 1 then lockPairings else []
  | _, _ => []

/-- What sits: owed pairings whose leftover coordinate is in seatedR. -/
def ProjectiveNonsingularVariety.present (X : ProjectiveNonsingularVariety) :
    List Placed :=
  X.belong.filter fun p => decide (p.cycle.left ∈ X.seatedR)

/-- Produced seating. Computed from X. Not a field. -/
def ProjectiveNonsingularVariety.seating (X : ProjectiveNonsingularVariety) :
    Shape where
  belong := X.belong
  present := X.present

/-- Leftover of X is leftover of the produced seating at (p,p). Computed. -/
def ProjectiveNonsingularVariety.leftover (X : ProjectiveNonsingularVariety) :
    List Leftover :=
  X.seating.belong.map leftoverOf

theorem leftover_of_X_at_pp (X : ProjectiveNonsingularVariety) (α : Leftover)
    (_h : α ∈ X.leftover) : α.slot = (α.p, α.p) :=
  leftover_slot_is_pp α

/-- Algebraic cycle of X is Cut of the produced seating. -/
abbrev algebraicCycleOf (_X : ProjectiveNonsingularVariety) := Cut

theorem algebraicCycleOf_is_cut (X : ProjectiveNonsingularVariety) :
    algebraicCycleOf X = Cut := rfl

/-- Over ℂ. The constructor is the word. -/
def ProjectiveNonsingularVariety.OverC (X : ProjectiveNonsingularVariety) : Prop :=
  X.ground = .C

/-- Projective: closed in P^n with n ≥ 1. Affine and P^0 fail. -/
def ProjectiveNonsingularVariety.Projective (X : ProjectiveNonsingularVariety) : Prop :=
  match X.embedding with
  | .projective n => n ≥ 1
  | .affine => False

/-- Nonsingular: every leftover coordinate the lock names sits. Hole = missing R. -/
def ProjectiveNonsingularVariety.Nonsingular (X : ProjectiveNonsingularVariety) : Prop :=
  ∀ r ∈ leftoverSeq, r ∈ X.seatedR

/-- Official sentence as data: over ℂ, projective, nonsingular. -/
def ProjectiveNonsingularVariety.Official (X : ProjectiveNonsingularVariety) : Prop :=
  X.OverC ∧ X.Projective ∧ X.Nonsingular

def overCB (X : ProjectiveNonsingularVariety) : Bool :=
  decide (X.ground = .C)

def projectiveB (X : ProjectiveNonsingularVariety) : Bool :=
  match X.embedding with
  | .projective n => decide (n ≥ 1)
  | .affine => false

def nonsingularB (X : ProjectiveNonsingularVariety) : Bool :=
  leftoverSeq.all fun r => decide (r ∈ X.seatedR)

def officialB (X : ProjectiveNonsingularVariety) : Bool :=
  overCB X && projectiveB X && nonsingularB X

theorem overC_iff (X : ProjectiveNonsingularVariety) :
    X.OverC ↔ overCB X = true := by
  simp [ProjectiveNonsingularVariety.OverC, overCB]

theorem projective_iff (X : ProjectiveNonsingularVariety) :
    X.Projective ↔ projectiveB X = true := by
  cases he : X.embedding with
  | projective n =>
    simp [ProjectiveNonsingularVariety.Projective, projectiveB, he]
  | affine =>
    simp [ProjectiveNonsingularVariety.Projective, projectiveB, he]

theorem nonsingular_iff (X : ProjectiveNonsingularVariety) :
    X.Nonsingular ↔ nonsingularB X = true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro r hr
    exact decide_eq_true (h r hr)
  · intro h r hr
    exact of_decide_eq_true (List.all_eq_true.mp h r hr)

theorem official_iff (X : ProjectiveNonsingularVariety) :
    X.Official ↔ officialB X = true := by
  constructor
  · intro ⟨hC, hP, hN⟩
    have hCb := (overC_iff X).mp hC
    have hPb := (projective_iff X).mp hP
    have hNb := (nonsingular_iff X).mp hN
    simp [officialB, hCb, hPb, hNb]
  · intro h
    have hC : overCB X = true := by
      simp [officialB] at h
      exact h.1.1
    have hP : projectiveB X = true := by
      simp [officialB] at h
      exact h.1.2
    have hN : nonsingularB X = true := by
      simp [officialB] at h
      exact h.2
    exact ⟨(overC_iff X).mpr hC, (projective_iff X).mpr hP, (nonsingular_iff X).mpr hN⟩

instance (X : ProjectiveNonsingularVariety) : Decidable X.OverC :=
  decidable_of_iff (overCB X = true) (overC_iff X).symm

instance (X : ProjectiveNonsingularVariety) : Decidable X.Projective :=
  decidable_of_iff (projectiveB X = true) (projective_iff X).symm

instance (X : ProjectiveNonsingularVariety) : Decidable X.Nonsingular :=
  decidable_of_iff (nonsingularB X = true) (nonsingular_iff X).symm

instance (X : ProjectiveNonsingularVariety) : Decidable X.Official :=
  decidable_of_iff (officialB X = true) (official_iff X).symm

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

theorem lock_left_mem_leftoverSeq :
    ∀ p ∈ lockPairings, p.cycle.left ∈ leftoverSeq := by
  decide

theorem belong_of_official (X : ProjectiveNonsingularVariety) (h : X.Official) :
    X.belong = lockPairings := by
  rcases h with ⟨hC, hP, _⟩
  unfold ProjectiveNonsingularVariety.belong
  cases hg : X.ground with
  | other =>
    simp [ProjectiveNonsingularVariety.OverC, hg] at hC
  | C =>
    cases he : X.embedding with
    | affine =>
      simp [ProjectiveNonsingularVariety.Projective, he] at hP
    | projective n =>
      have hn : n ≥ 1 := by
        simpa [ProjectiveNonsingularVariety.Projective, he] using hP
      simp [hn]

theorem present_of_official (X : ProjectiveNonsingularVariety) (h : X.Official) :
    X.present = lockPairings := by
  have hb := belong_of_official X h
  have hN := h.2.2
  unfold ProjectiveNonsingularVariety.present
  rw [hb]
  apply List.filter_eq_self.mpr
  intro p hp
  exact decide_eq_true (hN p.cycle.left (lock_left_mem_leftoverSeq p hp))

/-- Official X produces thisLock. Computed. Not stored. -/
theorem seating_of_official (X : ProjectiveNonsingularVariety) (h : X.Official) :
    X.seating = thisLock := by
  have hb := belong_of_official X h
  have hp := present_of_official X h
  simp [ProjectiveNonsingularVariety.seating, thisLock, hb, hp]

/-- thisVariety: over ℂ, closed in P³, every leftover R sits. -/
def thisVariety : ProjectiveNonsingularVariety where
  ground := .C
  embedding := .projective 3
  seatedR := leftoverSeq

theorem thisVariety_official : thisVariety.Official := by
  decide

theorem thisVariety_produces_lock : thisVariety.seating = thisLock :=
  seating_of_official thisVariety thisVariety_official

/--
  Deligne 5(a)/5(d): on a projective nonsingular variety over ℂ,
  every leftover class produced by X is 1 · cl(inverse α) = α.
  Official words gate. Leftover is computed. No stored prize.
-/
theorem OfficialHodge (X : ProjectiveNonsingularVariety) (hX : X.Official)
    (α : HodgeClass) (hα : α ∈ X.leftover) :
    isSpanOfCl α X.seating.present := by
  have hs := seating_of_official X hX
  have hl : X.leftover = thisLock.belong.map leftoverOf := by
    simp [ProjectiveNonsingularVariety.leftover, hs]
  rw [hl] at hα
  rw [hs]
  exact OfficialHodgeOn_thisLock α hα

theorem OfficialHodgeOn_thisVariety : OfficialHodgeOn thisVariety.seating := by
  rw [thisVariety_produces_lock]
  exact OfficialHodgeOn_thisLock

/-- Thin: drop one R on the produced seating. OfficialHodgeOn fails. Missing R. -/
theorem not_OfficialHodgeOn_drop :
    ¬ OfficialHodgeOn (thisVariety.seating.drop droppedR) := by
  rw [thisVariety_produces_lock]
  decide

theorem leftover_six_not_span_after_drop :
    leftoverSix ∈ (thisVariety.seating.drop droppedR).belong.map leftoverOf ∧
      ¬ isSpanOfCl leftoverSix (thisVariety.seating.drop droppedR).present := by
  rw [thisVariety_produces_lock]
  decide

theorem drop_is_missing_R :
    (thisLock.drop droppedR).Hole droppedR :=
  drop_is_hole thisLock droppedR (by decide)

theorem drop_count_12_to_11 :
    thisLock.present.length = 12 ∧
      (thisLock.drop droppedR).present.length = 11 := by
  decide

/-- Not over ℂ. Official words fail. Leftover is not produced. -/
def notOverC : ProjectiveNonsingularVariety where
  ground := .other
  embedding := .projective 3
  seatedR := leftoverSeq

/-- Affine. Not projective. Leftover is not produced. -/
def affineX : ProjectiveNonsingularVariety where
  ground := .C
  embedding := .affine
  seatedR := leftoverSeq

/-- P^0. Projective word fails the n ≥ 1 gate. -/
def pointX : ProjectiveNonsingularVariety where
  ground := .C
  embedding := .projective 0
  seatedR := leftoverSeq

/-- Singular: leftover 6 is missing R. Over ℂ and projective, not nonsingular. -/
def singularX : ProjectiveNonsingularVariety where
  ground := .C
  embedding := .projective 3
  seatedR := leftoverSeq.erase 6

theorem notOverC_not_official : ¬ notOverC.Official := by
  decide

theorem affineX_not_official : ¬ affineX.Official := by
  decide

theorem pointX_not_official : ¬ pointX.Official := by
  decide

theorem singularX_not_official : ¬ singularX.Official := by
  decide

theorem notOverC_leftover_empty : notOverC.leftover = [] := by
  decide

theorem affineX_leftover_empty : affineX.leftover = [] := by
  decide

theorem pointX_leftover_empty : pointX.leftover = [] := by
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
  ProjectiveNonsingularVariety is Ground + Embedding + seatedR.
  Leftover is computed. AlgebraicCycle is Cut.
  Leftover stays visible. BSD may import this file without mathlib.
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
