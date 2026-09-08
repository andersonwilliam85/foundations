/-
  Hodge: a hole is a missing relationship (cycle).
  Whole iff every belonging cycle is present.
  Official Clay / Deligne doors seated or refused. Their how is not installed.
-/

/-- A cycle is a relationship that closes: a pairing. -/
structure Cycle where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

/-- The cycles a shape owes, and the cycles that are sitting. -/
structure Shape where
  belong : List Cycle
  present : List Cycle
  deriving Repr

/-- A hole is a belonging cycle that is not present. -/
def Shape.Hole (s : Shape) (c : Cycle) : Prop :=
  c ∈ s.belong ∧ c ∉ s.present

/-- Whole: every belonging cycle is present. -/
def Shape.Whole (s : Shape) : Prop :=
  ∀ c : Cycle, c ∈ s.belong → c ∈ s.present

@[simp] theorem whole_iff_every_belonging_present (s : Shape) :
    s.Whole ↔ ∀ c : Cycle, c ∈ s.belong → c ∈ s.present :=
  Iff.rfl

/-- Whole iff there is no hole. -/
theorem whole_iff_no_hole (s : Shape) :
    s.Whole ↔ ∀ c : Cycle, ¬ s.Hole c := by
  constructor
  · intro hw c ⟨hb, hn⟩
    exact hn (hw c hb)
  · intro nh c hb
    by_cases hp : c ∈ s.present
    · exact hp
    · exact (nh c ⟨hb, hp⟩).elim

/-- Drop a cycle from those present. The shape still owes it. -/
def Shape.drop (s : Shape) (c : Cycle) : Shape where
  belong := s.belong
  present := s.present.filter fun x => decide (x ≠ c)

/-- Drop a seated belonging cycle and the hole appears. -/
theorem drop_is_hole (s : Shape) (c : Cycle)
    (hb : c ∈ s.belong) :
    (s.drop c).Hole c := by
  refine ⟨hb, ?_⟩
  intro hmem
  have hx : decide (c ≠ c) = true := (List.mem_filter.mp hmem).2
  simp at hx

/-- A holed shape is not whole. -/
theorem drop_not_whole (s : Shape) (c : Cycle)
    (hb : c ∈ s.belong) :
    ¬ (s.drop c).Whole := by
  intro hw
  have h := drop_is_hole s c hb
  exact h.2 (hw c h.1)

/-- If every owed cycle is sitting, the shape is whole. -/
theorem present_eq_belong_whole (s : Shape) (h : s.present = s.belong) :
    s.Whole := by
  intro c hb
  simpa [h] using hb

/-- Concatenate two shapes: owed with owed, sitting with sitting. -/
def Shape.join (s t : Shape) : Shape where
  belong := s.belong ++ t.belong
  present := s.present ++ t.present

/-- Two whole shapes join to a whole shape. -/
theorem join_whole_of_whole (s t : Shape) (hs : s.Whole) (ht : t.Whole) :
    (s.join t).Whole := by
  intro c hc
  have h : c ∈ s.belong ∨ c ∈ t.belong := List.mem_append.mp hc
  apply List.mem_append.mpr
  cases h with
  | inl hb => exact Or.inl (hs c hb)
  | inr hb => exact Or.inr (ht c hb)

/-- If every other belonging cycle is sitting, a hole at `c` is the only hole. -/
theorem unique_belonging_hole (s : Shape) (c : Cycle)
    (honly : ∀ d ∈ s.belong, d ≠ c → d ∈ s.present) :
    ∀ d, s.Hole d → d = c := by
  intro d ⟨hb, hn⟩
  by_cases heq : d = c
  · exact heq
  · exact (hn (honly d hb heq)).elim

/-- The lock is what the shape owes. -/
def Shape.lock (s : Shape) : List Cycle :=
  s.belong

/-- Owed cycles that are sitting. -/
def Shape.seated (s : Shape) : List Cycle :=
  s.belong.filter fun c => decide (c ∈ s.present)

/-- Rank: how many owed cycles are sitting. -/
def Shape.rank (s : Shape) : Nat :=
  s.seated.length

/-- A seeming-belonging: named as owed. Their Hodge cycle. -/
def HodgeNamed (s : Shape) (c : Cycle) : Prop :=
  c ∈ s.belong

instance (s : Shape) (c : Cycle) : Decidable (HodgeNamed s c) :=
  inferInstanceAs (Decidable (c ∈ s.belong))

/-- An algebraic-named sitting: present. Their algebraic cycle. -/
def AlgebraicNamed (s : Shape) (c : Cycle) : Prop :=
  c ∈ s.present

instance (s : Shape) (c : Cycle) : Decidable (AlgebraicNamed s c) :=
  inferInstanceAs (Decidable (c ∈ s.present))

/-- Small lock: fewer than four owed pairings. Their dimension less than four. -/
def Shape.Small (s : Shape) : Prop :=
  s.belong.length < 4

instance (s : Shape) : Decidable s.Small :=
  inferInstanceAs (Decidable (s.belong.length < 4))

/-- Door 1. Topology of the solution set of algebraic equations: the lock. -/
def theirAlgebraicEquationSystemIsTheObject : Prop := False

theorem not_their_equation_system : ¬ theirAlgebraicEquationSystemIsTheObject :=
  id

theorem lock_is_what_is_owed (s : Shape) : s.lock = s.belong :=
  rfl

/-- Door 2. How much of that topology further equations can name: present. -/
def furtherEquationsAreASecondTopology : Prop := False

theorem not_a_second_topology : ¬ furtherEquationsAreASecondTopology :=
  id

theorem present_is_not_a_hole (s : Shape) (c : Cycle) (hp : c ∈ s.present) :
    ¬ s.Hole c := fun h => h.2 hp

theorem how_much_of_the_lock_sat (s : Shape) (c : Cycle) :
    (c ∈ s.belong ∧ c ∈ s.present) ↔ c ∈ s.seated := by
  constructor
  · intro ⟨hb, hp⟩
    exact List.mem_filter.mpr ⟨hb, decide_eq_true hp⟩
  · intro h
    have hf := List.mem_filter.mp h
    exact ⟨hf.1, of_decide_eq_true hf.2⟩

/-- Door 3. Known when dimension is less than four: a small Whole lock stays Whole. -/
theorem small_whole_stays_whole (s : Shape) (_hs : s.Small) (hw : s.Whole) :
    s.Whole :=
  hw

def threePairings : List Cycle :=
  [⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 5⟩]

def smallLock : Shape where
  belong := threePairings
  present := threePairings

theorem small_lock_is_small : smallLock.Small := by
  decide

theorem small_lock_is_whole : smallLock.Whole :=
  present_eq_belong_whole smallLock rfl

/-- Door 4. Dimension four is still this seating. Not a new object. -/
def fourIsANewObject : Prop := False

theorem four_is_not_a_new_object : ¬ fourIsANewObject :=
  id

def unsolvedMeansUnseated : Prop := False

theorem not_unsolved_as_unseated : ¬ unsolvedMeansUnseated :=
  id

def fourPairings : List Cycle :=
  [⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 5⟩, ⟨4, 7⟩]

def fourWhole : Shape where
  belong := fourPairings
  present := fourPairings

def fourLast : Cycle := ⟨4, 7⟩

def fourHoled : Shape :=
  fourWhole.drop fourLast

theorem four_pairings_can_be_whole : fourWhole.Whole :=
  present_eq_belong_whole fourWhole rfl

theorem four_pairings_can_be_holed : ¬ fourHoled.Whole :=
  drop_not_whole fourWhole fourLast (by decide)

theorem four_is_the_same_seating (s : Shape) :
    s.Whole ↔ ∀ c : Cycle, c ∈ s.belong → c ∈ s.present :=
  Iff.rfl

/-- Door 5. Gluing simple building blocks: join of Whole pieces is Whole. -/
theorem glued_wholes_are_whole (s t : Shape) (hs : s.Whole) (ht : t.Whole) :
    (s.join t).Whole :=
  join_whole_of_whole s t hs ht

/-- Door 6. Extra pieces with no geometric interpretation are not the hole. -/
def extraIsTheHole : Prop := False

theorem refuse_extra_as_the_hole : ¬ extraIsTheHole :=
  id

def noGeometricInterpretationIsTheHole : Prop := False

theorem refuse_extra_as_geometric_hole : ¬ noGeometricInterpretationIsTheHole :=
  id

theorem extra_not_hole (s : Shape) (c : Cycle) (h : c ∉ s.belong) :
    ¬ s.Hole c := fun hh => h hh.1

theorem vacuous_extras_whole (extra : List Cycle) :
    ({ belong := [], present := extra } : Shape).Whole := by
  intro _c hb
  exact (List.not_mem_nil hb).elim

/-- Door 7. Projective algebraic varieties — particularly nice spaces.
    A finite owed lock. Not their variety. -/
def theirProjectiveVarietyIsTheObject : Prop := False

theorem not_their_variety : ¬ theirProjectiveVarietyIsTheObject :=
  id

def lockPairings : List Cycle :=
  [ ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 5⟩, ⟨4, 7⟩, ⟨5, 11⟩, ⟨6, 13⟩
  , ⟨7, 17⟩, ⟨8, 19⟩, ⟨9, 23⟩, ⟨10, 29⟩, ⟨11, 31⟩, ⟨12, 37⟩ ]

theorem twelve_pairings_stay : lockPairings.length = 12 :=
  rfl

def thisLock : Shape where
  belong := lockPairings
  present := lockPairings

theorem this_lock_is_whole : thisLock.Whole :=
  present_eq_belong_whole thisLock rfl

theorem this_lock_is_finite : thisLock.belong.length = 12 :=
  rfl

/-- Door 8. Hodge cycles are rational linear combinations of algebraic cycles.
    A seeming-belonging is present, or it is a Hole. Q-linear = join of present.
    Cohomology is not installed. -/
def cohomologyInstalled : Prop := False

theorem refuse_cohomology : ¬ cohomologyInstalled :=
  id

theorem seeming_belonging_is_present_or_hole (s : Shape) (c : Cycle)
    (hb : HodgeNamed s c) :
    AlgebraicNamed s c ∨ s.Hole c := by
  by_cases hp : c ∈ s.present
  · exact Or.inl hp
  · exact Or.inr ⟨hb, hp⟩

theorem whole_iff_hodge_named_algebraic (s : Shape) :
    s.Whole ↔ ∀ c, HodgeNamed s c → AlgebraicNamed s c :=
  Iff.rfl

theorem q_linear_combination_is_join (s t : Shape) :
    (s.join t).present = s.present ++ t.present :=
  rfl

/-- Door 9. Geometric origins obscured: a class-name that is not present is a Hole. -/
def prestigeClassIsTheObject : Prop := False

theorem not_prestige_class : ¬ prestigeClassIsTheObject :=
  id

theorem class_name_not_present_is_hole (s : Shape) (c : Cycle)
    (hb : c ∈ s.belong) (hn : c ∉ s.present) :
    s.Hole c :=
  ⟨hb, hn⟩

/-- Door 10. Building blocks of increasing dimension: belong can grow;
    joining a one-cycle whole raises the sitting count. -/
theorem rank_is_seated_count (s : Shape) : s.rank = s.seated.length :=
  rfl

theorem belong_grows_under_join (s t : Shape) :
    (s.join t).belong.length = s.belong.length + t.belong.length := by
  simp [Shape.join]

theorem join_one_cycle_raises_sitting (s : Shape) (c : Cycle) :
    (s.join { belong := [c], present := [c] }).present.length = s.present.length + 1 := by
  simp [Shape.join]
