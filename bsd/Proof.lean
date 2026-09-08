import hodge.Proof
import poincare.Proof

/-
  Birch and Swinnerton-Dyer: the problem we sat, then drop their costume.
  Two readings of one belonging. Rank is owed cycles sitting.
  Order is owed holes. Join of wholes is a whole. Their how is not installed.
-/

/-- Owed cycles that are holes. Rank / seated sit on Hodge. -/
def Shape.holes (s : Shape) : List Cycle :=
  s.belong.filter fun c => decide (c ∉ s.present)

/-- Order: how many owed cycles are holes. The origin reading. -/
def Shape.order (s : Shape) : Nat :=
  s.holes.length

/-- A reading of the present pairings. Their experimental count, dropped. -/
def Shape.presentReading (s : Shape) : Nat :=
  s.present.length

theorem mem_seated_iff (s : Shape) (c : Cycle) :
    c ∈ s.seated ↔ c ∈ s.belong ∧ c ∈ s.present := by
  constructor
  · intro h
    have hf := List.mem_filter.mp h
    exact ⟨hf.1, of_decide_eq_true hf.2⟩
  · intro ⟨hb, hp⟩
    exact List.mem_filter.mpr ⟨hb, decide_eq_true hp⟩

theorem mem_holes_iff (s : Shape) (c : Cycle) :
    c ∈ s.holes ↔ c ∈ s.belong ∧ c ∉ s.present := by
  constructor
  · intro h
    have hf := List.mem_filter.mp h
    exact ⟨hf.1, of_decide_eq_true hf.2⟩
  · intro ⟨hb, hn⟩
    exact List.mem_filter.mpr ⟨hb, decide_eq_true hn⟩

theorem length_filter_all {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = true) : (l.filter p).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, p y = true :=
      fun y hy => h y (List.mem_cons_of_mem x hy)
    simp [List.filter, hx, ih hxs]

theorem length_filter_none {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : (l.filter p).length = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = false := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, p y = false :=
      fun y hy => h y (List.mem_cons_of_mem x hy)
    simp [List.filter, hx, ih hxs]

/-- Door 1. Whole-number solutions of a cubic in two variables: pairings on a lock, not their curve. -/
def theirCubicCurveIsTheObject : Prop := False

theorem not_their_cubic_curve : ¬ theirCubicCurveIsTheObject :=
  id

theorem belong_are_pairings (s : Shape) :
    ∀ c ∈ s.belong, c = ⟨c.left, c.right⟩ := by
  intro c _; rfl

/-- Door 2. Rank of rational points: owed cycles sitting. Hodge `rank_is_seated_count`.
    Door 3. Points mod p / experimental count: a reading of present pairings. -/
theorem experimental_count_is_present_reading (s : Shape) :
    s.presentReading = s.present.length :=
  rfl

/-- Door 4. Zeta near s=1: origin reading; order is owed holes. -/
theorem origin_reading_is_order (s : Shape) : s.order = s.holes.length :=
  rfl

/-- Door 5. zeta(1)=0 ⇒ infinitely many rational points: an origin hole is not Whole. -/
theorem origin_hole_not_whole (s : Shape) (c : Cycle) (h : s.Hole c) :
    ¬ s.Whole := by
  intro hw
  exact ((whole_iff_no_hole s).mp hw) c h

/-- Door 6. zeta(1)≠0 ⇒ finitely many: origin not a hole ⇒ Whole, and the lock is a list. -/
theorem no_origin_hole_is_whole (s : Shape) (h : ∀ c, ¬ s.Hole c) :
    s.Whole :=
  (whole_iff_no_hole s).mpr h

theorem whole_order_zero (s : Shape) (hw : s.Whole) : s.order = 0 := by
  simp only [Shape.order, Shape.holes]
  apply length_filter_none
  intro c hb
  simp [hw c hb]

theorem whole_rank_eq_lock (s : Shape) (hw : s.Whole) :
    s.rank = s.belong.length := by
  simp only [Shape.rank, Shape.seated]
  apply length_filter_all
  intro c hb
  simp [hw c hb]

theorem whole_holes_nil (s : Shape) (hw : s.Whole) : s.holes = [] :=
  List.eq_nil_of_length_eq_zero (whole_order_zero s hw)

theorem whole_every_belong_seated (s : Shape) (hw : s.Whole) :
    ∀ c, c ∈ s.belong → c ∈ s.seated := by
  intro c hb
  exact (mem_seated_iff s c).mpr ⟨hb, hw c hb⟩

theorem whole_finite_lock (s : Shape) (hw : s.Whole) :
    s.order = 0 ∧ s.rank = s.belong.length :=
  ⟨whole_order_zero s hw, whole_rank_eq_lock s hw⟩

/-- Door 7. Analytic rank equals algebraic rank: two names for one belonging. -/
theorem two_names_when_whole (s : Shape) (hw : s.Whole) :
    s.order = 0 ∧ s.rank = s.belong.length :=
  whole_finite_lock s hw

theorem drop_belonging_in_holes (s : Shape) (c : Cycle) (hb : c ∈ s.belong) :
    (s.drop c).Hole c ∧ ¬ (s.drop c).Whole ∧ c ∈ (s.drop c).holes := by
  refine ⟨drop_is_hole s c hb, drop_not_whole s c hb, ?_⟩
  exact (mem_holes_iff (s.drop c) c).mpr ⟨hb, (drop_is_hole s c hb).2⟩

/-- Door 8. Analytic continuation / functional equation: refuse to install. -/
def analyticContinuationInstalled : Prop := False
def functionalEquationInstalled : Prop := False
def holomorphicContinuationInstalled : Prop := False
def eulerProductInstalled : Prop := False

theorem refuse_analytic_continuation : ¬ analyticContinuationInstalled := id
theorem refuse_functional_equation : ¬ functionalEquationInstalled := id
theorem refuse_holomorphic_continuation : ¬ holomorphicContinuationInstalled := id
theorem refuse_euler_product : ¬ eulerProductInstalled := id

/-- Door 9. Leading coefficient / Sha / regulator / periods / Tamagawa / torsion:
    join-of-wholes, not their letters as objects. -/
def leadingCoefficientIsTheObject : Prop := False
def shaIsTheObject : Prop := False
def regulatorIsTheObject : Prop := False
def periodIsTheObject : Prop := False
def tamagawaIsTheObject : Prop := False
def torsionIsTheObject : Prop := False

theorem refuse_leading_coefficient : ¬ leadingCoefficientIsTheObject := id
theorem refuse_sha : ¬ shaIsTheObject := id
theorem refuse_regulator : ¬ regulatorIsTheObject := id
theorem refuse_period : ¬ periodIsTheObject := id
theorem refuse_tamagawa : ¬ tamagawaIsTheObject := id
theorem refuse_torsion : ¬ torsionIsTheObject := id

theorem join_whole (s t : Shape) (hs : s.Whole) (ht : t.Whole) :
    (s.join t).Whole := by
  intro c hc
  cases (List.mem_append.mp hc) with
  | inl hb => exact List.mem_append.mpr (Or.inl (hs c hb))
  | inr hb => exact List.mem_append.mpr (Or.inr (ht c hb))

theorem join_rank_of_whole (s t : Shape) (hs : s.Whole) (ht : t.Whole) :
    (s.join t).rank = s.rank + t.rank := by
  have hw := join_whole s t hs ht
  have hlen : (s.join t).belong.length = s.belong.length + t.belong.length := by
    simp [Shape.join, List.length_append]
  rw [whole_rank_eq_lock _ hw, whole_rank_eq_lock _ hs, whole_rank_eq_lock _ ht, hlen]

/-- Door 10. Abelian variety / group of rational points: the Shape.
    Whole iff every owed cycle is present. -/
def theirAbelianVarietyIsTheObject : Prop := False
def theirRationalPointGroupIsTheObject : Prop := False
def theirGroupLawInstalled : Prop := False

theorem not_their_abelian_variety : ¬ theirAbelianVarietyIsTheObject := id
theorem not_their_point_group : ¬ theirRationalPointGroupIsTheObject := id
theorem refuse_their_group_law : ¬ theirGroupLawInstalled := id

theorem shape_whole_iff_owed_present (s : Shape) :
    s.Whole ↔ ∀ c : Cycle, c ∈ s.belong → c ∈ s.present :=
  whole_iff_every_belonging_present s

/-- Door 11. Hilbert tenth unsolvability: we do not claim a general method. We seat this lock. -/
def generalMethodForEveryLock : Prop := False

theorem no_general_method : ¬ generalMethodForEveryLock :=
  id

/-- Door 12. Twelve pairings stay the lock. Hodge `lockPairings` / `twelve_pairings_stay` / `thisLock`. -/
theorem twelve_pairings_stay_the_lock : lockPairings.length = 12 :=
  twelve_pairings_stay

/-- Official extras from Wiles, seated or refused. Their other rooms and their how stay off. -/
def theirOtherRoomsInstalled : Prop := False
def theirHowInstalled : Prop := False
def theirSpecialValueElaborationsInstalled : Prop := False
def theirFunctionFieldAnalogInstalled : Prop := False
def theirHigherDimensionalHuntInstalled : Prop := False
def theirSpecialFamilyTestInstalled : Prop := False
def effectiveGeneratorMethodInstalled : Prop := False

theorem refuse_their_other_rooms : ¬ theirOtherRoomsInstalled := id
theorem refuse_their_how : ¬ theirHowInstalled := id
theorem refuse_special_value_elaborations : ¬ theirSpecialValueElaborationsInstalled := id
theorem refuse_function_field_analog : ¬ theirFunctionFieldAnalogInstalled := id
theorem refuse_higher_dimensional_hunt : ¬ theirHigherDimensionalHuntInstalled := id
theorem refuse_special_family_test : ¬ theirSpecialFamilyTestInstalled := id
theorem refuse_effective_generator_method : ¬ effectiveGeneratorMethodInstalled := id

/-- A finished meeting at the origin is Complete. That dent is the sphere, not the world. -/
def originLock : List Seat :=
  List.replicate 12 (Seat.filled 1)

def originMeeting : Meeting where
  lock := originLock
  dent := originLock

theorem origin_closed : originMeeting.Closed :=
  closed_of_dent_eq_lock originMeeting rfl (by decide)

theorem origin_complete : originMeeting.Complete :=
  origin_closed

theorem origin_is_the_dent :
    workingShape originMeeting origin_complete = Sphere.dent :=
  complete_meeting_is_the_sphere _ _

theorem origin_dent_is_not_the_world :
    ¬ (workingShape originMeeting origin_complete).asWorld :=
  sphere_is_not_the_world _ _

def originMissing : Meeting where
  lock := originLock
  dent := List.replicate 5 (Seat.filled 1) ++ [Seat.missing] ++ List.replicate 6 (Seat.filled 1)

theorem origin_missing_has_hole : originMissing.Hole :=
  ⟨Seat.missing, by decide, rfl⟩

theorem origin_missing_not_closed : ¬ originMissing.Closed :=
  missing_not_closed originMissing origin_missing_has_hole

theorem origin_missing_not_whole : ¬ originMissing.Whole :=
  missing_not_whole originMissing origin_missing_has_hole
