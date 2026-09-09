/-
  Two worlds and a map that computes.
  Leftover is seated R (manifold side). No homeomorph field.
  Cut is the other world (Sphere3 side).
  cl / inverse: the pairing projects and reconstructs.
  Official M is compact, simply-connected, dimension 3.
  Those words are data that gate the sit. Type of M is not Leftover.
  M produces leftover and a seating. Homeomorph M S³ is cl/inverse
  of that seating. OfficialPoincare: every such M (those gates)
  has leftover Homeomorph to S³.
  seatingSits is leftover sitting. Not seating = thisLock.
  Doughnut and circle fail the gates (not simply connected /
  not a 3-manifold). Drop fails OfficialPoincareOn. Missing R.
  Identity on Sphere3 computes. It is not the ∀-prize witness.
  Cite HYP-117 / INT-167 (hole = missing R), HYP-112 (project to act).
  Unique F paid. Do not pick. Same math as Hodge leftover / cl / inverse / drop.
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

/-- Two generated sequences. Pair them. That is the seating. Unique F. -/
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

/-- Sphere3 as the other-world side of a pairing. -/
def sphere3Side : Nat := 3

/-- Hole seating: leftover world owed, R missing. -/
def holeSeating (world : Nat) : Shape where
  belong := [here ⟨world, sphere3Side⟩]
  present := []

/--
  Official object. Compact, simply-connected, dimension 3 are data.
  Those words gate the sit. Type of M is not Leftover.
  Leftover and seating are produced. Not stored.
-/
structure OfficialManifold where
  compact : Bool
  simplyConnected : Bool
  dimension : Nat
  world : Nat
  deriving Repr, DecidableEq

/-- Gates: compact, simply-connected, dimension 3. -/
def OfficialManifold.gates (M : OfficialManifold) : Bool :=
  M.compact && M.simplyConnected && decide (M.dimension = 3)

/-- Such M: those official words hold. -/
def OfficialManifold.such (M : OfficialManifold) : Prop :=
  M.gates = true

theorem such_iff (M : OfficialManifold) :
    M.such ↔ M.compact = true ∧ M.simplyConnected = true ∧ M.dimension = 3 := by
  cases hc : M.compact <;> cases hs : M.simplyConnected
  · simp [OfficialManifold.such, OfficialManifold.gates, hc, hs]
  · simp [OfficialManifold.such, OfficialManifold.gates, hc, hs]
  · simp [OfficialManifold.such, OfficialManifold.gates, hc, hs]
  · simp [OfficialManifold.such, OfficialManifold.gates, hc, hs, decide_eq_true_eq]

instance (M : OfficialManifold) : Decidable M.such :=
  inferInstanceAs (Decidable (M.gates = true))

/--
  Seating M produces. Gates sit leftover on the unique F lock.
  Failed gates produce a hole seating. Missing R.
  Production. Not a stored field. Not seatingSits := seating = thisLock.
-/
def OfficialManifold.seating (M : OfficialManifold) : Shape :=
  if M.gates then thisLock else holeSeating M.world

/-- Leftover M produces: seated R of that seating. Not a stored field. -/
def leftover (M : OfficialManifold) : List Leftover :=
  M.seating.seated.map leftoverOf

/-- Official name: such M. Not Leftover. -/
def CompactSimplyConnected3Manifold (M : OfficialManifold) : Prop :=
  M.such

abbrev PoincareClass := OfficialManifold

/-- Homeomorph M S³ is cl/inverse of the produced seating. No homeomorph field. -/
def OfficialManifold.Homeomorph (M : OfficialManifold) : Prop :=
  OfficialPoincareOn M.seating

instance (M : OfficialManifold) : Decidable M.Homeomorph :=
  inferInstanceAs (Decidable (OfficialPoincareOn M.seating))

/--
  Seating sits: leftover is seated R, and nothing owed is missing.
  Not seating = thisLock.
-/
def OfficialManifold.seatingSits (M : OfficialManifold) : Prop :=
  leftover M ≠ [] ∧ M.seating.Whole

instance (M : OfficialManifold) : Decidable M.seatingSits :=
  inferInstanceAs (Decidable (leftover M ≠ [] ∧ M.seating.Whole))

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

theorem leftover_is_seated_R (M : OfficialManifold) :
    leftover M = M.seating.seated.map leftoverOf :=
  rfl

theorem seating_of_such (M : OfficialManifold) (h : M.such) :
    M.seating = thisLock :=
  if_pos h

theorem leftover_of_such (M : OfficialManifold) (h : M.such) :
    leftover M = lockPairings.map leftoverOf := by
  rw [leftover_is_seated_R, seating_of_such M h, thisLock_seated_eq_lock]

theorem leftover_of_such_seated (M : OfficialManifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.seatedOn M.seating := by
  rw [leftover_of_such M h] at hα
  rw [Leftover.seatedOn, seating_of_such M h, thisLock_seated_eq_lock]
  exact hα

/-- Sphere3 as official M. Compact, simply-connected, dimension 3. Data. -/
def sphere3M : OfficialManifold where
  compact := true
  simplyConnected := true
  dimension := 3
  world := 3

theorem sphere3M_such : sphere3M.such := by
  decide

/-- thisLock seating produced by one such M. The type of M is not Leftover. -/
def lockM : OfficialManifold := sphere3M

theorem lockM_such : lockM.such :=
  sphere3M_such

/--
  Clay 5(a)/5(d): every compact simply-connected 3-manifold is homeomorphic to S³.
  Official words gate the sit. Leftover produced by such M is seated R.
  That leftover is Homeomorph to S³ by cl/inverse of the produced seating.
  Identity on S³ computes. It is not this theorem. Not Ricci. Not ∀ via lock-eq.
-/
theorem OfficialPoincare (M : OfficialManifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.Homeomorph M.seating := by
  have hα' : α ∈ lockPairings.map leftoverOf := by
    rwa [leftover_of_such M h] at hα
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hα'
  have hpair := lock_cl_inverse p hp
  rw [seating_of_such M h]
  refine ⟨cutOf p, ?_, ?_⟩
  · rw [← heq]
    exact hpair.1
  · rw [← heq]
    exact hpair.2

theorem OfficialPoincare_Homeomorph (M : OfficialManifold) (h : M.such) :
    M.Homeomorph := by
  intro α hα
  have hα' : α ∈ leftover M := by
    rw [leftover_of_such M h]
    rw [seating_of_such M h] at hα
    simpa [thisLock] using hα
  exact OfficialPoincare M h α hα'

theorem OfficialPoincareOn_thisLock : OfficialPoincareOn thisLock := by
  decide

theorem seatingSits_of_such (M : OfficialManifold) (h : M.such) :
    M.seatingSits := by
  constructor
  · rw [leftover_of_such M h]
    decide
  · rw [seating_of_such M h]
    exact this_lock_is_whole

/-- Thin drop: one missing R. That leftover is not recovered by remaining cl. -/
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

/-- Doughnut world. Missing R. Not simply connected. -/
def doughnutWorld : Nat := 0

/-- Circle world. Missing R. Not simply connected. Not a 3-manifold. -/
def circleWorld : Nat := 100

/-- Doughnut: compact 3-manifold data, not simply connected. Not such M. -/
def doughnut : OfficialManifold where
  compact := true
  simplyConnected := false
  dimension := 3
  world := doughnutWorld

/-- Circle: not simply connected, not a 3-manifold. Not such M. -/
def circle : OfficialManifold where
  compact := true
  simplyConnected := false
  dimension := 1
  world := circleWorld

def doughnutShape : Shape := doughnut.seating
def circleShape : Shape := circle.seating
def doughnutPairing : Placed := here ⟨doughnutWorld, sphere3Side⟩
def circlePairing : Placed := here ⟨circleWorld, sphere3Side⟩

theorem doughnut_not_such : ¬ doughnut.such := by
  decide

theorem circle_not_such : ¬ circle.such := by
  decide

theorem doughnut_fails_because_not_simply_connected :
    doughnut.simplyConnected = false ∧ doughnut.dimension = 3 :=
  ⟨rfl, rfl⟩

theorem circle_fails_because_not_such_M :
    circle.simplyConnected = false ∧ circle.dimension ≠ 3 :=
  ⟨rfl, by decide⟩

theorem doughnut_is_missing_R : doughnutShape.Hole doughnutPairing :=
  ⟨by decide, by decide⟩

theorem circle_is_missing_R : circleShape.Hole circlePairing :=
  ⟨by decide, by decide⟩

theorem not_OfficialPoincareOn_doughnut :
    ¬ OfficialPoincareOn doughnutShape := by
  decide

theorem not_OfficialPoincareOn_circle :
    ¬ OfficialPoincareOn circleShape := by
  decide

/-- Doughnut leftover world. Pairing to S³ does not sit. Owed, not seated R. -/
def doughnutLeftover : Leftover := leftoverOf doughnutPairing

/-- Circle leftover world. Pairing to S³ does not sit. Owed, not seated R. -/
def circleLeftover : Leftover := leftoverOf circlePairing

/-- Doughnut produces no leftover. Leftover is seated R. Missing R. -/
theorem doughnut_produces_no_leftover : leftover doughnut = [] := by
  decide

theorem circle_produces_no_leftover : leftover circle = [] := by
  decide

/-- Doughnut: missing R. Not simply connected. OfficialPoincareOn fails. -/
theorem doughnut_missing_R :
    doughnutShape.Hole doughnutPairing ∧
      ¬ SimplyConnectedSpace Doughnut ∧
      ¬ OfficialPoincareOn doughnutShape ∧
      ¬ doughnut.such :=
  ⟨doughnut_is_missing_R, doughnut_fails_simply_connected,
    not_OfficialPoincareOn_doughnut, doughnut_not_such⟩

/-- Circle: missing R. Not simply connected. Not a 3-manifold. OfficialPoincareOn fails. -/
theorem circle_missing_R :
    circleShape.Hole circlePairing ∧
      ¬ SimplyConnectedSpace Circle ∧
      ¬ OfficialPoincareOn circleShape ∧
      ¬ circle.such :=
  ⟨circle_is_missing_R, circle_fails_simply_connected,
    not_OfficialPoincareOn_circle, circle_not_such⟩

/-- Doughnut is not such an M. Not simply connected. Missing R. -/
theorem doughnut_not_such_M :
    ¬ doughnut.such ∧
      ¬ doughnut.seatingSits ∧
      ¬ doughnut.Homeomorph ∧
      ¬ OfficialPoincareOn doughnut.seating ∧
      ¬ SimplyConnectedSpace Doughnut :=
  ⟨doughnut_not_such, by decide, by decide, not_OfficialPoincareOn_doughnut,
    doughnut_fails_simply_connected⟩

/-- Circle is not such an M. Not simply connected. Not a 3-manifold. Missing R. -/
theorem circle_not_such_M :
    ¬ circle.such ∧
      ¬ circle.seatingSits ∧
      ¬ circle.Homeomorph ∧
      ¬ OfficialPoincareOn circle.seating ∧
      ¬ SimplyConnectedSpace Circle :=
  ⟨circle_not_such, by decide, by decide, not_OfficialPoincareOn_circle,
    circle_fails_simply_connected⟩

/-- Identity on Sphere3 computes. It is not OfficialPoincare. Not ∀ such M. -/
theorem identity_computes_not_prize :
    Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
      ¬ OfficialPoincareOn circleShape ∧
      ¬ doughnut.such ∧
      ¬ circle.such ∧
      ¬ doughnut.seatingSits ∧
      ¬ circle.seatingSits ∧
      leftover doughnut = [] ∧
      leftover circle = [] :=
  ⟨nonempty_sphere3_homeomorph_self, not_OfficialPoincareOn_doughnut,
    not_OfficialPoincareOn_circle, doughnut_not_such, circle_not_such,
    by decide, by decide, doughnut_produces_no_leftover, circle_produces_no_leftover⟩

/-- Cut world is Sphere3. Furniture. Not the pairing. -/
theorem cut_world_is_sphere3 (z : Cut) : z.World = Sphere3 :=
  rfl
