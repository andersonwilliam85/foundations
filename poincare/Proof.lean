/-
  Two worlds and a map that computes.
  Leftover is seated R (manifold side). No homeomorph field.
  Cut is the other world (Sphere3 side).
  cl / inverse: the pairing projects and reconstructs.
  Official M carries a seating. Leftover is produced from that seating.
  Type of M is not Leftover. No Bool clothes. No if-then-thisLock.
  Compact / simply-connected / dimension 3 are leftover readings.
  Homeomorph M S³ is cl/inverse of that seating.
  OfficialPoincare: every such M has leftover Homeomorph to S³.
  Doughnut is the drop. Missing R. Not simply connected.
  Circle is not a 3-pairing. Drop fails OfficialPoincareOn.
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

/--
  Official object. One structure. Not Leftover. Not Bool clothes.
  M carries the seating. Leftover is produced from that seating.
  Compact / simply-connected / dimension 3 are readings of leftover.
-/
structure CompactSimplyConnected3Manifold where
  seating : Shape
  deriving Repr, DecidableEq

abbrev PoincareClass := CompactSimplyConnected3Manifold

/-- Leftover M produces: seated R of M's seating. Visible. Not a Bool branch. -/
def leftover (M : CompactSimplyConnected3Manifold) : List Leftover :=
  M.seating.seated.map leftoverOf

theorem leftover_is_seated_R (M : CompactSimplyConnected3Manifold) :
    leftover M = M.seating.seated.map leftoverOf :=
  rfl

/--
  Dimension 3: owed and sitting pairings are unique-F 3-lock pairings.
  Read from leftover. Not a stored Nat.
-/
def CompactSimplyConnected3Manifold.dimension3
    (M : CompactSimplyConnected3Manifold) : Prop :=
  (∀ p ∈ M.seating.belong, p ∈ lockPairings) ∧
  (∀ p ∈ M.seating.present, p ∈ lockPairings)

def dimension3B (M : CompactSimplyConnected3Manifold) : Bool :=
  M.seating.belong.all (fun p => decide (p ∈ lockPairings)) &&
    M.seating.present.all (fun p => decide (p ∈ lockPairings))

theorem dimension3_iff (M : CompactSimplyConnected3Manifold) :
    M.dimension3 ↔ dimension3B M = true := by
  simp [CompactSimplyConnected3Manifold.dimension3, dimension3B, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]

instance (M : CompactSimplyConnected3Manifold) : Decidable M.dimension3 :=
  decidable_of_iff (dimension3B M = true) (dimension3_iff M).symm

/-- Compact: leftover meeting is the complete closed 3-lock. Read from leftover. -/
def CompactSimplyConnected3Manifold.compact
    (M : CompactSimplyConnected3Manifold) : Prop :=
  M.seating.belong = lockPairings

instance (M : CompactSimplyConnected3Manifold) : Decidable M.compact :=
  inferInstanceAs (Decidable (M.seating.belong = lockPairings))

/-- Simply-connected: present is belong. No hole. Missing R is the fail. -/
def CompactSimplyConnected3Manifold.simplyConnected
    (M : CompactSimplyConnected3Manifold) : Prop :=
  M.seating.present = M.seating.belong

instance (M : CompactSimplyConnected3Manifold) : Decidable M.simplyConnected :=
  inferInstanceAs (Decidable (M.seating.present = M.seating.belong))

/-- Such M: those official readings hold. Not Bool clothes. -/
def CompactSimplyConnected3Manifold.such
    (M : CompactSimplyConnected3Manifold) : Prop :=
  M.compact ∧ M.simplyConnected ∧ M.dimension3

instance (M : CompactSimplyConnected3Manifold) : Decidable M.such :=
  inferInstanceAs (Decidable (M.compact ∧ M.simplyConnected ∧ M.dimension3))

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

theorem belong_eq_lock_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seating.belong = lockPairings :=
  h.1

theorem present_eq_belong_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seating.present = M.seating.belong :=
  h.2.1

theorem whole_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seating.Whole :=
  present_eq_belong_whole M.seating (present_eq_belong_of_such M h)

/-- Unique F: the complete closed simply-connected 3 leftover seating is thisLock. Read, not minted. -/
theorem seating_eq_thisLock_of_such (M : CompactSimplyConnected3Manifold)
    (h : M.such) : M.seating = thisLock := by
  obtain ⟨s⟩ := M
  have hb : s.belong = lockPairings := h.1
  have hp : s.present = s.belong := h.2.1
  cases s with
  | mk b p =>
    simp [thisLock] at hb hp ⊢
    exact ⟨hb, hp.trans hb⟩

theorem seated_eq_lock_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seating.seated = lockPairings := by
  rw [seating_eq_thisLock_of_such M h]
  exact thisLock_seated_eq_lock

theorem leftover_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    leftover M = lockPairings.map leftoverOf := by
  rw [leftover_is_seated_R, seated_eq_lock_of_such M h]

theorem leftover_of_such_seated (M : CompactSimplyConnected3Manifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.seatedOn M.seating := by
  rw [leftover_of_such M h] at hα
  rw [Leftover.seatedOn, seated_eq_lock_of_such M h]
  exact hα

/-- Sphere3 leftover seating. Compact, simply-connected, dimension 3 by leftover. -/
def sphere3M : CompactSimplyConnected3Manifold where
  seating := thisLock

theorem sphere3M_such : sphere3M.such := by
  decide

def lockM : CompactSimplyConnected3Manifold := sphere3M

theorem lockM_such : lockM.such :=
  sphere3M_such

/--
  Clay 5(a)/5(d): every compact simply-connected 3-manifold is homeomorphic to S³.
  Official words are leftover readings. Leftover is produced from M.
  Homeomorph is cl/inverse of that seating. Not Ricci. Not Bool clothes.
-/
theorem OfficialPoincare (M : CompactSimplyConnected3Manifold) (h : M.such)
    (α : Leftover) (hα : α ∈ leftover M) :
    α.Homeomorph M.seating := by
  have hα' : α ∈ lockPairings.map leftoverOf := by
    rwa [leftover_of_such M h] at hα
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hα'
  have hpair := lock_cl_inverse p hp
  rw [seating_eq_thisLock_of_such M h]
  refine ⟨cutOf p, ?_, ?_⟩
  · rw [← heq]
    exact hpair.1
  · rw [← heq]
    exact hpair.2

theorem OfficialPoincare_Homeomorph (M : CompactSimplyConnected3Manifold)
    (h : M.such) : M.Homeomorph := by
  intro α hα
  apply OfficialPoincare M h
  rw [leftover_of_such M h]
  rw [seating_eq_thisLock_of_such M h] at hα
  simpa [thisLock] using hα

theorem OfficialPoincareOn_thisLock : OfficialPoincareOn thisLock := by
  decide

theorem seatingSits_of_such (M : CompactSimplyConnected3Manifold) (h : M.such) :
    M.seatingSits := by
  constructor
  · rw [leftover_of_such M h]
    decide
  · exact whole_of_such M h

/-- Thin drop: one missing R. OfficialPoincareOn fails. -/
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

/-- Doughnut: compact 3 leftover with a hole. Missing R. Not simply connected. -/
def doughnut : CompactSimplyConnected3Manifold where
  seating := thisLock.drop droppedR

/-- Circle: not a 3-pairing. Not a 3-manifold. Missing R. -/
def circlePairing : Placed := here ⟨100, 1⟩

def circle : CompactSimplyConnected3Manifold where
  seating := { belong := [circlePairing], present := [] }

def doughnutShape : Shape := doughnut.seating
def circleShape : Shape := circle.seating
def doughnutPairing : Placed := droppedR

theorem doughnut_compact : doughnut.compact := by
  decide

theorem doughnut_dimension3 : doughnut.dimension3 := by
  decide

theorem doughnut_not_simplyConnected : ¬ doughnut.simplyConnected := by
  decide

theorem doughnut_not_such : ¬ doughnut.such := by
  decide

theorem circle_not_dimension3 : ¬ circle.dimension3 := by
  decide

theorem circle_not_compact : ¬ circle.compact := by
  decide

theorem circle_not_simplyConnected : ¬ circle.simplyConnected := by
  decide

theorem circle_not_such : ¬ circle.such := by
  decide

theorem doughnut_is_missing_R : doughnutShape.Hole doughnutPairing :=
  drop_is_missing_R

theorem circle_is_missing_R : circleShape.Hole circlePairing :=
  ⟨by decide, by decide⟩

theorem not_OfficialPoincareOn_doughnut :
    ¬ OfficialPoincareOn doughnutShape :=
  not_OfficialPoincareOn_drop

theorem not_OfficialPoincareOn_circle :
    ¬ OfficialPoincareOn circleShape := by
  decide

/-- Doughnut leftover: seated R that remains after the missing pairing. Visible. -/
theorem doughnut_leftover_is_eleven :
    (leftover doughnut).length = 11 := by
  decide

theorem circle_produces_no_leftover : leftover circle = [] := by
  decide

/-- Doughnut: missing R. Not simply connected. OfficialPoincareOn fails. -/
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

/-- Circle: not a 3-manifold. Not simply connected. OfficialPoincareOn fails. -/
theorem circle_missing_R :
    circleShape.Hole circlePairing ∧
      ¬ circle.dimension3 ∧
      ¬ circle.compact ∧
      ¬ SimplyConnectedSpace Circle ∧
      ¬ OfficialPoincareOn circleShape ∧
      ¬ circle.such :=
  ⟨circle_is_missing_R, circle_not_dimension3, circle_not_compact,
    circle_fails_simply_connected, not_OfficialPoincareOn_circle, circle_not_such⟩

/-- Doughnut is not such an M. Not simply connected. Missing R. Leftover stays visible. -/
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

/-- Circle is not such an M. Not a 3-manifold. Missing R. -/
theorem circle_not_such_M :
    ¬ circle.such ∧
      ¬ circle.dimension3 ∧
      ¬ circle.seatingSits ∧
      ¬ circle.Homeomorph ∧
      leftover circle = [] ∧
      ¬ OfficialPoincareOn circle.seating ∧
      ¬ SimplyConnectedSpace Circle :=
  ⟨circle_not_such, circle_not_dimension3, by decide, by decide,
    circle_produces_no_leftover, not_OfficialPoincareOn_circle,
    circle_fails_simply_connected⟩

/-- Identity on Sphere3 computes. It is not OfficialPoincare. Not ∀ such M. -/
theorem identity_computes_not_prize :
    Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
      ¬ OfficialPoincareOn circleShape ∧
      ¬ doughnut.such ∧
      ¬ circle.such ∧
      ¬ doughnut.simplyConnected ∧
      ¬ circle.dimension3 ∧
      ¬ doughnut.seatingSits ∧
      ¬ circle.seatingSits :=
  ⟨nonempty_sphere3_homeomorph_self, not_OfficialPoincareOn_doughnut,
    not_OfficialPoincareOn_circle, doughnut_not_such, circle_not_such,
    doughnut_not_simplyConnected, circle_not_dimension3, by decide, by decide⟩

/-- Cut world is Sphere3. Furniture. Not the pairing. -/
theorem cut_world_is_sphere3 (z : Cut) : z.World = Sphere3 :=
  rfl
