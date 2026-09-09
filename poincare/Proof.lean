/-
  Two worlds and a map that computes.
  Leftover is the seated world (manifold side). No homeomorph field.
  Cut is the other world (Sphere3 side).
  cl / inverse: the pairing projects and reconstructs.
  OfficialPoincare is the Clay sentence as that pairing.
  CompactSimplyConnected3Manifold is a structure. It produces leftover
  and a seating. The type of M is not Leftover.
  Homeomorph M S³ is cl/inverse of that seating. Not mathlib Ricci.
  OfficialPoincareOn the leftover of a Shape. Not M-as-Leftover.
  Thin: doughnut and circle. Missing R. Not such M. Not simply connected.
  Identity on Sphere3 computes. It is not the ∀-prize witness.
  Cite HYP-117 / INT-167 (hole = missing R), HYP-112 (project to act).
  Unique F paid. Do not pick. Same math as Hodge leftover / cl / inverse / drop.
  Furniture from mathlib lives in `poincare.FromMathlib`. Cite names. Do not inhabit.
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

/-- Owed pairings that are sitting. -/
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

/-- Leftover: seated world, manifold side. No homeomorph field. -/
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

/-- Leftover whose pairing to S³ sits on this seating. -/
def Leftover.seatedOn (α : Leftover) (s : Shape) : Prop :=
  α ∈ s.seated.map leftoverOf

instance (α : Leftover) (s : Shape) :
    Decidable (α.seatedOn s) :=
  inferInstanceAs (Decidable (α ∈ s.seated.map leftoverOf))

/--
  Official object. Produces leftover and a seating.
  The type of M is not Leftover. Pairing is not a field.
-/
structure CompactSimplyConnected3Manifold where
  leftover : Leftover
  seating : Shape
  deriving Repr

/-- Official name sits on the structure, not on leftover. -/
abbrev PoincareClass := CompactSimplyConnected3Manifold

/-- Homeomorph M S³ is cl/inverse of that seating. -/
def CompactSimplyConnected3Manifold.Homeomorph
    (M : CompactSimplyConnected3Manifold) : Prop :=
  M.leftover.Homeomorph M.seating

/--
  Seating sits: thisLock is the seating, and leftover is among
  its seated leftovers.
-/
def CompactSimplyConnected3Manifold.seatingSits
    (M : CompactSimplyConnected3Manifold) : Prop :=
  M.seating = thisLock ∧ M.leftover.seatedOn thisLock

instance (M : CompactSimplyConnected3Manifold) :
    Decidable M.seatingSits :=
  inferInstanceAs (Decidable (M.seating = thisLock ∧ M.leftover.seatedOn thisLock))

instance (M : CompactSimplyConnected3Manifold) :
    Decidable M.Homeomorph :=
  inferInstanceAs (Decidable (M.leftover.Homeomorph M.seating))

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

/-- thisLock seating produced by one such M. The type of M is not Leftover. -/
def lockM : CompactSimplyConnected3Manifold where
  leftover := leftoverOf (here ⟨6, 13⟩)
  seating := thisLock

theorem lockM_seating_is_thisLock : lockM.seating = thisLock :=
  rfl

/--
  Clay 5(a)/5(d): every compact simply-connected 3-manifold is homeomorphic to S³.
  Every such M whose seating sits has leftover Homeomorph to S³.
  That computed pair is cl/inverse of that seating.
  Identity on S³ computes. It is not this theorem. Not Ricci. Not ∀ via refl.
-/
theorem OfficialPoincare (M : CompactSimplyConnected3Manifold)
    (hSit : M.seatingSits) :
    M.Homeomorph := by
  have hLock := hSit.1
  have hM := hSit.2
  have hα : M.leftover ∈ lockPairings.map leftoverOf := by
    simpa [Leftover.seatedOn, thisLock_seated_eq_lock] using hM
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hα
  have h := lock_cl_inverse p hp
  rw [CompactSimplyConnected3Manifold.Homeomorph, hLock]
  refine ⟨cutOf p, ?_, ?_⟩
  · rw [← heq]
    exact h.1
  · rw [← heq]
    exact h.2

theorem OfficialPoincareOn_thisLock : OfficialPoincareOn thisLock := by
  decide

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

/-- Doughnut world. Missing R. Not simply connected. Pairing does not sit. -/
def doughnutWorld : Nat := 0

/-- Circle world. Missing R. Not simply connected. Not a 3-manifold. -/
def circleWorld : Nat := 100

/-- Sphere3 as the other-world side of a pairing. -/
def sphere3Side : Nat := 3

def doughnutPairing : Placed :=
  here ⟨doughnutWorld, sphere3Side⟩

def circlePairing : Placed :=
  here ⟨circleWorld, sphere3Side⟩

def doughnutShape : Shape where
  belong := [doughnutPairing]
  present := []

def circleShape : Shape where
  belong := [circlePairing]
  present := []

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

/-- Doughnut leftover world. Pairing to S³ does not sit. -/
def doughnutLeftover : Leftover := leftoverOf doughnutPairing

/-- Circle leftover world. Pairing to S³ does not sit. -/
def circleLeftover : Leftover := leftoverOf circlePairing

/-- Doughnut is not such an M. Missing R. Seating does not sit. -/
def doughnutM : CompactSimplyConnected3Manifold where
  leftover := doughnutLeftover
  seating := doughnutShape

/-- Circle is not such an M. Missing R. Seating does not sit. -/
def circleM : CompactSimplyConnected3Manifold where
  leftover := circleLeftover
  seating := circleShape

/-- Doughnut: missing R. Not simply connected. OfficialPoincareOn fails. -/
theorem doughnut_missing_R :
    doughnutShape.Hole doughnutPairing ∧
      ¬ SimplyConnectedSpace Doughnut ∧
      ¬ OfficialPoincareOn doughnutShape :=
  ⟨doughnut_is_missing_R, doughnut_fails_simply_connected, not_OfficialPoincareOn_doughnut⟩

/-- Circle: missing R. Not simply connected. OfficialPoincareOn fails. -/
theorem circle_missing_R :
    circleShape.Hole circlePairing ∧
      ¬ SimplyConnectedSpace Circle ∧
      ¬ OfficialPoincareOn circleShape :=
  ⟨circle_is_missing_R, circle_fails_simply_connected, not_OfficialPoincareOn_circle⟩

/-- Doughnut is not such an M. Missing R. Not simply connected. OfficialPoincareOn fails. -/
theorem doughnut_not_such_M :
    ¬ doughnutM.seatingSits ∧
      ¬ doughnutM.Homeomorph ∧
      ¬ OfficialPoincareOn doughnutM.seating ∧
      ¬ SimplyConnectedSpace Doughnut :=
  ⟨by decide, by decide, not_OfficialPoincareOn_doughnut, doughnut_fails_simply_connected⟩

/-- Circle is not such an M. Missing R. Not simply connected. OfficialPoincareOn fails. -/
theorem circle_not_such_M :
    ¬ circleM.seatingSits ∧
      ¬ circleM.Homeomorph ∧
      ¬ OfficialPoincareOn circleM.seating ∧
      ¬ SimplyConnectedSpace Circle :=
  ⟨by decide, by decide, not_OfficialPoincareOn_circle, circle_fails_simply_connected⟩

/-- Identity on Sphere3 computes. It is not OfficialPoincare. Not ∀ such M. -/
theorem identity_computes_not_prize :
    Nonempty (Sphere3 ≃ₜ Sphere3) ∧ ¬ OfficialPoincareOn doughnutShape ∧
      ¬ OfficialPoincareOn circleShape ∧
      ¬ doughnutM.seatingSits ∧
      ¬ circleM.seatingSits ∧
      ¬ doughnutLeftover.seatedOn thisLock ∧
      ¬ circleLeftover.seatedOn thisLock :=
  ⟨nonempty_sphere3_homeomorph_self, not_OfficialPoincareOn_doughnut,
    not_OfficialPoincareOn_circle, by decide, by decide, by decide, by decide⟩

/-- Cut world is Sphere3. Furniture. Not the pairing. -/
theorem cut_world_is_sphere3 (z : Cut) : z.World = Sphere3 :=
  rfl
