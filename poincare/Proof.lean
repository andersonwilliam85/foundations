/-
  Poincaré (revised): a complete meeting is the sphere, not the world.
  Hole = missing relationship. Closed = the meeting finished.
  Sphere = the dent / working shape.
  S³ is not crowned as the world. Ricci is not installed.
  Official Clay / Milnor statements are seated or refused below.
-/

/-- A seat in a meeting. `missing` is a relationship that is not sitting. -/
inductive Seat where
  | filled (v : Nat)
  | missing
  deriving DecidableEq, Repr

/-- The lock is what the meeting owes. The dent is what sat. -/
structure Meeting where
  lock : List Seat
  dent : List Seat
  deriving Repr

/-- A hole is a missing relationship: a seat in the dent that did not sit. -/
def Meeting.Hole (m : Meeting) : Prop :=
  ∃ s ∈ m.dent, s = Seat.missing

/-- Closed: the meeting finished. The dent sat the lock, and nothing is missing. -/
def Meeting.Closed (m : Meeting) : Prop :=
  m.dent = m.lock ∧ ¬ m.Hole

/-- Whole is the finished meeting. -/
def Meeting.Whole (m : Meeting) : Prop :=
  m.Closed

/-- Complete: nothing missing, and the meeting finished. -/
def Meeting.Complete (m : Meeting) : Prop :=
  m.Closed

/-- Simply connected: every owed loop sits. No hole. -/
def Meeting.SimplyConnected (m : Meeting) : Prop :=
  ¬ m.Hole

/-- Tearing is a missing seat. -/
def Meeting.Tearing (m : Meeting) : Prop :=
  m.Hole

/-- Leaving the surface: the dent did not sit the lock. -/
def Meeting.LeftTheSurface (m : Meeting) : Prop :=
  m.dent ≠ m.lock

/-- The sphere is the working shape of a complete meeting. A dent. -/
inductive Sphere where
  | dent
  deriving DecidableEq, Repr

/-- A complete meeting yields the sphere as that dent. -/
def workingShape (m : Meeting) (_h : m.Complete) : Sphere :=
  .dent

theorem complete_meeting_is_the_sphere (m : Meeting) (h : m.Complete) :
    workingShape m h = Sphere.dent :=
  rfl

/-- The sphere is not the world. -/
def Sphere.asWorld : Sphere → Prop
  | .dent => False

theorem sphere_is_not_the_world (m : Meeting) (h : m.Complete) :
    ¬ (workingShape m h).asWorld :=
  id

/-- S³ is a named shape. It is not the world. -/
def S3_is_the_world : Prop := False

theorem not_S3_the_world : ¬ S3_is_the_world :=
  id

instance : Decidable S3_is_the_world :=
  .isFalse not_S3_the_world

/-- If the dent sat the lock and the lock has no missing seat, the meeting is closed. -/
theorem closed_of_dent_eq_lock
    (m : Meeting)
    (heq : m.dent = m.lock)
    (hnone : ∀ s ∈ m.lock, s ≠ Seat.missing) :
    m.Closed := by
  refine ⟨heq, ?_⟩
  intro ⟨s, hs, hm⟩
  exact hnone s (heq ▸ hs) hm

/-- A missing seat is not a finished meeting. -/
theorem missing_not_closed (m : Meeting) (h : m.Hole) :
    ¬ m.Closed := by
  intro ⟨_, hnone⟩
  exact hnone h

/-- A missing seat is not whole. -/
theorem missing_not_whole (m : Meeting) (h : m.Hole) :
    ¬ m.Whole :=
  missing_not_closed m h

/-- A hole is exactly a missing seat sitting in the dent. -/
theorem hole_iff_missing_mem (m : Meeting) :
    m.Hole ↔ Seat.missing ∈ m.dent := by
  constructor
  · intro ⟨s, hs, heq⟩
    exact heq ▸ hs
  · intro h
    exact ⟨Seat.missing, h, rfl⟩

instance (m : Meeting) : Decidable m.Hole :=
  decidable_of_iff (Seat.missing ∈ m.dent) (Iff.symm (hole_iff_missing_mem m))

instance (m : Meeting) : Decidable m.Closed :=
  inferInstanceAs (Decidable (m.dent = m.lock ∧ ¬ m.Hole))

instance (m : Meeting) : Decidable m.Complete :=
  inferInstanceAs (Decidable m.Closed)

instance (m : Meeting) : Decidable m.Whole :=
  inferInstanceAs (Decidable m.Closed)

instance (m : Meeting) : Decidable m.SimplyConnected :=
  inferInstanceAs (Decidable (¬ m.Hole))

instance (m : Meeting) : Decidable m.Tearing :=
  inferInstanceAs (Decidable m.Hole)

instance (m : Meeting) : Decidable m.LeftTheSurface :=
  inferInstanceAs (Decidable (m.dent ≠ m.lock))

/-- Closed meetings are simply connected: every owed loop sat. -/
theorem closed_is_simply_connected (m : Meeting) (h : m.Closed) :
    m.SimplyConnected :=
  h.2

/-- Unique working shape of a complete meeting is the dent. Do not crown it world. -/
theorem unique_working_shape_of_complete (m : Meeting) (h : m.Complete) :
    workingShape m h = Sphere.dent :=
  complete_meeting_is_the_sphere m h

/-- Eight geometries / standard pieces are not ontology. -/
def Eight_geometries_are_ontology : Prop := False

theorem not_eight_geometries_ontology : ¬ Eight_geometries_are_ontology :=
  id

instance : Decidable Eight_geometries_are_ontology :=
  .isFalse not_eight_geometries_ontology

/-- A catalog of worlds is not seated here. -/
def Catalog_of_worlds : Prop := False

theorem not_catalog_of_worlds : ¬ Catalog_of_worlds :=
  id

instance : Decidable Catalog_of_worlds :=
  .isFalse not_catalog_of_worlds

/-- Join of two meetings is still a meeting. -/
def Meeting.join (a b : Meeting) : Meeting where
  lock := a.lock ++ b.lock
  dent := a.dent ++ b.dent

/-- Join of finished meetings is still a finished meeting. -/
theorem join_of_closed_is_closed (a b : Meeting)
    (ha : a.Closed) (hb : b.Closed) :
    (a.join b).Closed := by
  refine ⟨?eq, ?none⟩
  · change a.dent ++ b.dent = a.lock ++ b.lock
    rw [ha.1, hb.1]
  · intro ⟨s, hs, hm⟩
    have hor : s ∈ a.dent ∨ s ∈ b.dent := List.mem_append.mp hs
    cases hor with
    | inl hin => exact ha.2 ⟨s, hin, hm⟩
    | inr hin => exact hb.2 ⟨s, hin, hm⟩

/-- A hole in either meeting is a hole in the join. -/
theorem join_with_hole_not_closed (a b : Meeting) (h : b.Hole) :
    ¬ (a.join b).Closed := by
  intro hc
  obtain ⟨s, hs, hm⟩ := h
  have hh : (a.join b).Hole :=
    ⟨s, List.mem_append.mpr (Or.inr hs), hm⟩
  exact hc.2 hh

/-- Ricci flow is their how. It is not the object. -/
def Ricci_is_the_object : Prop := False

theorem not_Ricci_the_object : ¬ Ricci_is_the_object :=
  id

instance : Decidable Ricci_is_the_object :=
  .isFalse not_Ricci_the_object

/-- Surgery is their how. It is not the object. -/
def Surgery_is_the_object : Prop := False

theorem not_Surgery_the_object : ¬ Surgery_is_the_object :=
  id

instance : Decidable Surgery_is_the_object :=
  .isFalse not_Surgery_the_object

/-- Hamilton’s program is their how. It is not the object. -/
def Hamilton_is_the_object : Prop := False

theorem not_Hamilton_the_object : ¬ Hamilton_is_the_object :=
  id

instance : Decidable Hamilton_is_the_object :=
  .isFalse not_Hamilton_the_object

/-- Cheeger–Gromov collapsing is their how. It is not the object. -/
def CheegerGromov_is_the_object : Prop := False

theorem not_CheegerGromov_the_object : ¬ CheegerGromov_is_the_object :=
  id

instance : Decidable CheegerGromov_is_the_object :=
  .isFalse not_CheegerGromov_the_object

/-- Geometrization is not installed as ontology. -/
def Geometrization_is_ontology : Prop := False

theorem not_geometrization_ontology : ¬ Geometrization_is_ontology :=
  id

instance : Decidable Geometrization_is_ontology :=
  .isFalse not_geometrization_ontology

/-- Completeness is the meeting finishing. -/
theorem completeness_is_the_meeting_finishing (m : Meeting) :
    m.Complete ↔ m.Closed :=
  Iff.rfl

/-- Closed is dent = lock and no missing seat. Compact / no tearing / stay on the surface. -/
theorem closed_iff_dent_eq_lock_no_missing (m : Meeting) :
    m.Closed ↔ m.dent = m.lock ∧ ¬ m.Hole :=
  Iff.rfl

theorem tearing_not_closed (m : Meeting) (h : m.Tearing) :
    ¬ m.Closed :=
  missing_not_closed m h

theorem left_surface_not_closed (m : Meeting) (h : m.LeftTheSurface) :
    ¬ m.Closed := by
  intro hc
  exact h hc.1

/-- Their prize is not this page. We seat our meeting. -/
def Clay_prize_is_this_page : Prop := False

theorem not_clay_prize_this_page : ¬ Clay_prize_is_this_page :=
  id

instance : Decidable Clay_prize_is_this_page :=
  .isFalse not_clay_prize_this_page

/-- Two-seat lock: the known smaller case (2-sphere). -/
def twoSeatLock : List Seat :=
  [Seat.filled 1, Seat.filled 1]

/-- Twelve-seat lock: the 3-sphere question stays this size. -/
def twelveSeatLock : List Seat :=
  List.replicate 12 (Seat.filled 1)

/-- Apple: Closed meeting. The rubber band sat the lock. No missing. -/
def apple : Meeting where
  lock := twoSeatLock
  dent := twoSeatLock

/-- Doughnut: a seat missing. The rubber band does not sit. -/
def doughnut : Meeting where
  lock := twoSeatLock
  dent := [Seat.filled 1, Seat.missing]

theorem apple_is_closed : apple.Closed :=
  closed_of_dent_eq_lock apple rfl (by decide)

theorem apple_is_complete : apple.Complete :=
  apple_is_closed

theorem apple_is_simply_connected : apple.SimplyConnected :=
  closed_is_simply_connected apple apple_is_closed

theorem doughnut_has_hole : doughnut.Hole :=
  ⟨Seat.missing, by decide, rfl⟩

theorem doughnut_not_closed : ¬ doughnut.Closed :=
  missing_not_closed doughnut doughnut_has_hole

theorem doughnut_tears : doughnut.Tearing :=
  doughnut_has_hole

/-- A smaller lock that is Closed is complete. The 2-sphere known case. -/
theorem two_seat_closed_is_complete
    (m : Meeting)
    (_hlock : m.lock = twoSeatLock)
    (h : m.Closed) :
    m.Complete :=
  h

theorem two_seat_apple_is_complete : apple.Complete :=
  two_seat_closed_is_complete apple rfl apple_is_closed

/-- Complete twelve-seat meeting is the dent, not the world. -/
theorem twelve_seat_complete_is_dent
    (m : Meeting)
    (_hlock : m.lock = twelveSeatLock)
    (h : m.Complete) :
    workingShape m h = Sphere.dent :=
  complete_meeting_is_the_sphere m h

theorem twelve_seat_dent_not_world
    (m : Meeting)
    (_hlock : m.lock = twelveSeatLock)
    (h : m.Complete) :
    ¬ (workingShape m h).asWorld :=
  sphere_is_not_the_world m h
