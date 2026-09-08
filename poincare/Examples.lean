import poincare.Proof

/-
  Hostile examples from the Poincaré seating only.
  Twelve filled seats stay. Drop one. The meeting is not finished.
  Every official door is pressed.
-/

def lock : List Seat :=
  twelveSeatLock

def complete : Meeting where
  lock := lock
  dent := lock

/-- Door: press the whole twelve-seat lock. Is the meeting closed? -/
example : complete.Closed :=
  closed_of_dent_eq_lock complete rfl (by decide)

/-- Door: that finished meeting is the sphere as dent. -/
example : workingShape complete (by
    exact closed_of_dent_eq_lock complete rfl (by decide)) = Sphere.dent :=
  twelve_seat_complete_is_dent complete rfl (by
    exact closed_of_dent_eq_lock complete rfl (by decide))

/-- Door: do not file that sphere as the world. -/
example : ¬ (workingShape complete (by
    exact closed_of_dent_eq_lock complete rfl (by decide))).asWorld :=
  twelve_seat_dent_not_world complete rfl (by
    exact closed_of_dent_eq_lock complete rfl (by decide))

def incomplete : Meeting where
  lock := lock
  dent := List.replicate 5 (Seat.filled 1) ++ [Seat.missing] ++ List.replicate 6 (Seat.filled 1)

theorem incomplete_has_hole : incomplete.Hole :=
  ⟨Seat.missing, by decide, rfl⟩

/-- Door: one missing seat. Is the meeting finished? -/
example : ¬ incomplete.Closed :=
  missing_not_closed incomplete incomplete_has_hole

/-- Door: a missing tooth is not whole. -/
example : ¬ incomplete.Whole :=
  missing_not_whole incomplete incomplete_has_hole

/-- Door: twelve seats stay. -/
example : lock.length = 12 :=
  rfl

/-- Door: S³ is not the world. -/
example : ¬ S3_is_the_world :=
  not_S3_the_world

/-- Door: unique working shape of a complete meeting is the dent. -/
example : workingShape complete (by
    exact closed_of_dent_eq_lock complete rfl (by decide)) = Sphere.dent :=
  unique_working_shape_of_complete complete (by
    exact closed_of_dent_eq_lock complete rfl (by decide))

/-- Door: simply connected means no hole. Closed meetings have that. -/
example : complete.SimplyConnected :=
  closed_is_simply_connected complete (by
    exact closed_of_dent_eq_lock complete rfl (by decide))

/-- Door: a hole is not simply connected. -/
example : ¬ incomplete.SimplyConnected :=
  fun h => h incomplete_has_hole

/-- Door: eight geometries are not ontology. -/
example : ¬ Eight_geometries_are_ontology :=
  not_eight_geometries_ontology

/-- Door: do not crown a catalog of worlds. -/
example : ¬ Catalog_of_worlds :=
  not_catalog_of_worlds

/-- Door: join of finished meetings is still a finished meeting. -/
example : (apple.join apple).Closed :=
  join_of_closed_is_closed apple apple apple_is_closed apple_is_closed

/-- Door: join with a hole is not finished. -/
example : ¬ (apple.join doughnut).Closed :=
  join_with_hole_not_closed apple doughnut doughnut_has_hole

/-- Door: Ricci is not the object. -/
example : ¬ Ricci_is_the_object :=
  not_Ricci_the_object

/-- Door: surgery is not the object. -/
example : ¬ Surgery_is_the_object :=
  not_Surgery_the_object

/-- Door: Hamilton is not the object. -/
example : ¬ Hamilton_is_the_object :=
  not_Hamilton_the_object

/-- Door: Cheeger–Gromov is not the object. -/
example : ¬ CheegerGromov_is_the_object :=
  not_CheegerGromov_the_object

/-- Door: geometrization is not ontology. Completeness is finishing. -/
example : ¬ Geometrization_is_ontology :=
  not_geometrization_ontology

example : complete.Complete ↔ complete.Closed :=
  completeness_is_the_meeting_finishing complete

/-- Door: apple sits. Doughnut tears. -/
example : apple.Closed :=
  apple_is_closed

example : apple.SimplyConnected :=
  apple_is_simply_connected

example : doughnut.Hole :=
  doughnut_has_hole

example : ¬ doughnut.Closed :=
  doughnut_not_closed

example : doughnut.Tearing :=
  doughnut_tears

/-- Door: two-seat closed lock is complete. -/
example : apple.Complete :=
  two_seat_apple_is_complete

/-- Door: tearing is not closed. Leaving the surface is not closed. -/
example : ¬ incomplete.Closed :=
  tearing_not_closed incomplete incomplete_has_hole

def leftSurface : Meeting where
  lock := lock
  dent := List.replicate 11 (Seat.filled 1)

theorem left_surface_left : leftSurface.LeftTheSurface := by
  decide

example : ¬ leftSurface.Closed :=
  left_surface_not_closed leftSurface left_surface_left

/-- Door: their prize is not this page. -/
example : ¬ Clay_prize_is_this_page :=
  not_clay_prize_this_page

/-- Hostile run: every door must come back true. -/
def run : Bool :=
  decide complete.Closed &&
  decide (¬ incomplete.Closed) &&
  decide (lock.length = 12) &&
  decide (¬ S3_is_the_world) &&
  decide complete.SimplyConnected &&
  decide (¬ incomplete.SimplyConnected) &&
  decide (¬ Eight_geometries_are_ontology) &&
  decide (¬ Catalog_of_worlds) &&
  decide (apple.join apple).Closed &&
  decide (¬ (apple.join doughnut).Closed) &&
  decide (¬ Ricci_is_the_object) &&
  decide (¬ Surgery_is_the_object) &&
  decide (¬ Hamilton_is_the_object) &&
  decide (¬ CheegerGromov_is_the_object) &&
  decide (¬ Geometrization_is_ontology) &&
  decide apple.Closed &&
  decide doughnut.Hole &&
  decide (¬ doughnut.Closed) &&
  decide apple.Complete &&
  decide (¬ leftSurface.Closed) &&
  decide (¬ Clay_prize_is_this_page)

#eval run
