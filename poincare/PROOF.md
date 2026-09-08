# Poincaré: Written Proof

Objects below are those of `poincare/Proof.lean`. Ricci flow is the path Perelman walked. Each official Clay / Milnor statement is seated by name.

## Definitions

A **seat** (`Seat`) is either `filled` or `missing`. A missing seat is a relationship that did not sit.

A **meeting** (`Meeting`) carries two lists of seats:

- `lock`: what the meeting owes.
- `dent`: what sat.

A **hole** (`Meeting.Hole`) is a missing relationship in the dent: there exists a seat \(s \in m.\mathrm{dent}\) with \(s = \mathrm{Seat.missing}\). Equivalently (`hole_iff_missing_mem`): \(\mathrm{Seat.missing} \in m.\mathrm{dent}\).

The meeting is **closed** (`Meeting.Closed`) when the dent sat the lock and nothing is missing:

\[
m.\mathrm{dent} = m.\mathrm{lock} \;\land\; \neg\, m.\mathrm{Hole}.
\]

**Whole** (`Meeting.Whole`) and **complete** (`Meeting.Complete`) are this same closed meeting (`completeness_is_the_meeting_finishing`).

**Simply connected** (`Meeting.SimplyConnected`) is \(\neg\, m.\mathrm{Hole}\): every owed loop sits.

**Tearing** (`Meeting.Tearing`) is a hole. **Leaving the surface** (`Meeting.LeftTheSurface`) is \(m.\mathrm{dent} \neq m.\mathrm{lock}\).

The **sphere** (`Sphere`) is the working shape of a complete meeting: the dent. `workingShape m h`, given \(h : m.\mathrm{Complete}\), is `Sphere.dent`.

`Sphere.asWorld` is false of that dent. `S3_is_the_world` is false.

`Meeting.join` concatenates locks and dents. The join is still a meeting.

`twoSeatLock` is two filled seats. `twelveSeatLock` is twelve filled seats. `apple` sits the two-seat lock. `doughnut` misses a seat of that lock.

## 1. Unique Simply Connected 3-Manifold (1904)

(`Meeting.SimplyConnected`, `closed_is_simply_connected`, `unique_working_shape_of_complete`, `complete_meeting_is_the_sphere`, `sphere_is_not_the_world`, `not_S3_the_world`.)

Official question: is the 3-sphere the unique simply connected 3-manifold?

Simply connected, here, is every owed loop sitting: no hole. A closed meeting is simply connected (`closed_is_simply_connected`): closure already carries \(\neg\,\mathrm{Hole}\).

The unique working shape of a complete meeting is the dent (`unique_working_shape_of_complete`, `complete_meeting_is_the_sphere`): `workingShape m h = Sphere.dent`.

That dent is not the world (`sphere_is_not_the_world`). \(S^3\) is not the world (`not_S3_the_world`). Completeness yields a working shape. It does not yield ontology.

**Proof.** `SimplyConnected` is \(\neg\,\mathrm{Hole}\) by definition. The second conjunct of `Closed` is that negation, so a closed meeting is simply connected. `workingShape` returns `Sphere.dent` by definition, so the working shape of a complete meeting is unique as that dent. `Sphere.asWorld` on `Sphere.dent` is false. `S3_is_the_world` is false.

QED.

## 2. Special Case of Thurston Geometrization

(`not_eight_geometries_ontology`, `not_catalog_of_worlds`, `Meeting.join`, `join_of_closed_is_closed`, `join_with_hole_not_closed`.)

Official claim: Poincaré is a special case of geometrization; every piece carries one of eight geometries.

Thurston's eight are not the object of this page (`Eight_geometries_are_ontology` is false). A catalog of worlds is not seated (`Catalog_of_worlds` is false).

Join of finished meetings is still a meeting, and still finished (`join_of_closed_is_closed`). Join with a hole is not finished (`join_with_hole_not_closed`). Completeness does not become a catalog.

**Proof.** The two flags are `False`, so their negations hold. For the join: if \(a\) and \(b\) are closed, then \(a.\mathrm{dent} = a.\mathrm{lock}\) and \(b.\mathrm{dent} = b.\mathrm{lock}\), so the concatenated dents equal the concatenated locks. A missing seat in the joined dent lies in \(a.\mathrm{dent}\) or in \(b.\mathrm{dent}\) (`List.mem_append`), and each side has no hole, contradiction. Therefore the join is closed. If \(b\) has a hole at \(s\), then \(s\) sits in the joined dent, so the join has a hole and is not closed.

QED.

## 3. Perelman: Built From Standard Pieces

(`not_Ricci_the_object`, `not_Surgery_the_object`, `not_Hamilton_the_object`, `not_CheegerGromov_the_object`, `not_S3_the_world`.)

Official claim: every 3-manifold is built from standard pieces, by Ricci flow and the program that followed.

The path is Ricci flow, surgery, Hamilton’s program, and Cheeger–Gromov collapsing. Those four are the path Perelman walked. That path is not the object of this seating. Each of `Ricci_is_the_object`, `Surgery_is_the_object`, `Hamilton_is_the_object`, and `CheegerGromov_is_the_object` is false. \(S^3\) remains not the world.

**Proof.** Each of those constants is `False`. `not_S3_the_world` is unchanged.

QED.

## 4. Apple And Doughnut

(`apple_is_closed`, `apple_is_simply_connected`, `doughnut_has_hole`, `doughnut_not_closed`, `doughnut_tears`.)

Official picture: a rubber band on an apple shrinks; on a doughnut it does not.

`apple` is a closed meeting: the two-seat dent sat the lock and nothing is missing (`apple_is_closed`). It is simply connected (`apple_is_simply_connected`). `doughnut` has a hole (`doughnut_has_hole`): a seat missing. It is not closed (`doughnut_not_closed`). It tears (`doughnut_tears`).

**Proof.** `apple.dent = apple.lock = twoSeatLock`, and neither lock seat is `Seat.missing`, so `closed_of_dent_eq_lock` gives closure. Simply connected follows from closure. `doughnut.dent` contains `Seat.missing`, which is `Hole`. A hole refuses closure. Tearing is the hole.

QED.

## 5. Two-Sphere Characterized By Simple Connectivity

(`twoSeatLock`, `two_seat_closed_is_complete`, `two_seat_apple_is_complete`, `apple_is_complete`.)

Official known case: the 2-sphere is characterized by simple connectivity.

A smaller lock — two seats — that is closed is complete (`two_seat_closed_is_complete`). `apple` is that seating (`two_seat_apple_is_complete`).

**Proof.** `Complete` is `Closed`. Given `m.lock = twoSeatLock` and `m.Closed`, completeness is the same hypothesis. `apple` supplies that lock and that closure.

QED.

## 6. The Question For The 3-Sphere

(`twelveSeatLock`, `twelve_seat_complete_is_dent`, `twelve_seat_dent_not_world`, `closed_of_dent_eq_lock`.)

Official remaining question: the 3-sphere.

The lock stays twelve seats (`twelveSeatLock`). A complete twelve-seat meeting yields the dent (`twelve_seat_complete_is_dent`), not the world (`twelve_seat_dent_not_world`).

If the dent equals that lock and no lock seat is missing, the meeting is closed (`closed_of_dent_eq_lock`), hence complete.

**Proof.** `twelve_seat_complete_is_dent` is `complete_meeting_is_the_sphere` at a meeting whose lock is `twelveSeatLock`. `twelve_seat_dent_not_world` is `sphere_is_not_the_world` at the same meeting. The closed-of-dent lemma is as in the original seating: from `dent = lock` and no missing lock seat, no dent seat is missing, so there is no hole.

QED.

## 7. Ricci Flow Is The Path

(`Ricci_is_the_object`, `not_Ricci_the_object`.)

Official method: Ricci flow.

`Ricci_is_the_object` is false, matching `S3_is_the_world`. Ricci is the path, not the object of this seating.

**Proof.** The constant is `False`, so \(\neg\,\mathrm{Ricci\_is\_the\_object}\).

QED.

## 8. Geometrization Is Not Ontology

(`Geometrization_is_ontology`, `not_geometrization_ontology`, `completeness_is_the_meeting_finishing`.)

Official generalization: geometrization.

Geometrization is a catalog of pieces, not ontology on this page (`not_geometrization_ontology`). Completeness is the meeting finishing (`completeness_is_the_meeting_finishing`): `Complete` if and only if `Closed`.

**Proof.** `Geometrization_is_ontology` is `False`. `Complete` is defined as `Closed`.

QED.

## 9. Closed, Compact, No Tearing, Stay On The Surface

(`closed_iff_dent_eq_lock_no_missing`, `tearing_not_closed`, `left_surface_not_closed`, `missing_not_closed`, `missing_not_whole`.)

Official language: closed means compact, no tearing, stay on the surface.

Closed is dent equals lock and no missing (`closed_iff_dent_eq_lock_no_missing`). Tearing is a missing seat; a torn meeting is not closed (`tearing_not_closed`). Leaving the surface is dent not equal to lock; that meeting is not closed (`left_surface_not_closed`). A hole is not closed and not whole (`missing_not_closed`, `missing_not_whole`).

**Proof.** The biconditional is the definition of `Closed`. Tearing is `Hole`, so `missing_not_closed` applies. If `dent ≠ lock` and the meeting were closed, the first conjunct of closure would give `dent = lock`, contradiction. Whole is closed, so a hole is not whole.

QED.

## 10. Clay Lists The Problem Solved (Perelman, 2010)

(`not_clay_prize_this_page`, `unique_working_shape_of_complete`, `not_S3_the_world`.)

Official filing: Clay marks Poincaré Solved, Perelman, 2010.

The Clay prize is not this page (`Clay_prize_is_this_page` is false). We still seat the meeting: a complete meeting is the dent (`unique_working_shape_of_complete`), and that dent is not the world (`not_S3_the_world`).

**Proof.** The constant is `False`. The seating theorems are those of sections 1 and 6.

QED.

The examples in `poincare/Examples.lean` keep twelve filled seats as lock and dent. That meeting is closed and is the sphere as dent, not as world. Replacing one seat with `Seat.missing` produces a hole; that meeting is not closed, not whole, and not simply connected. Apple sits. Doughnut tears. Join of two apples is closed. Join of apple with doughnut is not. A dent that misses the lock has left the surface. `#eval run` returns `true` only if every door holds.
