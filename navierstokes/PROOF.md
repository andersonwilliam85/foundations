# Navier–Stokes: Written Proof

Objects below are those of `Navierstokes/Proof.lean`. The official methods of the literature are not used as objects.

## Definitions

A **lock kind** (`LockKind`) is `open` or `periodic`. Two locks.

A **force** (`Force`) is `none`, or `outside` a cycle. An outside pairing.

A **flow** (`Flow`) carries:

- `lock`: the Hodge shape the flow owes.
- `instants`: a list of shapes.
- `force`: none, or an outside pairing.
- `kind`: open lock or periodic lock.

Place-and-time is a Poincaré `Meeting`. **Velocity** is the dent. **Pressure** is the lock. Those are two readings of one meeting. Fields are a language in Fefferman's statement.

**Incompressible** (`Incompressible`): the dent owes exactly the lock, \(m.\mathrm{dent} = m.\mathrm{lock}\).

The **first instant** (`Flow.firstInstant`) is the head of `instants`. **Initial** (`Flow.Initial`) is that head.

**Unforced** (`Flow.Unforced`): `force = none`. **Forced** (`Flow.Forced`): an outside cycle sits.

**Smooth** (`Flow.Smooth`): every instant is `Shape.Whole`. **Blow-up** (`Flow.BlowUp`): some instant has a `Shape.Hole`. A blow-up is not the world.

`Shape.join` concatenates owed with owed, sitting with sitting.

**Statement A–D** are Fefferman's four doors, seated as claims. The Clay prize is not claimed (`clayPrizeClaimed` is false).

`lockPairings` is twelve belonging pairings. That list stays the lock.

**Early hole** (`EarlyHole`): a blow-up, and the meeting is not closed.

**Small** (`Shape.Small`): the lock owes at most one cycle.

A **finished** flow (`Finished`) is a Poincaré meeting that closed.

## Line 1

(`two_readings_of_one_meeting`, `fields_not_installed`.)

Velocity is the dent. Pressure is the lock. They are two readings of one meeting. Fields are a language in the statement; this seating does not use them as objects.

**Proof.** Unfold the readings. `fieldsInstalled` is false.

QED.

## Line 2

(`incompressible_of_dent_eq_lock`, `incompressible_missing_not_closed`.)

If the dent equals the lock, the meeting is incompressible. If that meeting still has a missing seat, it is not closed.

**Proof.** The first claim is the definition. The second is `missing_not_closed`.

QED.

## Line 3

(`initial_is_first`, `empty_has_no_initial`.)

The initial condition is the first instant. An empty list of instants has no initial shape.

**Proof.** `Initial` is `head? = some s`. The empty list has `head? = none`.

QED.

## Line 4

(`unforced_of_none`, `unforced_not_forced`.)

No outside pairing is unforced. Unforced is not forced. A and B take none. C and D allow an outside pairing.

**Proof.** Unfold `Unforced`. If `force = none` and `force = outside c`, those constructors refuse each other.

QED.

## Line 5

(`viscosity_not_installed`, `euler_not_this_prize`.)

Viscosity is in Fefferman's statement. It is not the object of this seating. Euler is not this prize.

**Proof.** Both claims are false as installed objects. That is the seating.

QED.

## Line 6

(`decay_stranger_not_hole`.)

A stranger pairing — a cycle the shape does not owe — is not a hole.

**Proof.** A hole requires belonging. A stranger is not in `belong`.

QED.

## Line 7

(`smooth_of_every_instant_whole`, `drop_instant_not_smooth`, `blowup_not_smooth`, `missing_is_not_smooth_seats`.)

If every instant is Whole, the flow is Smooth. If an instant is `s.drop c` for a belonging cycle \(c\), that instant is a Hole (`drop_is_hole`) and the flow is not Smooth (`drop_not_whole`). A missing seat is not a smooth meeting.

**Proof.** Smooth is the universal over instants. A dropped belonging cycle is a hole; wholeness would force it present. A blow-up supplies such a hole. `NoMissing` is the negation of `Meeting.Hole`.

QED.

## Line 8

(`join_whole_of_whole`.)

The join of two whole shapes is whole. The bound stays when every piece stays whole.

**Proof.** Membership in a concatenation is membership in the left or the right. Wholeness of each piece supplies presentness. Concatenate those.

QED.

## Line 9

(`open_not_periodic`.)

Open lock and periodic lock are two locks. A flow is not both.

**Proof.** `LockKind.open = LockKind.periodic` has no constructor.

QED.

## Line 10

(`statementA_is_the_claim`.)

Statement A is the claim: every unforced open-lock flow is Smooth. The claim is seated. It is not proved as the Clay prize.

**Proof.** The biconditional is the definition.

QED.

## Line 11

(`statementB_is_the_claim`.)

Statement B is the claim: every unforced periodic-lock flow is Smooth. The claim is seated. It is not proved as the Clay prize.

**Proof.** The biconditional is the definition.

QED.

## Line 12

(`statementC_seated`.)

There sits a forced open-lock flow with a Hole.

**Proof.** `forcedOpenHole` owes `oneCycle`, presents nothing, carries an outside pairing, and is open. That is a hole, a force, and an open lock.

QED.

## Line 13

(`statementD_seated`.)

There sits a forced periodic-lock flow with a Hole.

**Proof.** `forcedPeriodicHole` is the same seating with a periodic lock.

QED.

## Line 14

(`clay_prize_not_claimed`.)

Clay asks for one of A–D. All four sit. The Clay prize is not claimed from this page.

**Proof.** `clayPrizeClaimed` is false.

QED.

## Line 15

(`two_dimensions_known`, `three_dimensions_are_the_lock`, `twelve_pairings_stay`.)

Two dimensions are known. Three dimensions are the lock. Twelve belonging pairings stay: \(\langle 1,2\rangle\) through \(\langle 12,37\rangle\).

**Proof.** The first two are seated true. The list has length 12.

QED.

## Line 16

(`hole_before_meeting_finishes`.)

A hole before the meeting finishes is a blow-up together with a meeting that is not closed.

**Proof.** Conjunction of the two hypotheses.

QED.

## Line 17

(`small_whole_stays_whole`, `small_drop_not_whole`.)

A small Whole lock stays Whole. Drop a belonging cycle and it does not.

**Proof.** The first is identity on `Shape.Whole`. The second is `drop_not_whole`.

QED.

## Finished meeting

(`finished_is_complete`, `finished_working_shape`, `finished_not_world`, `missing_not_finished`, `blowup_not_the_world`.)

A finished meeting is Complete. `workingShape` is `Sphere.dent`. That dent is not the world. A missing seat refuses a finished flow. `blowUpIsTheWorld` is false.

**Proof.** Reuse Poincaré: `complete_meeting_is_the_sphere`, `sphere_is_not_the_world`, `missing_not_closed`. `blowUpIsTheWorld` is false.

QED.

The examples in `Navierstokes/Examples.lean` walk each door. A seating that drops a pairing sits beside each one. The twelve pairings stay the lock.
