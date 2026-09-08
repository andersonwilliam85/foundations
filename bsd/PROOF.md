# Birch and Swinnerton-Dyer: Written Proof

Objects below are those of `bsd/Proof.lean`, which imports `hodge.Proof` and `poincare.Proof`. The official methods of the literature are not used as objects.

## Definitions

A **cycle** and a **shape** are Hodge's. A shape owes `belong` and sits `present`. A **hole** is an owed cycle that is not sitting. **Whole** means every owed cycle is present. Equivalently: there is no hole (`whole_iff_no_hole`).

`Shape.seated` is `belong` filtered to those in `present`. `Shape.holes` is `belong` filtered to those not in `present`. **Rank** is the length of `seated`. **Order** is the length of `holes`. They are two names for one belonging.

`Shape.presentReading` is the length of `present`. `Shape.join s t` appends `belong` and appends `present`.

A **seat** and a **meeting** are Poincaré's. **Closed** and **Complete** mean the dent sat the lock and nothing is missing. `workingShape` of a complete meeting is `Sphere.dent`. That dent is not the world.

The lock of this page is the same twelve pairings as Hodge: \(\langle 1,2\rangle,\ldots,\langle 12,37\rangle\).

## Door 1

(`not_their_cubic_curve`, `belong_are_pairings`.)

Official statement: whole-number solutions of a cubic in two variables; a curve.

The object is pairings on a lock. Every belonging cycle is a pairing \(\langle\mathrm{left},\mathrm{right}\rangle\). The curve names the lock.

**Proof.** `theirCubicCurveIsTheObject` is false. A cycle is its two numbers by the definition of `Cycle`.

QED.

## Door 2

(`rank_is_seated_count`.)

Official name: the rank of rational points.

Rank is how many owed cycles are sitting: `s.rank = s.seated.length`.

**Proof.** Definition.

QED.

## Door 3

(`experimental_count_is_present_reading`.)

Machine count: points mod \(p\).

The count is a reading of present pairings: `s.presentReading = s.present.length`.

**Proof.** Definition.

QED.

## Door 4

(`origin_reading_is_order`.)

Wiles's statement reads a series near \(s=1\) and calls it zeta.

The origin reading is order, and order is owed holes: `s.order = s.holes.length`.

**Proof.** Definition.

QED.

## Door 5

(`origin_hole_not_whole`, `drop_is_hole`, `drop_not_whole`, `drop_belonging_in_holes`.)

Wiles states \(\zeta(1)=0\) implies infinitely many rational points.

An origin hole is not Whole. If \(c\) belongs, `s.drop c` has a hole at \(c\), is not Whole, and \(c\) is in `holes`.

**Proof.** From `whole_iff_no_hole`, a hole refuses Whole. Hodge already gives the hole after a drop. Membership in `holes` is belonging and not present, which is the hole.

QED.

## Door 6

(`no_origin_hole_is_whole`, `whole_order_zero`, `whole_rank_eq_lock`, `whole_holes_nil`, `whole_every_belong_seated`, `whole_finite_lock`.)

Wiles states \(\zeta(1)\neq 0\) implies finitely many rational points.

If there is no origin hole, the shape is Whole. Then `holes = []`, order is \(0\), every belonging cycle is seated, and rank equals the length of `belong`. The lock is a list. That is the finite lock.

**Proof.** `whole_iff_no_hole` gives Whole from no hole. Under Whole, the seated filter keeps every owed cycle, so its length is `belong.length`. The holes filter keeps none, so its length is \(0\) and the list is empty.

QED.

## Door 7

(`two_names_when_whole`.)

Millennium line: analytic rank equals algebraic rank.

When the shape is Whole, order is \(0\) and rank is the lock. Two names for one belonging. Drop a seated belonging cycle and a hole appears: rank is no longer the full lock, order is no longer \(0\).

**Proof.** Door 6, plus Door 5.

QED.

## Door 8

(`refuse_analytic_continuation`, `refuse_functional_equation`, `refuse_holomorphic_continuation`, `refuse_euler_product`.)

The literature uses analytic continuation, a functional equation, holomorphic continuation, and an Euler product.

Those are the methods of the series. Each of those flags is false on this page.

**Proof.** Definition. The series methods are not objects of this seating.

QED.

## Door 9

(`refuse_leading_coefficient`, `refuse_sha`, `refuse_regulator`, `refuse_period`, `refuse_tamagawa`, `refuse_torsion`, `join_whole`, `join_rank_of_whole`.)

The official statement refines the leading coefficient into letters: Sha, regulator, periods, Tamagawa, torsion.

Those letters are not objects. Two Whole shapes join to a Whole shape. If both are Whole, the ranks add by list-append of the locks.

**Proof.** Each letter-flag is false. For join: a cycle in the appended `belong` sits in the first lock or the second; Whole on that side puts it in that side's `present`; append puts it in the joined `present`. Rank of a Whole shape is `belong.length`, and length adds under append.

QED.

## Door 10

(`not_their_abelian_variety`, `not_their_point_group`, `refuse_their_group_law`, `shape_whole_iff_owed_present`.)

The official statement files an abelian variety, a group of rational points, a group law, and a finitely generated decomposition.

The object is the Shape. Whole if and only if every owed cycle is present. The group and the group law are the literature's language for the same lock.

**Proof.** The three flags are false. The biconditional is Hodge's `whole_iff_every_belonging_present`.

QED.

## Door 11

(`no_general_method`, `this_lock_is_whole`.)

Hilbert's tenth is the older hunger: no general method for every equation. Wiles says no method is known for the elusive case, and that a stronger form would hand them generators.

We do not claim a general method for every lock. We seat this lock. `thisLock` is Whole.

**Proof.** `generalMethodForEveryLock` is false. `thisLock` has `present = belong`, so it is Whole.

QED.

## Door 12

(`twelve_pairings_stay_the_lock`.)

Twelve belonging pairings stay the lock: \(\langle 1,2\rangle\) through \(\langle 12,37\rangle\). The length is \(12\).

**Proof.** The list is written. Its length is \(12\).

QED.

## Origin meeting

(`origin_closed`, `origin_complete`, `origin_is_the_dent`, `origin_dent_is_not_the_world`, `origin_missing_not_closed`, `origin_missing_not_whole`.)

A finished meeting at the origin (twelve filled seats, dent sat the lock, nothing missing) is Complete. `workingShape` is `Sphere.dent`. That dent is not the world. A missing origin seat is a hole; that meeting is not closed and not whole.

**Proof.** Poincaré: `closed_of_dent_eq_lock`, `complete_meeting_is_the_sphere`, `sphere_is_not_the_world`, `missing_not_closed`, `missing_not_whole`.

QED.

## Official extras (Wiles)

(`refuse_their_other_rooms`, `refuse_their_how`, `refuse_special_value_elaborations`, `refuse_function_field_analog`, `refuse_higher_dimensional_hunt`, `refuse_special_family_test`, `refuse_effective_generator_method`.)

Wiles also names: genus-zero congruences and genus-two finiteness; descent and the tangent method; holomorphic continuation as a proved property of the series; the Taylor shape of that series at one; the completed series at the bad places; the same claim over other fields and for larger groups; later special-value elaborations; a function-field analog; an effective hunt for generators once the coefficient is integral; special-family tests; a hunt in higher dimension for rational curves and larger groups.

Those rooms are the literature's. Each flag is false on this page. Rank and order remain two names for one belonging.

**Proof.** Definition.

QED.

The examples in `bsd/Examples.lean` sit the twelve pairings, drop \(\langle 6,13\rangle\), join two whole halves, join a whole lock to a disjoint holed lock, and walk every official door. `#eval run` prints `ok`.
