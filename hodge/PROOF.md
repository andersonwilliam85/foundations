# Hodge: Written Proof

Objects below are those of `hodge/Proof.lean`. The official methods of the literature are not used as objects.

## Definitions

A **cycle** (`Cycle`) is a closing relationship: a pairing of two natural numbers, `left` and `right`.

A **shape** (`Shape`) carries two lists of cycles:

- `belong`: the cycles the shape owes. The lock (`Shape.lock`) is this list.
- `present`: the cycles that are sitting.

A cycle **belongs** when it is a member of `belong`. A cycle is **present** when it is a member of `present`. Belonging is not taste. If the shape lists the cycle among those owed, the cycle is owed.

A **hole** (`Shape.Hole`) at a cycle \(c\) is the conjunction

\[
c \in s.\mathrm{belong} \;\land\; c \notin s.\mathrm{present}.
\]

A shape is **whole** (`Shape.Whole`) when every belonging cycle is present:

\[
\forall\, c,\; c \in s.\mathrm{belong} \;\Rightarrow\; c \in s.\mathrm{present}.
\]

`whole_iff_every_belonging_present` is that biconditional. `whole_iff_no_hole` is the equivalent: Whole if and only if there is no hole.

`Shape.drop s c` is the shape with the same `belong` and with \(c\) removed from `present`. `drop_is_hole` and `drop_not_whole`: if \(c\) belongs, the drop has a hole at \(c\) and is not Whole.

`present_eq_belong_whole`: if `present = belong`, the shape is Whole.

`Shape.join s t` concatenates owed with owed, sitting with sitting. `join_whole_of_whole`: two Whole shapes join to a Whole shape.

`Shape.seated` is `belong` filtered to those in `present`. `Shape.rank` is the length of `seated`.

`HodgeNamed` is membership in `belong`. `AlgebraicNamed` is membership in `present`.

`Shape.Small`: the lock owes fewer than four pairings.

The lock of this page is twelve pairings: \(\langle 1,2\rangle,\ldots,\langle 12,37\rangle\) (`lockPairings`).

## Door 1

(`not_their_equation_system`, `lock_is_what_is_owed`.)

Official statement: the topology of the solution set of a system of algebraic equations.

The lock is what the shape owes: `s.lock = s.belong`. The equation system names the lock.

**Proof.** `theirAlgebraicEquationSystemIsTheObject` is false. `Shape.lock` is `belong`.

QED.

## Door 2

(`not_a_second_topology`, `present_is_not_a_hole`, `how_much_of_the_lock_sat`.)

Official ask: how much of that topology can be defined by further algebraic equations.

Present is what sat. A sitting cycle is not a hole. A cycle is seated if and only if it belongs and is present. Further equations are not a second topology.

**Proof.** A hole requires not-present. Membership in `seated` is the filter of `belong` by presentness.

QED.

## Door 3

(`small_whole_stays_whole`, `small_lock_is_small`, `small_lock_is_whole`.)

Known case: special when the dimension is less than four.

A small lock owes fewer than four pairings. `smallLock` owes three, all sitting. It is Small. It is Whole. A small Whole lock stays Whole.

**Proof.** Length of `threePairings` is three, which is less than four. `present = belong`, so Whole. The stay is the same Whole.

QED.

## Door 4

(`four_is_not_a_new_object`, `not_unsolved_as_unseated`, `four_pairings_can_be_whole`, `four_pairings_can_be_holed`, `four_is_the_same_seating`.)

The official statement lists dimension four as unknown.

Four pairings is still this seating. `fourWhole` is Whole. `fourHoled` is not. Four is not a new object. Unknown is not filed as unseated. Whole is still: every belonging cycle is present.

**Proof.** The two flags are false. `fourWhole` has `present = belong`. `fourHoled` is `fourWhole.drop fourLast`; `drop_not_whole` applies. The biconditional is the definition of Whole.

QED.

## Door 5

(`join_whole_of_whole`, `glued_wholes_are_whole`.)

The official statement approximates a shape by gluing simple building blocks of increasing dimension.

The join of two Whole shapes is Whole.

**Proof.** Membership in a concatenation is membership in the left or the right. Wholeness of each piece supplies presentness. Concatenate those.

QED.

## Door 6

(`refuse_extra_as_the_hole`, `refuse_extra_as_geometric_hole`, `extra_not_hole`, `vacuous_extras_whole`.)

The literature added a generalization with pieces that have no geometric interpretation.

Extras sitting that the lock never owed are not holes. An empty lock with extras sitting is Whole (vacuous). Those extras are not "the hole."

**Proof.** A hole requires belonging. A stranger is not in `belong`. An empty `belong` has no member, so every belonging-implies-present is vacuous. Both flags are false.

QED.

## Door 7

(`not_their_variety`, `twelve_pairings_stay`, `this_lock_is_whole`, `this_lock_is_finite`.)

The official statement names projective algebraic varieties as particularly nice spaces.

The object is a finite owed lock. Twelve pairings stay. `thisLock` is Whole. The variety names a nice space in the literature.

**Proof.** `lockPairings.length = 12`. `thisLock` has `present = belong`. The variety flag is false.

QED.

## Door 8

(`refuse_cohomology`, `seeming_belonging_is_present_or_hole`, `whole_iff_hodge_named_algebraic`, `q_linear_combination_is_join`.)

Official line: Hodge cycles are rational linear combinations of algebraic cycles.

A seeming-belonging (`HodgeNamed`) is actually present (`AlgebraicNamed`), or it is a Hole. Whole if and only if every Hodge-named cycle is an algebraic-named sitting. The \(\mathbb{Q}\)-linear combination is the join of present cycles: `(s.join t).present = s.present ++ t.present`. Cohomology is a language in the literature; this seating does not use it as an object.

**Proof.** If \(c\) belongs, it is present or not. If not, that is a Hole. The Whole biconditional is the definition under those two names. Join appends `present`. `cohomologyInstalled` is false.

QED.

## Door 9

(`not_prestige_class`, `class_name_not_present_is_hole`.)

The official statement says the geometric origins are obscured.

A class-name that is not present is a Hole. The miss is the relationship.

**Proof.** `Shape.Hole` is belonging and not present. The prestige flag is false.

QED.

## Door 10

(`rank_is_seated_count`, `belong_grows_under_join`, `join_one_cycle_raises_sitting`.)

The official statement grows dimension by joining building blocks.

Rank is how many owed cycles are sitting. Join grows the length of `belong`. Joining a one-cycle Whole raises the sitting count by one.

**Proof.** Rank is `seated.length`. Length adds under list-append. A singleton `present` appends one.

QED.

The examples in `hodge/Examples.lean` seat the twelve belonging pairings, then walk every official door. `#eval run` is the run.
