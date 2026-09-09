import bsd.Proof

/-
  OfficialBsd (E : EllipticCurve): leftover α of E has cut z.
  Rank = ord L as ClaySentence.
  EllipticCurve is a structure over ℚ. E produces a seating.
  Rank is leftover. Ord L is cut.
  FromMathlib is furniture. Not imported here: mathlib Cycle
  and the paid pairing Cycle cannot share a file.
  `#eval run` is Bool.
-/

def dropSixth : Shape := thisCurve.seating.drop droppedR

example : thisCurve.seating = thisLock :=
  thisCurve_produces_lock

example : rank thisCurve = thisCurve.seating.belong.map leftoverOf :=
  rank_is_leftover thisCurve

example : ord thisCurve = thisCurve.seating.present.map cutOf :=
  ord_is_cut thisCurve

example : ⟨lockP, 6⟩ ∈ rank thisCurve := by
  decide

example : ⟨13⟩ ∈ ord thisCurve := by
  decide

example : OfficialBsdOn thisCurve.seating :=
  OfficialBsdOn_thisCurve

example : ¬ OfficialBsdOn dropSixth :=
  not_OfficialBsdOn_drop

example : dropSixth.Hole droppedR :=
  hole_is_missing_R

example : ¬ dropSixth.Whole :=
  drop_not_whole thisCurve.seating droppedR (by decide)

example : thisCurve.seating.present.length = 12 ∧
    dropSixth.present.length = 11 :=
  drop_count_12_to_11

example : cl thisCurve.seating.present ⟨13⟩ = some ⟨lockP, 6⟩ :=
  cl_computes

example : inverse thisCurve.seating.present ⟨lockP, 6⟩ = some ⟨13⟩ :=
  inverse_computes

example : ClaySentence thisCurve ⟨lockP, 6⟩ ⟨13⟩ :=
  ⟨inverse_computes, cl_computes⟩

example : ¬ ClayOn dropSixth ⟨lockP, 6⟩ ⟨13⟩ := by
  decide

example : inverse thisCurve.seating.present (leftoverOf (here ⟨6, 13⟩)) =
    some (cutOf (here ⟨6, 13⟩)) :=
  (L_is_modeled_R (here ⟨6, 13⟩) (by decide)).1

example (α : Leftover) (hα : α ∈ rank thisCurve) :
    ∃ z : Cut, ClaySentence thisCurve α z :=
  OfficialBsd thisCurve α hα

def run : Bool :=
  decide (OfficialBsdOn thisCurve.seating) &&
  decide (¬ OfficialBsdOn dropSixth) &&
  decide (dropSixth.Hole droppedR) &&
  decide (¬ dropSixth.Whole) &&
  decide (thisCurve.seating.present.length = 12) &&
  decide (dropSixth.present.length = 11) &&
  decide (cl thisCurve.seating.present ⟨13⟩ = some ⟨lockP, 6⟩) &&
  decide (inverse thisCurve.seating.present ⟨lockP, 6⟩ = some ⟨13⟩) &&
  decide (ClaySentence thisCurve ⟨lockP, 6⟩ ⟨13⟩) &&
  decide (⟨lockP, 6⟩ ∈ rank thisCurve) &&
  decide (⟨13⟩ ∈ ord thisCurve) &&
  decide (¬ ClayOn dropSixth ⟨lockP, 6⟩ ⟨13⟩)

#eval run
