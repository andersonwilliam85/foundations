import bsd.Proof

/-
  OfficialBsd (E : EllipticCurve) (hE : E.IsElliptic): leftover α of E has cut z.
  Rank = ord L as ClaySentence.
  E is a curve over Q. Leftover of E(Q) produces the seating.
  thisCurve produces thisLock. Not two flags. Not Shape.
  Rank is leftover. Ord L is cut.
  FromMathlib is furniture. Not imported here: mathlib Cycle
  and the paid pairing Cycle cannot share a file.
  `#eval run` is Bool.
-/

def dropSixth : Shape := thisCurve.produce.drop droppedR

example : thisCurve.A = 0 :=
  rfl

example : thisCurve.B = 1 :=
  rfl

example : thisCurve.leftoverR = leftoverSeq :=
  rfl

example : thisCurve.IsElliptic :=
  thisCurve_isElliptic

example : thisCurve.produce = thisLock :=
  thisCurve_produces_lock

example : rank thisCurve = thisCurve.produce.belong.map leftoverOf :=
  rank_is_leftover thisCurve

example : RankReading = Leftover :=
  rank_reading_is_leftover

example : leftoverSix.r = 6 :=
  leftover_does_not_store_cut.1

example : ord thisCurve = thisCurve.produce.present.map cutOf :=
  ord_is_cut thisCurve

example : ⟨lockP, 6⟩ ∈ rank thisCurve := by
  decide

example : leftoverSix ∈ rank thisCurve := by
  decide

example : ⟨13⟩ ∈ ord thisCurve := by
  decide

example : OfficialBsdOn thisCurve.produce :=
  OfficialBsdOn_thisCurve

example : ¬ OfficialBsdOn dropSixth :=
  not_OfficialBsdOn_drop

example : leftoverSix ∈ dropSixth.belong.map leftoverOf ∧
    inverse dropSixth.present leftoverSix = none :=
  leftover_owed_after_drop

example : dropSixth.Hole droppedR :=
  hole_is_missing_R

example : ¬ dropSixth.Whole := by
  decide

example : thisCurve.produce.present.length = 12 ∧
    dropSixth.present.length = 11 :=
  thisCurve_drop_count_12_to_11

example : cl thisCurve.produce.present ⟨13⟩ = some ⟨lockP, 6⟩ :=
  cl_computes

example : inverse thisCurve.produce.present ⟨lockP, 6⟩ = some ⟨13⟩ :=
  inverse_computes

example : ClaySentence thisCurve ⟨lockP, 6⟩ ⟨13⟩ :=
  ⟨inverse_computes, cl_computes⟩

example : ¬ ClayOn dropSixth ⟨lockP, 6⟩ ⟨13⟩ := by
  decide

example : inverse thisCurve.produce.present (leftoverOf (here ⟨6, 13⟩)) =
    some (cutOf (here ⟨6, 13⟩)) :=
  (L_is_modeled_R thisCurve (here ⟨6, 13⟩) (by decide)).1

example (α : Leftover) (hα : α ∈ rank thisCurve) :
    ∃ z : Cut, ClaySentence thisCurve α z :=
  OfficialBsd thisCurve thisCurve_isElliptic α hα

def run : Bool :=
  decide (thisCurve.A = 0) &&
  decide (thisCurve.B = 1) &&
  decide (thisCurve.leftoverR = leftoverSeq) &&
  decide thisCurve.IsElliptic &&
  decide (thisCurve.produce = thisLock) &&
  decide (OfficialBsdOn thisCurve.produce) &&
  decide (¬ OfficialBsdOn dropSixth) &&
  decide (dropSixth.Hole droppedR) &&
  decide (¬ dropSixth.Whole) &&
  decide (thisCurve.produce.present.length = 12) &&
  decide (dropSixth.present.length = 11) &&
  decide (cl thisCurve.produce.present ⟨13⟩ = some ⟨lockP, 6⟩) &&
  decide (inverse thisCurve.produce.present ⟨lockP, 6⟩ = some ⟨13⟩) &&
  decide (ClaySentence thisCurve ⟨lockP, 6⟩ ⟨13⟩) &&
  decide (⟨lockP, 6⟩ ∈ rank thisCurve) &&
  decide (leftoverSix ∈ rank thisCurve) &&
  decide (leftoverSix.r = 6) &&
  decide (inverse dropSixth.present leftoverSix = none) &&
  decide (⟨13⟩ ∈ ord thisCurve) &&
  decide (¬ ClayOn dropSixth ⟨lockP, 6⟩ ⟨13⟩)

#eval run
