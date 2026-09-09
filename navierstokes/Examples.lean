import navierstokes.Proof

open scoped ContDiff
open Set

/-
  OfficialNS produces leftover (leftover T := cl). IsLeftover witnesses.
  Continuation through T is the pairing. A hole is a missing R.
  Official Smooth: leftover with continuation-R.
  Thin / C / D: leftover on [0, 1); continuation-R missing.
  Fefferman decay on the force: SpatialSchwartz / periodic analog
  on sitting times. On [0, 1) jumpForce is 0 — that decays.
  (A) and (B): leftover produced from each admissible unforced datum
  has OfficialSmooth. leftover T := cl. Not one rest leftover.
  jumpForce is not spacetime-smooth. Forced MissingR is not Unforced.
  Official Smooth is not Smooth. Euler door empty.
-/

/-- Prize A. Leftover from each admissible unforced open datum. -/
example : clayA :=
  fefferman_A

example : OfficialA (restOpenDatum.leftover 1) :=
  fefferman_A restOpenDatum 1 one_pos

example : OfficialA (restOpen.leftover 1) :=
  leftover_officialA restOpen one_pos restOpen_open restOpen_unforced restOpen_smooth

example : (restOpen.leftover 1).u0 = restOpen.u0 :=
  leftover_u0 restOpen 1

example : (restOpenDatum.leftover 1).u0 = restOpenDatum.u0 :=
  restOpenDatum.leftover_from_datum 1

/-- Prize B. Leftover from each admissible unforced periodic datum. -/
example : clayB :=
  fefferman_B

example : OfficialB (restPeriodicDatum.leftover 1) :=
  fefferman_B restPeriodicDatum 1 one_pos

example : OfficialB (restPeriodic.leftover 1) :=
  leftover_officialB restPeriodic one_pos restPeriodic_periodic
    restPeriodic_unforced restPeriodic_smooth

/-- jumpForce leftover decays on [0, 1) and has MissingR. Not their (C): force jumps. -/
example : forcedOpenHole.Open ∧ forcedOpenHole.IsLeftover 1 ∧
    forcedOpenHole.FeffermanDecay ∧ forcedOpenHole.MissingR :=
  ⟨forcedOpenHole_open, forcedOpenHole_is_leftover,
    forcedOpenHole_feffermanDecay, forcedOpenHole_missing_R⟩

example : ¬ forcedOpenHole.SpacetimeSmoothForce :=
  forcedOpenHole_not_spacetimeSmoothForce

/-- jumpForce leftover is not their (D). Force is not spacetime-smooth. -/
example : forcedPeriodicHole.Periodic ∧ forcedPeriodicHole.IsLeftover 1 ∧
    forcedPeriodicHole.FeffermanDecay ∧ forcedPeriodicHole.MissingR :=
  ⟨forcedPeriodicHole_periodic, forcedPeriodicHole_is_leftover,
    forcedPeriodicHole_feffermanDecay, forcedPeriodicHole_missing_R⟩

example : ¬ forcedPeriodicHole.SpacetimeSmoothForce :=
  forcedPeriodicHole_not_spacetimeSmoothForce

/-- Rest open sits and is Smooth. Not the prize. -/
example : restOpen.Open ∧ restOpen.Unforced ∧ restOpen.Satisfies ∧ restOpen.Smooth :=
  ⟨restOpen_open, restOpen_unforced, restOpen_satisfies, restOpen_smooth⟩

example : restOpen.InitialPopulated :=
  rest_initial _

example : ¬ restOpen.BlowUp :=
  restOpen_not_blowup

/-- Rest periodic sits and is Smooth. Not the prize. -/
example : restPeriodic.Periodic ∧ restPeriodic.Unforced ∧ restPeriodic.Smooth :=
  ⟨restPeriodic_periodic, restPeriodic_unforced, restPeriodic_smooth⟩

example : ¬ restPeriodic.BlowUp :=
  restPeriodic_not_blowup

/-- OfficialNS produces leftover. IsLeftover witnesses. leftover T := cl. -/
example : (restOpen.leftover 1).IsLeftover 1 :=
  leftover_isLeftover restOpen one_pos

example : restOpenCut = restOpen.leftover 1 :=
  restOpenCut_produced

/-- cl of leftover is leftover. Last projection wins. -/
example : (restOpen.leftover 1).leftover (1 / 2) = restOpen.leftover (1 / 2) :=
  leftover_leftover restOpen 1 (1 / 2)

/-- Leftover of any Smooth sit is OfficialSmooth. OfficialSmooth ≠ Smooth. -/
example : (restOpen.leftover 1).OfficialSmooth :=
  leftover_officialSmooth_of_smooth restOpen one_pos restOpen_smooth

/-- Leftover is seated on [0, T). Continuation is not stored. -/
example : restOpenCut.IsLeftover 1 :=
  restOpenCut_is_leftover

/-- cl projects rest onto [0, 1). inverse reconstructs the continuation. -/
example : inverse restOpenCut 1 restOpen :=
  restOpen_inverse

/-- Official Smooth: leftover whose continuation-R sits. (A) seats here. -/
example : restOpenCut.OfficialSmooth :=
  restOpenCut_officialSmooth

example : restPeriodicCut.OfficialSmooth :=
  restPeriodicCut_officialSmooth

example : ¬ restOpenCut.MissingR :=
  restOpenCut_not_missingR

/-- Forced leftover is produced, not a hand-built Ico sit. -/
example : forcedOpenHole = forcedOpenSit.leftover 1 :=
  forcedOpenHole_produced

example : (forcedOpenSit.leftover 1).IsLeftover 1 :=
  leftover_isLeftover forcedOpenSit one_pos

/-- Thin / C: leftover on [0, 1); force decays; continuation-R missing. -/
example : forcedOpenHole.IsLeftover 1 ∧ forcedOpenHole.FeffermanDecay ∧
    forcedOpenHole.MissingR ∧ ¬ forcedOpenHole.OfficialSmooth :=
  ⟨forcedOpenHole_is_leftover, forcedOpenHole_feffermanDecay,
    forcedOpenHole_missing_R, forcedOpenHole_not_officialSmooth⟩

example : forcedPeriodicHole.FeffermanDecay ∧ forcedPeriodicHole.MissingR ∧
    ¬ forcedPeriodicHole.OfficialSmooth :=
  ⟨forcedPeriodicHole_feffermanDecay, forcedPeriodicHole_missing_R,
    forcedPeriodicHole_not_officialSmooth⟩

/-- Forced MissingR is not Unforced. It does not refute (A). -/
example : forcedOpenHole.MissingR ∧ ¬ OfficialA forcedOpenHole :=
  missingR_forced_not_refute_A

example : forcedPeriodicHole.MissingR ∧ ¬ OfficialB forcedPeriodicHole :=
  missingR_forced_not_refute_B

/-- Leftover is not Global. Official Smooth is the pairing, not a tag. -/
example : ¬ restOpenCut.Global :=
  restOpenCut_not_global

example : restOpenCut.OfficialSmooth ∧ ¬ restOpenCut.Smooth :=
  ⟨restOpenCut_officialSmooth, restOpenCut_not_smooth⟩

/-- Open is not periodic. -/
example : ¬ (restOpen.Open ∧ restOpen.Periodic) :=
  fun ⟨ho, hp⟩ => open_not_periodic ho hp

/-- Blow-up is not Smooth. -/
example (sol : OfficialNS) (h : sol.BlowUp) : ¬ sol.Smooth :=
  blowup_not_smooth sol h

/-- Operators on the rest field are zero. -/
example (t : Time) (x : Place) :
    timeDeriv restOpen.velocity t x = 0 :=
  timeDeriv_const 0 t x

example (t : Time) (x : Place) :
    viscousLap restOpen.velocity t x = 0 :=
  viscousLap_const 0 t x

example (x : Place) :
    divergence restOpen.u0 x = 0 :=
  divergence_const 0 x

example (t : Time) (x : Place) :
    gradPressure restOpen.pressure t x = 0 :=
  gradPressure_const 0 t x

/-- Euler is not this prize. The door is empty. -/
example (e : EulerDoor) : False :=
  nomatch e
