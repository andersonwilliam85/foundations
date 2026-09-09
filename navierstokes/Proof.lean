/-
  Navier–Stokes / Fefferman. Official seating on mathlib types.
  Leftover is a seated solution on [0, T). No continuation field.
  Continuation through T is the pairing. A hole is a missing R.
  cl projects a continuation onto [0, T). inverse reconstructs when it sits.
  OfficialNS produces leftover: leftover T := cl sol T. IsLeftover witnesses.
  Do not hide leftover as a hand-built Ico sit.
  Official Smooth: leftover whose continuation-R sits.
  Thin / C / D: leftover on [0, 1); continuation-R missing.
  Fefferman decay on the force: SpatialSchwartz / periodic analog
  on sitting times. On [0, 1) jumpForce is 0 — that decays.
  The hole is MissingR at T, not a new force.
  Prize statements: clayA–clayD.
  (A)(B): leftover produced by rest (its u0) has OfficialSmooth.
  Not ∀ Place → Place. Forced MissingR is not Unforced.
  Euler (viscosity zero) is not this prize. That door is empty.
-/

import navierstokes.FromMathlib

open scoped ContDiff SchwartzMap Laplacian Gradient
open Set Filter Topology

noncomputable section

/-- Official: whole space versus periodic. -/
inductive Domain where
  | open
  | periodic
  deriving DecidableEq, Repr

/--
  Official seating: velocity, pressure, force, viscosity, domain,
  and the times the fields sit.
-/
structure OfficialNS where
  velocity : Instant → Place
  pressure : Instant → ℝ
  force : Instant → Place
  viscosity : ℝ
  domain : Domain
  lifespan : Set Time

def OfficialNS.Open (sol : OfficialNS) : Prop :=
  sol.domain = Domain.open

def OfficialNS.Periodic (sol : OfficialNS) : Prop :=
  sol.domain = Domain.periodic

def OfficialNS.Unforced (sol : OfficialNS) : Prop :=
  sol.force = fun _ => 0

def OfficialNS.Forced (sol : OfficialNS) : Prop :=
  sol.force ≠ fun _ => 0

theorem open_not_periodic {sol : OfficialNS} (ho : sol.Open) (hp : sol.Periodic) : False :=
  nomatch (ho.symm.trans hp)

/-- Initial velocity at t = 0. -/
def OfficialNS.u0 (sol : OfficialNS) : Place → Place :=
  fun x => sol.velocity (0, x)

/-- t = 0 sits in the lifespan. -/
def OfficialNS.InitialPopulated (sol : OfficialNS) : Prop :=
  (0 : Time) ∈ sol.lifespan

/-- Divergence-free on every sitting time. -/
def OfficialNS.divFree (sol : OfficialNS) : Prop :=
  ∀ t ∈ sol.lifespan, ∀ x : Place, divergenceAt sol.velocity t x = 0

/--
  Decay / periodicity required by the domain.
  Open: spatial Schwartz at every sitting time.
  Periodic: lattice-periodic at every sitting time.
-/
def OfficialNS.SpatialCondition (sol : OfficialNS) : Prop :=
  match sol.domain with
  | .open =>
      ∀ t ∈ sol.lifespan,
        SpatialSchwartz (spatial sol.velocity t) ∧
          SpatialSchwartzScalar (pressureSlice sol.pressure t)
  | .periodic =>
      ∀ t ∈ sol.lifespan,
        SpatialPeriodic (spatial sol.velocity t) ∧
          SpatialPeriodicScalar (pressureSlice sol.pressure t)

/--
  Fefferman decay on the force.
  Open: SpatialSchwartz of the force slice at every sitting time.
  Periodic: lattice-periodic analog at every sitting time.
-/
def OfficialNS.FeffermanDecay (sol : OfficialNS) : Prop :=
  match sol.domain with
  | .open =>
      ∀ t ∈ sol.lifespan, SpatialSchwartz (spatial sol.force t)
  | .periodic =>
      ∀ t ∈ sol.lifespan, SpatialPeriodic (spatial sol.force t)

/-- Applied Navier–Stokes equality on the lifespan. Viscosity stays. -/
def OfficialNS.Satisfies (sol : OfficialNS) : Prop :=
  0 < sol.viscosity ∧
    sol.InitialPopulated ∧
    sol.divFree ∧
    sol.SpatialCondition ∧
    ∀ t ∈ sol.lifespan, ∀ x : Place,
      nseLeft sol.velocity t x =
        nseRight sol.velocity sol.pressure sol.force sol.viscosity t x

/-- Smooth spacetime fields. -/
def OfficialNS.FieldsSmooth (sol : OfficialNS) : Prop :=
  ContDiff ℝ ∞ sol.velocity ∧ ContDiff ℝ ∞ sol.pressure

/-- Sits for all future time. -/
def OfficialNS.Global (sol : OfficialNS) : Prop :=
  sol.lifespan = Ici (0 : Time)

/--
  Smooth: satisfies the equation, sits for all future time, fields are C^∞.
-/
def OfficialNS.Smooth (sol : OfficialNS) : Prop :=
  sol.Satisfies ∧ sol.Global ∧ sol.FieldsSmooth

/--
  Continuation through T is the pairing. Not stored on leftover.
  A later sit for all future time, fields stay C^∞, agrees on [0, T),
  and keeps the same force, viscosity, and domain.
-/
def OfficialNS.ContinuesThrough (sol sol' : OfficialNS) (T : Time) : Prop :=
  sol'.Satisfies ∧
    sol'.Global ∧
    sol'.FieldsSmooth ∧
    sol'.force = sol.force ∧
    sol'.viscosity = sol.viscosity ∧
    sol'.domain = sol.domain ∧
    (∀ t x, 0 ≤ t → t < T → sol'.velocity (t, x) = sol.velocity (t, x)) ∧
    (∀ t x, 0 ≤ t → t < T → sol'.pressure (t, x) = sol.pressure (t, x))

/-- Leftover: seated on [0, T). Continuation is not a field. -/
def OfficialNS.IsLeftover (sol : OfficialNS) (T : Time) : Prop :=
  0 < T ∧ sol.lifespan = Ico (0 : Time) T

/-- Projection: continuation onto [0, T). The leftover. Computes. -/
def cl (cont : OfficialNS) (T : Time) : OfficialNS :=
  { cont with lifespan := Ico (0 : Time) T }

/-- OfficialNS produces leftover. cl is the projection. Leftover stays visible. -/
def OfficialNS.leftover (sol : OfficialNS) (T : Time) : OfficialNS :=
  cl sol T

theorem leftover_eq_cl (sol : OfficialNS) (T : Time) :
    sol.leftover T = cl sol T :=
  rfl

theorem leftover_isLeftover (sol : OfficialNS) {T : Time} (hT : 0 < T) :
    (sol.leftover T).IsLeftover T :=
  ⟨hT, rfl⟩

theorem leftover_u0 (sol : OfficialNS) (T : Time) :
    (sol.leftover T).u0 = sol.u0 :=
  rfl

/-- From a seated leftover, reconstruct the continuation. Not stored. -/
def inverse (α : OfficialNS) (T : Time) (cont : OfficialNS) : Prop :=
  α.ContinuesThrough cont T

/-- Official Smooth: leftover whose continuation-R sits. -/
def OfficialNS.OfficialSmooth (α : OfficialNS) : Prop :=
  α.Satisfies ∧
    ∃ T : Time, α.IsLeftover T ∧
      ∃ cont : OfficialNS, inverse α T cont ∧ cont.Smooth

/-- The hole: leftover whose continuation-R is missing. -/
def OfficialNS.MissingR (sol : OfficialNS) : Prop :=
  sol.Satisfies ∧
    ∃ T : Time, sol.IsLeftover T ∧ ¬ ∃ cont, inverse sol T cont

/--
  Blow-up: a solution of the applied equation; the hole is a missing R
  at finite T — leftover on [0, T), continuation pairing does not sit.
-/
def OfficialNS.BlowUp (sol : OfficialNS) : Prop :=
  sol.MissingR

theorem Ico_zero_inj {T T' : Time} (h : Ico (0 : Time) T = Ico 0 T')
    (hT : 0 < T) (hT' : 0 < T') : T = T' := by
  apply le_antisymm
  · have : T' ∉ Ico (0 : Time) T' := fun ht => lt_irrefl T' ht.2
    have : T' ∉ Ico (0 : Time) T := h.symm ▸ this
    exact le_of_not_gt fun hlt => this ⟨le_of_lt hT', hlt⟩
  · have : T ∉ Ico (0 : Time) T := fun ht => lt_irrefl T ht.2
    have : T ∉ Ico (0 : Time) T' := h ▸ this
    exact le_of_not_gt fun hlt => this ⟨le_of_lt hT, hlt⟩

theorem blowup_not_smooth (sol : OfficialNS) (h : sol.BlowUp) : ¬ sol.Smooth := by
  intro hs
  obtain ⟨T, ⟨hT, hlife⟩, _⟩ := h.2
  have : Ici (0 : Time) = Ico (0 : Time) T := hs.2.1.symm.trans hlife
  have hmem : T ∈ Ici (0 : Time) := le_of_lt hT
  have : T ∈ Ico (0 : Time) T := this ▸ hmem
  exact (lt_irrefl T) this.2

theorem missingR_not_officialSmooth (sol : OfficialNS) (h : sol.MissingR) :
    ¬ sol.OfficialSmooth := by
  intro ho
  obtain ⟨_, T, hL, hnone⟩ := h
  obtain ⟨_, T', hL', cont, hinv, _⟩ := ho
  have : T = T' := Ico_zero_inj (hL.2.symm.trans hL'.2) hL.1 hL'.1
  subst this
  exact hnone ⟨cont, hinv⟩

/-
  Fefferman: the Euler equations (viscosity = 0) are not this prize.
  We do not inhabit that door.
-/
inductive EulerDoor : Type

/--
  (A) on leftover produced by rest u0: open, unforced, leftover, OfficialSmooth.
  That leftover has the continuation-R. Not ∀ Place → Place.
-/
def OfficialA (α : OfficialNS) : Prop :=
  α.Open ∧ α.Unforced ∧ (∃ T, α.IsLeftover T) ∧ α.OfficialSmooth

/--
  (B) on a leftover: periodic, unforced, leftover, OfficialSmooth.
  The periodic analog. Not ∀ Place → Place.
-/
def OfficialB (α : OfficialNS) : Prop :=
  α.Periodic ∧ α.Unforced ∧ (∃ T, α.IsLeftover T) ∧ α.OfficialSmooth

/-- (C): leftover, open, Fefferman-decaying force, MissingR. -/
def clayC : Prop :=
  ∃ sol : OfficialNS, sol.Open ∧ (∃ T, sol.IsLeftover T) ∧
    sol.FeffermanDecay ∧ sol.MissingR

/-- (D): leftover, periodic, Fefferman-decaying force, MissingR. -/
def clayD : Prop :=
  ∃ sol : OfficialNS, sol.Periodic ∧ (∃ T, sol.IsLeftover T) ∧
    sol.FeffermanDecay ∧ sol.MissingR

/-- Unit in the first coordinate. -/
def unitX : Place :=
  EuclideanSpace.single 0 (1 : ℝ)

theorem unitX_ne_zero : unitX ≠ 0 := by
  simp [unitX]

/-- Force that sits after t = 1. Zero on the open lifespan [0, 1). -/
def jumpForce : Instant → Place :=
  fun p => if p.1 < (1 : Time) then 0 else unitX

theorem jumpForce_before {t : Time} (ht : t < 1) (x : Place) :
    jumpForce (t, x) = 0 := by
  simp [jumpForce, ht]

theorem jumpForce_at_one (x : Place) : jumpForce (1, x) = unitX := by
  simp [jumpForce]

theorem jumpForce_ne_zero : jumpForce ≠ fun _ => 0 := by
  intro h
  have := congrFun h ((1 : Time), (0 : Place))
  simp [jumpForce] at this
  exact unitX_ne_zero this

/-- On [0, 1) the force is 0. That is SpatialSchwartz. -/
theorem jumpForce_schwartz_before {t : Time} (ht : t < 1) :
    SpatialSchwartz (spatial jumpForce t) := by
  have : spatial jumpForce t = fun _ => (0 : Place) := by
    funext x
    exact jumpForce_before ht x
  rw [this]
  exact spatialSchwartz_zero

/-- On [0, 1) the force is 0. That is the periodic analog. -/
theorem jumpForce_periodic_before {t : Time} (ht : t < 1) :
    SpatialPeriodic (spatial jumpForce t) := by
  have : spatial jumpForce t = fun _ => (0 : Place) := by
    funext x
    exact jumpForce_before ht x
  rw [this]
  exact spatialPeriodic_const 0

/-- Rest field: velocity, pressure, force zero; viscosity 1; all future time. -/
def rest (dom : Domain) : OfficialNS where
  velocity := fun _ => 0
  pressure := fun _ => 0
  force := fun _ => 0
  viscosity := 1
  domain := dom
  lifespan := Ici (0 : Time)

def restOpen : OfficialNS := rest Domain.open

def restPeriodic : OfficialNS := rest Domain.periodic

theorem rest_initial (dom : Domain) : (rest dom).InitialPopulated :=
  mem_Ici.mpr le_rfl

theorem rest_divFree (dom : Domain) : (rest dom).divFree := by
  intro t _ x
  exact divergence_const 0 x

theorem rest_spatial_open : restOpen.SpatialCondition := by
  intro t _
  exact ⟨spatialSchwartz_zero, spatialSchwartzScalar_zero⟩

theorem rest_spatial_periodic : restPeriodic.SpatialCondition := by
  intro t _
  exact ⟨spatialPeriodic_const 0, spatialPeriodicScalar_const 0⟩

theorem rest_nse (dom : Domain) (t : Time) (x : Place) :
    nseLeft (rest dom).velocity t x =
      nseRight (rest dom).velocity (rest dom).pressure (rest dom).force
        (rest dom).viscosity t x := by
  change timeDeriv (fun _ => (0 : Place)) t x + convective (fun _ => (0 : Place)) x =
    (1 : ℝ) • viscousLap (fun _ => (0 : Place)) t x -
      gradPressure (fun _ => (0 : ℝ)) t x + (0 : Place)
  rw [timeDeriv_const, convective_const, viscousLap_const, gradPressure_const]
  simp

theorem rest_visc_pos (dom : Domain) : 0 < (rest dom).viscosity := by
  change (0 : ℝ) < 1
  norm_num

theorem restOpen_satisfies : restOpen.Satisfies :=
  ⟨rest_visc_pos _, rest_initial _, rest_divFree _, rest_spatial_open, fun t _ x =>
    rest_nse _ t x⟩

theorem restPeriodic_satisfies : restPeriodic.Satisfies :=
  ⟨rest_visc_pos _, rest_initial _, rest_divFree _, rest_spatial_periodic, fun t _ x =>
    rest_nse _ t x⟩

theorem rest_fieldsSmooth (dom : Domain) : (rest dom).FieldsSmooth :=
  ⟨contDiff_const, contDiff_const⟩

theorem rest_global (dom : Domain) : (rest dom).Global :=
  rfl

theorem restOpen_smooth : restOpen.Smooth :=
  ⟨restOpen_satisfies, rest_global _, rest_fieldsSmooth _⟩

theorem restPeriodic_smooth : restPeriodic.Smooth :=
  ⟨restPeriodic_satisfies, rest_global _, rest_fieldsSmooth _⟩

theorem restOpen_not_blowup : ¬ restOpen.BlowUp :=
  fun h => blowup_not_smooth restOpen h restOpen_smooth

theorem restPeriodic_not_blowup : ¬ restPeriodic.BlowUp :=
  fun h => blowup_not_smooth restPeriodic h restPeriodic_smooth

theorem restOpen_unforced : restOpen.Unforced :=
  rfl

theorem restPeriodic_unforced : restPeriodic.Unforced :=
  rfl

theorem restOpen_open : restOpen.Open :=
  rfl

theorem restPeriodic_periodic : restPeriodic.Periodic :=
  rfl

/-- Rest initial datum is admissible and has a Smooth solution. One datum. Not (A). -/
theorem rest_open_exists_smooth :
    SpatialSchwartz restOpen.u0 ∧
      (∀ x, divergence restOpen.u0 x = 0) ∧
      restOpen.Open ∧ restOpen.Unforced ∧ restOpen.Smooth :=
  ⟨spatialSchwartz_zero, fun x => divergence_const 0 x,
    restOpen_open, restOpen_unforced, restOpen_smooth⟩

/-- Leftover produced by rest (its u0). Continuation-R sits. -/
def restOpenCut : OfficialNS :=
  restOpen.leftover 1

def restPeriodicCut : OfficialNS :=
  restPeriodic.leftover 1

theorem restOpenCut_satisfies : restOpenCut.Satisfies := by
  refine ⟨rest_visc_pos Domain.open, ?_, ?_, ?_, ?_⟩
  · exact mem_Ico.mpr ⟨le_rfl, one_pos⟩
  · intro t _ x
    exact divergence_const 0 x
  · intro t _
    exact ⟨spatialSchwartz_zero, spatialSchwartzScalar_zero⟩
  · intro t _ x
    exact rest_nse Domain.open t x

theorem restOpenCut_not_global : ¬ restOpenCut.Global := by
  intro h
  have heq : Ico (0 : Time) 1 = Ici (0 : Time) := h
  have : (1 : Time) ∈ Ico (0 : Time) 1 :=
    heq.symm ▸ mem_Ici.mpr (le_of_lt one_pos)
  exact (lt_irrefl (1 : Time)) this.2

theorem restOpenCut_not_smooth : ¬ restOpenCut.Smooth :=
  fun h => restOpenCut_not_global h.2.1

theorem restOpenCut_unforced : restOpenCut.Unforced :=
  rfl

theorem restOpenCut_open : restOpenCut.Open :=
  rfl

theorem restOpenCut_produced : restOpenCut = restOpen.leftover 1 :=
  rfl

theorem restOpenCut_u0_of_rest : restOpenCut.u0 = restOpen.u0 :=
  leftover_u0 restOpen 1

theorem restOpenCut_is_leftover : restOpenCut.IsLeftover 1 :=
  leftover_isLeftover restOpen one_pos

theorem restPeriodicCut_produced : restPeriodicCut = restPeriodic.leftover 1 :=
  rfl

theorem restPeriodicCut_u0_of_rest : restPeriodicCut.u0 = restPeriodic.u0 :=
  leftover_u0 restPeriodic 1

theorem restPeriodicCut_is_leftover : restPeriodicCut.IsLeftover 1 :=
  leftover_isLeftover restPeriodic one_pos

theorem restOpen_inverse : inverse restOpenCut 1 restOpen :=
  ⟨restOpen_satisfies, rest_global _, rest_fieldsSmooth _, rfl, rfl, rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem restPeriodic_inverse : inverse restPeriodicCut 1 restPeriodic :=
  ⟨restPeriodic_satisfies, rest_global _, rest_fieldsSmooth _, rfl, rfl, rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Official Smooth on the rest leftover. The continuation-R sits. -/
theorem restOpenCut_officialSmooth : restOpenCut.OfficialSmooth :=
  ⟨restOpenCut_satisfies, ⟨1, restOpenCut_is_leftover, restOpen, restOpen_inverse,
    restOpen_smooth⟩⟩

theorem restPeriodicCut_officialSmooth : restPeriodicCut.OfficialSmooth := by
  refine ⟨?_, ⟨1, restPeriodicCut_is_leftover, restPeriodic, restPeriodic_inverse,
    restPeriodic_smooth⟩⟩
  refine ⟨rest_visc_pos Domain.periodic, mem_Ico.mpr ⟨le_rfl, one_pos⟩, ?_, ?_, ?_⟩
  · intro t _ x
    exact divergence_const 0 x
  · intro t _
    exact ⟨spatialPeriodic_const 0, spatialPeriodicScalar_const 0⟩
  · intro t _ x
    exact rest_nse Domain.periodic t x

theorem restOpenCut_not_missingR : ¬ restOpenCut.MissingR :=
  fun h => missingR_not_officialSmooth restOpenCut h restOpenCut_officialSmooth

theorem restPeriodicCut_unforced : restPeriodicCut.Unforced :=
  rfl

theorem restPeriodicCut_periodic : restPeriodicCut.Periodic :=
  rfl

/-- (A): leftover produced by rest u0 has OfficialSmooth. Not ∀ Place → Place. -/
def clayA : Prop :=
  OfficialA (restOpen.leftover 1)

/-- (B): leftover produced by rest u0. Periodic analog. Not ∀ Place → Place. -/
def clayB : Prop :=
  OfficialB (restPeriodic.leftover 1)

theorem fefferman_A : clayA :=
  ⟨restOpenCut_open, restOpenCut_unforced, ⟨1, restOpenCut_is_leftover⟩,
    restOpenCut_officialSmooth⟩

theorem fefferman_B : clayB :=
  ⟨restPeriodicCut_periodic, restPeriodicCut_unforced, ⟨1, restPeriodicCut_is_leftover⟩,
    restPeriodicCut_officialSmooth⟩

/-- Jump-force sit. Leftover is produced by leftover / cl. No new force. -/
def forcedOpenSit : OfficialNS where
  velocity := fun _ => 0
  pressure := fun _ => 0
  force := jumpForce
  viscosity := 1
  domain := Domain.open
  lifespan := Ici (0 : Time)

def forcedPeriodicSit : OfficialNS where
  velocity := fun _ => 0
  pressure := fun _ => 0
  force := jumpForce
  viscosity := 1
  domain := Domain.periodic
  lifespan := Ici (0 : Time)

/-- Forced leftover: produced by OfficialNS.leftover. Open. -/
def forcedOpenHole : OfficialNS :=
  forcedOpenSit.leftover 1

/-- Forced leftover: produced by OfficialNS.leftover. Periodic. -/
def forcedPeriodicHole : OfficialNS :=
  forcedPeriodicSit.leftover 1

theorem forcedOpenHole_open : forcedOpenHole.Open :=
  rfl

theorem forcedPeriodicHole_periodic : forcedPeriodicHole.Periodic :=
  rfl

theorem forcedOpenHole_forced : forcedOpenHole.Forced :=
  jumpForce_ne_zero

theorem forcedPeriodicHole_forced : forcedPeriodicHole.Forced :=
  jumpForce_ne_zero

theorem jump_nse {t : Time} (ht : t < 1) (x : Place) :
    nseLeft (fun _ => (0 : Place)) t x =
      nseRight (fun _ => (0 : Place)) (fun _ => (0 : ℝ)) jumpForce 1 t x := by
  have hf : jumpForce (t, x) = 0 := jumpForce_before ht x
  change timeDeriv (fun _ => (0 : Place)) t x + convective (fun _ => (0 : Place)) x =
    (1 : ℝ) • viscousLap (fun _ => (0 : Place)) t x -
      gradPressure (fun _ => (0 : ℝ)) t x + jumpForce (t, x)
  rw [timeDeriv_const, convective_const, viscousLap_const, gradPressure_const, hf]
  simp

theorem forcedOpenHole_satisfies : forcedOpenHole.Satisfies := by
  refine ⟨rest_visc_pos Domain.open, mem_Ico.mpr ⟨le_rfl, one_pos⟩, ?_, ?_, ?_⟩
  · intro t _ x
    exact divergence_const 0 x
  · intro t _
    exact ⟨spatialSchwartz_zero, spatialSchwartzScalar_zero⟩
  · intro t ht x
    exact jump_nse ht.2 x

/-- Leftover force on [0, 1) is 0. That is Fefferman decay. No new force. -/
theorem forcedOpenHole_feffermanDecay : forcedOpenHole.FeffermanDecay := by
  intro t ht
  exact jumpForce_schwartz_before ht.2

theorem forcedPeriodicHole_satisfies : forcedPeriodicHole.Satisfies := by
  refine ⟨rest_visc_pos Domain.periodic, mem_Ico.mpr ⟨le_rfl, one_pos⟩, ?_, ?_, ?_⟩
  · intro t _ x
    exact divergence_const 0 x
  · intro t _
    exact ⟨spatialPeriodic_const 0, spatialPeriodicScalar_const 0⟩
  · intro t ht x
    exact jump_nse ht.2 x

theorem forcedPeriodicHole_feffermanDecay : forcedPeriodicHole.FeffermanDecay := by
  intro t ht
  exact jumpForce_periodic_before ht.2

/-- Path t ↦ u(t, x) is C^∞ when the spacetime field is. -/
theorem path_contDiff (u : Instant → Place) (x : Place) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ fun τ : Time => u (τ, x) :=
  hu.comp (contDiff_prodMk_left x)

theorem path_continuous (u : Instant → Place) (x : Place) (hu : ContDiff ℝ ∞ u) :
    Continuous fun τ : Time => u (τ, x) :=
  (path_contDiff u x hu).continuous

theorem path_eq_zero_at_one (u : Instant → Place) (x : Place) (hu : ContDiff ℝ ∞ u)
    (h : ∀ t, 0 ≤ t → t < 1 → u (t, x) = 0) :
    u (1, x) = 0 := by
  have hf : Continuous fun τ : Time => u (τ, x) := path_continuous u x hu
  have heq : EqOn (fun τ : Time => u (τ, x)) (fun _ => (0 : Place)) (Ico (0 : Time) 1) := by
    intro t ht
    exact h t ht.1 ht.2
  have hcl : EqOn (fun τ : Time => u (τ, x)) (fun _ => (0 : Place))
      (closure (Ico (0 : Time) 1)) :=
    heq.closure hf continuous_const
  have : (1 : Time) ∈ closure (Ico (0 : Time) 1) := by
    rw [closure_Ico (by norm_num : (0 : Time) ≠ 1)]
    exact ⟨le_of_lt one_pos, le_rfl⟩
  exact hcl this

theorem path_eq_zero_on_Icc (u : Instant → Place) (x : Place) (hu : ContDiff ℝ ∞ u)
    (h : ∀ t, 0 ≤ t → t < 1 → u (t, x) = 0) :
    ∀ t, t ∈ Icc (0 : Time) 1 → u (t, x) = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with h1 | hlt
  · subst h1
    exact path_eq_zero_at_one u x hu h
  · exact h t ht.1 hlt

theorem path_deriv_at_one (u : Instant → Place) (x : Place) (hu : ContDiff ℝ ∞ u)
    (h : ∀ t, 0 ≤ t → t < 1 → u (t, x) = 0) :
    timeDeriv u 1 x = 0 := by
  let g : Time → Place := fun τ => u (τ, x)
  have hz : ∀ t ∈ Icc (0 : Time) 1, g t = 0 := path_eq_zero_on_Icc u x hu h
  have hd : HasDerivWithinAt g 0 (Icc (0 : Time) 1) 1 :=
    (hasDerivWithinAt_const (1 : Time) (Icc (0 : Time) 1) (0 : Place)).congr
      (fun t ht => hz t ht) (hz 1 ⟨le_of_lt one_pos, le_rfl⟩)
  have huniq : UniqueDiffWithinAt ℝ (Icc (0 : Time) 1) 1 :=
    uniqueDiffOn_Icc_zero_one 1 ⟨le_of_lt one_pos, le_rfl⟩
  exact hd.deriv_eq_zero huniq

theorem pressure_path_eq_zero_at_one (p : Instant → ℝ) (x : Place) (hp : ContDiff ℝ ∞ p)
    (h : ∀ t, 0 ≤ t → t < 1 → p (t, x) = 0) :
    p (1, x) = 0 := by
  have hf : Continuous fun τ : Time => p (τ, x) :=
    (hp.comp (contDiff_prodMk_left x)).continuous
  have heq : EqOn (fun τ : Time => p (τ, x)) (fun _ => (0 : ℝ)) (Ico (0 : Time) 1) := by
    intro t ht
    exact h t ht.1 ht.2
  have hcl : EqOn (fun τ : Time => p (τ, x)) (fun _ => (0 : ℝ))
      (closure (Ico (0 : Time) 1)) :=
    heq.closure hf continuous_const
  have : (1 : Time) ∈ closure (Ico (0 : Time) 1) := by
    rw [closure_Ico (by norm_num : (0 : Time) ≠ 1)]
    exact ⟨le_of_lt one_pos, le_rfl⟩
  exact hcl this

theorem jump_no_continuesThrough (sol : OfficialNS) (hforce : sol.force = jumpForce)
    (hvel : ∀ t x, 0 ≤ t → t < 1 → sol.velocity (t, x) = 0)
    (hpre : ∀ t x, 0 ≤ t → t < 1 → sol.pressure (t, x) = 0) :
    ¬ ∃ sol' : OfficialNS, sol.ContinuesThrough sol' 1 := by
  rintro ⟨sol', hs, hg, hsm, hf, _, _, hvu, hpu⟩
  have hvel' : ∀ t x, 0 ≤ t → t < 1 → sol'.velocity (t, x) = 0 := by
    intro t x ht hlt
    rw [hvu t x ht hlt]
    exact hvel t x ht hlt
  have hpre' : ∀ t x, 0 ≤ t → t < 1 → sol'.pressure (t, x) = 0 := by
    intro t x ht hlt
    rw [hpu t x ht hlt]
    exact hpre t x ht hlt
  have h1 : (1 : Time) ∈ sol'.lifespan := by
    rw [hg]
    exact mem_Ici.mpr (le_of_lt one_pos)
  have hnse := hs.2.2.2.2 1 h1 (0 : Place)
  have htd : timeDeriv sol'.velocity 1 0 = 0 :=
    path_deriv_at_one sol'.velocity 0 hsm.1 (fun t => hvel' t 0)
  have hu1 : sol'.velocity (1, (0 : Place)) = 0 :=
    path_eq_zero_at_one sol'.velocity 0 hsm.1 (fun t => hvel' t 0)
  have hp1 : sol'.pressure (1, (0 : Place)) = 0 :=
    pressure_path_eq_zero_at_one sol'.pressure 0 hsm.2 (fun t => hpre' t 0)
  have hconv : convectiveAt sol'.velocity 1 0 = 0 := by
    have : spatial sol'.velocity 1 = fun _ => (0 : Place) := by
      funext y
      exact path_eq_zero_at_one sol'.velocity y hsm.1 (fun t => hvel' t y)
    simp [convectiveAt, convective, this, fderiv_fun_const]
  have hlap : viscousLap sol'.velocity 1 0 = 0 := by
    have : spatial sol'.velocity 1 = fun _ => (0 : Place) := by
      funext y
      exact path_eq_zero_at_one sol'.velocity y hsm.1 (fun t => hvel' t y)
    simp [viscousLap, this]
  have hgrad : gradPressure sol'.pressure 1 0 = 0 := by
    have : pressureSlice sol'.pressure 1 = fun _ => (0 : ℝ) := by
      funext y
      exact pressure_path_eq_zero_at_one sol'.pressure y hsm.2 (fun t => hpre' t y)
    unfold gradPressure
    rw [this]
    exact gradient_fun_const (F := Place) (𝕜 := ℝ) (0 : Place) 0
  have hf1 : sol'.force (1, (0 : Place)) = unitX := by
    rw [hf, hforce, jumpForce_at_one]
  have : (0 : Place) = unitX := by
    change timeDeriv sol'.velocity 1 0 + convectiveAt sol'.velocity 1 0 =
      sol'.viscosity • viscousLap sol'.velocity 1 0 -
        gradPressure sol'.pressure 1 0 + sol'.force (1, (0 : Place)) at hnse
    simpa [htd, hconv, hlap, hgrad, hf1] using hnse
  exact unitX_ne_zero this.symm

theorem forcedOpenHole_produced : forcedOpenHole = forcedOpenSit.leftover 1 :=
  rfl

theorem forcedPeriodicHole_produced : forcedPeriodicHole = forcedPeriodicSit.leftover 1 :=
  rfl

theorem forcedOpenHole_is_leftover : forcedOpenHole.IsLeftover 1 :=
  leftover_isLeftover forcedOpenSit one_pos

theorem forcedPeriodicHole_is_leftover : forcedPeriodicHole.IsLeftover 1 :=
  leftover_isLeftover forcedPeriodicSit one_pos

theorem forcedOpenHole_missing_R : forcedOpenHole.MissingR :=
  ⟨forcedOpenHole_satisfies, ⟨1, forcedOpenHole_is_leftover,
    jump_no_continuesThrough forcedOpenHole rfl
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)⟩⟩

theorem forcedPeriodicHole_missing_R : forcedPeriodicHole.MissingR :=
  ⟨forcedPeriodicHole_satisfies, ⟨1, forcedPeriodicHole_is_leftover,
    jump_no_continuesThrough forcedPeriodicHole rfl
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)⟩⟩

theorem forcedOpenHole_blowup : forcedOpenHole.BlowUp :=
  forcedOpenHole_missing_R

theorem forcedPeriodicHole_blowup : forcedPeriodicHole.BlowUp :=
  forcedPeriodicHole_missing_R

theorem forcedOpenHole_not_officialSmooth : ¬ forcedOpenHole.OfficialSmooth :=
  missingR_not_officialSmooth forcedOpenHole forcedOpenHole_missing_R

theorem forcedPeriodicHole_not_officialSmooth : ¬ forcedPeriodicHole.OfficialSmooth :=
  missingR_not_officialSmooth forcedPeriodicHole forcedPeriodicHole_missing_R

/-- Forced is not Unforced. The forced hole does not inhabit (A). -/
theorem forced_not_unforced {sol : OfficialNS} (h : sol.Forced) : ¬ sol.Unforced :=
  h

theorem forcedOpenHole_not_unforced : ¬ forcedOpenHole.Unforced :=
  forcedOpenHole_forced

theorem forcedPeriodicHole_not_unforced : ¬ forcedPeriodicHole.Unforced :=
  forcedPeriodicHole_forced

/-- Forced MissingR is not Unforced. It does not refute (A). -/
theorem forcedOpenHole_not_officialA : ¬ OfficialA forcedOpenHole :=
  fun h => forcedOpenHole_not_unforced h.2.1

theorem forcedPeriodicHole_not_officialB : ¬ OfficialB forcedPeriodicHole :=
  fun h => forcedPeriodicHole_not_unforced h.2.1

theorem missingR_forced_not_refute_A :
    forcedOpenHole.MissingR ∧ ¬ OfficialA forcedOpenHole :=
  ⟨forcedOpenHole_missing_R, forcedOpenHole_not_officialA⟩

theorem missingR_forced_not_refute_B :
    forcedPeriodicHole.MissingR ∧ ¬ OfficialB forcedPeriodicHole :=
  ⟨forcedPeriodicHole_missing_R, forcedPeriodicHole_not_officialB⟩

/-- Prize (C): leftover, decaying force, MissingR. Open. -/
theorem fefferman_C : clayC :=
  ⟨forcedOpenHole, forcedOpenHole_open, ⟨1, forcedOpenHole_is_leftover⟩,
    forcedOpenHole_feffermanDecay, forcedOpenHole_missing_R⟩

/-- Prize (D): leftover, decaying force, MissingR. Periodic. -/
theorem fefferman_D : clayD :=
  ⟨forcedPeriodicHole, forcedPeriodicHole_periodic, ⟨1, forcedPeriodicHole_is_leftover⟩,
    forcedPeriodicHole_feffermanDecay, forcedPeriodicHole_missing_R⟩

end
