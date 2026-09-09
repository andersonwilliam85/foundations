/-
  Algebraic de Rham complex of an R-algebra S.
  Terms: ⋀[S]^n (Ω[S⁄R]).
  d is the exterior derivative of KaehlerDifferential.D.
  Not the zero map. Not ell-adic. Not Zariski homology.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open ExteriorAlgebra CliffordAlgebra CategoryTheory

universe u

/-! ### House inclusion of a stupid truncation (`IsTruncGE`)

mathlib marks `e.stupidTruncFunctor C ⟶ 𝟭` as TODO in
`Algebra.Homology.Embedding.StupidTrunc`. This is that inclusion,
house-side, not a mathlib PR. It is a chain map. Do not sorry it.
-/

namespace HomologicalComplex

open Category Limits
open scoped Classical

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K : HomologicalComplex C c') (e : c.Embedding c')

/-- Component of the inclusion `K.stupidTrunc e ⟶ K` at index `i'`. -/
noncomputable def ιStupidTrunc_f [e.IsTruncGE] (i' : ι') :
    (K.stupidTrunc e).X i' ⟶ K.X i' :=
  if h : ∃ i, e.f i = i' then
    (K.stupidTruncXIso e h.choose_spec).hom
  else
    0

lemma ιStupidTrunc_f_eq [e.IsTruncGE] {i : ι} {i' : ι'} (hi : e.f i = i') :
    K.ιStupidTrunc_f e i' = (K.stupidTruncXIso e hi).hom := by
  have h : ∃ k, e.f k = i' := ⟨i, hi⟩
  have hk : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  dsimp [ιStupidTrunc_f]
  rw [dif_pos h]
  subst hk
  rfl

lemma ιStupidTrunc_f_eq_zero [e.IsTruncGE] (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    K.ιStupidTrunc_f e i' = 0 := by
  dsimp [ιStupidTrunc_f]
  exact dif_neg fun ⟨i, hi'⟩ => hi i hi'

lemma stupidTrunc_d_eq [e.IsRelIff] {i j : ι} {i' j' : ι'}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' =
      (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫ (K.stupidTruncXIso e hj).inv := by
  subst hi hj
  simp only [stupidTrunc, stupidTruncXIso, Iso.trans_hom, Iso.trans_inv, assoc]
  rw [(K.restriction e).extend_d_eq e (i := i) (j := j) rfl rfl]
  simp [restriction, eqToIso]

/--
  Inclusion `K.stupidTrunc e ⟶ K` when `e.IsTruncGE`.
  On the image of `e.f` this is the identity via `stupidTruncXIso`.
  Off the image the source is zero.
  `IsTruncGE` makes this a chain map: if `c'.Rel (e.f j) k'` then `k'` is in the image.
-/
noncomputable def ιStupidTrunc [e.IsTruncGE] : K.stupidTrunc e ⟶ K where
  f := K.ιStupidTrunc_f e
  comm' i' j' hij := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      have hij' : c'.Rel (e.f i) j' := by rwa [hi]
      obtain ⟨j, hj⟩ := e.mem_next hij'
      rw [ιStupidTrunc_f_eq K e hi, ιStupidTrunc_f_eq K e hj, K.stupidTrunc_d_eq e hi hj]
      simp
    · exact (K.isZero_stupidTrunc_X e i' fun i h => hi ⟨i, h⟩).eq_of_src _ _

variable (e e' : c.Embedding c')

/--
  Component of `K.stupidTrunc e ⟶ K.stupidTrunc e'` when the image of `e`
  sits inside the image of `e'`.
-/
noncomputable def ιStupidTruncLE_f [e.IsTruncGE] [e'.IsTruncGE]
    (hsubset : ∀ i', (∃ i, e.f i = i') → (∃ j, e'.f j = i')) (i' : ι') :
    (K.stupidTrunc e).X i' ⟶ (K.stupidTrunc e').X i' :=
  if h : ∃ i, e.f i = i' then
    (K.stupidTruncXIso e h.choose_spec).hom ≫
      (K.stupidTruncXIso e' (hsubset i' h).choose_spec).inv
  else
    0

lemma ιStupidTruncLE_f_eq [e.IsTruncGE] [e'.IsTruncGE]
    (hsubset : ∀ i', (∃ i, e.f i = i') → (∃ j, e'.f j = i'))
    {i j : ι} {i' : ι'} (hi : e.f i = i') (hj : e'.f j = i') :
    K.ιStupidTruncLE_f e e' hsubset i' =
      (K.stupidTruncXIso e hi).hom ≫ (K.stupidTruncXIso e' hj).inv := by
  have h : ∃ k, e.f k = i' := ⟨i, hi⟩
  have hk : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  have h' := hsubset i' h
  have hj' : h'.choose = j := e'.injective_f (h'.choose_spec.trans hj.symm)
  dsimp [ιStupidTruncLE_f]
  rw [dif_pos h]
  subst hk
  subst hj'
  rfl

lemma ιStupidTruncLE_f_eq_zero [e.IsTruncGE] [e'.IsTruncGE]
    (hsubset : ∀ i', (∃ i, e.f i = i') → (∃ j, e'.f j = i'))
    (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    K.ιStupidTruncLE_f e e' hsubset i' = 0 := by
  dsimp [ιStupidTruncLE_f]
  exact dif_neg fun ⟨i, hi'⟩ => hi i hi'

/--
  Inclusion `K.stupidTrunc e ⟶ K.stupidTrunc e'` when the image of `e`
  sits inside the image of `e'`. A chain map. House-side.
-/
noncomputable def ιStupidTruncLE [e.IsTruncGE] [e'.IsTruncGE]
    (hsubset : ∀ i', (∃ i, e.f i = i') → (∃ j, e'.f j = i')) :
    K.stupidTrunc e ⟶ K.stupidTrunc e' where
  f := K.ιStupidTruncLE_f e e' hsubset
  comm' i' j' hij := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      have hij' : c'.Rel (e.f i) j' := by rwa [hi]
      obtain ⟨k, hk⟩ := e.mem_next hij'
      obtain ⟨j, hj⟩ := hsubset i' ⟨i, hi⟩
      obtain ⟨k', hk'⟩ := hsubset j' ⟨k, hk⟩
      rw [ιStupidTruncLE_f_eq K e e' hsubset hi hj,
        ιStupidTruncLE_f_eq K e e' hsubset hk hk',
        K.stupidTrunc_d_eq e hi hk, K.stupidTrunc_d_eq e' hj hk']
      simp
    · exact (K.isZero_stupidTrunc_X e i' fun i h => hi ⟨i, h⟩).eq_of_src _ _

lemma ιStupidTruncLE_comp_ι [e.IsTruncGE] [e'.IsTruncGE]
    (hsubset : ∀ i', (∃ i, e.f i = i') → (∃ j, e'.f j = i')) :
    K.ιStupidTruncLE e e' hsubset ≫ K.ιStupidTrunc e' = K.ιStupidTrunc e := by
  ext i'
  dsimp [ιStupidTruncLE, ιStupidTrunc]
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    obtain ⟨j, hj⟩ := hsubset i' ⟨i, hi⟩
    rw [ιStupidTruncLE_f_eq K e e' hsubset hi hj, ιStupidTrunc_f_eq K e' hj,
      ιStupidTrunc_f_eq K e hi]
    simp
  · rw [ιStupidTruncLE_f_eq_zero K e e' hsubset i' fun i h => hi ⟨i, h⟩,
      ιStupidTrunc_f_eq_zero K e i' fun i h => hi ⟨i, h⟩, zero_comp]

end HomologicalComplex

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

abbrev ExtE := ExteriorAlgebra S (Ω[S⁄R])

/-! ### Degree-1 exterior derivative via `kerTotal` -/

noncomputable def d1Slot (t : S) : S →ₗ[R] ExtE R S :=
  (LinearMap.mulRight (R := S) (ι S (KaehlerDifferential.D R S t))).restrictScalars R ∘ₗ
    (ι S).restrictScalars R ∘ₗ (KaehlerDifferential.D R S).toLinearMap

noncomputable def d1Pre : (S →₀ S) →ₗ[R] ExtE R S :=
  Finsupp.lsum (S := R) (d1Slot R S)

theorem d1Pre_single (t s : S) :
    d1Pre R S (Finsupp.single t s) =
      ι S (KaehlerDifferential.D R S s) * ι S (KaehlerDifferential.D R S t) :=
  Finsupp.lsum_single (S := R) (d1Slot R S) t s

theorem d1Pre_add_gen (x y : S) :
    d1Pre R S (Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x + y) 1) = 0 := by
  simp only [map_sub, map_add, d1Pre_single, (KaehlerDifferential.D R S).map_add, mul_add]
  abel

theorem d1Pre_mul_gen (x y : S) :
    d1Pre R S (Finsupp.single y x + Finsupp.single x y - Finsupp.single (x * y) 1) = 0 := by
  simp only [map_sub, map_add, d1Pre_single, (KaehlerDifferential.D R S).map_one_eq_zero,
    map_zero, mul_zero, sub_zero]
  convert ι_add_mul_swap (R := S) (KaehlerDifferential.D R S x) (KaehlerDifferential.D R S y)
  simp

theorem d1Pre_const_gen (r : R) :
    d1Pre R S (Finsupp.single (algebraMap R S r) 1) = 0 := by
  rw [d1Pre_single, (KaehlerDifferential.D R S).map_algebraMap, map_zero, mul_zero]

theorem d1Pre_smul_add_gen (z x y : S) :
    d1Pre R S (z • (Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x + y) 1)) = 0 := by
  simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one, map_sub, map_add,
    d1Pre_single, (KaehlerDifferential.D R S).map_add, mul_add]
  abel

theorem d1Pre_smul_mul_gen (z x y : S) :
    d1Pre R S (z • (Finsupp.single y x + Finsupp.single x y - Finsupp.single (x * y) 1)) = 0 := by
  simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one, map_sub, map_add,
    d1Pre_single]
  rw [(KaehlerDifferential.D R S).leibniz z x, (KaehlerDifferential.D R S).leibniz z y,
    (KaehlerDifferential.D R S).leibniz x y]
  simp only [map_add, mul_add, add_mul, (ι S).map_smul]
  -- `a * (s • b) = s • (a * b)` because algebraMap s commutes with a.
  have hpull (s : S) (a b : ExtE R S) : a * (s • b) = s • (a * b) := by
    simp only [Algebra.smul_def]
    rw [← mul_assoc, ← Algebra.commutes s a, mul_assoc]
  simp only [smul_mul_assoc, hpull]
  have hswap := ι_add_mul_swap (R := S) (KaehlerDifferential.D R S x) (KaehlerDifferential.D R S y)
  have hcancel :
      z • (ι S (KaehlerDifferential.D R S x) * ι S (KaehlerDifferential.D R S y)) +
            x • (ι S (KaehlerDifferential.D R S z) * ι S (KaehlerDifferential.D R S y)) +
          (z • (ι S (KaehlerDifferential.D R S y) * ι S (KaehlerDifferential.D R S x)) +
            y • (ι S (KaehlerDifferential.D R S z) * ι S (KaehlerDifferential.D R S x))) -
        (x • (ι S (KaehlerDifferential.D R S z) * ι S (KaehlerDifferential.D R S y)) +
          y • (ι S (KaehlerDifferential.D R S z) * ι S (KaehlerDifferential.D R S x))) =
        z • (ι S (KaehlerDifferential.D R S x) * ι S (KaehlerDifferential.D R S y) +
          ι S (KaehlerDifferential.D R S y) * ι S (KaehlerDifferential.D R S x)) := by
    simp only [smul_add]
    abel
  rw [hcancel, hswap, smul_zero]

theorem d1Pre_smul_const_gen (z : S) (r : R) :
    d1Pre R S (z • Finsupp.single (algebraMap R S r) 1) = 0 := by
  simp [Finsupp.smul_single, d1Pre_single, (KaehlerDifferential.D R S).map_algebraMap]

theorem d1Pre_mem_kerTotal {f : S →₀ S} (hf : f ∈ KaehlerDifferential.kerTotal R S) :
    d1Pre R S f = 0 := by
  have hstrong : ∀ g ∈ KaehlerDifferential.kerTotal R S, ∀ z : S, d1Pre R S (z • g) = 0 := by
    intro g hg
    refine Submodule.span_induction
      (p := fun g _ => ∀ z : S, d1Pre R S (z • g) = 0) ?_ ?_ ?_ ?_ hg
    · rintro g h z
      rcases h with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩
      · exact d1Pre_smul_add_gen R S z x y
      · exact d1Pre_smul_mul_gen R S z x y
      · exact d1Pre_smul_const_gen R S z r
    · intro z; simp
    · intro x y _ _ hx hy z; simp [hx z, hy z]
    · intro a g _ ih z; simpa [smul_smul] using ih (z * a)
  simpa using hstrong f hf 1

theorem d1Pre_ker : (KaehlerDifferential.kerTotal R S).restrictScalars R ≤
    LinearMap.ker (d1Pre R S) :=
  fun _f hf => d1Pre_mem_kerTotal R S hf

noncomputable def d1Quot :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) →ₗ[R] ExtE R S :=
  ((KaehlerDifferential.kerTotal R S).restrictScalars R).liftQ (d1Pre R S) (d1Pre_ker R S)

noncomputable def d1 : Ω[S⁄R] →ₗ[R] ExtE R S :=
  d1Quot R S ∘ₗ
    (KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.restrictScalars R

theorem d1_apply_linearCombination (f : S →₀ S) :
    d1 R S (Finsupp.linearCombination S (KaehlerDifferential.D R S) f) = d1Pre R S f := by
  have hmk :
      KaehlerDifferential.quotKerTotalEquiv R S ((KaehlerDifferential.kerTotal R S).mkQ f) =
        Finsupp.linearCombination S (KaehlerDifferential.D R S) f :=
    rfl
  have hsymm :
      (KaehlerDifferential.quotKerTotalEquiv R S).symm
        (Finsupp.linearCombination S (KaehlerDifferential.D R S) f) =
      (KaehlerDifferential.kerTotal R S).mkQ f := by
    apply (KaehlerDifferential.quotKerTotalEquiv R S).injective
    rw [LinearEquiv.apply_symm_apply, hmk]
  change d1Quot R S
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm
        (Finsupp.linearCombination S (KaehlerDifferential.D R S) f)) =
    d1Pre R S f
  rw [hsymm]
  exact Submodule.liftQ_apply _ _ f

theorem d1_smul_D (s t : S) :
    d1 R S (s • KaehlerDifferential.D R S t) =
      ι S (KaehlerDifferential.D R S s) * ι S (KaehlerDifferential.D R S t) := by
  simpa [Finsupp.linearCombination_single] using
    (d1_apply_linearCombination R S (Finsupp.single t s)).trans (d1Pre_single R S t s)

theorem d1_D (t : S) : d1 R S (KaehlerDifferential.D R S t) = 0 := by
  have h := d1_smul_D R S 1 t
  simpa using h

theorem d1_leibniz (ω : Ω[S⁄R]) (s : S) :
    d1 R S (s • ω) =
      ι S (KaehlerDifferential.D R S s) * ι S ω + s • d1 R S ω := by
  have hspan : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction
    (p := fun ω _ => ∀ s : S,
      d1 R S (s • ω) = ι S (KaehlerDifferential.D R S s) * ι S ω + s • d1 R S ω)
    ?_ ?_ ?_ ?_ hspan s
  · rintro _ ⟨t, rfl⟩ s
    rw [d1_smul_D, d1_D, smul_zero, add_zero]
  · intro s; simp
  · intro x y _ _ hx hy s
    simp [smul_add, hx s, hy s, mul_add, add_smul]; abel
  · intro a x _ ih s
    rw [smul_smul, ih (s * a), (KaehlerDifferential.D R S).leibniz, map_add, add_mul,
      (ι S).map_smul, smul_mul_assoc]
    simp [ih a, (ι S).map_smul, smul_mul_assoc, smul_add, smul_smul]
    abel

theorem d1_mem_two (ω : Ω[S⁄R]) : d1 R S ω ∈ ⋀[S]^2 (Ω[S⁄R]) := by
  have hspan : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun ω _ => d1 R S ω ∈ ⋀[S]^2 (Ω[S⁄R]))
    ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨t, rfl⟩
    simp [d1_D]
  · exact zero_mem _
  · intro x y _ _ hx hy; simpa [map_add] using add_mem hx hy
  · intro s x _ hx
    rw [d1_leibniz]
    refine add_mem ?_ (Submodule.smul_mem _ _ hx)
    have h1 : ι S (KaehlerDifferential.D R S s) ∈ ⋀[S]^1 (Ω[S⁄R]) := by
      simpa [Submodule.pow_one] using LinearMap.mem_range_self (ι S) _
    have hx1 : ι S x ∈ ⋀[S]^1 (Ω[S⁄R]) := by
      simpa [Submodule.pow_one] using LinearMap.mem_range_self (ι S) x
    exact SetLike.mul_mem_graded h1 hx1

theorem involute_eq_self_of_mem_two {x : ExtE R S} (hx : x ∈ ⋀[S]^2 (Ω[S⁄R])) :
    involute x = x := by
  have : x ∈ Submodule.span S (Set.range (ιMulti S 2 (M := Ω[S⁄R]))) := by
    rw [ιMulti_span_fixedDegree]; exact hx
  refine Submodule.span_induction (p := fun x _ => involute x = x) ?_ ?_ ?_ ?_ this
  · rintro _ ⟨v, rfl⟩
    simp [ιMulti_apply, involute_prod_map_ι]
  · simp
  · intro a b _ _ ha hb; simp [ha, hb]
  · intro s x _ hx; simp [Algebra.smul_def, hx]

theorem d1_commute_ι (ω η : Ω[S⁄R]) : d1 R S ω * ι S η = ι S η * d1 R S ω := by
  have hspan : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction
    (p := fun ω _ => d1 R S ω * ι S η = ι S η * d1 R S ω) ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨t, rfl⟩; simp [d1_D]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy, add_mul, mul_add]
  · intro s x _ hx
    rw [d1_leibniz, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hx]
    have hswap1 := ι_add_mul_swap (R := S) (KaehlerDifferential.D R S s) η
    have hswap2 := ι_add_mul_swap (R := S) x η
    have hιx : ι S x * ι S η = -(ι S η * ι S x) :=
      add_eq_zero_iff_eq_neg.mp hswap2
    have hDs : ι S (KaehlerDifferential.D R S s) * ι S η =
        -(ι S η * ι S (KaehlerDifferential.D R S s)) :=
      add_eq_zero_iff_eq_neg.mp hswap1
    have hforms :
        ι S (KaehlerDifferential.D R S s) * ι S x * ι S η =
          ι S η * ι S (KaehlerDifferential.D R S s) * ι S x := by
      calc
        ι S (KaehlerDifferential.D R S s) * ι S x * ι S η
            = ι S (KaehlerDifferential.D R S s) * (ι S x * ι S η) := by
              rw [mul_assoc]
          _ = ι S (KaehlerDifferential.D R S s) * -(ι S η * ι S x) := by
              rw [hιx]
          _ = -(ι S (KaehlerDifferential.D R S s) * ι S η * ι S x) := by
              simp [neg_mul, mul_assoc]
          _ = -(-(ι S η * ι S (KaehlerDifferential.D R S s)) * ι S x) := by
              rw [hDs]
          _ = ι S η * ι S (KaehlerDifferential.D R S s) * ι S x := by
              simp [neg_mul, mul_assoc]
    simp [mul_assoc, hforms]

/-! ### Graded dual numbers, additive structure from the product -/

structure ExtDiff where
  val : ExtE R S
  dval : ExtE R S

namespace ExtDiff

variable {R S}

@[ext]
theorem ext {x y : ExtDiff R S} (h1 : x.val = y.val) (h2 : x.dval = y.dval) : x = y := by
  cases x; cases y; congr

def equivProd : ExtDiff R S ≃ ExtE R S × ExtE R S where
  toFun x := (x.val, x.dval)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (ExtDiff R S) :=
  (equivProd (R := R) (S := S)).addCommGroup

@[simp] theorem add_val (x y : ExtDiff R S) : (x + y).val = x.val + y.val := rfl
@[simp] theorem add_dval (x y : ExtDiff R S) : (x + y).dval = x.dval + y.dval := rfl
@[simp] theorem zero_val : (0 : ExtDiff R S).val = 0 := rfl
@[simp] theorem zero_dval : (0 : ExtDiff R S).dval = 0 := rfl
@[simp] theorem neg_val (x : ExtDiff R S) : (-x).val = -x.val := rfl
@[simp] theorem neg_dval (x : ExtDiff R S) : (-x).dval = -x.dval := rfl

noncomputable instance : One (ExtDiff R S) where one := ⟨1, 0⟩

noncomputable instance : Mul (ExtDiff R S) where
  mul x y := ⟨x.val * y.val, x.dval * y.val + involute x.val * y.dval⟩

@[simp] theorem one_val : (1 : ExtDiff R S).val = 1 := rfl
@[simp] theorem one_dval : (1 : ExtDiff R S).dval = 0 := rfl
@[simp] theorem mul_val (x y : ExtDiff R S) : (x * y).val = x.val * y.val := rfl
@[simp] theorem mul_dval (x y : ExtDiff R S) :
    (x * y).dval = x.dval * y.val + involute x.val * y.dval := rfl

noncomputable instance : Ring (ExtDiff R S) :=
  { (inferInstance : AddCommGroup (ExtDiff R S)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => by
      ext
      · simp [mul_assoc]
      · simp [mul_add, add_mul, mul_assoc, map_mul]; abel
    one_mul := fun a => by ext <;> simp [map_one]
    mul_one := fun a => by ext <;> simp
    zero_mul := fun _ => by ext <;> simp
    mul_zero := fun _ => by ext <;> simp
    left_distrib := fun _ _ _ => by ext <;> simp [mul_add]; abel
    right_distrib := fun _ _ _ => by ext <;> simp [add_mul, map_add]; abel }

theorem ι_mul_involute (s : S) (x : ExtE R S) :
    ι S (KaehlerDifferential.D R S s) * x =
      involute x * ι S (KaehlerDifferential.D R S s) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [Algebra.commutes]
  | add a b ha hb =>
    simp [ha, hb, add_mul, mul_add, map_add]
  | ι_mul a m ha =>
    have hswap := ι_add_mul_swap (R := S) (KaehlerDifferential.D R S s) m
    have hneg : ι S (KaehlerDifferential.D R S s) * ι S m =
        -(ι S m * ι S (KaehlerDifferential.D R S s)) :=
      add_eq_zero_iff_eq_neg.mp hswap
    calc
      ι S (KaehlerDifferential.D R S s) * (ι S m * a)
          = (ι S (KaehlerDifferential.D R S s) * ι S m) * a := by
            rw [← mul_assoc]
        _ = (-(ι S m * ι S (KaehlerDifferential.D R S s))) * a := by
            rw [hneg]
        _ = -(ι S m * (ι S (KaehlerDifferential.D R S s) * a)) := by
            simp [neg_mul, mul_assoc]
        _ = -(ι S m * (involute a * ι S (KaehlerDifferential.D R S s))) := by
            rw [ha]
        _ = involute (ι S m) * involute a * ι S (KaehlerDifferential.D R S s) := by
            simp [involute_ι, neg_mul, mul_assoc]
        _ = involute (ι S m * a) * ι S (KaehlerDifferential.D R S s) := by
            simp [map_mul, mul_assoc]

noncomputable instance : SMul S (ExtDiff R S) where
  smul s x := ⟨s • x.val, ι S (KaehlerDifferential.D R S s) * x.val + s • x.dval⟩

@[simp] theorem smul_val (s : S) (x : ExtDiff R S) : (s • x).val = s • x.val := rfl
@[simp] theorem smul_dval (s : S) (x : ExtDiff R S) :
    (s • x).dval = ι S (KaehlerDifferential.D R S s) * x.val + s • x.dval := rfl

noncomputable instance : Module S (ExtDiff R S) where
  one_smul x := by
    ext
    · simp
    · simp [(KaehlerDifferential.D R S).map_one_eq_zero]
  mul_smul s t x := by
    ext
    · simp [mul_smul]
    · simp only [smul_dval, smul_val, (KaehlerDifferential.D R S).leibniz, map_add, mul_add,
        add_mul, (ι S).map_smul, Algebra.smul_def, map_mul]
      have h1 : algebraMap S (ExtE R S) s * ι S (KaehlerDifferential.D R S t) * x.val =
          algebraMap S (ExtE R S) s * (ι S (KaehlerDifferential.D R S t) * x.val) :=
        mul_assoc _ _ _
      have h2 : algebraMap S (ExtE R S) t * ι S (KaehlerDifferential.D R S s) * x.val =
          ι S (KaehlerDifferential.D R S s) * (algebraMap S (ExtE R S) t * x.val) := by
        rw [Algebra.commutes t (ι S (KaehlerDifferential.D R S s)), mul_assoc]
      have h3 : algebraMap S (ExtE R S) s * algebraMap S (ExtE R S) t * x.dval =
          algebraMap S (ExtE R S) s * (algebraMap S (ExtE R S) t * x.dval) :=
        mul_assoc _ _ _
      rw [h1, h2, h3]
      abel
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by
    ext
    · simp [smul_add]
    · simp [mul_add, smul_add]; abel
  add_smul s t x := by
    ext
    · simp [add_smul]
    · simp [add_smul, (KaehlerDifferential.D R S).map_add, map_add, add_mul]; abel
  zero_smul _ := by
    ext
    · simp
    · simp [(KaehlerDifferential.D R S).map_zero]

noncomputable instance : Algebra S (ExtDiff R S) where
  algebraMap :=
    { toFun := fun s => ⟨algebraMap S (ExtE R S) s, ι S (KaehlerDifferential.D R S s)⟩
      map_one' := by ext <;> simp [(KaehlerDifferential.D R S).map_one_eq_zero]
      map_mul' := fun s t => by
        ext
        · simp
        · simp only [mul_dval, (KaehlerDifferential.D R S).leibniz, map_add, (ι S).map_smul,
            Algebra.smul_def, AlgHom.commutes]
          rw [Algebra.commutes s (ι S (KaehlerDifferential.D R S t)),
            Algebra.commutes t (ι S (KaehlerDifferential.D R S s))]
          abel
      map_zero' := by ext <;> simp
      map_add' := fun s t => by ext <;> simp [map_add] }
  commutes' := fun s x => by
    ext
    · simp [Algebra.commutes]
    · change
          ι S (KaehlerDifferential.D R S s) * x.val +
              involute (algebraMap S (ExtE R S) s) * x.dval =
            x.dval * algebraMap S (ExtE R S) s +
              involute x.val * ι S (KaehlerDifferential.D R S s)
      rw [ι_mul_involute, AlgHom.commutes, Algebra.commutes]
      abel
  smul_def' := fun s x => by
    ext
    · simp [Algebra.smul_def]
    · simp [Algebra.smul_def, AlgHom.commutes]

end ExtDiff

noncomputable def toExtDiff : Ω[S⁄R] →ₗ[S] ExtDiff R S where
  toFun ω := ⟨ι S ω, d1 R S ω⟩
  map_add' := by intros; ext <;> simp
  map_smul' s ω := by
    ext
    · simp
    · have hd : (algebraMap S (ExtDiff R S) s).dval =
          ι S (KaehlerDifferential.D R S s) := rfl
      have hv : (algebraMap S (ExtDiff R S) s).val =
          algebraMap S (ExtE R S) s := rfl
      simp [d1_leibniz, Algebra.smul_def, ExtDiff.mul_dval, hd, hv, AlgHom.commutes]

theorem toExtDiff_sq (ω : Ω[S⁄R]) : toExtDiff R S ω * toExtDiff R S ω = 0 := by
  ext
  · exact ExteriorAlgebra.ι_sq_zero ω
  · change d1 R S ω * ι S ω + involute (ι S ω) * d1 R S ω = 0
    rw [involute_ι, d1_commute_ι R S ω ω]
    simp [neg_mul]

noncomputable def liftExt : ExtE R S →ₐ[S] ExtDiff R S :=
  ExteriorAlgebra.lift S ⟨toExtDiff R S, toExtDiff_sq R S⟩

theorem liftExt_ι (ω : Ω[S⁄R]) : liftExt R S (ι S ω) = toExtDiff R S ω :=
  ExteriorAlgebra.lift_ι_apply (R := S) (toExtDiff R S) (toExtDiff_sq R S) ω

theorem liftExt_algebraMap (s : S) :
    liftExt R S (algebraMap S (ExtE R S) s) = algebraMap S (ExtDiff R S) s :=
  AlgHom.commutes _ s

noncomputable def dOnExterior : ExtE R S →ₗ[R] ExtE R S where
  toFun x := (liftExt R S x).dval
  map_add' := by intros; simp [map_add]
  map_smul' r x := by
    have hmap : algebraMap R (ExtE R S) r = algebraMap S (ExtE R S) (algebraMap R S r) :=
      (IsScalarTower.algebraMap_apply R S (ExtE R S) r).symm
    have hlift :
        liftExt R S (algebraMap S (ExtE R S) (algebraMap R S r) * x) =
          algebraMap S (ExtDiff R S) (algebraMap R S r) * liftExt R S x := by
      rw [map_mul, liftExt_algebraMap]
    simp only [Algebra.smul_def, hmap, hlift, ExtDiff.mul_dval]
    have hd :
        (algebraMap S (ExtDiff R S) (algebraMap R S r)).dval =
          ι S (KaehlerDifferential.D R S (algebraMap R S r)) := rfl
    have hv :
        (algebraMap S (ExtDiff R S) (algebraMap R S r)).val =
          algebraMap S (ExtE R S) (algebraMap R S r) := rfl
    rw [hd, hv, (KaehlerDifferential.D R S).map_algebraMap, map_zero, zero_mul, zero_add,
      AlgHom.commutes]
    simp [RingHom.id_apply, hmap]

theorem dOnExterior_apply (x : ExtE R S) :
    dOnExterior R S x = (liftExt R S x).dval := rfl

theorem liftExt_val (x : ExtE R S) : (liftExt R S x).val = x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap s =>
    rw [liftExt_algebraMap]; rfl
  | add a b ha hb =>
    simp [ha, hb]
  | ι_mul a m ha =>
    rw [map_mul, liftExt_ι]
    change ι S m * (liftExt R S a).val = ι S m * a
    rw [ha]

theorem dOnExterior_algebraMap (s : S) :
    dOnExterior R S (algebraMap S (ExtE R S) s) = ι S (KaehlerDifferential.D R S s) := by
  rw [dOnExterior_apply, liftExt_algebraMap]; rfl

theorem dOnExterior_mul (x y : ExtE R S) :
    dOnExterior R S (x * y) =
      dOnExterior R S x * y + involute x * dOnExterior R S y := by
  simp [dOnExterior_apply, map_mul, liftExt_val]

theorem dOnExterior_ι (ω : Ω[S⁄R]) : dOnExterior R S (ι S ω) = d1 R S ω := by
  rw [dOnExterior_apply, liftExt_ι]; rfl

theorem dOnExterior_d1 (ω : Ω[S⁄R]) : dOnExterior R S (d1 R S ω) = 0 := by
  have hspan : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun ω _ => dOnExterior R S (d1 R S ω) = 0)
    ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨t, rfl⟩; simp [d1_D]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro s x _ hx
    rw [d1_leibniz, map_add, dOnExterior_mul, dOnExterior_ι, d1_D, zero_mul, zero_add,
      involute_ι]
    rw [Algebra.smul_def, dOnExterior_mul, dOnExterior_algebraMap, hx, mul_zero, add_zero]
    rw [dOnExterior_ι]
    simp [neg_mul]

set_option maxHeartbeats 800000 in
theorem dOnExterior_sq (x : ExtE R S) : dOnExterior R S (dOnExterior R S x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap s =>
    rw [dOnExterior_algebraMap, dOnExterior_ι, d1_D]
  | add a b ha hb =>
    simp [ha, hb]
  | ι_mul a m ha =>
    rw [dOnExterior_mul, dOnExterior_ι, involute_ι]
    rw [map_add, dOnExterior_mul, dOnExterior_d1, zero_mul, zero_add]
    rw [dOnExterior_mul, map_neg, dOnExterior_ι, ha, mul_zero, add_zero]
    rw [involute_eq_self_of_mem_two (R := R) (S := S) (x := d1 R S m) (d1_mem_two R S m)]
    simp [neg_mul, map_neg]

theorem dOnExterior_mem_succ {n : ℕ} {x : ExtE R S} (hx : x ∈ ⋀[S]^n (Ω[S⁄R])) :
    dOnExterior R S x ∈ ⋀[S]^(n + 1) (Ω[S⁄R]) := by
  refine Submodule.pow_induction_on_left'
    (M := LinearMap.range (ι S : Ω[S⁄R] →ₗ[S] ExtE R S))
    (C := fun n x _ => dOnExterior R S x ∈ ⋀[S]^(n + 1) (Ω[S⁄R])) ?_ ?_ ?_ hx
  · intro s
    rw [dOnExterior_algebraMap]
    simpa [Submodule.pow_one] using LinearMap.mem_range_self (ι S) _
  · intro x y i _ _ hx hy
    simpa [map_add] using add_mem hx hy
  · intro m hm i x hx ih
    obtain ⟨ω, rfl⟩ := hm
    rw [dOnExterior_mul, dOnExterior_ι]
    refine add_mem ?_ ?_
    · have h2 := d1_mem_two R S ω
      have : d1 R S ω * x ∈ ⋀[S]^(2 + i) (Ω[S⁄R]) :=
        SetLike.mul_mem_graded h2 hx
      convert this using 2
      omega
    · have h1 : involute (ι S ω) ∈ ⋀[S]^1 (Ω[S⁄R]) := by
        rw [involute_ι]
        simpa [Submodule.pow_one] using neg_mem (LinearMap.mem_range_self (ι S) ω)
      have : involute (ι S ω) * dOnExterior R S x ∈ ⋀[S]^(1 + (i + 1)) (Ω[S⁄R]) :=
        SetLike.mul_mem_graded h1 ih
      convert this using 2
      omega

noncomputable def d (n : ℕ) :
    ⋀[S]^n (Ω[S⁄R]) →ₗ[R] ⋀[S]^(n + 1) (Ω[S⁄R]) :=
  let p := (⋀[S]^n (Ω[S⁄R])).restrictScalars R
  let q := (⋀[S]^(n + 1) (Ω[S⁄R])).restrictScalars R
  (dOnExterior R S).restrict (p := p) (q := q) fun x hx => dOnExterior_mem_succ R S hx

theorem d_comp_d (n : ℕ) : (d R S (n + 1)).comp (d R S n) = 0 := by
  ext x
  exact dOnExterior_sq R S (x : ExtE R S)

open ModuleCat

noncomputable abbrev deRhamTerm (n : ℕ) : ModuleCat R :=
  of R (⋀[S]^n (Ω[S⁄R]))

noncomputable def deRhamD (n : ℕ) : deRhamTerm R S n ⟶ deRhamTerm R S (n + 1) :=
  ofHom (d R S n)

theorem deRhamD_comp (n : ℕ) : deRhamD R S n ≫ deRhamD R S (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  exact d_comp_d R S n

namespace KaehlerDifferential

/--
  Algebraic de Rham complex of `S` over `R`.
  Terms are `⋀[S]^n (Ω[S⁄R])`.
  `d` is the exterior derivative of `KaehlerDifferential.D`.
-/
noncomputable def DeRhamComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (deRhamTerm R S) (deRhamD R S) fun n => deRhamD_comp R S n

/-- Total algebraic de Rham cohomology in degree `n`. One `ℕ` degree. Not `(p,q)`. -/
noncomputable abbrev deRhamCohomology (n : ℕ) : ModuleCat R :=
  (DeRhamComplex R S).homology n

/-- Embedding `n ↦ n+p` of `up ℕ` into itself. Image is degrees `≥ p`. -/
abbrev hodgeShapeEmbedding (p : ℕ) :
    ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' (ComplexShape.up ℕ) (ComplexShape.up ℕ) (· + p)
    (add_left_injective p) fun i j => by
      change i + 1 = j ↔ i + p + 1 = j + p
      constructor <;> intro h <;> omega

/--
  Stupid truncation `σ≥p` of the de Rham complex.
  This is the Hodge filtration on the complex.
-/
noncomputable def deRhamHodgeFiltration (p : ℕ) : CochainComplex (ModuleCat R) ℕ :=
  (DeRhamComplex R S).stupidTrunc (hodgeShapeEmbedding p)

instance hodgeShapeEmbedding_isTruncGE (p : ℕ) :
    (hodgeShapeEmbedding p).IsTruncGE where
  mem_next {j k'} h :=
    ⟨j + 1, by
      change (j + p) + 1 = k' at h
      change (j + 1) + p = k'
      omega⟩

/-- Inclusion `σ≥p ⟶ Ω^•`. House `ιStupidTrunc`. A chain map. -/
noncomputable def deRhamHodgeFiltrationι (p : ℕ) :
    deRhamHodgeFiltration R S p ⟶ DeRhamComplex R S :=
  (DeRhamComplex R S).ιStupidTrunc (hodgeShapeEmbedding p)

/-- Induced map `H^n(σ≥p) → H_dR^n`. -/
noncomputable def deRhamHodgeFilteredMap (p n : ℕ) :
    (deRhamHodgeFiltration R S p).homology n ⟶ deRhamCohomology R S n :=
  HomologicalComplex.homologyMap (deRhamHodgeFiltrationι R S p) n

/--
  `F^p H_dR^n := im(H^n(σ≥p) → H_dR^n)`.
  A submodule of total `deRhamCohomology n`. One `ℕ` degree.
  Not `H^{p,q}`. The associated graded is not `H^{p,q}`.
-/
noncomputable def deRhamHodgeFiltered (p n : ℕ) :
    Submodule R (deRhamCohomology R S n) :=
  LinearMap.range (deRhamHodgeFilteredMap R S p n).hom

/-- If `p ≤ q` then degrees `≥ q` sit inside degrees `≥ p`. -/
lemma hodgeShapeEmbedding_image_of_le {p q : ℕ} (hpq : p ≤ q) (i' : ℕ)
    (h : ∃ i, (hodgeShapeEmbedding q).f i = i') :
    ∃ j, (hodgeShapeEmbedding p).f j = i' := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i + (q - p), ?_⟩
  change i + (q - p) + p = i'
  change i + q = i' at hi
  omega

/-- Inclusion `σ≥q ⟶ σ≥p` when `p ≤ q`. A chain map. -/
noncomputable def deRhamHodgeFiltrationιLE {p q : ℕ} (hpq : p ≤ q) :
    deRhamHodgeFiltration R S q ⟶ deRhamHodgeFiltration R S p :=
  (DeRhamComplex R S).ιStupidTruncLE (hodgeShapeEmbedding q) (hodgeShapeEmbedding p)
    (hodgeShapeEmbedding_image_of_le hpq)

lemma deRhamHodgeFiltrationιLE_comp {p q : ℕ} (hpq : p ≤ q) :
    deRhamHodgeFiltrationιLE R S hpq ≫ deRhamHodgeFiltrationι R S p =
      deRhamHodgeFiltrationι R S q :=
  HomologicalComplex.ιStupidTruncLE_comp_ι (DeRhamComplex R S)
    (hodgeShapeEmbedding q) (hodgeShapeEmbedding p) (hodgeShapeEmbedding_image_of_le hpq)

/-- The Hodge filtration is decreasing: `p ≤ q` implies `F^q ⊆ F^p`. -/
theorem deRhamHodgeFiltered_antitone {p q n : ℕ} (hpq : p ≤ q) :
    deRhamHodgeFiltered R S q n ≤ deRhamHodgeFiltered R S p n := by
  have hcomp := deRhamHodgeFiltrationιLE_comp R S hpq
  have hmap :
      deRhamHodgeFilteredMap R S q n =
        HomologicalComplex.homologyMap (deRhamHodgeFiltrationιLE R S hpq) n ≫
          deRhamHodgeFilteredMap R S p n := by
    unfold deRhamHodgeFilteredMap
    rw [← hcomp, HomologicalComplex.homologyMap_comp]
  change LinearMap.range (deRhamHodgeFilteredMap R S q n).hom ≤
    LinearMap.range (deRhamHodgeFilteredMap R S p n).hom
  rw [hmap, ModuleCat.hom_comp]
  exact LinearMap.range_comp_le_range _ _

theorem deRhamHodgeFiltered_succ_le (p n : ℕ) :
    deRhamHodgeFiltered R S (p + 1) n ≤ deRhamHodgeFiltered R S p n :=
  deRhamHodgeFiltered_antitone R S (Nat.le_succ p)

/--
  Associated graded `Gr_F^p H_dR^n := F^p / (F^p ∩ F^{p+1})`.
  A quotient of submodules of one group. Not `H^{p,q}`.
  Hodge-to-de-Rham degeneracy would identify this with `H^{n-p}(X, Ω^p)`.
  That identification does not sit.
-/
noncomputable def deRhamHodgeAssociatedGraded (p n : ℕ) :=
  let Fp := deRhamHodgeFiltered R S p n
  Fp ⧸ Submodule.comap Fp.subtype (deRhamHodgeFiltered R S (p + 1) n)

/-- Same-filtration meet `F^p ∩ F^q`. Both sides are submodules of `H_dR^n`.
  Not `F^p ∩ F̄^q`. The conjugate filtration does not sit. -/
noncomputable def deRhamHodgeFilteredInf (p q n : ℕ) :
    Submodule R (deRhamCohomology R S n) :=
  deRhamHodgeFiltered R S p n ⊓ deRhamHodgeFiltered R S q n

theorem deRhamHodgeFilteredInf_eq_of_le {p q n : ℕ} (hpq : p ≤ q) :
    deRhamHodgeFilteredInf R S p q n = deRhamHodgeFiltered R S q n :=
  inf_eq_right.mpr (deRhamHodgeFiltered_antitone R S hpq)

end KaehlerDifferential
