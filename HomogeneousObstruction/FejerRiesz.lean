import HomogeneousObstruction.Basic

namespace HomogeneousObstruction

open Complex Metric Polynomial Real Set
open scoped BigOperators ComplexConjugate Polynomial

noncomputable section

/-!
# Strict Fejer--Riesz factorisation

The Laurent polynomial associated to a real trigonometric polynomial of actual
degree `L` is an ordinary polynomial of degree `2 * L`.  Conjugate symmetry of
the Laurent coefficients becomes invariance under `conjReflect` below.

The auxiliary root lemmas deliberately work with `Multiset`s.  Thus reciprocal
conjugate pairing retains root multiplicities, which is essential when roots
are repeated.
-/

/-- Reverse the coefficients of a complex polynomial and conjugate them. -/
def conjReflect (p : ℂ[X]) : ℂ[X] :=
  (p.map (starRingEnd ℂ)).reflect p.natDegree

/-- Reverse a product of linear factors at its exact (multiset) degree. -/
theorem reflect_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map fun a : ℂ => X - C a).prod).reflect s.card =
      (s.map fun a : ℂ => 1 - C a * X).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons]
      rw [show s.card + 1 = 1 + s.card by omega]
      rw [reflect_mul (X - C a) ((s.map fun a : ℂ => X - C a).prod)
        (F := 1) (G := s.card) (by simp) (by simp)]
      rw [ih]
      simp [sub_eq_add_neg]

private theorem one_sub_C_mul_X_eq (a : ℂ) (ha : a ≠ 0) :
    (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
  rw [mul_sub]
  simp only [map_neg, ← C.map_mul, neg_mul]
  rw [mul_inv_cancel₀ ha]
  simp
  ring

/-- Explicit factorisation of a reflected polynomial through the inverses of
its roots.  The nonzero constant coefficient rules out the exceptional root
zero. -/
theorem reflect_eq_C_mul_prod_inv_roots (p : ℂ[X]) (hp : p ≠ 0)
    (h0 : p.coeff 0 ≠ 0) :
    p.reflect p.natDegree =
      C (p.leadingCoeff * (p.roots.map fun a => -a).prod) *
        (p.roots.map fun a => X - C a⁻¹).prod := by
  have hs := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := hs.natDegree_eq_card_roots.symm
  rw [congrArg (fun r : ℂ[X] => r.reflect p.natDegree) hs.eq_prod_roots]
  rw [show p.natDegree = 0 + p.roots.card by omega]
  rw [reflect_mul (C p.leadingCoeff)
    ((p.roots.map fun a => X - C a).prod) (F := 0) (G := p.roots.card)
    (by simp) (by simp)]
  rw [reflect_prod_X_sub_C]
  simp only [reflect_C, pow_zero, mul_one]
  have hroot0 : ∀ a ∈ p.roots, a ≠ 0 := by
    intro a ha ha0
    subst a
    have he : p.eval 0 = 0 := (mem_roots hp).mp ha
    exact h0 ((coeff_zero_eq_eval_zero p).trans he)
  rw [Multiset.map_congr rfl (fun a ha => one_sub_C_mul_X_eq a (hroot0 a ha))]
  rw [Multiset.prod_map_mul]
  have hC := map_multiset_prod C (p.roots.map fun a => -a)
  simp only [Multiset.map_map, Function.comp_apply] at hC
  rw [← hC, ← mul_assoc, ← C.map_mul]

/-- Reversing a complex polynomial sends its root multiset to the inverse root
multiset, including all multiplicities. -/
theorem roots_reflect (p : ℂ[X]) (hp : p ≠ 0) (h0 : p.coeff 0 ≠ 0) :
    (p.reflect p.natDegree).roots = p.roots.map Inv.inv := by
  rw [reflect_eq_C_mul_prod_inv_roots p hp h0]
  rw [roots_C_mul _]
  · simpa only [Multiset.map_map, Function.comp_apply] using
      roots_multiset_prod_X_sub_C (p.roots.map Inv.inv)
  · exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) <|
      Multiset.prod_ne_zero <| by
        simp only [Multiset.mem_map, not_exists, not_and]
        intro a ha hnega
        have ha0 : a = 0 := neg_eq_zero.mp hnega
        subst a
        have he : p.eval 0 = 0 := (mem_roots hp).mp ha
        exact h0 ((coeff_zero_eq_eval_zero p).trans he)

/-- Conjugate-reflection sends each root `a` to `conj(a)⁻¹`, retaining its
multiplicity. -/
theorem roots_conjReflect (p : ℂ[X]) (hp : p ≠ 0) (h0 : p.coeff 0 ≠ 0) :
    (conjReflect p).roots =
      p.roots.map (fun a => (starRingEnd ℂ a)⁻¹) := by
  have hdeg : (p.map (starRingEnd ℂ)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (starRingEnd ℂ).injective p
  unfold conjReflect
  rw [← hdeg, roots_reflect (p.map (starRingEnd ℂ))]
  · rw [(IsAlgClosed.splits p).roots_map]
    simp only [Multiset.map_map, Function.comp_apply]
  · exact (p.map_ne_zero_iff (starRingEnd ℂ).injective).mpr hp
  · rw [coeff_map]
    intro hc
    apply h0
    exact (starRingEnd ℂ).injective (hc.trans (map_zero _).symm)

/-- Reciprocal conjugation, the root-pairing involution for self-inversive
polynomials. -/
def reciprocalConj (z : ℂ) : ℂ := (starRingEnd ℂ z)⁻¹

@[simp] theorem reciprocalConj_zero : reciprocalConj 0 = 0 := by
  simp [reciprocalConj]

@[simp] theorem reciprocalConj_reciprocalConj (z : ℂ) :
    reciprocalConj (reciprocalConj z) = z := by
  simp [reciprocalConj, map_inv₀]

theorem reciprocalConj_injective : Function.Injective reciprocalConj :=
  fun a b h => by
    rw [← reciprocalConj_reciprocalConj a, h, reciprocalConj_reciprocalConj]

@[simp] theorem norm_reciprocalConj (z : ℂ) :
    ‖reciprocalConj z‖ = ‖z‖⁻¹ := by
  simp [reciprocalConj, norm_inv]

/-- The roots of a strictly nonvanishing self-inversive polynomial split into
equal multisets outside and inside the unit circle.  The inside multiset is the
reciprocal-conjugate image of the outside one. -/
theorem selfInversive_root_partition {A : ℂ[X]} {L : ℕ}
    (hdeg : A.natDegree = 2 * L) (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hunit : ∀ a ∈ A.roots, ‖a‖ ≠ 1) :
    let outside := A.roots.filter (fun a => 1 < ‖a‖)
    outside.card = L ∧
      A.roots = outside + outside.map reciprocalConj := by
  have hA : A ≠ 0 := by
    intro h
    subst A
    simp at h0
  have hroot_ne : ∀ a ∈ A.roots, a ≠ 0 := by
    intro a ha ha0
    subst a
    have he : A.eval 0 = 0 := (mem_roots hA).mp ha
    exact h0 ((coeff_zero_eq_eval_zero A).trans he)
  have hroot_pair : A.roots.map reciprocalConj = A.roots := by
    calc
      A.roots.map reciprocalConj = (conjReflect A).roots := by
        simpa only [reciprocalConj] using (roots_conjReflect A hA h0).symm
      _ = A.roots := congrArg roots hself
  let outside := A.roots.filter (fun a => 1 < ‖a‖)
  let inside := A.roots.filter (fun a => ‖a‖ < 1)
  have hinside : inside = outside.map reciprocalConj := by
    unfold inside outside
    calc
      A.roots.filter (fun a => ‖a‖ < 1) =
          (A.roots.map reciprocalConj).filter (fun a => ‖a‖ < 1) := by
            rw [hroot_pair]
      _ = Multiset.map reciprocalConj
          (A.roots.filter (fun a => ‖reciprocalConj a‖ < 1)) := by
            rw [Multiset.filter_map]
            rfl
      _ = Multiset.map reciprocalConj
          (A.roots.filter (fun a => 1 < ‖a‖)) := by
            congr 1
            apply Multiset.filter_congr
            intro a ha
            rw [norm_reciprocalConj, inv_lt_one₀ (norm_pos_iff.mpr (hroot_ne a ha))]
  have hnotoutside :
      A.roots.filter (fun a => ¬1 < ‖a‖) = inside := by
    unfold inside
    apply Multiset.filter_congr
    intro a ha
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (hunit a ha)
    · intro h
      exact not_lt_of_ge h.le
  have hpartition : outside + inside = A.roots := by
    unfold outside
    rw [← hnotoutside]
    exact Multiset.filter_add_not (fun a : ℂ => 1 < ‖a‖) A.roots
  have hroots_card : A.roots.card = 2 * L := by
    rw [← (IsAlgClosed.splits A).natDegree_eq_card_roots, hdeg]
  have hout_card : outside.card = L := by
    have hc := congrArg Multiset.card hpartition
    simp only [Multiset.card_add] at hc
    have hic := congrArg Multiset.card hinside
    simp only [Multiset.card_map] at hic
    omega
  refine ⟨hout_card, ?_⟩
  calc
    A.roots = outside + inside := hpartition.symm
    _ = outside + outside.map reciprocalConj := congrArg (outside + ·) hinside

/-- Strict positivity of the Laurent trace excludes roots of the associated
ordinary polynomial on the unit circle. -/
theorem no_unit_roots_of_positive_laurent_representation
    {p : ℝ → ℝ} {A : ℂ[X]} {L : ℕ}
    (hA : A ≠ 0)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((θ : ℂ) * I)))
    (hpos : ∀ θ, 0 < p θ) :
    ∀ a ∈ A.roots, ‖a‖ ≠ 1 := by
  intro a ha hnorm
  have hasphere : a ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere] using hnorm
  have hrange : range (circleMap 0 1) = sphere (0 : ℂ) 1 := by
    simpa using range_circleMap (0 : ℂ) 1
  rw [← hrange] at hasphere
  obtain ⟨θ, hθ⟩ := hasphere
  have hz : Complex.exp ((θ : ℂ) * I) = a := by
    simpa [circleMap_zero] using hθ
  have haeval : A.eval a = 0 := (mem_roots hA).mp ha
  have hpzero : (p θ : ℂ) = 0 := by
    rw [hrep θ, hz, haeval, mul_zero]
  exact (ne_of_gt (hpos θ)) (ofReal_eq_zero.mp hpzero)

private theorem reciprocal_pair_identity (z b : ℂ) (hz : ‖z‖ = 1) (hb : b ≠ 0) :
    z⁻¹ * (z - b) * (z - reciprocalConj b) =
      (-b) * ((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
  rw [show (((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ)) =
    (starRingEnd ℂ (1 - b⁻¹ * z)) * (1 - b⁻¹ * z) by
      rw [Complex.conj_mul']
      norm_cast]
  simp only [map_sub, map_one, map_mul, map_inv₀, reciprocalConj]
  rw [← Complex.inv_eq_conj hz]
  field_simp [hb, hz0]
  ring

/-- Evaluation form of reciprocal-conjugate root pairing on the unit circle. -/
theorem laurent_eval_eq_pair_product {A : ℂ[X]} {L : ℕ} (s : Multiset ℂ)
    (hcard : s.card = L)
    (hroots : A.roots = s + s.map reciprocalConj)
    (hsne : ∀ b ∈ s, b ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    z⁻¹ ^ L * A.eval z =
      (A.leadingCoeff * (s.map fun b => -b).prod) *
        (s.map fun b => (((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ))).prod := by
  rw [(IsAlgClosed.splits A).eval_eq_prod_roots]
  rw [hroots, Multiset.map_add, Multiset.prod_add]
  simp only [Multiset.map_map, Function.comp_apply]
  calc
    z⁻¹ ^ L *
        (A.leadingCoeff * ((s.map fun b => z - b).prod *
          (s.map fun b => z - reciprocalConj b).prod)) =
      A.leadingCoeff *
        (s.map fun b => z⁻¹ * (z - b) * (z - reciprocalConj b)).prod := by
          rw [Multiset.prod_map_mul]
          rw [Multiset.prod_map_mul]
          simp only [Multiset.map_const', Multiset.prod_replicate, hcard]
          ring
    _ = A.leadingCoeff *
        (s.map fun b => (-b) * (((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ))).prod := by
          congr 1
          apply congrArg Multiset.prod
          apply Multiset.map_congr rfl
          intro b hb
          exact reciprocal_pair_identity z b hz (hsne b hb)
    _ = (A.leadingCoeff * (s.map fun b => -b).prod) *
        (s.map fun b => (((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ))).prod := by
          rw [Multiset.prod_map_mul]
          ring

/-- The product form exported by strict Fejer--Riesz.  `D` is an a priori
Fourier-degree bound, while `L` is the actual factor count. -/
structure StrictFejerRieszData (p : ℝ → ℝ) (D : ℕ) where
  L : ℕ
  degree_le : L ≤ D
  alpha : Fin L → ℂ
  alpha_ne_zero : ∀ j, alpha j ≠ 0
  alpha_norm_lt_one : ∀ j, ‖alpha j‖ < 1
  c : ℝ
  c_pos : 0 < c
  factorization : ∀ θ : ℝ,
    p θ = c * ∏ j, ‖1 - alpha j * Complex.exp ((θ : ℂ) * I)‖ ^ 2

/-- The zero-free polynomial appearing in the statement of strict
Fejer--Riesz, recovered from the inside-disk parameters. -/
noncomputable def StrictFejerRieszData.spectralFactor
    {p : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D) : ℂ[X] :=
  C (Real.sqrt data.c : ℂ) * ∏ j, (1 - C (data.alpha j) * X)

theorem StrictFejerRieszData.spectralFactor_natDegree
    {p : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D) :
    data.spectralFactor.natDegree = data.L := by
  rw [StrictFejerRieszData.spectralFactor,
    natDegree_C_mul (by exact_mod_cast Real.sqrt_ne_zero'.mpr data.c_pos)]
  have hfactor_ne : ∀ j ∈ (Finset.univ : Finset (Fin data.L)),
      (1 - C (data.alpha j) * X : ℂ[X]) ≠ 0 := by
    intro j _ hzero
    have heval := congrArg (Polynomial.eval (0 : ℂ)) hzero
    simp at heval
  rw [Polynomial.natDegree_prod
    (s := (Finset.univ : Finset (Fin data.L)))
    (f := fun j : Fin data.L => (1 - C (data.alpha j) * X : ℂ[X])) hfactor_ne]
  calc
    ∑ j ∈ (Finset.univ : Finset (Fin data.L)),
        (1 - C (data.alpha j) * X).natDegree =
        ∑ _j ∈ (Finset.univ : Finset (Fin data.L)), 1 := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (1 - C (data.alpha j) * X).natDegree =
            (C (data.alpha j) * X).natDegree :=
          natDegree_sub_eq_right_of_natDegree_lt (by
            rw [natDegree_C_mul_X _ (data.alpha_ne_zero j)]
            simp)
        _ = 1 := natDegree_C_mul_X _ (data.alpha_ne_zero j)
    _ = data.L := by simp

theorem StrictFejerRieszData.spectralFactor_ne_zero_closedDisk
    {p : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Polynomial.eval z data.spectralFactor ≠ 0 := by
  rw [StrictFejerRieszData.spectralFactor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod]
  apply mul_ne_zero
  · exact_mod_cast Real.sqrt_ne_zero'.mpr data.c_pos
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _ hzero
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at hzero
    have heq : data.alpha j * z = 1 := (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (data.alpha j), norm_nonneg z,
      data.alpha_norm_lt_one j]

theorem StrictFejerRieszData.spectralFactor_factorization
    {p : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D) (θ : ℝ) :
    p θ = ‖Polynomial.eval (Complex.exp ((θ : ℂ) * I)) data.spectralFactor‖ ^ 2 := by
  rw [data.factorization, StrictFejerRieszData.spectralFactor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, norm_mul,
    norm_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_pow, Finset.prod_pow]
  have hsqrt : ‖(Real.sqrt data.c : ℂ)‖ ^ 2 = data.c := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg data.c), Real.sq_sqrt data.c_pos.le]
  rw [hsqrt]

/-- Polynomial-form strict Fejer--Riesz data, matching Lemma 5.1 in the
paper: `Q` has its stated degree, has no zero in the closed unit disk, and its
unit-circle squared norm is the positive trigonometric polynomial. -/
structure StrictFejerRieszPolynomialData (p : ℝ → ℝ) (D : ℕ) where
  L : ℕ
  degree_le : L ≤ D
  Q : ℂ[X]
  degree_eq : Q.natDegree = L
  zero_free_closedDisk : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0
  factorization : ∀ θ : ℝ,
    p θ = ‖Q.eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2

noncomputable def StrictFejerRieszData.toPolynomialData
    {p : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D) :
    StrictFejerRieszPolynomialData p D where
  L := data.L
  degree_le := data.degree_le
  Q := data.spectralFactor
  degree_eq := data.spectralFactor_natDegree
  zero_free_closedDisk := fun _ hz => data.spectralFactor_ne_zero_closedDisk hz
  factorization := data.spectralFactor_factorization

private theorem prod_fin_toList {α M : Type*} [CommMonoid M]
    (s : Multiset α) (f : α → M) :
    ∏ j : Fin s.toList.length, f s.toList[j.1] = (s.map f).prod := by
  rw [Fin.prod_univ_fun_getElem]
  simpa using congrArg Multiset.prod (Multiset.coe_toList (s.map f))

private theorem coe_multiset_prod (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map fun x => ((f x : ℝ) : ℂ)).prod = ((s.map f).prod : ℂ) := by
  rw [show ((s.map f).prod : ℂ) = Complex.ofRealHom (s.map f).prod by rfl]
  rw [map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/-- Strict Fejer--Riesz factorisation in the algebraic form used by the
logarithmic Fourier estimate.

`A` is the ordinary polynomial obtained from the Laurent polynomial by
multiplication by `z^L`; consequently its degree is `2L` and its unit-circle
trace is `z⁻ᴸ A(z)`.  The conclusion uses the zero-free factor, written with
parameters `alpha` strictly inside the open unit disk. -/
noncomputable def strictFejerRieszDataOfSelfInversive
    {p : ℝ → ℝ} {D L : ℕ} (A : ℂ[X])
    (hLD : L ≤ D)
    (hdeg : A.natDegree = 2 * L)
    (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((θ : ℂ) * I)))
    (hpos : ∀ θ, 0 < p θ) :
    StrictFejerRieszData p D := by
  have hA : A ≠ 0 := by
    intro h
    subst A
    simp at h0
  have hunit := no_unit_roots_of_positive_laurent_representation hA hrep hpos
  let s := A.roots.filter (fun a => 1 < ‖a‖)
  obtain ⟨hscard, hroots⟩ := selfInversive_root_partition hdeg h0 hself hunit
  change s.card = L at hscard
  change A.roots = s + s.map reciprocalConj at hroots
  have hsne : ∀ b ∈ s, b ≠ 0 := by
    intro b hb hb0
    subst b
    have hbout : 1 < ‖(0 : ℂ)‖ := (Multiset.mem_filter.mp hb).2
    norm_num at hbout
  let K : ℂ := A.leadingCoeff * (s.map fun b => -b).prod
  let r0 : ℝ := (s.map fun b => ‖1 - b⁻¹‖ ^ 2).prod
  have hr0pos : 0 < r0 := by
    apply Multiset.prod_pos
    intro r hr
    rw [Multiset.mem_map] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    have hbout : 1 < ‖b‖ := (Multiset.mem_filter.mp hb).2
    have hbnorm : 0 < ‖b‖ := lt_trans zero_lt_one hbout
    have hbinv : ‖b⁻¹‖ < 1 := by
      rw [norm_inv, inv_lt_one₀ hbnorm]
      exact hbout
    have hne : 1 - b⁻¹ ≠ 0 := by
      intro h
      have heq : b⁻¹ = 1 := (sub_eq_zero.mp h).symm
      have := congrArg norm heq
      simp only [norm_one] at this
      linarith
    positivity
  have hz0 : ‖Complex.exp (((0 : ℝ) : ℂ) * I)‖ = 1 := by simp
  have hpair0 := laurent_eval_eq_pair_product s hscard hroots hsne
    (Complex.exp (((0 : ℝ) : ℂ) * I)) hz0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, inv_one, one_pow, one_mul,
    mul_one] at hpair0
  change A.eval 1 = K *
    (s.map fun b => (((‖1 - b⁻¹‖ ^ 2 : ℝ) : ℂ))).prod at hpair0
  have hcoe0 := coe_multiset_prod s (fun b => ‖1 - b⁻¹‖ ^ 2)
  have heq0 : (p 0 : ℂ) = K * (r0 : ℂ) := by
    have hrep0 : (p 0 : ℂ) = A.eval 1 := by simpa using hrep 0
    rw [hrep0, hpair0]
    change K * (s.map fun b => (((‖1 - b⁻¹‖ ^ 2 : ℝ) : ℂ))).prod = K * (r0 : ℂ)
    rw [hcoe0]
  have hKre : 0 < K.re := by
    have hre := congrArg Complex.re heq0
    simp only [ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero] at hre
    nlinarith [hpos 0, hr0pos]
  have hKim : K.im = 0 := by
    have him := congrArg Complex.im heq0
    simp only [ofReal_im, mul_im, ofReal_re, mul_zero, zero_add] at him
    nlinarith [hr0pos]
  have hK : K = (K.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hKim]
  let rootsList := s.toList
  let alpha : Fin rootsList.length → ℂ := fun j => rootsList[j.1]⁻¹
  refine
    { L := rootsList.length
      degree_le := ?_
      alpha := alpha
      alpha_ne_zero := ?_
      alpha_norm_lt_one := ?_
      c := K.re
      c_pos := hKre
      factorization := ?_ }
  · rw [show rootsList.length = L by simpa [rootsList] using hscard]
    exact hLD
  · intro j
    apply inv_ne_zero
    apply hsne rootsList[j.1]
    have hjlist : rootsList[j.1] ∈ rootsList := List.getElem_mem j.2
    change s.toList[j.1] ∈ s
    exact Multiset.mem_toList.mp hjlist
  · intro j
    have hjlist : rootsList[j.1] ∈ rootsList := List.getElem_mem j.2
    have hjs : rootsList[j.1] ∈ s := by
      change s.toList[j.1] ∈ s.toList at hjlist
      exact Multiset.mem_toList.mp hjlist
    have hjout : 1 < ‖rootsList[j.1]‖ := (Multiset.mem_filter.mp hjs).2
    have hjpos : 0 < ‖rootsList[j.1]‖ := lt_trans zero_lt_one hjout
    simp only [alpha, norm_inv]
    rwa [inv_lt_one₀ hjpos]
  · intro θ
    let z := Complex.exp ((θ : ℂ) * I)
    have hz : ‖z‖ = 1 := by simp [z]
    have hpair := laurent_eval_eq_pair_product s hscard hroots hsne z hz
    have hcoe := coe_multiset_prod s (fun b => ‖1 - b⁻¹ * z‖ ^ 2)
    have heq : (p θ : ℂ) = K *
        (s.map fun b => (((‖1 - b⁻¹ * z‖ ^ 2 : ℝ) : ℂ))).prod := by
      rw [hrep θ]
      rw [hpair]
    rw [hK, hcoe] at heq
    have hre := congrArg Complex.re heq
    simp only [ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero] at hre
    have hfin := prod_fin_toList s (fun b => ‖1 - b⁻¹ * z‖ ^ 2)
    calc
      p θ = K.re * (s.map fun b => ‖1 - b⁻¹ * z‖ ^ 2).prod := hre
      _ = K.re * ∏ j, ‖1 - alpha j * Complex.exp ((θ : ℂ) * I)‖ ^ 2 := by
        apply congrArg (K.re * ·)
        simpa [rootsList, alpha, z] using hfin.symm

/-- The theorem-form interface to `strictFejerRieszDataOfSelfInversive`. -/
theorem strictFejerRiesz_of_selfInversive
    {p : ℝ → ℝ} {D L : ℕ} (A : ℂ[X])
    (hLD : L ≤ D)
    (hdeg : A.natDegree = 2 * L)
    (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((θ : ℂ) * I)))
    (hpos : ∀ θ, 0 < p θ) :
  Nonempty (StrictFejerRieszData p D) :=
  ⟨strictFejerRieszDataOfSelfInversive A hLD hdeg h0 hself hrep hpos⟩

/-- The polynomial-form statement of strict Fejer--Riesz obtained from the
self-inversive Laurent polynomial. -/
theorem strictFejerRiesz_polynomial_of_selfInversive
    {p : ℝ → ℝ} {D L : ℕ} (A : ℂ[X])
    (hLD : L ≤ D)
    (hdeg : A.natDegree = 2 * L)
    (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((θ : ℂ) * I)))
    (hpos : ∀ θ, 0 < p θ) :
    Nonempty (StrictFejerRieszPolynomialData p D) := by
  obtain ⟨data⟩ := strictFejerRiesz_of_selfInversive A hLD hdeg h0 hself hrep hpos
  exact ⟨data.toPolynomialData⟩

private theorem padded_coeff_symmetry {A : ℂ[X]} {D : ℕ}
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A) (i : ℕ) :
    A.coeff i = starRingEnd ℂ (A.coeff (Polynomial.revAt (2 * D) i)) := by
  calc
    A.coeff i = ((A.map (starRingEnd ℂ)).reflect (2 * D)).coeff i :=
      congrArg (fun q : ℂ[X] => q.coeff i) hself.symm
    _ = starRingEnd ℂ (A.coeff (Polynomial.revAt (2 * D) i)) := by
      rw [coeff_reflect, coeff_map]

private theorem padded_natTrailingDegree {A : ℂ[X]} {D : ℕ}
    (hA : A ≠ 0) (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A) :
    A.natTrailingDegree = 2 * D - A.natDegree := by
  let n := A.natDegree
  let k := 2 * D - n
  have hnk : n + k = 2 * D := by omega
  have hcoeff := padded_coeff_symmetry hself
  have hknz : A.coeff k ≠ 0 := by
    have hnz : A.coeff n ≠ 0 := by
      change A.leadingCoeff ≠ 0
      exact leadingCoeff_ne_zero.mpr hA
    have hsymn := hcoeff n
    rw [Polynomial.revAt_le hdeg] at hsymn
    change A.coeff n = starRingEnd ℂ (A.coeff k) at hsymn
    intro hk
    apply hnz
    rw [hsymn, hk, map_zero]
  apply le_antisymm
  · exact natTrailingDegree_le_of_ne_zero hknz
  · apply le_natTrailingDegree hA
    intro i hi
    rw [hcoeff i]
    have hin : n < Polynomial.revAt (2 * D) i := by
      rw [Polynomial.revAt_le (le_trans (Nat.le_of_lt hi) (Nat.sub_le _ _))]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hin, map_zero]

private theorem padded_center_le_natDegree {A : ℂ[X]} {D : ℕ}
    (hA : A ≠ 0) (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A) :
    D ≤ A.natDegree := by
  have ht := padded_natTrailingDegree hA hdeg hself
  have hle := A.natTrailingDegree_le_natDegree
  omega

private theorem reverse_natDegree_of_padded {A : ℂ[X]} {D : ℕ}
    (hA : A ≠ 0) (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A) :
    A.reverse.natDegree = 2 * (A.natDegree - D) := by
  rw [reverse_natDegree, padded_natTrailingDegree hA hdeg hself]
  have hDn := padded_center_le_natDegree hA hdeg hself
  omega

private theorem reverse_conjReflect_of_padded {A : ℂ[X]} {D : ℕ}
    (hA : A ≠ 0) (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A) :
    conjReflect A.reverse = A.reverse := by
  let n := A.natDegree
  let k := 2 * D - n
  let m := n - k
  have ht := padded_natTrailingDegree hA hdeg hself
  have hDn := padded_center_le_natDegree hA hdeg hself
  have hBdeg : A.reverse.natDegree = m := by
    rw [reverse_natDegree, ht]
  have hmn : m ≤ n := Nat.sub_le _ _
  have hcoeff := padded_coeff_symmetry hself
  ext i
  unfold conjReflect
  rw [coeff_reflect, coeff_map]
  rw [hBdeg]
  by_cases hi : i ≤ m
  · rw [Polynomial.revAt_le hi]
    rw [coeff_reverse, Polynomial.revAt_le (Nat.sub_le _ _ |>.trans hmn)]
    rw [coeff_reverse, Polynomial.revAt_le (hi.trans hmn)]
    have hsym := hcoeff (n - i)
    rw [Polynomial.revAt_le ((Nat.sub_le _ _).trans hdeg)] at hsym
    change A.coeff (n - i) = starRingEnd ℂ (A.coeff (2 * D - (n - i))) at hsym
    have he1 : n - (m - i) = k + i := by omega
    have he2 : 2 * D - (n - i) = k + i := by omega
    rw [he2] at hsym
    rw [he1]
    exact hsym.symm
  · have him : m < i := Nat.lt_of_not_ge hi
    rw [Polynomial.revAt_eq_self_of_lt him]
    rw [coeff_eq_zero_of_natDegree_lt (hBdeg ▸ him), map_zero]

private theorem reverse_coeff_zero_ne_of_ne {A : ℂ[X]} (hA : A ≠ 0) :
    A.reverse.coeff 0 ≠ 0 := by
  rw [coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr hA

private theorem reverse_laurent_representation_of_padded
    {p : ℝ → ℝ} {A : ℂ[X]} {D : ℕ}
    (hA : A ≠ 0) (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ D *
        A.eval (Complex.exp ((θ : ℂ) * I))) :
    ∀ θ : ℝ, (p (-θ) : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ (A.natDegree - D) *
        A.reverse.eval (Complex.exp ((θ : ℂ) * I)) := by
  intro θ
  let z := Complex.exp ((θ : ℂ) * I)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzneg : Complex.exp (((-θ : ℝ) : ℂ) * I) = z⁻¹ := by
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
  letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
  have hev := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z⁻¹) A
  simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at hev
  have hDn := padded_center_le_natDegree hA hdeg hself
  rw [hrep (-θ), hzneg, inv_inv]
  change z ^ D * A.eval z⁻¹ =
    z⁻¹ ^ (A.natDegree - D) * A.reverse.eval z
  rw [← hev]
  let L := A.natDegree - D
  have hn : A.natDegree = D + L := by omega
  have hcancel : z ^ D * (z⁻¹) ^ D = 1 := by
    rw [← mul_pow]
    simp [hz0]
  change z ^ D * (A.reverse.eval z * (z⁻¹) ^ A.natDegree) =
    (z⁻¹) ^ L * A.reverse.eval z
  rw [hn, pow_add]
  calc
    z ^ D * (A.reverse.eval z * ((z⁻¹) ^ D * (z⁻¹) ^ L)) =
        (z ^ D * (z⁻¹) ^ D) * ((z⁻¹) ^ L * A.reverse.eval z) := by ring
    _ = (z⁻¹) ^ L * A.reverse.eval z := by rw [hcancel, one_mul]

private theorem norm_one_sub_mul_exp_neg (a : ℂ) (θ : ℝ) :
    ‖1 - a * Complex.exp (((-θ : ℝ) : ℂ) * I)‖ =
      ‖1 - starRingEnd ℂ a * Complex.exp ((θ : ℂ) * I)‖ := by
  rw [← Complex.norm_conj]
  congr 1
  simp only [map_sub, map_one, map_mul]
  congr 2
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  apply Complex.ext <;> simp

/-- Conjugating the disk roots changes a factorisation of `p (-θ)` into one
of `p θ`; the factor count and strict disk bounds are unchanged. -/
noncomputable def StrictFejerRieszData.of_neg
    {p : ℝ → ℝ} {D : ℕ}
    (data : StrictFejerRieszData (fun θ => p (-θ)) D) :
    StrictFejerRieszData p D := by
  refine
    { L := data.L
      degree_le := data.degree_le
      alpha := fun j => starRingEnd ℂ (data.alpha j)
      alpha_ne_zero := ?_
      alpha_norm_lt_one := ?_
      c := data.c
      c_pos := data.c_pos
      factorization := ?_ }
  · intro j h
    exact data.alpha_ne_zero j ((starRingEnd ℂ).injective (h.trans (map_zero _).symm))
  · intro j
    simpa only [Complex.norm_conj] using data.alpha_norm_lt_one j
  · intro θ
    have hfac := data.factorization (-θ)
    simp only [neg_neg] at hfac
    rw [hfac]
    apply congrArg (data.c * ·)
    apply Finset.prod_congr rfl
    intro j _
    rw [norm_one_sub_mul_exp_neg]

/-- Strict Fejer--Riesz for a Laurent polynomial stored with a padded degree.
Zero coefficients at both ends are removed internally; no endpoint
nonvanishing assumption is required. -/
theorem strictFejerRiesz_of_padded_selfInversive
    {p : ℝ → ℝ} {D : ℕ} (A : ℂ[X])
    (hA : A ≠ 0)
    (hdeg : A.natDegree ≤ 2 * D)
    (hself : (A.map (starRingEnd ℂ)).reflect (2 * D) = A)
    (hrep : ∀ θ : ℝ, (p θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ D *
        A.eval (Complex.exp ((θ : ℂ) * I)))
    (hpos : ∀ θ, 0 < p θ) :
    Nonempty (StrictFejerRieszData p D) := by
  let L := A.natDegree - D
  have hLD : L ≤ D := by
    dsimp [L]
    omega
  have hBdeg : A.reverse.natDegree = 2 * L := by
    simpa [L] using reverse_natDegree_of_padded hA hdeg hself
  have hB0 : A.reverse.coeff 0 ≠ 0 := reverse_coeff_zero_ne_of_ne hA
  have hBself : conjReflect A.reverse = A.reverse :=
    reverse_conjReflect_of_padded hA hdeg hself
  have hBrep : ∀ θ : ℝ, ((fun t => p (-t)) θ : ℂ) =
      (Complex.exp ((θ : ℂ) * I))⁻¹ ^ L *
        A.reverse.eval (Complex.exp ((θ : ℂ) * I)) := by
    simpa [L] using reverse_laurent_representation_of_padded hA hdeg hself hrep
  have hBpos : ∀ θ : ℝ, 0 < (fun t => p (-t)) θ := fun θ => hpos (-θ)
  obtain ⟨data⟩ := strictFejerRiesz_of_selfInversive A.reverse hLD hBdeg hB0 hBself hBrep hBpos
  exact ⟨data.of_neg⟩

end

end HomogeneousObstruction
