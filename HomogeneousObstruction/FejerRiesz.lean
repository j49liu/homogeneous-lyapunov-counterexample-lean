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
    simpa only [abs_one] using range_circleMap (0 : ℂ) 1
  rw [← hrange] at hasphere
  obtain ⟨θ, hθ⟩ := hasphere
  have hz : Complex.exp ((θ : ℂ) * I) = a := by
    simpa [circleMap_zero] using hθ
  have haeval : A.eval a = 0 := (mem_roots hA).mp ha
  have hpzero : (p θ : ℂ) = 0 := by
    rw [hrep θ, hz, haeval, mul_zero]
  exact (ne_of_gt (hpos θ)) (ofReal_eq_zero.mp hpzero)

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

end

end HomogeneousObstruction
