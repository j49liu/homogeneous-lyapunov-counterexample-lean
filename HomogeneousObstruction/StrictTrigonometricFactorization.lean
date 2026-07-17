import HomogeneousObstruction.FejerRiesz

namespace HomogeneousObstruction

open Complex Metric Polynomial Real Set
open scoped BigOperators ComplexConjugate Polynomial

noncomputable section

/-!
# Strict trigonometric factorization

This file records the proof objects used in the paper: the polynomial B
formed from the roots outside the unit disk, its reciprocal-conjugate
polynomial Bsharp, the identity A = κ B Bsharp, and the zero-free spectral
factor Q = sqrt κ B.
-/

/-- The polynomial B(z) = ∏ (z - β) formed from a multiset of roots. -/
def manuscriptB (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun beta => X - C beta).prod

/-- The paper's B#(z) = z^L overline(B(1 / overline z)). -/
def manuscriptBsharp (B : ℂ[X]) (L : ℕ) : ℂ[X] :=
  (B.map (starRingEnd ℂ)).reflect L

@[simp] theorem manuscriptB_natDegree (s : Multiset ℂ) :
    (manuscriptB s).natDegree = s.card := by
  simp [manuscriptB]

theorem manuscriptB_monic (s : Multiset ℂ) : (manuscriptB s).Monic := by
  exact monic_multisetProd_X_sub_C s

theorem manuscriptB_ne_zero (s : Multiset ℂ) : manuscriptB s ≠ 0 :=
  (manuscriptB_monic s).ne_zero

@[simp] theorem manuscriptB_roots (s : Multiset ℂ) :
    (manuscriptB s).roots = s := by
  exact roots_multiset_prod_X_sub_C s

theorem manuscriptB_coeff_zero_ne {s : Multiset ℂ}
    (hs : ∀ beta ∈ s, beta ≠ 0) :
    (manuscriptB s).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero, manuscriptB, eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C,
    zero_sub]
  apply Multiset.prod_ne_zero
  intro hzero
  rw [Multiset.mem_map] at hzero
  obtain ⟨beta, hbeta, hneg⟩ := hzero
  exact hs beta hbeta (neg_eq_zero.mp hneg)

theorem manuscriptBsharp_ne_zero {s : Multiset ℂ}
    (_hs : ∀ beta ∈ s, beta ≠ 0) :
    manuscriptBsharp (manuscriptB s) s.card ≠ 0 := by
  unfold manuscriptBsharp
  intro hzero
  have hmap : (manuscriptB s).map (starRingEnd ℂ) = 0 :=
    reflect_eq_zero_iff.mp hzero
  exact (Polynomial.map_ne_zero (manuscriptB_ne_zero s)) hmap

theorem manuscriptBsharp_natDegree {s : Multiset ℂ}
    (hs : ∀ beta ∈ s, beta ≠ 0) :
    (manuscriptBsharp (manuscriptB s) s.card).natDegree = s.card := by
  apply le_antisymm
  · unfold manuscriptBsharp
    have hmap : ((manuscriptB s).map (starRingEnd ℂ)).natDegree = s.card := by
      rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,
        manuscriptB_natDegree]
    exact (natDegree_reflect_le (p :=
      (manuscriptB s).map (starRingEnd ℂ)) (N := s.card)).trans_eq
        (by rw [hmap, max_self])
  · apply le_natDegree_of_ne_zero
    unfold manuscriptBsharp
    rw [coeff_reflect, coeff_map, Polynomial.revAt_le le_rfl,
      Nat.sub_self]
    intro hmap
    exact manuscriptB_coeff_zero_ne hs <|
      (starRingEnd ℂ).injective (hmap.trans (map_zero _).symm)

theorem manuscriptBsharp_roots {s : Multiset ℂ}
    (hs : ∀ beta ∈ s, beta ≠ 0) :
    (manuscriptBsharp (manuscriptB s) s.card).roots =
      s.map reciprocalConj := by
  have hsharp : manuscriptBsharp (manuscriptB s) s.card =
      conjReflect (manuscriptB s) := by
    simp [manuscriptBsharp, conjReflect]
  rw [hsharp]
  rw [roots_conjReflect (manuscriptB s) (manuscriptB_ne_zero s)
    (manuscriptB_coeff_zero_ne hs), manuscriptB_roots]
  rfl

private theorem eval_map_conj (B : ℂ[X]) (z : ℂ) :
    (B.map (starRingEnd ℂ)).eval z =
      starRingEnd ℂ (B.eval (starRingEnd ℂ z)) := by
  simpa using
    (Polynomial.eval_map_apply (p := B) (f := starRingEnd ℂ)
      (starRingEnd ℂ z))

/-- On the unit circle, the paper's reciprocal-conjugate polynomial satisfies
B#(z) = z^L conjugate(B(z)). -/
theorem manuscriptBsharp_eval_unit
    {B : ℂ[X]} {L : ℕ} (hdeg : B.natDegree = L)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (manuscriptBsharp B L).eval z =
      z ^ L * starRingEnd ℂ (B.eval z) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
  letI : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have hreflect := eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ L
    (B.map (starRingEnd ℂ)) (by simp [hdeg])
  simp only [eval₂_id, invOf_eq_inv, inv_inv] at hreflect
  rw [manuscriptBsharp]
  have hinv : z⁻¹ = starRingEnd ℂ z := Complex.inv_eq_conj hz
  rw [eval_map_conj] at hreflect
  have hconjInv : starRingEnd ℂ z⁻¹ = z := by
    rw [hinv]
    simp
  rw [hconjInv] at hreflect
  have hcancel : z⁻¹ ^ L * z ^ L = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
  have hcancel' : z ^ L * z⁻¹ ^ L = 1 := by
    rw [mul_comm]
    exact hcancel
  calc
    ((B.map (starRingEnd ℂ)).reflect L).eval z =
        ((B.map (starRingEnd ℂ)).reflect L).eval z * 1 := by rw [mul_one]
    _ = ((B.map (starRingEnd ℂ)).reflect L).eval z *
        (z⁻¹ ^ L * z ^ L) := by rw [hcancel]
    _ = z ^ L *
        (((B.map (starRingEnd ℂ)).reflect L).eval z * z⁻¹ ^ L) := by ring
    _ = z ^ L * starRingEnd ℂ (B.eval z) := by rw [hreflect]

/-- The manuscript step saying that A and B B# have the same roots and
degree, hence differ by a nonzero scalar. -/
theorem manuscript_exists_kappa_mul_B_Bsharp
    {A : ℂ[X]} {L : ℕ} (hA : A ≠ 0)
    (s : Multiset ℂ) (hcard : s.card = L)
    (hroots : A.roots = s + s.map reciprocalConj)
    (hs : ∀ beta ∈ s, beta ≠ 0) :
    ∃ kappa : ℂ, kappa ≠ 0 ∧
      A = C kappa *
        (manuscriptB s * manuscriptBsharp (manuscriptB s) L) := by
  have hsharpL :
      manuscriptBsharp (manuscriptB s) L =
        manuscriptBsharp (manuscriptB s) s.card := by rw [hcard]
  have hsharp0 : manuscriptBsharp (manuscriptB s) L ≠ 0 := by
    rw [hsharpL]
    exact manuscriptBsharp_ne_zero hs
  let D := manuscriptB s * manuscriptBsharp (manuscriptB s) L
  have hD : D ≠ 0 := mul_ne_zero (manuscriptB_ne_zero s) hsharp0
  have hDroots : D.roots = A.roots := by
    rw [show D = manuscriptB s * manuscriptBsharp (manuscriptB s) L by rfl,
      roots_mul hD, manuscriptB_roots, hsharpL, manuscriptBsharp_roots hs,
      hroots]
  let kappa := A.leadingCoeff / D.leadingCoeff
  have hlcA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hlcD : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hD
  refine ⟨kappa, div_ne_zero hlcA hlcD, ?_⟩
  have hAprod := (IsAlgClosed.splits A).eq_prod_roots
  have hDprod := (IsAlgClosed.splits D).eq_prod_roots
  rw [hDroots] at hDprod
  calc
    A = C A.leadingCoeff *
        (A.roots.map fun a : ℂ => X - C a).prod := hAprod
    _ = C (A.leadingCoeff / D.leadingCoeff) *
        (C D.leadingCoeff *
          (A.roots.map fun a : ℂ => X - C a).prod) := by
      rw [← mul_assoc, ← C.map_mul,
        div_mul_cancel₀ A.leadingCoeff hlcD]
    _ = C kappa *
        (C D.leadingCoeff *
          (A.roots.map fun a : ℂ => X - C a).prod) := by rfl
    _ = C kappa * D :=
      congrArg (fun T : ℂ[X] => C kappa * T) hDprod.symm
    _ = C kappa *
        (manuscriptB s * manuscriptBsharp (manuscriptB s) L) := rfl

/-- Evaluating the manuscript identity `A = κ B B#` on the unit circle
turns the cleared Laurent polynomial into `κ |B|²`. -/
theorem manuscript_laurent_eval_eq_kappa_norm_sq
    {A : ℂ[X]} {L : ℕ} {s : Multiset ℂ} {kappa z : ℂ}
    (hcard : s.card = L)
    (hAeq : A = C kappa *
      (manuscriptB s * manuscriptBsharp (manuscriptB s) L))
    (hz : ‖z‖ = 1) :
    z⁻¹ ^ L * A.eval z =
      kappa * (((‖(manuscriptB s).eval z‖ ^ 2 : ℝ) : ℂ)) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
  have hdeg : (manuscriptB s).natDegree = L := by simp [hcard]
  have hcancel : z⁻¹ ^ L * z ^ L = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
  have hcancel' : z ^ L * z⁻¹ ^ L = 1 := by
    rw [mul_comm]
    exact hcancel
  rw [hAeq, eval_mul, eval_C, eval_mul,
    manuscriptBsharp_eval_unit hdeg hz]
  rw [show (manuscriptB s).eval z *
      (z ^ L * starRingEnd ℂ ((manuscriptB s).eval z)) =
      z ^ L * ((manuscriptB s).eval z *
        starRingEnd ℂ ((manuscriptB s).eval z)) by ring]
  rw [Complex.mul_conj']
  ring_nf
  rw [hcancel']
  norm_cast
  simp

private theorem manuscript_prod_fin_toList {α M : Type*} [CommMonoid M]
    (s : Multiset α) (f : α → M) :
    ∏ j : Fin s.toList.length, f s.toList[j.1] = (s.map f).prod := by
  rw [Fin.prod_univ_fun_getElem]
  simp

/-- A product of factors `z - β` with all `β` outside the unit disk has no
zero in the closed unit disk. -/
theorem manuscriptB_eval_ne_closedDisk {s : Multiset ℂ}
    (hout : ∀ beta ∈ s, 1 < ‖beta‖) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (manuscriptB s).eval z ≠ 0 := by
  rw [manuscriptB, eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]
  apply Multiset.prod_ne_zero
  intro hzero
  rw [Multiset.mem_map] at hzero
  obtain ⟨beta, hbeta, hzbeta⟩ := hzero
  have heq : z = beta := sub_eq_zero.mp hzbeta
  exact (not_lt_of_ge hz) (heq ▸ hout beta hbeta)

private theorem manuscript_X_sub_C_eq_normalized_factor
    (beta : ℂ) (hbeta : beta ≠ 0) :
    (X - C beta : ℂ[X]) =
      C (-beta) * (1 - C beta⁻¹ * X) := by
  symm
  calc
    C (-beta) * (1 - C beta⁻¹ * X) =
        C (-beta) - (C (-beta) * C beta⁻¹) * X := by ring
    _ = C (-beta) - C ((-beta) * beta⁻¹) * X := by
      rw [← C.map_mul]
    _ = C (-beta) - C (-1) * X := by
      rw [neg_mul, mul_inv_cancel₀ hbeta]
    _ = X - C beta := by simp; ring

/-- The normalized product data obtained from a particular polynomial
spectral factor.  This structure records that the `StrictFejerRieszData`
used in the logarithmic argument is obtained by factoring the very same
zero-free polynomial `factor.Q` supplied by the strict trigonometric
factorization lemma. -/
structure ManuscriptNormalizedStrictFejerRieszData
    (p : ℝ → ℝ) (D : ℕ) (factor : StrictFejerRieszPolynomialData p D) where
  normalized : StrictFejerRieszData p D
  normalized_degree : normalized.L = factor.L
  factorConstant : ℂ
  factorConstant_ne_zero : factorConstant ≠ 0
  Q_normalized_factorization :
    factor.Q = C factorConstant *
      ∏ j : Fin normalized.L, (1 - C (normalized.alpha j) * X)
  normalized_constant_eq_norm_sq :
    normalized.c = ‖factorConstant‖ ^ 2

/-- Normalize a returned zero-free polynomial factor
`Q` as `Q = C ∏ₗ (1 - αₗ X)`, with exactly `deg Q` factors and
`|αₗ| < 1`.  The squared-norm product used in the logarithmic proof is
derived by evaluating this polynomial identity on the unit circle; it is not
proved independently from the earlier outside-root polynomial `B`. -/
theorem manuscript_normalize_strict_trigonometric_factor
    {p : ℝ → ℝ} {D : ℕ} (factor : StrictFejerRieszPolynomialData p D) :
    Nonempty (ManuscriptNormalizedStrictFejerRieszData p D factor) := by
  have hQeval0 : factor.Q.eval 0 ≠ 0 :=
    factor.zero_free_closedDisk 0 (by simp)
  have hQ : factor.Q ≠ 0 := by
    intro hzero
    rw [hzero] at hQeval0
    simp at hQeval0
  let s := factor.Q.roots
  have hscard : s.card = factor.L := by
    change factor.Q.roots.card = factor.L
    rw [← (IsAlgClosed.splits factor.Q).natDegree_eq_card_roots,
      factor.degree_eq]
  have hsout : ∀ beta ∈ s, 1 < ‖beta‖ := by
    intro beta hbeta
    by_contra hnot
    have hle : ‖beta‖ ≤ 1 := le_of_not_gt hnot
    have heval : factor.Q.eval beta = 0 :=
      (mem_roots hQ).mp hbeta
    exact factor.zero_free_closedDisk beta hle heval
  have hsne : ∀ beta ∈ s, beta ≠ 0 := by
    intro beta hbeta hzero
    subst beta
    have : 1 < ‖(0 : ℂ)‖ := hsout 0 hbeta
    norm_num at this
  let rootsList := s.toList
  let alpha : Fin rootsList.length → ℂ :=
    fun j => rootsList[j.1]⁻¹
  let factorConstant : ℂ :=
    factor.Q.leadingCoeff * (s.map fun beta => -beta).prod
  have hfactorConstant_ne : factorConstant ≠ 0 := by
    apply mul_ne_zero (leadingCoeff_ne_zero.mpr hQ)
    apply Multiset.prod_ne_zero
    intro hzero
    rw [Multiset.mem_map] at hzero
    obtain ⟨beta, hbeta, hneg⟩ := hzero
    exact hsne beta hbeta (neg_eq_zero.mp hneg)
  have hrootsNormalized :
      manuscriptB s = C ((s.map fun beta => -beta).prod) *
        ∏ j : Fin rootsList.length,
          (1 - C (alpha j) * X) := by
    rw [manuscriptB]
    rw [Multiset.map_congr rfl (fun beta hbeta =>
      manuscript_X_sub_C_eq_normalized_factor beta (hsne beta hbeta))]
    rw [Multiset.prod_map_mul]
    have hC := map_multiset_prod C (s.map fun beta => -beta)
    simp only [Multiset.map_map, Function.comp_apply] at hC
    rw [← hC]
    rw [show (s.map fun beta => (1 - C beta⁻¹ * X : ℂ[X])).prod =
        ∏ j : Fin rootsList.length, (1 - C (alpha j) * X) by
      simpa [rootsList, alpha] using
        (manuscript_prod_fin_toList s
          (fun beta => (1 - C beta⁻¹ * X : ℂ[X]))).symm]
  have hQnormalized :
      factor.Q = C factorConstant *
        ∏ j : Fin rootsList.length, (1 - C (alpha j) * X) := by
    calc
      factor.Q = C factor.Q.leadingCoeff * manuscriptB s := by
        exact (IsAlgClosed.splits factor.Q).eq_prod_roots
      _ = C factorConstant *
          ∏ j : Fin rootsList.length, (1 - C (alpha j) * X) := by
        rw [hrootsNormalized, ← mul_assoc, ← C.map_mul]
  let data : StrictFejerRieszData p D :=
    { L := rootsList.length
      degree_le := by
        have hlen : rootsList.length = factor.L := by
          simpa [rootsList] using hscard
        rw [hlen]
        exact factor.degree_le
      alpha := alpha
      alpha_ne_zero := by
        intro j
        apply inv_ne_zero
        apply hsne rootsList[j.1]
        have hj := List.getElem_mem (l := rootsList) j.2
        exact Multiset.mem_toList.mp hj
      alpha_norm_lt_one := by
        intro j
        have hjlist := List.getElem_mem (l := rootsList) j.2
        have hjs : rootsList[j.1] ∈ s := Multiset.mem_toList.mp hjlist
        have hjout := hsout rootsList[j.1] hjs
        have hjpos : 0 < ‖rootsList[j.1]‖ := lt_trans zero_lt_one hjout
        simp only [alpha, norm_inv]
        rwa [inv_lt_one₀ hjpos]
      c := ‖factorConstant‖ ^ 2
      c_pos := pow_pos (norm_pos_iff.mpr hfactorConstant_ne) 2
      factorization := by
        intro theta
        let z := Complex.exp ((theta : ℂ) * I)
        have hQeval : factor.Q.eval z = factorConstant *
            ∏ j : Fin rootsList.length, (1 - alpha j * z) := by
          rw [hQnormalized, eval_mul, eval_C, eval_prod]
          simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
        rw [factor.factorization theta, hQeval, norm_mul, mul_pow,
          norm_prod, Finset.prod_pow] }
  refine ⟨{
    normalized := data
    normalized_degree := ?_
    factorConstant := factorConstant
    factorConstant_ne_zero := hfactorConstant_ne
    Q_normalized_factorization := ?_
    normalized_constant_eq_norm_sq := rfl }⟩
  · change rootsList.length = factor.L
    simpa [rootsList] using hscard
  · change factor.Q = C factorConstant *
      ∏ j : Fin rootsList.length, (1 - C (alpha j) * X)
    exact hQnormalized

/-- The complete set of proof objects in the manuscript's strict
Fejer--Riesz argument.  In particular, this exposes the outside-root
polynomial `B`, its reciprocal-conjugate `B#`, the positive scalar `κ`, and
the choice `Q = sqrt κ B`, rather than hiding those steps behind a different
factorisation. -/
structure ManuscriptStrictFejerRieszData
    (p : ℝ → ℝ) (D : ℕ) (A : ℂ[X]) (L : ℕ) where
  outside : Multiset ℂ
  outside_card : outside.card = L
  outside_roots : A.roots = outside + outside.map reciprocalConj
  outside_norm_gt_one : ∀ beta ∈ outside, 1 < ‖beta‖
  kappa : ℝ
  kappa_pos : 0 < kappa
  cleared_factorization : A = C (kappa : ℂ) *
    (manuscriptB outside * manuscriptBsharp (manuscriptB outside) L)
  Q : ℂ[X]
  Q_eq : Q = C (Real.sqrt kappa : ℂ) * manuscriptB outside
  Q_degree : Q.natDegree = L
  Q_zero_free_closedDisk : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0
  Q_factorization : ∀ theta : ℝ,
    p theta = ‖Q.eval (Complex.exp ((theta : ℂ) * I))‖ ^ 2

/-- Strict Fejer--Riesz proved in exactly the root-factorization order used
in the manuscript: split the roots, form `B` and `B#`, identify the positive
constant `κ`, and take `Q = sqrt κ B`.  The stated factorization theorem
below returns this `Q`; its caller then normalizes that same polynomial for
the logarithmic calculation. -/
theorem manuscript_strictFejerRiesz_of_selfInversive
    {p : ℝ → ℝ} {D L : ℕ} (A : ℂ[X])
    (_hLD : L ≤ D)
    (hdeg : A.natDegree = 2 * L)
    (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hrep : ∀ theta : ℝ, (p theta : ℂ) =
      (Complex.exp ((theta : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((theta : ℂ) * I)))
    (hpos : ∀ theta, 0 < p theta) :
    Nonempty (ManuscriptStrictFejerRieszData p D A L) := by
  have hA : A ≠ 0 := by
    intro hzero
    subst A
    simp at h0
  have hunit : ∀ a ∈ A.roots, ‖a‖ ≠ 1 :=
    no_unit_roots_of_positive_laurent_representation hA hrep hpos
  let s := A.roots.filter (fun a => 1 < ‖a‖)
  obtain ⟨hscard, hroots⟩ :=
    selfInversive_root_partition hdeg h0 hself hunit
  change s.card = L at hscard
  change A.roots = s + s.map reciprocalConj at hroots
  have hsout : ∀ beta ∈ s, 1 < ‖beta‖ := by
    intro beta hbeta
    exact (Multiset.mem_filter.mp hbeta).2
  have hsne : ∀ beta ∈ s, beta ≠ 0 := by
    intro beta hbeta hzero
    subst beta
    have : 1 < ‖(0 : ℂ)‖ := hsout 0 hbeta
    norm_num at this
  obtain ⟨kappaC, hkappaC_ne, hAeq⟩ :=
    manuscript_exists_kappa_mul_B_Bsharp hA s hscard hroots hsne
  have hcircle (theta : ℝ) :
      (p theta : ℂ) = kappaC *
        (((‖(manuscriptB s).eval
          (Complex.exp ((theta : ℂ) * I))‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hrep theta]
    exact manuscript_laurent_eval_eq_kappa_norm_sq hscard hAeq (by simp)
  let r0 : ℝ := ‖(manuscriptB s).eval 1‖ ^ 2
  have hB1ne : (manuscriptB s).eval 1 ≠ 0 :=
    manuscriptB_eval_ne_closedDisk hsout (by simp)
  have hr0pos : 0 < r0 := by
    exact pow_pos (norm_pos_iff.mpr hB1ne) 2
  have heq0 := hcircle 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at heq0
  change (p 0 : ℂ) = kappaC * (r0 : ℂ) at heq0
  have hkappa_re : 0 < kappaC.re := by
    have hre := congrArg Complex.re heq0
    simp only [ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero] at hre
    nlinarith [hpos 0, hr0pos]
  have hkappa_im : kappaC.im = 0 := by
    have him := congrArg Complex.im heq0
    simp only [ofReal_im, mul_im, ofReal_re, mul_zero, zero_add] at him
    nlinarith [hr0pos]
  have hkappa_real : kappaC = (kappaC.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hkappa_im]
  let kappa : ℝ := kappaC.re
  let Q : ℂ[X] := C (Real.sqrt kappa : ℂ) * manuscriptB s
  have hkappa : 0 < kappa := hkappa_re
  have hQdegree : Q.natDegree = L := by
    dsimp [Q]
    rw [natDegree_C_mul]
    · exact hscard ▸ manuscriptB_natDegree s
    · exact_mod_cast Real.sqrt_ne_zero'.mpr hkappa
  have hQzero : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0 := by
    intro z hz
    dsimp [Q]
    rw [eval_mul, eval_C]
    apply mul_ne_zero
    · exact_mod_cast Real.sqrt_ne_zero'.mpr hkappa
    · exact manuscriptB_eval_ne_closedDisk hsout hz
  have hp_eq_kappa_norm (theta : ℝ) :
      p theta = kappa * ‖(manuscriptB s).eval
        (Complex.exp ((theta : ℂ) * I))‖ ^ 2 := by
    have hc := hcircle theta
    rw [hkappa_real] at hc
    apply Complex.ofReal_injective
    simpa [kappa] using hc
  have hQfactor : ∀ theta : ℝ,
      p theta = ‖Q.eval (Complex.exp ((theta : ℂ) * I))‖ ^ 2 := by
    intro theta
    rw [hp_eq_kappa_norm theta]
    dsimp [Q]
    rw [eval_mul, eval_C, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg kappa), Real.sq_sqrt hkappa.le]
  refine ⟨{
    outside := s
    outside_card := hscard
    outside_roots := hroots
    outside_norm_gt_one := hsout
    kappa := kappa
    kappa_pos := hkappa
    cleared_factorization := ?_
    Q := Q
    Q_eq := rfl
    Q_degree := hQdegree
    Q_zero_free_closedDisk := hQzero
    Q_factorization := hQfactor }⟩
  · rw [← hkappa_real]
    exact hAeq

/-- The conclusion of the manuscript's strict trigonometric factorization
lemma, retaining the equality between the actual Fourier degree `L` and the
degree field of the returned polynomial factor. -/
structure ManuscriptStrictTrigonometricFactorizationData
    (p : ℝ → ℝ) (D L : ℕ) where
  polynomial : StrictFejerRieszPolynomialData p D
  polynomial_degree : polynomial.L = L

/-- The manuscript's strict trigonometric factorization lemma, including its
explicit “`L = 0` is immediate” branch.  For `L > 0`, the polynomial `Q` is
built in the direct order `A = κ B B#`, `Q = sqrt(κ) B`.  Its retained
degree equality lets the subsequent normalization theorem factor this same
`Q`, so the logarithmic argument is transitive through this theorem. -/
theorem manuscript_strict_trigonometric_factorization
    {p : ℝ → ℝ} {D L : ℕ} (A : ℂ[X])
    (hLD : L ≤ D)
    (hdeg : A.natDegree = 2 * L)
    (h0 : A.coeff 0 ≠ 0)
    (hself : conjReflect A = A)
    (hrep : ∀ theta : ℝ, (p theta : ℂ) =
      (Complex.exp ((theta : ℂ) * I))⁻¹ ^ L *
        A.eval (Complex.exp ((theta : ℂ) * I)))
    (hpos : ∀ theta, 0 < p theta) :
    Nonempty (ManuscriptStrictTrigonometricFactorizationData p D L) := by
  by_cases hLzero : L = 0
  · subst L
    have hAdeg : A.natDegree = 0 := by simpa using hdeg
    have hAconst : A = C (A.coeff 0) :=
      eq_C_of_natDegree_eq_zero hAdeg
    have hpconst (theta : ℝ) : p theta = p 0 := by
      apply Complex.ofReal_injective
      rw [hrep theta, hrep 0]
      rw [hAconst]
      simp only [pow_zero, one_mul, eval_C]
    let Q : ℂ[X] := C (Real.sqrt (p 0) : ℂ)
    refine ⟨{
      polynomial := {
        L := 0
        degree_le := Nat.zero_le D
        Q := Q
        degree_eq := by simp [Q]
        zero_free_closedDisk := ?_
        factorization := ?_ }
      polynomial_degree := rfl }⟩
    · intro z _hz
      simp only [Q, eval_C]
      exact_mod_cast Real.sqrt_ne_zero'.mpr (hpos 0)
    · intro theta
      rw [hpconst theta]
      simp only [Q, eval_C, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg (p 0)), Real.sq_sqrt (hpos 0).le]
  · obtain ⟨rootData⟩ := manuscript_strictFejerRiesz_of_selfInversive
      A hLD hdeg h0 hself hrep hpos
    refine ⟨{
      polynomial := {
        L := L
        degree_le := hLD
        Q := rootData.Q
        degree_eq := rootData.Q_degree
        zero_free_closedDisk := rootData.Q_zero_free_closedDisk
        factorization := rootData.Q_factorization }
      polynomial_degree := rfl }⟩

end

end HomogeneousObstruction
