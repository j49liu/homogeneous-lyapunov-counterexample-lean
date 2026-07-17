import HomogeneousObstruction.HalfAnglePolynomial
import HomogeneousObstruction.StrictTrigonometricFactorization
import HomogeneousObstruction.FourierBasic

namespace HomogeneousObstruction

open Complex Polynomial
open scoped BigOperators ComplexConjugate Polynomial

noncomputable section

/-!
# Actual Fourier degree and the finite even expansion

This file isolates the order of the first part of Lemma 5.2.  For a
homogeneous polynomial of degree `2 * N`, it first writes the circle trace as
a finite sum of the even modes `-2N, ..., 2N`.  It then chooses the actual
factor count supplied by the strict Fejer--Riesz theorem and treats its
degree-zero case before any logarithmic-series calculation.
-/

/-- The signed Fourier mode represented by coefficient `k` of the cleared
half-angle polynomial.  As `0 ≤ k ≤ 2N`, these modes run from `-N` to `N`. -/
def centeredHalfAngleMode (N k : ℕ) : ℤ := (k : ℤ) - (N : ℤ)

/-- The coefficient of the half-angle Laurent expansion at the centered
index `k`. -/
def halfAngleFourierCoefficient (P : BivariatePolynomial) (k : ℕ) : ℂ :=
  (halfAnglePolynomial P).coeff k

/-- Fourier coefficients of the real-valued half-angle trace have the
conjugate symmetry used in the manuscript: with the convention
`exp (-i j φ)`, conjugating the coefficient at `j` gives the coefficient at
`-j`.  This proof deliberately goes through the normalized integral
definition, so the sign convention is part of the formal statement. -/
private theorem paperFourierCoeff_ofReal_conj_neg
    (u : ℝ → ℝ) (j : ℤ) :
    star (paperFourierCoeff (fun phi => (u phi : ℂ)) j) =
      paperFourierCoeff (fun phi => (u phi : ℂ)) (-j) := by
  rw [paperFourierCoeff_eq_integral, paperFourierCoeff_eq_integral]
  rw [star_mul]
  have hconj :
      star (∫ phi in (0 : ℝ)..2 * Real.pi,
          (u phi : ℂ) * Complex.exp (-I * (j : ℂ) * (phi : ℂ))) =
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          star ((u phi : ℂ) *
            Complex.exp (-I * (j : ℂ) * (phi : ℂ))) := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact integral_conj.symm
  rw [hconj]
  have hconstant : star (1 / (2 * (Real.pi : ℂ))) =
      1 / (2 * (Real.pi : ℂ)) := by simp
  rw [hconstant, mul_comm]
  congr 1
  · apply intervalIntegral.integral_congr
    intro phi _
    dsimp only
    rw [star_mul]
    change
      conj (Complex.exp (-I * (j : ℂ) * (phi : ℂ))) *
          conj (u phi : ℂ) =
        (u phi : ℂ) *
          Complex.exp (-I * ((-j : ℤ) : ℂ) * (phi : ℂ))
    rw [Complex.conj_ofReal, ← Complex.exp_conj]
    have harg :
        conj (-I * (j : ℂ) * (phi : ℂ)) =
          -I * ((-j : ℤ) : ℂ) * (phi : ℂ) := by
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
        map_intCast, Int.cast_neg]
      ring
    rw [harg, mul_comm]

private theorem exp_centered_mode_eq
    (N k : ℕ) (phi : ℝ) :
    Complex.exp (((centeredHalfAngleMode N k : ℤ) : ℂ) * (phi : ℂ) * I) =
      Complex.exp ((phi : ℂ) * I) ^ centeredHalfAngleMode N k := by
  rw [← Complex.exp_int_mul]
  congr 1
  ring

private theorem inv_pow_mul_pow_eq_centered_zpow
    (z : ℂ) (hz : z ≠ 0) (N k : ℕ) :
    z⁻¹ ^ N * z ^ k = z ^ centeredHalfAngleMode N k := by
  rw [show z⁻¹ ^ N = z ^ (-(N : ℤ)) by simp]
  rw [show z ^ k = z ^ (k : ℤ) by simp]
  rw [← zpow_add₀ hz]
  congr 1
  simp [centeredHalfAngleMode, sub_eq_add_neg, add_comm]

private theorem halfAngleTrace_finiteFourierExpansion_direct
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (phi : ℝ) :
    (halfAngleTrace P phi : ℂ) =
      ∑ k ∈ Finset.range (2 * N + 1),
        halfAngleFourierCoefficient P k *
          Complex.exp (((centeredHalfAngleMode N k : ℤ) : ℂ) * (phi : ℂ) * I) := by
  let z : ℂ := Complex.exp ((phi : ℂ) * I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hdeg : (halfAnglePolynomial P).natDegree < 2 * N + 1 :=
    Nat.lt_succ_of_le (halfAnglePolynomial_natDegree_le hhom)
  rw [halfAnglePolynomial_laurent_representation hhom]
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [halfAngleFourierCoefficient]
  change z⁻¹ ^ N * ((halfAnglePolynomial P).coeff k * z ^ k) = _
  calc
    z⁻¹ ^ N * ((halfAnglePolynomial P).coeff k * z ^ k) =
        (halfAnglePolynomial P).coeff k * (z⁻¹ ^ N * z ^ k) := by ring
    _ = (halfAnglePolynomial P).coeff k * z ^ centeredHalfAngleMode N k := by
      rw [inv_pow_mul_pow_eq_centered_zpow z hz]
    _ = (halfAnglePolynomial P).coeff k *
          Complex.exp (((centeredHalfAngleMode N k : ℤ) : ℂ) * (phi : ℂ) * I) := by
      rw [exp_centered_mode_eq]

/-- The manuscript's displayed even-mode expansion
`p(theta) = ∑_{j=-N}^N c_j exp(2 i j theta)`.  The natural index `k`
represents the signed index `j = k - N`. -/
theorem circleTrace_evenFourierExpansion
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (theta : ℝ) :
    (circleTrace P theta : ℂ) =
      ∑ k ∈ Finset.range (2 * N + 1),
        halfAngleFourierCoefficient P k *
          Complex.exp
            ((2 : ℂ) * ((centeredHalfAngleMode N k : ℤ) : ℂ) *
              (theta : ℂ) * I) := by
  rw [← halfAngleTrace_two_mul P theta]
  rw [halfAngleTrace_finiteFourierExpansion_direct hhom]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun z : ℂ => halfAngleFourierCoefficient P k * z)
  apply congrArg Complex.exp
  push_cast
  ring

/-- The manuscript's finite Fourier expansion of the half-angle trace
`q(phi) = p(phi / 2)`, with modes `j = -N, ..., N`.  Its proof is routed
through the displayed even-mode expansion of `p`, making the manuscript's
half-angle step an active dependency of the coefficient calculation below. -/
theorem halfAngleTrace_finiteFourierExpansion
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (phi : ℝ) :
    (halfAngleTrace P phi : ℂ) =
      ∑ k ∈ Finset.range (2 * N + 1),
        halfAngleFourierCoefficient P k *
          Complex.exp (((centeredHalfAngleMode N k : ℤ) : ℂ) * (phi : ℂ) * I) := by
  change (circleTrace P (phi / 2) : ℂ) = _
  rw [circleTrace_evenFourierExpansion hhom]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun z : ℂ => halfAngleFourierCoefficient P k * z)
  apply congrArg Complex.exp
  push_cast
  ring

/-- The algebraic coefficient in the displayed Laurent expansion is exactly
the integral-defined Fourier coefficient with the paper's convention
`exp(-i j φ)/(2π)`.  Thus the `L` below is literally the Fourier degree, not
merely an algebraic support bound. -/
theorem halfAngleFourierCoefficient_eq_paperFourierCoeff
    {P : BivariatePolynomial} {N k : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hk : k < 2 * N + 1) :
    paperFourierCoeff (fun phi => (halfAngleTrace P phi : ℂ))
        (centeredHalfAngleMode N k) =
      halfAngleFourierCoefficient P k := by
  let u : Fin (2 * N + 1) → ℝ → ℂ := fun j phi =>
    halfAngleFourierCoefficient P j *
      Complex.exp (((centeredHalfAngleMode N j : ℤ) : ℂ) * (phi : ℂ) * I)
  have hexp : (fun phi => (halfAngleTrace P phi : ℂ)) =
      fun phi => ∑ j, u j phi := by
    funext phi
    rw [halfAngleTrace_finiteFourierExpansion hhom]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => halfAngleFourierCoefficient P j *
        Complex.exp (((centeredHalfAngleMode N j : ℤ) : ℂ) *
          (phi : ℂ) * I)) (2 * N + 1)]
  rw [hexp, paperFourierCoeff_finset_sum u (fun _ => by fun_prop)]
  have hmode (j : Fin (2 * N + 1)) :
      paperFourierCoeff (u j) (centeredHalfAngleMode N k) =
        halfAngleFourierCoefficient P j *
          (Pi.single (centeredHalfAngleMode N j) (1 : ℂ) : ℤ → ℂ)
            (centeredHalfAngleMode N k) := by
    rw [show u j = fun phi : ℝ => halfAngleFourierCoefficient P j *
        Complex.exp (((centeredHalfAngleMode N j : ℤ) : ℂ) *
          (phi : ℂ) * I) by rfl]
    rw [paperFourierCoeff_const_mul]
    rw [show (fun phi : ℝ =>
          Complex.exp (((centeredHalfAngleMode N j : ℤ) : ℂ) *
            (phi : ℂ) * I)) =
        fun phi : ℝ => fourier (centeredHalfAngleMode N j)
          (phi : AddCircle (2 * Real.pi)) by
      funext phi
      exact exp_int_mul_I_eq_fourier _ _]
    rw [paperFourierCoeff_fourier]
  simp_rw [hmode]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro j _ hj
    have hmode_ne : centeredHalfAngleMode N j ≠ centeredHalfAngleMode N k := by
      intro heq
      apply hj
      apply Fin.ext
      dsimp [centeredHalfAngleMode] at heq ⊢
      omega
    simp [hmode_ne]
  · simp

/-- Because `q` is real-valued, its manuscript Fourier coefficients satisfy
`conj(c_j) = c_{-j}`.  Here indices are stored in the centered natural range
`0, ..., 2N`.  This is the coefficient symmetry used below to prove the
self-inversiveness of the actual-degree cleared polynomial. -/
theorem halfAngleFourierCoefficient_conj_symm
    {P : BivariatePolynomial} {N k : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hk : k < 2 * N + 1) :
    star (halfAngleFourierCoefficient P k) =
      halfAngleFourierCoefficient P (2 * N - k) := by
  have hkreflect : 2 * N - k < 2 * N + 1 := by omega
  have hmode :
      -(centeredHalfAngleMode N k) =
        centeredHalfAngleMode N (2 * N - k) := by
    dsimp [centeredHalfAngleMode]
    omega
  have hreal := paperFourierCoeff_ofReal_conj_neg
    (halfAngleTrace P) (centeredHalfAngleMode N k)
  rw [halfAngleFourierCoefficient_eq_paperFourierCoeff hhom hk] at hreal
  rw [hmode,
    halfAngleFourierCoefficient_eq_paperFourierCoeff hhom hkreflect] at hreal
  exact hreal

/-- The actual Fourier degree of the half-angle trace.  The cleared Laurent
polynomial is centred at `N`; hence its largest signed mode is
`natDegree - N`.  Real-valued Fourier conjugacy gives the matching negative
mode. -/
def manuscriptHalfAngleFourierDegree (P : BivariatePolynomial) (N : ℕ) : ℕ :=
  (halfAnglePolynomial P).natDegree - N

private theorem paperAverage_halfAngleTrace_pos
    {P : BivariatePolynomial} (hpd : PositiveDefinite P) :
    0 < paperAverage (halfAngleTrace P) := by
  unfold paperAverage
  apply mul_pos
  · positivity
  · apply intervalIntegral.integral_pos Real.two_pi_pos
    · exact (halfAngleTrace_continuous P).continuousOn
    · intro phi _
      exact (hpd.halfAngleTrace_pos phi).le
    · refine ⟨Real.pi, ?_, hpd.halfAngleTrace_pos Real.pi⟩
      constructor
      · exact Real.pi_pos.le
      · nlinarith [Real.pi_pos]

private theorem halfAnglePolynomial_center_le_natDegree
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    N ≤ (halfAnglePolynomial P).natDegree := by
  have hk : N < 2 * N + 1 := by omega
  have hbridge := halfAngleFourierCoefficient_eq_paperFourierCoeff hhom hk
  have hmode : centeredHalfAngleMode N N = 0 := by
    simp [centeredHalfAngleMode]
  have hcoefficient :
      halfAngleFourierCoefficient P N =
        (paperAverage (halfAngleTrace P) : ℂ) := by
    rw [← hbridge, hmode]
    exact realPaperFourierCoeff_zero (halfAngleTrace P)
  have hcoefficient_ne : halfAngleFourierCoefficient P N ≠ 0 := by
    rw [hcoefficient]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (paperAverage_halfAngleTrace_pos hpd))
  exact le_natDegree_of_ne_zero hcoefficient_ne

theorem manuscriptHalfAngleFourierDegree_le
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) :
    manuscriptHalfAngleFourierDegree P N ≤ N := by
  dsimp [manuscriptHalfAngleFourierDegree]
  have hdeg := halfAnglePolynomial_natDegree_le hhom
  omega

/-- The cleared Laurent numerator has degree `N + L`, where `L` is the
manuscript's actual Fourier degree. -/
theorem halfAnglePolynomial_natDegree_eq_center_add_actualDegree
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    (halfAnglePolynomial P).natDegree =
      N + manuscriptHalfAngleFourierDegree P N := by
  dsimp [manuscriptHalfAngleFourierDegree]
  have hcenter := halfAnglePolynomial_center_le_natDegree hhom hpd
  omega

/-- Every nonzero Laurent coefficient lies between the modes `-L` and `L`.
This is the support part of the assertion that `L` is the actual degree. -/
theorem halfAngleFourierCoefficient_support
    {P : BivariatePolynomial} {N k : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hk : halfAngleFourierCoefficient P k ≠ 0) :
    N - manuscriptHalfAngleFourierDegree P N ≤ k ∧
      k ≤ N + manuscriptHalfAngleFourierDegree P N := by
  let A := halfAnglePolynomial P
  let L := manuscriptHalfAngleFourierDegree P N
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have hnat : A.natDegree = N + L :=
    halfAnglePolynomial_natDegree_eq_center_add_actualDegree hhom hpd
  have hkA : A.coeff k ≠ 0 := hk
  have hupper : k ≤ N + L := by
    rw [← hnat]
    exact le_natDegree_of_ne_zero hkA
  refine ⟨?_, hupper⟩
  by_contra hlower
  have hklt : k < N - L := Nat.lt_of_not_ge hlower
  have hk_le : k ≤ 2 * N := by omega
  have hfar : A.natDegree < 2 * N - k := by
    rw [hnat]
    omega
  have hreflect_lt : 2 * N - k < 2 * N + 1 := by omega
  have hsym := halfAngleFourierCoefficient_conj_symm hhom hreflect_lt
  have hreflect : 2 * N - (2 * N - k) = k := by omega
  rw [hreflect] at hsym
  have hzero : halfAngleFourierCoefficient P (2 * N - k) = 0 :=
    coeff_eq_zero_of_natDegree_lt hfar
  rw [hzero, star_zero] at hsym
  exact hk hsym.symm

/-- The coefficient at the top mode `L` is nonzero. -/
theorem halfAngleFourierCoefficient_top_ne_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    halfAngleFourierCoefficient P
      (N + manuscriptHalfAngleFourierDegree P N) ≠ 0 := by
  rw [halfAngleFourierCoefficient,
    ← halfAnglePolynomial_natDegree_eq_center_add_actualDegree hhom hpd]
  exact leadingCoeff_ne_zero.mpr
    (halfAnglePolynomial_ne_zero_of_positiveDefinite hhom hpd)

/-- The real-valued Fourier conjugacy `conj(c_L) = c_{-L}` makes the
coefficient at the bottom mode nonzero as well. -/
theorem halfAngleFourierCoefficient_bottom_ne_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    halfAngleFourierCoefficient P
      (N - manuscriptHalfAngleFourierDegree P N) ≠ 0 := by
  let L := manuscriptHalfAngleFourierDegree P N
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have htop_index : N + L < 2 * N + 1 := by omega
  have hsym := halfAngleFourierCoefficient_conj_symm hhom htop_index
  have hreflect : 2 * N - (N + L) = N - L := by omega
  rw [hreflect] at hsym
  have htop : halfAngleFourierCoefficient P (N + L) ≠ 0 :=
    halfAngleFourierCoefficient_top_ne_zero hhom hpd
  rw [← hsym]
  simpa using (starRingEnd ℂ).injective.ne htop

/-! ## The manuscript's actual-degree cleared polynomial -/

/-- The polynomial

`A_L(z) = ∑_{j=-L}^L c_j z^(j+L)`

from the strict Fejer--Riesz proof in the manuscript.  The natural summation
index `k = j + L` runs from `0` to `2L`; the corresponding coefficient in the
original polynomial centred at `N` has index `N - L + k`. -/
def manuscriptClearedPolynomial (P : BivariatePolynomial) (N : ℕ) : ℂ[X] :=
  let L := manuscriptHalfAngleFourierDegree P N
  ∑ k ∈ Finset.range (2 * L + 1),
    Polynomial.monomial k
      (halfAngleFourierCoefficient P (N - L + k))

@[simp] theorem manuscriptClearedPolynomial_coeff
    (P : BivariatePolynomial) (N k : ℕ) :
    (manuscriptClearedPolynomial P N).coeff k =
      if k < 2 * manuscriptHalfAngleFourierDegree P N + 1 then
        halfAngleFourierCoefficient P
          (N - manuscriptHalfAngleFourierDegree P N + k)
      else 0 := by
  classical
  simp [manuscriptClearedPolynomial, Polynomial.coeff_monomial, eq_comm]

/-- The manuscript's cleared polynomial has degree exactly `2L`. -/
theorem manuscriptClearedPolynomial_natDegree
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    (manuscriptClearedPolynomial P N).natDegree =
      2 * manuscriptHalfAngleFourierDegree P N := by
  let L := manuscriptHalfAngleFourierDegree P N
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have htop : halfAngleFourierCoefficient P (N + L) ≠ 0 :=
    halfAngleFourierCoefficient_top_ne_zero hhom hpd
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [manuscriptClearedPolynomial_coeff]
    rw [if_neg (by omega)]
  · rw [manuscriptClearedPolynomial_coeff]
    rw [if_pos (by omega)]
    have hindex :
        N - manuscriptHalfAngleFourierDegree P N +
            2 * manuscriptHalfAngleFourierDegree P N =
          N + manuscriptHalfAngleFourierDegree P N := by
      have hbound := manuscriptHalfAngleFourierDegree_le hhom
      omega
    rw [hindex]
    simpa [L] using htop

/-- Its constant coefficient is the nonzero coefficient of the bottom mode
`-L`. -/
theorem manuscriptClearedPolynomial_coeff_zero_ne
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    (manuscriptClearedPolynomial P N).coeff 0 ≠ 0 := by
  let L := manuscriptHalfAngleFourierDegree P N
  have hbottom : halfAngleFourierCoefficient P (N - L) ≠ 0 :=
    halfAngleFourierCoefficient_bottom_ne_zero hhom hpd
  rw [manuscriptClearedPolynomial_coeff]
  rw [if_pos (by omega)]
  simp only [add_zero]
  exact hbottom

/-- The original polynomial centred at `N` is obtained from the manuscript's
actual-degree polynomial by restoring the `N - L` zero coefficients at the
bottom.  This is a coefficient shift, not polynomial reversal. -/
theorem halfAnglePolynomial_eq_X_pow_mul_manuscriptClearedPolynomial
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    halfAnglePolynomial P =
      Polynomial.X ^ (N - manuscriptHalfAngleFourierDegree P N) *
        manuscriptClearedPolynomial P N := by
  let A := halfAnglePolynomial P
  let L := manuscriptHalfAngleFourierDegree P N
  let lo := N - L
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have hnat : A.natDegree = N + L :=
    halfAnglePolynomial_natDegree_eq_center_add_actualDegree hhom hpd
  ext k
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hlow : lo ≤ k
  · rw [if_pos hlow]
    by_cases hhigh : k ≤ N + L
    · rw [manuscriptClearedPolynomial_coeff]
      rw [if_pos (by
        dsimp [lo, L] at hlow hhigh ⊢
        omega)]
      congr 1
      dsimp [halfAngleFourierCoefficient, lo, L]
      omega
    · have hAzero : A.coeff k = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hnat]
        exact Nat.lt_of_not_ge hhigh
      rw [hAzero, manuscriptClearedPolynomial_coeff]
      rw [if_neg (by
        dsimp [lo, L] at hlow hhigh ⊢
        omega)]
  · rw [if_neg hlow]
    have hAzero : A.coeff k = 0 := by
      by_contra hk
      have hk' : halfAngleFourierCoefficient P k ≠ 0 := hk
      have hsupp := halfAngleFourierCoefficient_support hhom hpd hk'
      exact hlow hsupp.1
    exact hAzero

/-- The manuscript's exact Laurent representation

`q(phi) = exp(-i L phi) A_L(exp(i phi))`.

It follows by removing the lower `N - L` padding from the polynomial already
centred at `N`. -/
theorem manuscriptClearedPolynomial_laurent_representation
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) (phi : ℝ) :
    (halfAngleTrace P phi : ℂ) =
      Complex.exp
          (-(((manuscriptHalfAngleFourierDegree P N : ℕ) : ℂ) *
            (phi : ℂ) * I)) *
        Polynomial.eval (Complex.exp ((phi : ℂ) * I))
          (manuscriptClearedPolynomial P N) := by
  let L := manuscriptHalfAngleFourierDegree P N
  let z : ℂ := Complex.exp ((phi : ℂ) * I)
  let B := manuscriptClearedPolynomial P N
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hsplit : N = L + (N - L) := by omega
  have hexpL : Complex.exp ((L : ℂ) * (phi : ℂ) * I) = z ^ L := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hexpNeg :
      Complex.exp (-((L : ℂ) * (phi : ℂ) * I)) = z⁻¹ ^ L := by
    rw [Complex.exp_neg, hexpL, inv_pow]
  rw [halfAnglePolynomial_laurent_representation hhom]
  rw [halfAnglePolynomial_eq_X_pow_mul_manuscriptClearedPolynomial hhom hpd]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  change z⁻¹ ^ N * (z ^ (N - L) * Polynomial.eval z B) =
    Complex.exp (-((L : ℂ) * (phi : ℂ) * I)) * Polynomial.eval z B
  rw [show z⁻¹ ^ N = z⁻¹ ^ L * z⁻¹ ^ (N - L) by
    nth_rewrite 1 [hsplit]
    rw [pow_add]]
  calc
    (z⁻¹ ^ L * z⁻¹ ^ (N - L)) *
          (z ^ (N - L) * Polynomial.eval z B) =
        z⁻¹ ^ L *
          ((z⁻¹ ^ (N - L) * z ^ (N - L)) * Polynomial.eval z B) := by
      ring
    _ = z⁻¹ ^ L * Polynomial.eval z B := by
      rw [← mul_pow, inv_mul_cancel₀ hz, one_pow, one_mul]
    _ = Complex.exp (-((L : ℂ) * (phi : ℂ) * I)) *
          Polynomial.eval z B := by rw [hexpNeg]

/-- The actual-degree polynomial has the self-inversive symmetry used in the
manuscript's reciprocal-conjugate root pairing. -/
theorem manuscriptClearedPolynomial_conjReflect
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    conjReflect (manuscriptClearedPolynomial P N) =
      manuscriptClearedPolynomial P N := by
  let L := manuscriptHalfAngleFourierDegree P N
  let B := manuscriptClearedPolynomial P N
  have hLle : L ≤ N := manuscriptHalfAngleFourierDegree_le hhom
  have hBdeg : B.natDegree = 2 * L :=
    manuscriptClearedPolynomial_natDegree hhom hpd
  ext k
  unfold conjReflect
  rw [hBdeg, coeff_reflect, coeff_map]
  by_cases hk : k ≤ 2 * L
  · rw [Polynomial.revAt_le hk]
    rw [manuscriptClearedPolynomial_coeff,
      if_pos (by omega : 2 * L - k < 2 * L + 1)]
    rw [manuscriptClearedPolynomial_coeff,
      if_pos (by omega : k < 2 * L + 1)]
    let index := N - L + (2 * L - k)
    have hindex_lt : index < 2 * N + 1 := by
      dsimp [index]
      omega
    have hsym := halfAngleFourierCoefficient_conj_symm hhom hindex_lt
    have hindex_reflect :
        2 * N - index = N - L + k := by
      dsimp [index]
      omega
    rw [hindex_reflect] at hsym
    exact hsym
  · have hk' : 2 * L < k := Nat.lt_of_not_ge hk
    rw [Polynomial.revAt_eq_self_of_lt hk']
    rw [manuscriptClearedPolynomial_coeff, if_neg (by omega)]
    simp

private theorem halfAnglePolynomial_coeff_eq_zero_off_center
    {P : BivariatePolynomial} {N k : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hL : manuscriptHalfAngleFourierDegree P N = 0) (hk : k ≠ N) :
    (halfAnglePolynomial P).coeff k = 0 := by
  by_contra hcoeff
  have hsupp := halfAngleFourierCoefficient_support hhom hpd hcoeff
  simp only [hL, Nat.sub_zero, Nat.add_zero] at hsupp
  exact hk (Nat.le_antisymm hsupp.2 hsupp.1)

/-- The `L = 0` branch in Lemma 5.2: the half-angle trace is constant. -/
theorem halfAngleTrace_eq_const_of_manuscriptDegree_eq_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hL : manuscriptHalfAngleFourierDegree P N = 0) :
    halfAngleTrace P = fun _ => halfAngleTrace P 0 := by
  funext phi
  apply Complex.ofReal_injective
  have hcenter (t : ℝ) :
      (halfAngleTrace P t : ℂ) = (halfAnglePolynomial P).coeff N := by
    rw [halfAngleTrace_finiteFourierExpansion hhom]
    rw [Finset.sum_eq_single N]
    · simp [halfAngleFourierCoefficient, centeredHalfAngleMode]
    · intro k hk_range hk_ne
      simp [halfAngleFourierCoefficient,
        halfAnglePolynomial_coeff_eq_zero_off_center hhom hpd hL hk_ne]
    · simp only [Finset.mem_range]
      omega
  exact (hcenter phi).trans (hcenter 0).symm

/-- Consequently the original circle trace `p` is constant as well. -/
theorem circleTrace_eq_const_of_manuscriptDegree_eq_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hL : manuscriptHalfAngleFourierDegree P N = 0) :
    circleTrace P = fun _ => halfAngleTrace P 0 := by
  funext theta
  rw [← halfAngleTrace_two_mul P theta]
  exact congrFun
    (halfAngleTrace_eq_const_of_manuscriptDegree_eq_zero hhom hpd hL)
    (2 * theta)

/-- In the `L = 0` branch, `p'` vanishes identically. -/
theorem circleTraceDerivative_eq_zero_of_manuscriptDegree_eq_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hL : manuscriptHalfAngleFourierDegree P N = 0) :
    circleTraceDerivative P = 0 := by
  funext theta
  change circleTraceDerivative P theta = 0
  have hconst := circleTrace_eq_const_of_manuscriptDegree_eq_zero hhom hpd hL
  have hderiv := circleTrace_hasDerivAt P theta
  rw [hconst] at hderiv
  exact (hderiv.unique (hasDerivAt_const theta
    (halfAngleTrace P 0)))

/-- Thus the normalized logarithmic derivative in Lemma 5.2 is zero in the
constant case, before the factorization-series argument begins. -/
theorem normalizedCircleTraceDerivative_eq_zero_of_manuscriptDegree_eq_zero
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (hL : manuscriptHalfAngleFourierDegree P N = 0) :
    (fun theta =>
      circleTraceDerivative P theta /
        (((2 * N : ℕ) : ℝ) * circleTrace P theta)) = 0 := by
  funext theta
  rw [circleTraceDerivative_eq_zero_of_manuscriptDegree_eq_zero hhom hpd hL]
  simp

private theorem manuscriptClearedPolynomial_unitCircle_representation
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    ∀ theta : ℝ, (halfAngleTrace P theta : ℂ) =
      (Complex.exp ((theta : ℂ) * I))⁻¹ ^
          manuscriptHalfAngleFourierDegree P N *
        (manuscriptClearedPolynomial P N).eval
          (Complex.exp ((theta : ℂ) * I)) := by
  intro theta
  rw [manuscriptClearedPolynomial_laurent_representation hhom hpd]
  congr 1
  calc
    Complex.exp (-((manuscriptHalfAngleFourierDegree P N : ℂ) *
        (theta : ℂ) * I)) =
        Complex.exp ((manuscriptHalfAngleFourierDegree P N : ℂ) *
          (-((theta : ℂ) * I))) := by congr 1; ring
    _ = Complex.exp (-((theta : ℂ) * I)) ^
        manuscriptHalfAngleFourierDegree P N :=
      Complex.exp_nat_mul _ _
    _ = (Complex.exp ((theta : ℂ) * I))⁻¹ ^
        manuscriptHalfAngleFourierDegree P N := by
      rw [Complex.exp_neg]

/-- The normalized factors exported after the manuscript's positive-degree
branch.  This calls the stated strict trigonometric factorization and then
normalizes that same returned polynomial `Q`, with the factor count tied to
the actual Fourier degree by the accompanying equality. -/
theorem manuscriptHalfAngleFactorization_of_degree_pos
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P)
    (_hL : 0 < manuscriptHalfAngleFourierDegree P N) :
    ∃ data : StrictFejerRieszData (halfAngleTrace P) N,
      data.L = manuscriptHalfAngleFourierDegree P N := by
  obtain ⟨factorization⟩ := manuscript_strict_trigonometric_factorization
    (manuscriptClearedPolynomial P N)
    (manuscriptHalfAngleFourierDegree_le hhom)
    (manuscriptClearedPolynomial_natDegree hhom hpd)
    (manuscriptClearedPolynomial_coeff_zero_ne hhom hpd)
    (manuscriptClearedPolynomial_conjReflect hhom hpd)
    (manuscriptClearedPolynomial_unitCircle_representation hhom hpd)
    hpd.halfAngleTrace_pos
  obtain ⟨normalization⟩ :=
    manuscript_normalize_strict_trigonometric_factor factorization.polynomial
  exact ⟨normalization.normalized,
    normalization.normalized_degree.trans factorization.polynomial_degree⟩

end

end HomogeneousObstruction
