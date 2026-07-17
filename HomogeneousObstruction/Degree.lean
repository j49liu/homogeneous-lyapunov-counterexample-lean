import HomogeneousObstruction.Basic

namespace HomogeneousObstruction

open scoped BigOperators Matrix
open MvPolynomial

noncomputable section

/-- Evaluation of a homogeneous polynomial commutes with scalar dilation, with the
expected power of the homogeneous degree. -/
theorem evalAt_smul_of_isHomogeneous {P : BivariatePolynomial} {n : ℕ}
    (hP : P.IsHomogeneous n) (a : ℝ) (z : Point) :
    evalAt P (a • z) = a ^ n * evalAt P z := by
  classical
  simp only [evalAt, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := hP.degree_eq_sum_deg_support hd
  have hprod : (∏ i ∈ d.support, (a • z) i ^ d i) =
      a ^ n * ∏ i ∈ d.support, z i ^ d i := by
    calc
      (∏ i ∈ d.support, (a • z) i ^ d i) =
          ∏ i ∈ d.support, (a ^ d i * z i ^ d i) := by
            apply Finset.prod_congr rfl
            intro i _
            simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      _ = (∏ i ∈ d.support, a ^ d i) * ∏ i ∈ d.support, z i ^ d i := by
            rw [Finset.prod_mul_distrib]
      _ = a ^ (∑ i ∈ d.support, d i) * ∏ i ∈ d.support, z i ^ d i := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = a ^ n * ∏ i ∈ d.support, z i ^ d i := by rw [← hdeg]
  rw [hprod]
  ring

/-- In particular, a homogeneous polynomial changes under antipodal negation by
the parity factor `(-1)^n`. -/
theorem evalAt_neg_of_isHomogeneous {P : BivariatePolynomial} {n : ℕ}
    (hP : P.IsHomogeneous n) (z : Point) :
    evalAt P (-z) = (-1 : ℝ) ^ n * evalAt P z := by
  simpa using evalAt_smul_of_isHomogeneous hP (-1 : ℝ) z

/-- A half-turn of the circle parametrization is antipodal. -/
theorem circlePoint_add_pi (theta : ℝ) :
    circlePoint (theta + Real.pi) = -circlePoint theta := by
  funext i
  fin_cases i
  · simp [circlePoint, Real.cos_add_pi]
  · simp [circlePoint, Real.sin_add_pi]

/-- Explicit parity bookkeeping for an even homogeneous circle trace: only
even angular modes can occur, equivalently the trace is `pi`-periodic. -/
theorem circleTrace_pi_periodic_of_evenDegree
    {P : BivariatePolynomial} {N : ℕ} (hP : P.IsHomogeneous (2 * N)) :
    Function.Periodic (circleTrace P) Real.pi := by
  intro theta
  rw [circleTrace, circlePoint_add_pi, evalAt_neg_of_isHomogeneous hP]
  simp [circleTrace]

/-- A positive definite polynomial is not the zero polynomial. -/
theorem PositiveDefinite.ne_zero {P : BivariatePolynomial} (hP : PositiveDefinite P) :
    P ≠ 0 := by
  let e : Point := ![1, 0]
  have he : e ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [e] at h0
  intro hzero
  have hpositive := hP.2 e he
  simp [evalAt, hzero] at hpositive

/-- The degree of a positive definite homogeneous polynomial is positive; degree
zero is ruled out using the required value at the origin. -/
theorem positive_degree_of_positiveDefinite {P : BivariatePolynomial} {n : ℕ}
    (hhom : P.IsHomogeneous n) (hP : PositiveDefinite P) :
    0 < n := by
  apply Nat.pos_of_ne_zero
  intro hn
  subst n
  have htd : P.totalDegree = 0 := hhom.totalDegree hP.ne_zero
  have hconst : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp htd
  have hcoeff : P.coeff 0 = 0 := by
    simpa [PositiveDefinite, evalAt, eval_zero, constantCoeff_eq] using hP.1
  apply hP.ne_zero
  rw [hconst, hcoeff]
  simp

/-- The degree of a positive definite homogeneous polynomial is even, since an
odd-degree homogeneous polynomial takes opposite values at antipodal points. -/
theorem even_degree_of_positiveDefinite {P : BivariatePolynomial} {n : ℕ}
    (hhom : P.IsHomogeneous n) (hP : PositiveDefinite P) :
    Even n := by
  rcases Nat.even_or_odd n with hn | hn
  · exact hn
  · let e : Point := ![1, 0]
    have he : e ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp [e] at h0
    have hne : -e ≠ 0 := neg_ne_zero.mpr he
    have hp := hP.2 e he
    have hnp := hP.2 (-e) hne
    have heval := evalAt_neg_of_isHomogeneous hhom e
    rw [hn.neg_one_pow] at heval
    norm_num at heval
    linarith

/-- A positive definite homogeneous polynomial has degree `2 * N` for some
strictly positive `N`.  This is the form used by the logarithmic Fourier bound. -/
theorem exists_positive_even_homogeneous_degree {P : BivariatePolynomial}
    (hhom : Homogeneous P) (hP : PositiveDefinite P) :
    ∃ N : ℕ, 0 < N ∧ P.IsHomogeneous (2 * N) := by
  obtain ⟨n, hn⟩ := hhom
  have hnpos := positive_degree_of_positiveDefinite hn hP
  obtain ⟨N, hN⟩ := even_degree_of_positiveDefinite hn hP
  refine ⟨N, ?_, ?_⟩
  · omega
  · convert hn using 1
    omega

end

end HomogeneousObstruction
