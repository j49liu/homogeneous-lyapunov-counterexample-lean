import HomogeneousObstruction.LogSeries
import HomogeneousObstruction.ActualFourierDegree

namespace HomogeneousObstruction

open Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-!
# The logarithmic second-harmonic estimate

This file completes Lemma 5.2 in the order used in the manuscript.  Let `L`
be the actual Fourier degree of the half-angle trace `q`.  The proof first
disposes of `L = 0`, when `q` and the normalized logarithmic derivative are
constant and zero, respectively.  In the branch `L > 0`, it uses the
manuscript's direct strict Fejer--Riesz construction

`A_L = kappa * B * B#`, `Q = sqrt(kappa) * B`,

followed by the normalized factorization with exactly `L` disk parameters.
The coefficient formula is supplied by the manuscript's uniformly
convergent logarithmic Taylor series, and the estimate is then exactly

`|g-hat_2| <= N⁻¹ sum |alpha_l| < L / N <= 1`.
-/

/-- The normalized logarithmic derivative in Lemma 5.2. -/
def normalizedLogDerivative (N : ℕ) (p p' : ℝ → ℝ) (theta : ℝ) : ℝ :=
  p' theta / ((2 * N : ℕ) * p theta)

/-- Lemma 5.2 of the paper, with the paper's Fourier sign convention and
`1 / (2 * pi)` normalization.  The factor count in the strict estimate is
the actual Fourier degree `L`, not merely its a priori upper bound `N`. -/
theorem logarithmicSecondHarmonicBound
    {P : BivariatePolynomial} {N : ℕ} (hN : 0 < N)
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    ‖realPaperFourierCoeff
      (normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P)) 2‖ < 1 := by
  let L := manuscriptHalfAngleFourierDegree P N
  by_cases hLzero : L = 0
  · have hzero :=
      normalizedCircleTraceDerivative_eq_zero_of_manuscriptDegree_eq_zero
        hhom hpd hLzero
    have hfun :
        normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P) = 0 := by
      simpa only [normalizedLogDerivative] using hzero
    rw [hfun]
    rw [realPaperFourierCoeff, paperFourierCoeff_eq_integral]
    simp
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hLzero
    obtain ⟨data, hdataL⟩ :=
      manuscriptHalfAngleFactorization_of_degree_pos hhom hpd hLpos
    have hqpos : ∀ phi, 0 < halfAngleTrace P phi := hpd.halfAngleTrace_pos
    have hformula := manuscript_logarithmic_fourier_formula
      hN hqpos (halfAngleTrace_hasDerivAt P) data
    have hbridge :
        (fun theta : ℝ =>
          ((normalizedLogDerivative N (circleTrace P)
            (circleTraceDerivative P) theta : ℝ) : ℂ)) =
        (fun theta : ℝ =>
          ((halfAngleTraceDerivative P (2 * theta) /
            ((N : ℝ) * halfAngleTrace P (2 * theta)) : ℝ) : ℂ)) := by
      funext theta
      rw [halfAngleTraceDerivative_two_mul, halfAngleTrace_two_mul]
      simp only [normalizedLogDerivative]
      push_cast
      ring
    have hcoeff :
        realPaperFourierCoeff
            (normalizedLogDerivative N (circleTrace P)
              (circleTraceDerivative P)) 2 =
          -(I / (N : ℂ)) * ∑ j, data.alpha j := by
      rw [realPaperFourierCoeff, hbridge]
      exact hformula
    rw [hcoeff]
    have hdataLpos : 0 < data.L := by omega
    have hnonempty : (Finset.univ : Finset (Fin data.L)).Nonempty :=
      ⟨⟨0, hdataLpos⟩, Finset.mem_univ _⟩
    have hsumTerms :
        ∑ j : Fin data.L, ‖data.alpha j‖ < (L : ℝ) := by
      calc
        ∑ j : Fin data.L, ‖data.alpha j‖ <
            ∑ _j : Fin data.L, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hnonempty
            (fun j _ => data.alpha_norm_lt_one j)
        _ = (data.L : ℝ) := by simp
        _ = (L : ℝ) := by exact_mod_cast hdataL
    have hLle : (L : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast manuscriptHalfAngleFourierDegree_le hhom
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    calc
      ‖-(I / (N : ℂ)) * ∑ j, data.alpha j‖ ≤
          (N : ℝ)⁻¹ * ∑ j, ‖data.alpha j‖ := by
        rw [norm_mul, norm_neg, norm_div, norm_I, Complex.norm_natCast,
          one_div]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (inv_nonneg.mpr hNreal.le)
      _ < (N : ℝ)⁻¹ * (L : ℝ) :=
        mul_lt_mul_of_pos_left hsumTerms (inv_pos.mpr hNreal)
      _ = (L : ℝ) / (N : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_one hNreal).2 hLle

end

end HomogeneousObstruction
