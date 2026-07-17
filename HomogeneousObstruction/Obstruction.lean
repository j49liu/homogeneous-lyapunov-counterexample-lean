import HomogeneousObstruction.LogBound
import HomogeneousObstruction.Degree

namespace HomogeneousObstruction

open Complex

noncomputable section

/-- The nonnegative weight in the Fourier contradiction, equation (5.8) of the paper. -/
def obstructionWeight (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  1 - 5 * Real.cos (2 * θ) - g θ

/-- The final Fourier contradiction, parametrized by the strict logarithmic second-harmonic
bound.  This is the outside layer of the proof of main theorem item (3). -/
theorem fourierContradiction_of_log_bound
    {P : BivariatePolynomial} {N : ℕ}
    (hN : 0 < N)
    (hhom : P.IsHomogeneous (2 * N))
    (hpd : PositiveDefinite P)
    (hlie : LieNonpositive P)
    (hlog :
      ‖realPaperFourierCoeff
        (normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P)) 2‖ < 1) :
    False := by
  let g : ℝ → ℝ := normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P)
  let w : ℝ → ℝ := obstructionWeight g
  have htwoN_nat : 0 < 2 * N := Nat.mul_pos (by norm_num) hN
  have htwoN : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast htwoN_nat
  have htwoN_ne : (((2 * N : ℕ) : ℝ)) ≠ 0 := htwoN.ne'
  have hp (θ : ℝ) : 0 < circleTrace P θ := hpd.circleTrace_pos θ

  have hg_eq : g = fun θ ↦
      (((2 * N : ℕ) : ℝ))⁻¹ *
        (circleTraceDerivative P θ / circleTrace P θ) := by
    funext θ
    dsimp [g, normalizedLogDerivative]
    field_simp [htwoN_ne, (hp θ).ne']

  have hp_period : circleTrace P (2 * Real.pi) = circleTrace P 0 := by
    simpa using circleTrace_periodic P 0
  have hg_zero : realPaperFourierCoeff g 0 = 0 := by
    rw [hg_eq]
    exact realPaperFourierCoeff_const_mul_logDerivative_zero
      (circleTrace P) (circleTraceDerivative P) (((2 * N : ℕ) : ℝ))⁻¹
      hp (circleTrace_hasDerivAt P) (circleTraceDerivative_continuous P) hp_period

  have hg_cont : Continuous g := by
    rw [hg_eq]
    exact continuous_const.mul
      ((circleTraceDerivative_continuous P).div (circleTrace_continuous P)
        (fun θ ↦ (hp θ).ne'))
  have hbase_cont : Continuous (fun θ : ℝ ↦ 1 - 5 * Real.cos (2 * θ)) := by
    fun_prop
  have hfiveCos_cont : Continuous (fun θ : ℝ ↦ 5 * Real.cos (2 * θ)) := by
    fun_prop
  have hw_cont : Continuous w := by
    dsimp [w, obstructionWeight]
    exact hbase_cont.sub hg_cont

  have hw_nonneg : ∀ θ, 0 ≤ w θ := by
    intro θ
    have hLie := hlie (circlePoint θ)
    rw [lieDerivative_on_circle hhom θ] at hLie
    have hden : 0 < (((2 * N : ℕ) : ℝ)) * circleTrace P θ :=
      mul_pos htwoN (hp θ)
    dsimp [w, obstructionWeight, g, normalizedLogDerivative]
    rw [sub_nonneg, div_le_iff₀ hden]
    dsimp [radialCoefficient] at hLie
    nlinarith

  have hbase_coeff (n : ℤ) :
      realPaperFourierCoeff (fun θ : ℝ ↦ 1 - 5 * Real.cos (2 * θ)) n =
        realPaperFourierCoeff (fun _ : ℝ ↦ 1) n -
          realPaperFourierCoeff (fun θ : ℝ ↦ 5 * Real.cos (2 * θ)) n := by
    exact realPaperFourierCoeff_sub _ _ continuous_const hfiveCos_cont n
  have hw_coeff (n : ℤ) :
      realPaperFourierCoeff w n =
        realPaperFourierCoeff (fun θ : ℝ ↦ 1 - 5 * Real.cos (2 * θ)) n -
          realPaperFourierCoeff g n := by
    dsimp [w, obstructionWeight]
    exact realPaperFourierCoeff_sub _ _ hbase_cont hg_cont n

  have hw_zero : realPaperFourierCoeff w 0 = 1 := by
    rw [hw_coeff 0, hbase_coeff 0, realPaperFourierCoeff_const_mul,
      realPaperFourierCoeff_one_zero, realPaperFourierCoeff_cos_two_zero, hg_zero]
    norm_num
  have hw_two : realPaperFourierCoeff w 2 =
      -(5 / 2 : ℂ) - realPaperFourierCoeff g 2 := by
    rw [hw_coeff 2, hbase_coeff 2, realPaperFourierCoeff_const_mul,
      realPaperFourierCoeff_one_two, realPaperFourierCoeff_cos_two_two]
    norm_num

  have hw_bound : ‖realPaperFourierCoeff w 2‖ ≤ 1 := by
    have h := norm_realPaperFourierCoeff_le_zero_re w hw_nonneg 2
    rw [hw_zero] at h
    simpa using h
  have hg_bound : ‖realPaperFourierCoeff g 2‖ < 1 := by
    simpa [g] using hlog
  have hsum :
      realPaperFourierCoeff w 2 + realPaperFourierCoeff g 2 = -(5 / 2 : ℂ) := by
    rw [hw_two]
    ring
  have htriangle := norm_add_le (realPaperFourierCoeff w 2) (realPaperFourierCoeff g 2)
  rw [hsum] at htriangle
  have hnorm : ‖-(5 / 2 : ℂ)‖ = (5 / 2 : ℝ) := by norm_num
  rw [hnorm] at htriangle
  nlinarith

/-- Main theorem item (3), in pointwise form.  The homogeneous degree is not
assumed even or positive: both facts are derived from positive definiteness. -/
theorem no_positiveDefinite_homogeneous_polynomial
    (P : BivariatePolynomial) (hhom : Homogeneous P) (hpd : PositiveDefinite P) :
    ¬ LieNonpositive P := by
  intro hlie
  obtain ⟨N, hN, hdegree⟩ := exists_positive_even_homogeneous_degree hhom hpd
  exact fourierContradiction_of_log_bound hN hdegree hpd hlie
    (logarithmicSecondHarmonicBound hN hdegree hpd)

/-- Main theorem item (3), literally as a nonexistence statement over
homogeneous polynomials of arbitrary degree. -/
theorem mainTheorem_item3 :
    ¬ ∃ P : BivariatePolynomial,
      Homogeneous P ∧ PositiveDefinite P ∧ LieNonpositive P := by
  rintro ⟨P, hhom, hpd, hlie⟩
  exact no_positiveDefinite_homogeneous_polynomial P hhom hpd hlie

end

end HomogeneousObstruction
