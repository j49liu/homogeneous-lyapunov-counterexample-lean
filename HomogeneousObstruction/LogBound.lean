import HomogeneousObstruction.FejerRiesz
import HomogeneousObstruction.FourierBasic
import HomogeneousObstruction.MeanLemmas
import HomogeneousObstruction.HalfAnglePolynomial
import Mathlib.Analysis.Calculus.LogDeriv

namespace HomogeneousObstruction

open Complex Metric Set
open scoped BigOperators ComplexConjugate

noncomputable section

/-!
# The logarithmic second-harmonic estimate

This follows the paper's half-angle proof: factor
`q(phi) = p(phi / 2)`, whose actual factor count is at most `N`, compute mode
one of its normalized logarithmic derivative, and then transport mode one to
mode two under `phi = 2 * theta`.  Logarithmic differentiation of the finite
product is kept algebraic, so no branch of the complex logarithm is needed.
-/

/-- The normalized logarithmic derivative in Lemma 5.2. -/
def normalizedLogDerivative (N : ℕ) (p p' : ℝ → ℝ) (θ : ℝ) : ℝ :=
  p' θ / ((2 * N : ℕ) * p θ)

/-- The degree-normalized logarithmic derivative of the paper's half-angle
trace `q`.  Its denominator is `N`, rather than the original degree `2 * N`. -/
def halfAngleNormalizedLogDerivative (N : ℕ) (q q' : ℝ → ℝ) (phi : ℝ) : ℝ :=
  q' phi / ((N : ℕ) * q phi)

private def unitCircle (θ : ℝ) : ℂ := circleMap 0 1 θ

@[simp] private theorem norm_unitCircle (θ : ℝ) : ‖unitCircle θ‖ = 1 := by
  simp [unitCircle]

private theorem unitCircle_ne_zero (θ : ℝ) : unitCircle θ ≠ 0 :=
  norm_pos_iff.mp (by rw [norm_unitCircle]; norm_num)

private theorem one_sub_alpha_unitCircle_ne_zero {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) :
    1 - a * unitCircle θ ≠ 0 := by
  intro h
  have haz : a * unitCircle θ = 1 := (sub_eq_zero.mp h).symm
  have hn := congrArg norm haz
  rw [norm_mul, norm_unitCircle, mul_one, norm_one] at hn
  linarith

private theorem one_sub_conj_alpha_inv_unitCircle_ne_zero {a : ℂ} (ha : ‖a‖ < 1)
    (θ : ℝ) :
    1 - (starRingEnd ℂ a) * (unitCircle θ)⁻¹ ≠ 0 := by
  intro h
  have haz : (starRingEnd ℂ a) * (unitCircle θ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
  have hn := congrArg norm haz
  rw [norm_mul, norm_inv, norm_unitCircle, inv_one, mul_one, starRingEnd_apply, norm_star,
    norm_one] at hn
  linarith

private theorem normSq_factor_identity (a : ℂ) (θ : ℝ) :
    (((‖1 - a * unitCircle θ‖ ^ 2 : ℝ) : ℂ)) =
      (1 - a * unitCircle θ) *
        (1 - (starRingEnd ℂ a) * (unitCircle θ)⁻¹) := by
  rw [Complex.inv_eq_conj (norm_unitCircle θ)]
  rw [show (((‖1 - a * unitCircle θ‖ ^ 2 : ℝ) : ℂ)) =
      (starRingEnd ℂ (1 - a * unitCircle θ)) * (1 - a * unitCircle θ) by
    rw [Complex.conj_mul']
    norm_cast]
  simp only [map_sub, map_one, map_mul]
  ring

private theorem hasDerivAt_posFactor (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => 1 - a * unitCircle t)
      (-a * (unitCircle θ * I)) θ := by
  have hz := hasDerivAt_circleMap (0 : ℂ) 1 θ
  have ha := hz.const_mul a
  simpa [unitCircle] using (hasDerivAt_const (x := θ) (c := (1 : ℂ))).sub ha

private theorem hasDerivAt_invUnitCircle (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (unitCircle t)⁻¹)
      (-(unitCircle θ)⁻¹ * I) θ := by
  have hneg : HasDerivAt (fun t : ℝ ↦ -t) (-1) θ := (hasDerivAt_id θ).neg
  have hi := (hasDerivAt_circleMap (0 : ℂ) 1 (-θ)).scomp θ hneg
  convert hi using 1
  · ext t
    simp [unitCircle, circleMap_zero_inv]
  · simp [unitCircle, circleMap_zero_inv]

private theorem hasDerivAt_negFactor (a : ℂ) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => 1 - (starRingEnd ℂ a) * (unitCircle t)⁻¹)
      ((starRingEnd ℂ a) * (unitCircle θ)⁻¹ * I) θ := by
  have hi := (hasDerivAt_invUnitCircle θ).const_mul (starRingEnd ℂ a)
  convert (hasDerivAt_const (x := θ) (c := (1 : ℂ))).sub hi using 1
  ring

private theorem logDeriv_posFactor (a : ℂ) (θ : ℝ) :
    logDeriv (fun t : ℝ => 1 - a * unitCircle t) θ =
      (-a * (unitCircle θ * I)) / (1 - a * unitCircle θ) := by
  rw [logDeriv_apply, (hasDerivAt_posFactor a θ).deriv]

private theorem logDeriv_negFactor (a : ℂ) (θ : ℝ) :
    logDeriv (fun t : ℝ => 1 - (starRingEnd ℂ a) * (unitCircle t)⁻¹) θ =
      ((starRingEnd ℂ a) * (unitCircle θ)⁻¹ * I) /
        (1 - (starRingEnd ℂ a) * (unitCircle θ)⁻¹) := by
  rw [logDeriv_apply, (hasDerivAt_negFactor a θ).deriv]

/-- Fourier mode one, with the paper's sign and normalization, is a circle
average after multiplication by `z⁻¹`. -/
theorem paperFourierCoeff_comp_unitCircle_one (F : ℂ → ℂ) :
    paperFourierCoeff (fun phi : ℝ => F (unitCircle phi)) 1 =
      Real.circleAverage (fun z : ℂ => z⁻¹ * F z) 0 1 := by
  rw [paperFourierCoeff_eq_integral, Real.circleAverage_def]
  simp only [one_div, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  apply intervalIntegral.integral_congr
  intro phi _
  simp only [unitCircle, circleMap_zero, Int.cast_one]
  rw [mul_comm]
  congr 1
  rw [Complex.ofReal_one, one_mul, ← Complex.exp_neg]
  congr 1
  ring

private def posFactorTerm (a : ℂ) (θ : ℝ) : ℂ :=
  (-a * (unitCircle θ * I)) / (1 - a * unitCircle θ)

private def negFactorTerm (a : ℂ) (θ : ℝ) : ℂ :=
  ((starRingEnd ℂ a) * (unitCircle θ)⁻¹ * I) /
    (1 - (starRingEnd ℂ a) * (unitCircle θ)⁻¹)

private theorem continuous_posFactorTerm {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (posFactorTerm a) := by
  have hu : Continuous unitCircle := by
    simpa [unitCircle] using continuous_circleMap (0 : ℂ) 1
  apply Continuous.div
  · exact continuous_const.mul (hu.mul continuous_const)
  · exact continuous_const.sub (continuous_const.mul hu)
  · exact one_sub_alpha_unitCircle_ne_zero ha

private theorem continuous_negFactorTerm {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (negFactorTerm a) := by
  have hu : Continuous unitCircle := by
    simpa [unitCircle] using continuous_circleMap (0 : ℂ) 1
  have hui : Continuous (fun θ => (unitCircle θ)⁻¹) :=
    hu.inv₀ unitCircle_ne_zero
  apply Continuous.div
  · exact (continuous_const.mul hui).mul continuous_const
  · exact continuous_const.sub (continuous_const.mul hui)
  · exact one_sub_conj_alpha_inv_unitCircle_ne_zero ha

private theorem paperFourierCoeff_posFactorTerm_one {a : ℂ} (ha : ‖a‖ < 1) :
    paperFourierCoeff (posFactorTerm a) 1 = -I * a := by
  calc
    paperFourierCoeff (posFactorTerm a) 1 =
        Real.circleAverage
          (fun z : ℂ => z⁻¹ * ((-a * (z * I)) / (1 - a * z))) 0 1 := by
      exact paperFourierCoeff_comp_unitCircle_one
        (fun z : ℂ => (-a * (z * I)) / (1 - a * z))
    _ = Real.circleAverage
          (fun z : ℂ => (-I) * (a / (1 - a * z))) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz0 : z ≠ 0 := by
        have hn : ‖z‖ = 1 := by simpa [mem_sphere] using hz
        intro h
        simp [h] at hn
      field_simp [hz0]
    _ = (-I) * Real.circleAverage (fun z : ℂ => a / (1 - a * z)) 0 1 := by
      change Real.circleAverage
          (fun z : ℂ => (-I) • (a / (1 - a * z))) 0 1 =
        (-I) • Real.circleAverage (fun z : ℂ => a / (1 - a * z)) 0 1
      exact Real.circleAverage_fun_smul
    _ = -I * a := by rw [circleAverage_div_one_sub_mul ha]

private theorem paperFourierCoeff_negFactorTerm_one {a : ℂ} (ha : ‖a‖ < 1) :
    paperFourierCoeff (negFactorTerm a) 1 = 0 := by
  calc
    paperFourierCoeff (negFactorTerm a) 1 =
        Real.circleAverage
          (fun z : ℂ => z⁻¹ * (((starRingEnd ℂ a) * z⁻¹ * I) /
            (1 - (starRingEnd ℂ a) * z⁻¹))) 0 1 := by
      exact paperFourierCoeff_comp_unitCircle_one
        (fun z : ℂ => ((starRingEnd ℂ a) * z⁻¹ * I) /
          (1 - (starRingEnd ℂ a) * z⁻¹))
    _ = Real.circleAverage
          (fun z : ℂ => I * ((starRingEnd ℂ a) * z⁻¹ ^ 2 /
            (1 - (starRingEnd ℂ a) * z⁻¹))) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz0 : z ≠ 0 := by
        have hn : ‖z‖ = 1 := by simpa [mem_sphere] using hz
        intro h
        simp [h] at hn
      field_simp [hz0]
    _ = I * Real.circleAverage
          (fun z : ℂ => (starRingEnd ℂ a) * z⁻¹ ^ 2 /
            (1 - (starRingEnd ℂ a) * z⁻¹)) 0 1 := by
      change Real.circleAverage
          (fun z : ℂ => I • ((starRingEnd ℂ a) * z⁻¹ ^ 2 /
            (1 - (starRingEnd ℂ a) * z⁻¹))) 0 1 =
        I • Real.circleAverage
          (fun z : ℂ => (starRingEnd ℂ a) * z⁻¹ ^ 2 /
            (1 - (starRingEnd ℂ a) * z⁻¹)) 0 1
      exact Real.circleAverage_fun_smul
    _ = 0 := by
      have ha' : ‖starRingEnd ℂ a‖ < 1 := by
        rw [starRingEnd_apply, norm_star]
        exact ha
      have havg := circleAverage_mul_inv_pow_div_one_sub_mul_inv
        (a := starRingEnd ℂ a) ha' (k := 2) (by norm_num : 0 < 2)
      rw [havg, mul_zero]

/-- The exact mode-one contribution of one factor in the paper's half-angle
factorization. -/
theorem paperFourierCoeff_factorTerm_one {a : ℂ} (ha : ‖a‖ < 1) :
    paperFourierCoeff (fun phi => posFactorTerm a phi + negFactorTerm a phi) 1 =
      -I * a := by
  rw [paperFourierCoeff_add _ _ (continuous_posFactorTerm ha)
    (continuous_negFactorTerm ha), paperFourierCoeff_posFactorTerm_one ha,
    paperFourierCoeff_negFactorTerm_one ha, add_zero]

private theorem factorization_as_complex_product {p : ℝ → ℝ} {D : ℕ}
    (data : StrictFejerRieszData p D) :
    (fun θ : ℝ => (p θ : ℂ)) = fun θ =>
      (data.c : ℂ) * ∏ j,
        ((1 - data.alpha j * unitCircle θ) *
          (1 - (starRingEnd ℂ (data.alpha j)) * (unitCircle θ)⁻¹)) := by
  funext θ
  rw [data.factorization]
  rw [Complex.ofReal_mul, Complex.ofReal_prod]
  apply congrArg ((data.c : ℂ) * ·)
  apply Finset.prod_congr rfl
  intro j _
  simpa [unitCircle, circleMap_zero, Complex.ofReal_one, one_mul] using
    normSq_factor_identity (data.alpha j) θ

/-- Algebraic logarithmic differentiation of the strict factorization. -/
theorem complex_logDerivative_eq_sum_factorTerms
    {p dp : ℝ → ℝ} {D : ℕ} (data : StrictFejerRieszData p D)
    (hderiv : ∀ θ, HasDerivAt p (dp θ) θ) (θ : ℝ) :
    ((dp θ / p θ : ℝ) : ℂ) =
      ∑ j, (posFactorTerm (data.alpha j) θ + negFactorTerm (data.alpha j) θ) := by
  have hleft :
      logDeriv (fun t : ℝ => (p t : ℂ)) θ = ((dp θ / p θ : ℝ) : ℂ) := by
    rw [logDeriv_apply, (hderiv θ).ofReal_comp.deriv]
    norm_cast
  rw [← hleft, factorization_as_complex_product data]
  rw [logDeriv_const_mul θ (data.c : ℂ) (by exact_mod_cast data.c_pos.ne')]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro j _
    rw [logDeriv_mul θ
      (one_sub_alpha_unitCircle_ne_zero (data.alpha_norm_lt_one j) θ)
      (one_sub_conj_alpha_inv_unitCircle_ne_zero (data.alpha_norm_lt_one j) θ)
      (hasDerivAt_posFactor (data.alpha j) θ).differentiableAt
      (hasDerivAt_negFactor (data.alpha j) θ).differentiableAt]
    rw [logDeriv_posFactor, logDeriv_negFactor]
    rfl
  · intro j _
    exact mul_ne_zero
      (one_sub_alpha_unitCircle_ne_zero (data.alpha_norm_lt_one j) θ)
      (one_sub_conj_alpha_inv_unitCircle_ne_zero (data.alpha_norm_lt_one j) θ)
  · intro j _
    exact (hasDerivAt_posFactor (data.alpha j) θ).mul
      (hasDerivAt_negFactor (data.alpha j) θ) |>.differentiableAt

private theorem paperFourierCoeff_finset_sum {J : Type*} [Fintype J]
    (u : J → ℝ → ℂ) (hu : ∀ j, Continuous (u j)) (n : ℤ) :
    paperFourierCoeff (fun θ => ∑ j, u j θ) n =
      ∑ j, paperFourierCoeff (u j) n := by
  simp_rw [paperFourierCoeff_eq_integral, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro j _
    exact ((hu j).mul (by fun_prop)).intervalIntegrable _ _

/-- The paper's exact coefficient formula after factoring the half-angle trace:
`ĝ₂ = -(i/N) ∑ α`.  At this stage it is mode one of `q`; the subsequent
doubling lemma transports it to mode two of the original circle trace. -/
theorem halfAngleNormalizedLogDerivative_fourierCoeff_one_of_factorization
    {N : ℕ} (hN : 0 < N) {q dq : ℝ → ℝ}
    (hq : ∀ phi, 0 < q phi) (hderiv : ∀ phi, HasDerivAt q (dq phi) phi)
    (data : StrictFejerRieszData q N) :
    realPaperFourierCoeff (halfAngleNormalizedLogDerivative N q dq) 1 =
      -(I / (N : ℂ)) * ∑ j, data.alpha j := by
  have hfun :
      (fun phi : ℝ => (halfAngleNormalizedLogDerivative N q dq phi : ℂ)) =
        fun phi => (((N : ℝ)⁻¹ : ℂ) *
          ∑ j, (posFactorTerm (data.alpha j) phi +
            negFactorTerm (data.alpha j) phi)) := by
    funext phi
    have hq0 : q phi ≠ 0 := (hq phi).ne'
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hreal :
        halfAngleNormalizedLogDerivative N q dq phi =
          (N : ℝ)⁻¹ * (dq phi / q phi) := by
      rw [halfAngleNormalizedLogDerivative]
      field_simp
    rw [hreal, Complex.ofReal_mul, Complex.ofReal_inv]
    rw [complex_logDerivative_eq_sum_factorTerms data hderiv phi]
  rw [realPaperFourierCoeff, hfun, paperFourierCoeff_const_mul]
  rw [paperFourierCoeff_finset_sum]
  · rw [show (∑ j, paperFourierCoeff
        (fun phi => posFactorTerm (data.alpha j) phi +
          negFactorTerm (data.alpha j) phi) 1) =
        ∑ j, (-I * data.alpha j) by
      apply Finset.sum_congr rfl
      intro j _
      exact paperFourierCoeff_factorTerm_one (data.alpha_norm_lt_one j)]
    rw [← Finset.mul_sum]
    push_cast
    field_simp
  · intro j
    exact (continuous_posFactorTerm (data.alpha_norm_lt_one j)).add
      (continuous_negFactorTerm (data.alpha_norm_lt_one j))

/-- The strict `L/N` estimate in Lemma 5.2, with `L` the actual Fourier
degree of the half-angle trace supplied by strict Fejer--Riesz. -/
theorem halfAngleNormalizedLogDerivative_fourierCoeff_one_norm_lt_one
    {N : ℕ} (hN : 0 < N) {q dq : ℝ → ℝ}
    (hq : ∀ phi, 0 < q phi) (hderiv : ∀ phi, HasDerivAt q (dq phi) phi)
    (data : StrictFejerRieszData q N) :
    ‖realPaperFourierCoeff (halfAngleNormalizedLogDerivative N q dq) 1‖ < 1 := by
  rw [halfAngleNormalizedLogDerivative_fourierCoeff_one_of_factorization
    hN hq hderiv data]
  by_cases hL : data.L = 0
  · have hsum : ∑ j : Fin data.L, data.alpha j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      omega
    rw [hsum]
    simp
  · have hLpos : 0 < data.L := Nat.pos_of_ne_zero hL
    have hnonempty : (Finset.univ : Finset (Fin data.L)).Nonempty :=
      ⟨⟨0, hLpos⟩, Finset.mem_univ _⟩
    have hsum_terms :
        ∑ j : Fin data.L, ‖data.alpha j‖ < (data.L : ℝ) := by
      calc
        ∑ j : Fin data.L, ‖data.alpha j‖ <
            ∑ _j : Fin data.L, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hnonempty
            (fun j _ => data.alpha_norm_lt_one j)
        _ = (data.L : ℝ) := by simp
    have hnorm_sum : ‖∑ j : Fin data.L, data.alpha j‖ < (data.L : ℝ) :=
      lt_of_le_of_lt (norm_sum_le _ _) hsum_terms
    have hdegree : (data.L : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast data.degree_le
    have hnorm_lt : ‖∑ j : Fin data.L, data.alpha j‖ < (N : ℝ) :=
      lt_of_lt_of_le hnorm_sum hdegree
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [norm_mul, norm_neg, norm_div, norm_I, Complex.norm_natCast, one_div]
    calc
      (N : ℝ)⁻¹ * ‖∑ j : Fin data.L, data.alpha j‖ <
          (N : ℝ)⁻¹ * (N : ℝ) :=
        mul_lt_mul_of_pos_left hnorm_lt (inv_pos.mpr hNreal)
      _ = 1 := inv_mul_cancel₀ hNreal.ne'

/-- Lemma 5.2 of the paper, with the paper's Fourier sign convention and
`1/(2π)` normalization. -/
theorem logarithmicSecondHarmonicBound
    {P : BivariatePolynomial} {N : ℕ} (hN : 0 < N)
    (hhom : P.IsHomogeneous (2 * N)) (hpd : PositiveDefinite P) :
    ‖realPaperFourierCoeff
      (normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P)) 2‖ < 1 := by
  obtain ⟨data⟩ := strictFejerRiesz_halfAngle hhom hpd
  let H : ℝ → ℝ := halfAngleNormalizedLogDerivative N
    (halfAngleTrace P) (halfAngleTraceDerivative P)
  have hqpos : ∀ phi, 0 < halfAngleTrace P phi := hpd.halfAngleTrace_pos
  have hbound : ‖realPaperFourierCoeff H 1‖ < 1 := by
    exact halfAngleNormalizedLogDerivative_fourierCoeff_one_norm_lt_one
      hN hqpos (halfAngleTrace_hasDerivAt P) data
  have hHcont : Continuous H := by
    dsimp [H, halfAngleNormalizedLogDerivative]
    apply Continuous.div
    · exact halfAngleTraceDerivative_continuous P
    · exact continuous_const.mul (halfAngleTrace_continuous P)
    · intro phi
      exact mul_ne_zero (by exact_mod_cast hN.ne') (hqpos phi).ne'
  have hHperiod : Function.Periodic H (2 * Real.pi) := by
    intro phi
    dsimp [H, halfAngleNormalizedLogDerivative]
    rw [halfAngleTraceDerivative_periodic hhom phi,
      halfAngleTrace_periodic hhom phi]
  have hrescale :
      normalizedLogDerivative N (circleTrace P) (circleTraceDerivative P) =
        fun theta => H (2 * theta) := by
    funext theta
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp [H, halfAngleNormalizedLogDerivative, normalizedLogDerivative,
      halfAngleTrace, halfAngleTraceDerivative]
    field_simp
    push_cast
    ring
  rw [hrescale, realPaperFourierCoeff_comp_two H hHcont hHperiod]
  exact hbound

end

end HomogeneousObstruction
