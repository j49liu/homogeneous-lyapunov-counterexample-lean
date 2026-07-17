import HomogeneousObstruction.FejerRiesz
import HomogeneousObstruction.FourierBasic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

namespace HomogeneousObstruction

open Complex Set
open scoped BigOperators ComplexConjugate Interval Real

noncomputable section

/-!
# The logarithmic series calculation in Lemma 5.2

This file formalizes the analytic calculation as it is written in the
manuscript.  For `‖a‖ < 1`, the principal logarithm on the disk
`{1 - z | ‖z‖ < 1}` is expanded into its Taylor series.  Both that series and
its differentiated series are proved to converge uniformly in the angular
variable.  Fourier coefficients are then read from the differentiated
series.

The index `n = 0` is retained below with value zero.  Thus the Lean sums over
`n : ℕ` are literally the manuscript's sums over `n ≥ 1` with a harmless
zero term prepended.
-/

/-- The positive-frequency Taylor term
`-a^n e^{2 i n theta} / n` in `log (1 - a e^{2 i theta})`.
The value at `n = 0` is zero by Lean's division convention. -/
def positiveLogSeriesTerm (a : ℂ) (n : ℕ) (theta : ℝ) : ℂ :=
  -(a ^ n / (n : ℂ)) *
    Complex.exp ((n : ℂ) * (2 * I * (theta : ℂ)))

/-- The termwise derivative of `positiveLogSeriesTerm`. -/
def positiveLogSeriesDerivativeTerm (a : ℂ) (n : ℕ) (theta : ℝ) : ℂ :=
  -(a ^ n / (n : ℂ)) * ((n : ℂ) * (2 * I)) *
    Complex.exp ((n : ℂ) * (2 * I * (theta : ℂ)))

/-- The conjugate negative-frequency Taylor term
`-conj(a)^n e^{-2 i n theta} / n`. -/
def negativeLogSeriesTerm (a : ℂ) (n : ℕ) (theta : ℝ) : ℂ :=
  -((starRingEnd ℂ a) ^ n / (n : ℂ)) *
    Complex.exp ((n : ℂ) * (-(2 * I * (theta : ℂ))))

/-- The termwise derivative of `negativeLogSeriesTerm`. -/
def negativeLogSeriesDerivativeTerm (a : ℂ) (n : ℕ) (theta : ℝ) : ℂ :=
  -((starRingEnd ℂ a) ^ n / (n : ℂ)) * (-(n : ℂ) * (2 * I)) *
    Complex.exp ((n : ℂ) * (-(2 * I * (theta : ℂ))))

private theorem positiveLogSeriesTerm_hasDerivAt (a : ℂ) (n : ℕ) (theta : ℝ) :
    HasDerivAt (positiveLogSeriesTerm a n)
      (positiveLogSeriesDerivativeTerm a n theta) theta := by
  have hlin : HasDerivAt
      (fun t : ℝ => (n : ℂ) * (2 * I * (t : ℂ)))
      ((n : ℂ) * (2 * I)) theta := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 theta :=
      (hasDerivAt_id theta).ofReal_comp
    convert hid.const_mul ((n : ℂ) * (2 * I)) using 1 <;> ring_nf
  have hexp := hlin.cexp
  convert hexp.const_mul (-(a ^ n / (n : ℂ))) using 1
  · simp only [positiveLogSeriesDerivativeTerm]
    ring

private theorem negativeLogSeriesTerm_hasDerivAt (a : ℂ) (n : ℕ) (theta : ℝ) :
    HasDerivAt (negativeLogSeriesTerm a n)
      (negativeLogSeriesDerivativeTerm a n theta) theta := by
  have hlin : HasDerivAt
      (fun t : ℝ => (n : ℂ) * (-(2 * I * (t : ℂ))))
      (-(n : ℂ) * (2 * I)) theta := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 theta :=
      (hasDerivAt_id theta).ofReal_comp
    convert hid.const_mul (-(n : ℂ) * (2 * I)) using 1 <;> ring_nf
  have hexp := hlin.cexp
  convert hexp.const_mul (-((starRingEnd ℂ a) ^ n / (n : ℂ))) using 1
  · simp only [negativeLogSeriesDerivativeTerm]
    ring

@[simp] private theorem norm_positiveLogPhase (n : ℕ) (theta : ℝ) :
    ‖Complex.exp ((n : ℂ) * (2 * I * (theta : ℂ)))‖ = 1 := by
  rw [norm_exp]
  simp

@[simp] private theorem norm_negativeLogPhase (n : ℕ) (theta : ℝ) :
    ‖Complex.exp ((n : ℂ) * (-(2 * I * (theta : ℂ))))‖ = 1 := by
  rw [norm_exp]
  simp

private theorem norm_positiveLogSeriesTerm_le (a : ℂ) (n : ℕ) (theta : ℝ) :
    ‖positiveLogSeriesTerm a n theta‖ ≤ ‖a‖ ^ n := by
  cases n with
  | zero => simp [positiveLogSeriesTerm]
  | succ n =>
      rw [positiveLogSeriesTerm, norm_mul, norm_neg, norm_div, norm_pow,
        norm_positiveLogPhase, mul_one]
      simp only [norm_natCast]
      apply div_le_self
      · positivity
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)

private theorem norm_negativeLogSeriesTerm_le (a : ℂ) (n : ℕ) (theta : ℝ) :
    ‖negativeLogSeriesTerm a n theta‖ ≤ ‖a‖ ^ n := by
  cases n with
  | zero => simp [negativeLogSeriesTerm]
  | succ n =>
      rw [negativeLogSeriesTerm, norm_mul, norm_neg, norm_div, norm_pow,
        norm_negativeLogPhase, mul_one, starRingEnd_apply, norm_star]
      simp only [norm_natCast]
      apply div_le_self
      · positivity
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)

private theorem norm_positiveLogSeriesDerivativeTerm_le
    (a : ℂ) (n : ℕ) (theta : ℝ) :
    ‖positiveLogSeriesDerivativeTerm a n theta‖ ≤ 2 * ‖a‖ ^ n := by
  cases n with
  | zero => simp [positiveLogSeriesDerivativeTerm]
  | succ n =>
      rw [positiveLogSeriesDerivativeTerm]
      simp only [norm_mul, norm_neg, norm_div, norm_pow, norm_natCast,
        norm_positiveLogPhase, mul_one, norm_ofNat, norm_I]
      field_simp
      exact le_rfl

private theorem norm_negativeLogSeriesDerivativeTerm_le
    (a : ℂ) (n : ℕ) (theta : ℝ) :
    ‖negativeLogSeriesDerivativeTerm a n theta‖ ≤ 2 * ‖a‖ ^ n := by
  cases n with
  | zero => simp [negativeLogSeriesDerivativeTerm]
  | succ n =>
      rw [negativeLogSeriesDerivativeTerm]
      simp only [norm_mul, norm_neg, norm_div, norm_pow, norm_natCast,
        norm_negativeLogPhase, mul_one, norm_ofNat, norm_I, starRingEnd_apply,
        norm_star]
      field_simp
      exact le_rfl

private theorem norm_two_mul_geometric_summable {a : ℂ} (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => 2 * ‖a‖ ^ n) :=
  (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_left 2

/-- The manuscript's positive-frequency logarithmic Taylor series, pointwise.
The logarithm is mathlib's principal `Complex.log`; the open unit-disk
hypothesis puts every argument in its slit-plane domain. -/
theorem positiveLogSeries_hasSum {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    HasSum (positiveLogSeriesTerm a · theta)
      (Complex.log (1 - a * Complex.exp (2 * I * (theta : ℂ)))) := by
  have hz : ‖a * Complex.exp (2 * I * (theta : ℂ))‖ < 1 := by
    rw [norm_mul]
    have he : ‖Complex.exp (2 * I * (theta : ℂ))‖ = 1 := by
      rw [norm_exp]
      simp
    rw [he, mul_one]
    exact ha
  have hs := (Complex.hasSum_taylorSeries_neg_log hz).neg
  simpa only [neg_neg] using hs.congr_fun (fun n => by
    rw [positiveLogSeriesTerm, mul_pow, ← Complex.exp_nat_mul]
    ring)

/-- The conjugate negative-frequency logarithmic Taylor series, pointwise. -/
theorem negativeLogSeries_hasSum {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    HasSum (negativeLogSeriesTerm a · theta)
      (Complex.log
        (1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ))))) := by
  have hz : ‖(starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ)))‖ < 1 := by
    rw [norm_mul, starRingEnd_apply, norm_star]
    have he : ‖Complex.exp (-(2 * I * (theta : ℂ)))‖ = 1 := by
      rw [norm_exp]
      simp
    rw [he, mul_one]
    exact ha
  have hs := (Complex.hasSum_taylorSeries_neg_log hz).neg
  simpa only [neg_neg] using hs.congr_fun (fun n => by
    rw [negativeLogSeriesTerm, mul_pow, ← Complex.exp_nat_mul]
    ring)

/-- Uniform convergence of the manuscript's logarithmic Taylor series. -/
theorem positiveLogSeries_hasSumUniformly {a : ℂ} (ha : ‖a‖ < 1) :
    HasSumUniformlyOn (positiveLogSeriesTerm a)
      (fun theta => Complex.log (1 - a * Complex.exp (2 * I * (theta : ℂ))))
      Set.univ := by
  have hu := HasSumUniformlyOn.of_norm_le_summable
    (summable_geometric_of_lt_one (norm_nonneg a) ha)
    (s := Set.univ) (fun n theta _ => norm_positiveLogSeriesTerm_le a n theta)
  exact hu.congr_right fun theta _ => (positiveLogSeries_hasSum ha theta).tsum_eq

/-- Uniform convergence of the conjugate logarithmic Taylor series. -/
theorem negativeLogSeries_hasSumUniformly {a : ℂ} (ha : ‖a‖ < 1) :
    HasSumUniformlyOn (negativeLogSeriesTerm a)
      (fun theta => Complex.log
        (1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ)))))
      Set.univ := by
  have hu := HasSumUniformlyOn.of_norm_le_summable
    (summable_geometric_of_lt_one (norm_nonneg a) ha)
    (s := Set.univ) (fun n theta _ => norm_negativeLogSeriesTerm_le a n theta)
  exact hu.congr_right fun theta _ => (negativeLogSeries_hasSum ha theta).tsum_eq

/-- Uniform convergence of the differentiated positive-frequency series. -/
theorem positiveLogDerivativeSeries_hasSumUniformly {a : ℂ} (ha : ‖a‖ < 1) :
    HasSumUniformlyOn (positiveLogSeriesDerivativeTerm a)
      (fun theta => ∑' n, positiveLogSeriesDerivativeTerm a n theta) Set.univ :=
  HasSumUniformlyOn.of_norm_le_summable (norm_two_mul_geometric_summable ha)
    (fun n theta _ => norm_positiveLogSeriesDerivativeTerm_le a n theta)

/-- Uniform convergence of the differentiated negative-frequency series. -/
theorem negativeLogDerivativeSeries_hasSumUniformly {a : ℂ} (ha : ‖a‖ < 1) :
    HasSumUniformlyOn (negativeLogSeriesDerivativeTerm a)
      (fun theta => ∑' n, negativeLogSeriesDerivativeTerm a n theta) Set.univ :=
  HasSumUniformlyOn.of_norm_le_summable (norm_two_mul_geometric_summable ha)
    (fun n theta _ => norm_negativeLogSeriesDerivativeTerm_le a n theta)

/-- Termwise differentiation of the positive-frequency logarithmic series. -/
theorem positiveLogSeries_hasDerivAt {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.log (1 - a * Complex.exp (2 * I * (t : ℂ))))
      (∑' n, positiveLogSeriesDerivativeTerm a n theta) theta := by
  apply hasDerivAt_of_tendstoUniformlyOn (l := Filter.atTop) isOpen_univ
      (positiveLogDerivativeSeries_hasSumUniformly ha).tendstoUniformlyOn
  · filter_upwards with s
    intro t _
    exact HasDerivAt.fun_sum fun n hn =>
      positiveLogSeriesTerm_hasDerivAt a n t
  · intro t _
    exact (positiveLogSeries_hasSumUniformly ha).tendstoUniformlyOn.tendsto_at
      (Set.mem_univ t)
  · exact Set.mem_univ theta

/-- Termwise differentiation of the conjugate negative-frequency series. -/
theorem negativeLogSeries_hasDerivAt {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.log
        (1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (t : ℂ)))))
      (∑' n, negativeLogSeriesDerivativeTerm a n theta) theta := by
  apply hasDerivAt_of_tendstoUniformlyOn (l := Filter.atTop) isOpen_univ
      (negativeLogDerivativeSeries_hasSumUniformly ha).tendstoUniformlyOn
  · filter_upwards with s
    intro t _
    exact HasDerivAt.fun_sum fun n hn =>
      negativeLogSeriesTerm_hasDerivAt a n t
  · intro t _
    exact (negativeLogSeries_hasSumUniformly ha).tendstoUniformlyOn.tendsto_at
      (Set.mem_univ t)
  · exact Set.mem_univ theta

/-! ## Fourier coefficients of the differentiated series -/

private theorem norm_paperFourierWeight (k : ℤ) (theta : ℝ) :
    ‖Complex.exp (-I * (k : ℂ) * (theta : ℂ))‖ = 1 := by
  rw [norm_exp]
  simp

/-- A uniformly convergent series of continuous functions may be integrated
term by term in the paper's Fourier coefficient convention.  This is the
analytic justification behind "comparison of the Fourier coefficients" in
Lemma 5.2. -/
private theorem paperFourierCoeff_tsum_of_hasSumUniformlyOn
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Continuous (f n))
    (huniform : HasSumUniformlyOn f (fun theta => ∑' n, f n theta) Set.univ)
    (k : ℤ) :
    paperFourierCoeff (fun theta => ∑' n, f n theta) k =
      ∑' n, paperFourierCoeff (f n) k := by
  let weight : ℝ → ℂ := fun theta =>
    Complex.exp (-I * (k : ℂ) * (theta : ℂ))
  have hweight : Continuous weight := by
    dsimp [weight]
    fun_prop
  let F : ℕ → C(ℝ, ℂ) := fun n =>
    ⟨fun theta => f n theta * weight theta, (hf n).mul hweight⟩
  have hfsum (theta : ℝ) : Summable (fun n => f n theta) :=
    (huniform.hasSum (Set.mem_univ theta)).summable
  have hpoint (theta : ℝ) :
      (∑' n, F n theta) = (∑' n, f n theta) * weight theta := by
    exact (hfsum theta).tsum_mul_right (weight theta)
  have hFuniform : TendstoUniformlyOn
      (fun s : Finset ℕ => fun theta => ∑ n ∈ s, F n theta)
      (fun theta => ∑' n, F n theta) Filter.atTop
      (uIcc (0 : ℝ) (2 * Real.pi)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    have hu := Metric.tendstoUniformlyOn_iff.mp huniform.tendstoUniformlyOn
      epsilon hepsilon
    filter_upwards [hu] with s hs
    intro theta htheta
    rw [hpoint]
    have hfinite : (∑ n ∈ s, F n theta) =
        (∑ n ∈ s, f n theta) * weight theta := by
      simp only [F, ContinuousMap.coe_mk, Finset.sum_mul]
    rw [hfinite]
    rw [Complex.dist_eq, ← sub_mul, norm_mul,
      norm_paperFourierWeight, mul_one]
    simpa only [Complex.dist_eq] using hs theta (Set.mem_univ theta)
  have hInt := hFuniform.tendsto_intervalIntegral_of_continuousOn
    (μ := MeasureTheory.volume)
    (Filter.Eventually.of_forall fun s =>
      (continuous_finsetSum s fun n _ => (F n).continuous).continuousOn)
  have hsint : HasSum
      (fun n => ∫ theta in (0 : ℝ)..2 * Real.pi, F n theta)
      (∫ theta in (0 : ℝ)..2 * Real.pi, ∑' n, F n theta) := by
    change Filter.Tendsto
      (fun s : Finset ℕ => ∑ n ∈ s,
        ∫ theta in (0 : ℝ)..2 * Real.pi, F n theta)
      Filter.atTop
      (nhds (∫ theta in (0 : ℝ)..2 * Real.pi, ∑' n, F n theta))
    convert hInt using 1
    funext s
    rw [intervalIntegral.integral_finsetSum]
    intro n _
    exact (F n).continuous.intervalIntegrable _ _
  have hmap := hsint.mul_left (1 / (2 * Real.pi) : ℂ)
  have hterms :
      (fun n => (1 / (2 * Real.pi) : ℂ) *
        ∫ theta in (0 : ℝ)..2 * Real.pi, F n theta) =
      (fun n => paperFourierCoeff (f n) k) := by
    funext n
    rw [paperFourierCoeff_eq_integral]
    rfl
  rw [hterms] at hmap
  have hlimit :
      (1 / (2 * Real.pi) : ℂ) *
          ∫ theta in (0 : ℝ)..2 * Real.pi, ∑' n, F n theta =
        paperFourierCoeff (fun theta => ∑' n, f n theta) k := by
    rw [paperFourierCoeff_eq_integral]
    apply congrArg ((1 / (2 * Real.pi) : ℂ) * ·)
    apply intervalIntegral.integral_congr
    intro theta _
    exact hpoint theta
  rw [hlimit] at hmap
  exact hmap.tsum_eq.symm

private theorem positiveLogPhase_eq_fourier (n : ℕ) (theta : ℝ) :
    Complex.exp ((n : ℂ) * (2 * I * (theta : ℂ))) =
      fourier (T := 2 * Real.pi) (2 * (n : ℤ))
        (theta : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

private theorem negativeLogPhase_eq_fourier (n : ℕ) (theta : ℝ) :
    Complex.exp ((n : ℂ) * (-(2 * I * (theta : ℂ)))) =
      fourier (T := 2 * Real.pi) (-(2 * (n : ℤ)))
        (theta : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

private theorem continuous_positiveLogSeriesDerivativeTerm (a : ℂ) (n : ℕ) :
    Continuous (positiveLogSeriesDerivativeTerm a n) := by
  unfold positiveLogSeriesDerivativeTerm
  fun_prop

private theorem continuous_negativeLogSeriesDerivativeTerm (a : ℂ) (n : ℕ) :
    Continuous (negativeLogSeriesDerivativeTerm a n) := by
  unfold negativeLogSeriesDerivativeTerm
  fun_prop

private theorem paperFourierCoeff_positiveDerivativeTerm_two
    (a : ℂ) (n : ℕ) :
    paperFourierCoeff (positiveLogSeriesDerivativeTerm a n) 2 =
      if n = 1 then -2 * I * a else 0 := by
  have hfun : positiveLogSeriesDerivativeTerm a n = fun theta : ℝ =>
      (-(a ^ n / (n : ℂ)) * ((n : ℂ) * (2 * I))) *
        fourier (T := 2 * Real.pi) (2 * (n : ℤ))
          (theta : AddCircle (2 * Real.pi)) := by
    funext theta
    rw [positiveLogSeriesDerivativeTerm, positiveLogPhase_eq_fourier]
  rw [hfun]
  rw [paperFourierCoeff_const_mul, paperFourierCoeff_fourier]
  by_cases hn : n = 1
  · subst n
    simp
    ring
  · simp [hn]

private theorem paperFourierCoeff_negativeDerivativeTerm_two
    (a : ℂ) (n : ℕ) :
    paperFourierCoeff (negativeLogSeriesDerivativeTerm a n) 2 = 0 := by
  have hfun : negativeLogSeriesDerivativeTerm a n = fun theta : ℝ =>
      (-((starRingEnd ℂ a) ^ n / (n : ℂ)) * (-(n : ℂ) * (2 * I))) *
        fourier (T := 2 * Real.pi) (-(2 * (n : ℤ)))
          (theta : AddCircle (2 * Real.pi)) := by
    funext theta
    rw [negativeLogSeriesDerivativeTerm, negativeLogPhase_eq_fourier]
  rw [hfun]
  rw [paperFourierCoeff_const_mul, paperFourierCoeff_fourier]
  have hindex : (-(2 * (n : ℤ)) : ℤ) ≠ 2 := by omega
  simp [hindex]

/-- The positive-frequency branch contributes exactly `-2 i a` to mode
two, obtained by integrating its uniformly convergent differentiated Taylor
series term by term. -/
theorem paperFourierCoeff_positiveLogDerivativeSeries_two
    {a : ℂ} (ha : ‖a‖ < 1) :
    paperFourierCoeff
      (fun theta => ∑' n, positiveLogSeriesDerivativeTerm a n theta) 2 =
      -2 * I * a := by
  rw [paperFourierCoeff_tsum_of_hasSumUniformlyOn
    (positiveLogSeriesDerivativeTerm a)
    (continuous_positiveLogSeriesDerivativeTerm a)
    (positiveLogDerivativeSeries_hasSumUniformly ha) 2]
  simp_rw [paperFourierCoeff_positiveDerivativeTerm_two]
  simp

/-- The conjugate negative-frequency branch has no mode-two contribution,
again computed from its differentiated Taylor series. -/
theorem paperFourierCoeff_negativeLogDerivativeSeries_two
    {a : ℂ} (ha : ‖a‖ < 1) :
    paperFourierCoeff
      (fun theta => ∑' n, negativeLogSeriesDerivativeTerm a n theta) 2 = 0 := by
  rw [paperFourierCoeff_tsum_of_hasSumUniformlyOn
    (negativeLogSeriesDerivativeTerm a)
    (continuous_negativeLogSeriesDerivativeTerm a)
    (negativeLogDerivativeSeries_hasSumUniformly ha) 2]
  simp_rw [paperFourierCoeff_negativeDerivativeTerm_two]
  simp

/-! ## The factorized expansion of `G` -/

/-- The complex-valued coercion of the manuscript's real function
`G(theta) = (2N)⁻¹ log(q(2 theta))`. -/
def manuscriptG (N : ℕ) (q : ℝ → ℝ) (theta : ℝ) : ℂ :=
  ((Real.log (q (2 * theta)) / (2 * N : ℝ) : ℝ) : ℂ)

private theorem conjugate_positive_factor (a : ℂ) (theta : ℝ) :
    starRingEnd ℂ (1 - a * Complex.exp (2 * I * (theta : ℂ))) =
      1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ))) := by
  rw [map_sub, map_one, map_mul]
  congr 2
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

private theorem one_sub_factor_ne_zero {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    1 - a * Complex.exp (2 * I * (theta : ℂ)) ≠ 0 := by
  intro h
  have heq : a * Complex.exp (2 * I * (theta : ℂ)) = 1 :=
    (sub_eq_zero.mp h).symm
  have hn := congrArg norm heq
  rw [norm_mul] at hn
  have he : ‖Complex.exp (2 * I * (theta : ℂ))‖ = 1 := by
    rw [norm_exp]
    simp
  rw [he, mul_one, norm_one] at hn
  linarith

private theorem log_normSq_factor_eq_log_add_conjLog
    {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    ((Real.log (‖1 - a * Complex.exp (2 * I * (theta : ℂ))‖ ^ 2) : ℝ) : ℂ) =
      Complex.log (1 - a * Complex.exp (2 * I * (theta : ℂ))) +
        Complex.log
          (1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ)))) := by
  let z : ℂ := 1 - a * Complex.exp (2 * I * (theta : ℂ))
  have hzslit : z ∈ Complex.slitPlane := by
    change 1 + (-(a * Complex.exp (2 * I * (theta : ℂ)))) ∈ Complex.slitPlane
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_neg, norm_mul]
    have he : ‖Complex.exp (2 * I * (theta : ℂ))‖ = 1 := by
      rw [norm_exp]
      simp
    rw [he, mul_one]
    exact ha
  have hconj :
      Complex.log
          (1 - (starRingEnd ℂ a) * Complex.exp (-(2 * I * (theta : ℂ)))) =
        starRingEnd ℂ (Complex.log z) := by
    rw [← conjugate_positive_factor a theta]
    exact Complex.log_conj z (Complex.slitPlane_arg_ne_pi hzslit)
  rw [hconj]
  change ((Real.log (‖z‖ ^ 2) : ℝ) : ℂ) =
    Complex.log z + starRingEnd ℂ (Complex.log z)
  apply Complex.ext
  · simp [Complex.log_re, Real.log_pow]
    ring
  · simp

/-- The exact finite logarithmic expansion displayed in Lemma 5.2 after the
strict Fejer--Riesz factorization. -/
theorem manuscriptG_eq_factor_log_expansion
    {q : ℝ → ℝ} {N : ℕ} (data : StrictFejerRieszData q N) (theta : ℝ) :
    manuscriptG N q theta =
      (1 / (2 * (N : ℂ))) *
        ((Real.log data.c : ℂ) +
          ∑ j,
            (Complex.log
                (1 - data.alpha j * Complex.exp (2 * I * (theta : ℂ))) +
              Complex.log
                (1 - (starRingEnd ℂ (data.alpha j)) *
                  Complex.exp (-(2 * I * (theta : ℂ)))))) := by
  have hfac_ne (j : Fin data.L) :
      ‖1 - data.alpha j * Complex.exp (2 * I * (theta : ℂ))‖ ^ 2 ≠ 0 := by
    positivity [one_sub_factor_ne_zero (data.alpha_norm_lt_one j) theta]
  have hlog :
      Real.log (q (2 * theta)) = Real.log data.c +
        ∑ j, Real.log
          (‖1 - data.alpha j * Complex.exp (2 * I * (theta : ℂ))‖ ^ 2) := by
    rw [data.factorization]
    have hphase :
        Complex.exp ((((2 * theta : ℝ) : ℂ)) * I) =
          Complex.exp (2 * I * (theta : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hphase]
    rw [Real.log_mul data.c_pos.ne' (Finset.prod_ne_zero_iff.mpr
      (fun j _ => hfac_ne j))]
    rw [Real.log_prod (fun j _ => hfac_ne j)]
  rw [manuscriptG, hlog]
  push_cast
  simp_rw [log_normSq_factor_eq_log_add_conjLog
    (data.alpha_norm_lt_one _)]
  ring

private theorem continuous_positiveLogDerivativeSeries
    {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (fun theta => ∑' n, positiveLogSeriesDerivativeTerm a n theta) := by
  rw [← continuousOn_univ]
  exact (positiveLogDerivativeSeries_hasSumUniformly ha).tendstoUniformlyOn.continuousOn
    (Filter.Frequently.of_forall fun s =>
      (continuous_finsetSum s fun n _ =>
        continuous_positiveLogSeriesDerivativeTerm a n).continuousOn)

private theorem continuous_negativeLogDerivativeSeries
    {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (fun theta => ∑' n, negativeLogSeriesDerivativeTerm a n theta) := by
  rw [← continuousOn_univ]
  exact (negativeLogDerivativeSeries_hasSumUniformly ha).tendstoUniformlyOn.continuousOn
    (Filter.Frequently.of_forall fun s =>
      (continuous_finsetSum s fun n _ =>
        continuous_negativeLogSeriesDerivativeTerm a n).continuousOn)

/-- Direct differentiation of the real function `G` from the manuscript. -/
theorem manuscriptG_hasDerivAt
    {q dq : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    (hq : ∀ phi, 0 < q phi)
    (hderiv : ∀ phi, HasDerivAt q (dq phi) phi) (theta : ℝ) :
    HasDerivAt (manuscriptG N q)
      ((dq (2 * theta) / ((N : ℝ) * q (2 * theta)) : ℝ) : ℂ) theta := by
  have htwo : HasDerivAt (fun t : ℝ => 2 * t) 2 theta := by
    simpa using (hasDerivAt_id theta).const_mul 2
  have hcomp : HasDerivAt (fun t : ℝ => q (2 * t))
      (2 * dq (2 * theta)) theta := by
    convert (hderiv (2 * theta)).scomp theta htwo using 1
  have hlog := hcomp.log (hq (2 * theta)).ne'
  have hscaled := hlog.div_const (2 * N : ℝ)
  have hcast := hscaled.ofReal_comp
  convert hcast using 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  norm_cast
  field_simp [hNr]
  push_cast
  ring

/-- Differentiating the finite factorwise logarithmic expansion by means of
the uniformly convergent Taylor series. -/
theorem manuscriptG_hasDerivAt_factor_log_series
    {q : ℝ → ℝ} {N : ℕ} (data : StrictFejerRieszData q N) (theta : ℝ) :
    HasDerivAt (manuscriptG N q)
      ((1 / (2 * (N : ℂ))) *
        ∑ j,
          ((∑' n, positiveLogSeriesDerivativeTerm (data.alpha j) n theta) +
            ∑' n, negativeLogSeriesDerivativeTerm (data.alpha j) n theta)) theta := by
  have hsum : HasDerivAt
      (fun t : ℝ =>
        ∑ j,
          (Complex.log
              (1 - data.alpha j * Complex.exp (2 * I * (t : ℂ))) +
            Complex.log
              (1 - (starRingEnd ℂ (data.alpha j)) *
                Complex.exp (-(2 * I * (t : ℂ))))))
      (∑ j,
        ((∑' n, positiveLogSeriesDerivativeTerm (data.alpha j) n theta) +
          ∑' n, negativeLogSeriesDerivativeTerm (data.alpha j) n theta)) theta := by
    apply HasDerivAt.fun_sum
    intro j _
    exact (positiveLogSeries_hasDerivAt (data.alpha_norm_lt_one j) theta).add
      (negativeLogSeries_hasDerivAt (data.alpha_norm_lt_one j) theta)
  have hrhs := ((hasDerivAt_const (x := theta) (c := (Real.log data.c : ℂ))).add hsum).const_mul
    (1 / (2 * (N : ℂ)))
  have hfun : manuscriptG N q = fun t : ℝ =>
      (1 / (2 * (N : ℂ))) *
        ((Real.log data.c : ℂ) +
          ∑ j,
            (Complex.log
                (1 - data.alpha j * Complex.exp (2 * I * (t : ℂ))) +
              Complex.log
                (1 - (starRingEnd ℂ (data.alpha j)) *
                  Complex.exp (-(2 * I * (t : ℂ)))))) := by
    funext t
    exact manuscriptG_eq_factor_log_expansion data t
  rw [hfun]
  simpa using hrhs

private theorem paperFourierCoeff_finset_sum_series {J : Type*} [Fintype J]
    (u : J → ℝ → ℂ) (hu : ∀ j, Continuous (u j)) (n : ℤ) :
    paperFourierCoeff (fun theta => ∑ j, u j theta) n =
      ∑ j, paperFourierCoeff (u j) n := by
  simp_rw [paperFourierCoeff_eq_integral, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro j _
    exact ((hu j).mul (by fun_prop)).intervalIntegrable _ _

/-- The manuscript's exact coefficient identity
`g-hat_2 = -(i/N) sum alpha`, proved through its logarithmic Taylor series. -/
theorem manuscript_logarithmic_fourier_formula
    {q dq : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    (hq : ∀ phi, 0 < q phi)
    (hderiv : ∀ phi, HasDerivAt q (dq phi) phi)
    (data : StrictFejerRieszData q N) :
    paperFourierCoeff
        (fun theta =>
          ((dq (2 * theta) / ((N : ℝ) * q (2 * theta)) : ℝ) : ℂ)) 2 =
      -(I / (N : ℂ)) * ∑ j, data.alpha j := by
  have hpoint (theta : ℝ) :
      ((dq (2 * theta) / ((N : ℝ) * q (2 * theta)) : ℝ) : ℂ) =
        (1 / (2 * (N : ℂ))) *
          ∑ j,
            ((∑' n, positiveLogSeriesDerivativeTerm (data.alpha j) n theta) +
              ∑' n, negativeLogSeriesDerivativeTerm (data.alpha j) n theta) := by
    exact (manuscriptG_hasDerivAt hN hq hderiv theta).unique
      (manuscriptG_hasDerivAt_factor_log_series data theta)
  rw [show (fun theta =>
      ((dq (2 * theta) / ((N : ℝ) * q (2 * theta)) : ℝ) : ℂ)) =
      fun theta => (1 / (2 * (N : ℂ))) *
        ∑ j,
          ((∑' n, positiveLogSeriesDerivativeTerm (data.alpha j) n theta) +
            ∑' n, negativeLogSeriesDerivativeTerm (data.alpha j) n theta) by
    funext theta
    exact hpoint theta]
  rw [paperFourierCoeff_const_mul]
  rw [paperFourierCoeff_finset_sum_series]
  · simp_rw [paperFourierCoeff_add _ _
      (continuous_positiveLogDerivativeSeries (data.alpha_norm_lt_one _))
      (continuous_negativeLogDerivativeSeries (data.alpha_norm_lt_one _)) 2]
    simp_rw [paperFourierCoeff_positiveLogDerivativeSeries_two
      (data.alpha_norm_lt_one _)]
    simp_rw [paperFourierCoeff_negativeLogDerivativeSeries_two
      (data.alpha_norm_lt_one _), add_zero]
    rw [← Finset.mul_sum]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · intro j
    exact (continuous_positiveLogDerivativeSeries (data.alpha_norm_lt_one j)).add
      (continuous_negativeLogDerivativeSeries (data.alpha_norm_lt_one j))

end

end HomogeneousObstruction
