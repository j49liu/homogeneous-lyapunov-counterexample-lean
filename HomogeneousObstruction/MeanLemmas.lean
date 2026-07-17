import HomogeneousObstruction.Basic
import Mathlib.Analysis.Complex.MeanValue

namespace HomogeneousObstruction

open Metric Set
open scoped ComplexConjugate

noncomputable section

private theorem one_sub_mul_ne_zero_on_closedBall {a z : ℂ} (ha : ‖a‖ < 1)
    (hz : z ∈ closedBall (0 : ℂ) 1) : 1 - a * z ≠ 0 := by
  intro h
  have haz : a * z = 1 := (sub_eq_zero.mp h).symm
  have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
  have hnorm := congrArg norm haz
  rw [norm_mul, norm_one] at hnorm
  nlinarith [norm_nonneg a, norm_nonneg z]

theorem diffContOnCl_div_one_sub_mul {a : ℂ} (ha : ‖a‖ < 1) :
    DiffContOnCl ℂ (fun z : ℂ => a / (1 - a * z)) (ball 0 1) := by
  have hden : DiffContOnCl ℂ (fun z : ℂ => 1 - a * z) (ball 0 1) := by
    have hd : Differentiable ℂ (fun z : ℂ => 1 - a * z) := by fun_prop
    exact hd.diffContOnCl
  have hinv : DiffContOnCl ℂ (fun z : ℂ => (1 - a * z)⁻¹) (ball 0 1) := by
    apply hden.inv
    intro z hz
    apply one_sub_mul_ne_zero_on_closedBall ha
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hz
    exact hz
  simpa [div_eq_mul_inv, smul_eq_mul] using hinv.const_smul a

/-- Mean-value computation replacing the geometric-series step in the paper. -/
theorem circleAverage_div_one_sub_mul {a : ℂ} (ha : ‖a‖ < 1) :
    Real.circleAverage (fun z : ℂ => a / (1 - a * z)) 0 1 = a := by
  have hf : DiffContOnCl ℂ (fun z : ℂ => a / (1 - a * z))
      (ball 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using diffContOnCl_div_one_sub_mul ha
  simpa using hf.circleAverage (c := (0 : ℂ)) (R := (1 : ℝ))

theorem circleAverage_mul_pow_div_one_sub_mul {a : ℂ} (ha : ‖a‖ < 1)
    {k : ℕ} (hk : 0 < k) :
    Real.circleAverage (fun z : ℂ => a * z ^ k / (1 - a * z)) 0 1 = 0 := by
  have hpow : DiffContOnCl ℂ (fun z : ℂ => z ^ k) (ball 0 1) := by
    have hd : Differentiable ℂ (fun z : ℂ => z ^ k) := by fun_prop
    exact hd.diffContOnCl
  have hprod : DiffContOnCl ℂ (fun z : ℂ => a * z ^ k / (1 - a * z))
      (ball 0 1) := by
    have := hpow.smul (diffContOnCl_div_one_sub_mul ha)
    simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hf : DiffContOnCl ℂ (fun z : ℂ => a * z ^ k / (1 - a * z))
      (ball 0 |(1 : ℝ)|) := by simpa using hprod
  simpa [zero_pow hk.ne'] using hf.circleAverage (c := (0 : ℂ)) (R := (1 : ℝ))

/-- Negative powers contribute no positive Fourier mode; inversion turns them into a holomorphic
function vanishing at the centre. -/
theorem circleAverage_mul_inv_pow_div_one_sub_mul_inv {a : ℂ} (ha : ‖a‖ < 1)
    {k : ℕ} (hk : 0 < k) :
    Real.circleAverage (fun z : ℂ => a * z⁻¹ ^ k / (1 - a * z⁻¹)) 0 1 = 0 := by
  exact (Real.circleAverage_zero_one_congr_inv
    (f := fun z : ℂ => a * z ^ k / (1 - a * z))).trans
      (circleAverage_mul_pow_div_one_sub_mul ha hk)

end

end HomogeneousObstruction
