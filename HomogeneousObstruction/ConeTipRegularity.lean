import Mathlib

/-!
# Regularity at a quadratic cone tip

This file packages the `k = 2` case of the paper's cone-tip regularity
lemma.  It is stated in terms of the two estimates used in the manuscript:
the function is `O(‖x‖²)` and its derivative, extended by zero at the tip,
is `O(‖x‖)`.  These estimates prove differentiability at the tip with zero
derivative and continuity of the extended derivative, respectively.

The result is deliberately independent of the particular angular profile of
the Lyapunov function.  Smoothness away from the tip and the two estimates can
therefore be proved directly from the explicit formula in the application.
-/

namespace HomogeneousObstruction

open Asymptotics Filter Set
open scoped Topology

noncomputable section

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The `k = 2` case of the regularity-at-a-cone-tip lemma.

Suppose `F` vanishes at the origin and is quadratically bounded there.  Away
from the origin let `D x` be its Fréchet derivative.  If `D`, extended by zero
at the origin, is continuous away from the origin and linearly bounded at the
origin, then `F` is globally `C¹`; its derivative at the origin is zero.

The hypotheses are global bounds only for convenience.  This is exactly the
form needed for a degree-two homogeneous function, where homogeneity turns
bounds on the unit sphere into the displayed global estimates.
-/
theorem coneTip_contDiff_one
    (F : E → G) (D : E → E →L[ℝ] G)
    (C₀ C₁ : ℝ)
    (hF_zero : F 0 = 0)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2)
    (hD_zero : D 0 = 0)
    (hD_bound : ∀ x, ‖D x‖ ≤ C₁ * ‖x‖)
    (hD_continuous_off_zero : ContinuousOn D ({0} : Set E)ᶜ)
    (hF_deriv_off_zero : ∀ x ≠ 0, HasFDerivAt F (D x) x) :
    ContDiff ℝ 1 F := by
  have hF_bigO : F =O[nhds (0 : E)] fun x : E ↦ ‖x‖ ^ 2 :=
    IsBigO.of_bound C₀ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hF_bound x)
  have hF_littleO : F =o[nhds (0 : E)] fun x : E ↦ x :=
    hF_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hF_deriv_zero : HasFDerivAt F (0 : E →L[ℝ] G) 0 := by
    apply HasFDerivAt.of_isLittleO
    simpa [hF_zero] using hF_littleO

  have hD_bigO : D =O[nhds (0 : E)] fun x : E ↦ ‖x‖ :=
    IsBigO.of_bound C₁ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hD_bound x)
  have hD_tendsto_zero : Tendsto D (nhds (0 : E)) (nhds 0) :=
    hD_bigO.trans_tendsto tendsto_norm_zero
  have hD_continuous_at_zero : ContinuousAt D 0 := by
    rw [ContinuousAt, hD_zero]
    exact hD_tendsto_zero
  have hD_continuous : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hD_continuous_at_zero
    · have hx' : x ∈ ({0} : Set E)ᶜ := by simpa
      exact (hD_continuous_off_zero x hx').continuousAt
        (isOpen_compl_singleton.mem_nhds hx')

  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨D, hD_continuous, ?_⟩
  intro x
  by_cases hx : x = 0
  · simpa [hx, hD_zero] using hF_deriv_zero
  · exact hF_deriv_off_zero x hx

/-- The derivative at the cone tip supplied by `coneTip_contDiff_one` is zero.

This separate statement makes the "every derivative through order one
vanishes at the origin" conclusion of the manuscript explicit for `k = 2`.
-/
theorem coneTip_fderiv_zero
    (F : E → G)
    (hF_zero : F 0 = 0)
    (C₀ : ℝ)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2) :
    fderiv ℝ F 0 = 0 := by
  have hF_bigO : F =O[nhds (0 : E)] fun x : E ↦ ‖x‖ ^ 2 :=
    IsBigO.of_bound C₀ (Filter.Eventually.of_forall fun x ↦ by
      simpa using hF_bound x)
  have hF_littleO : F =o[nhds (0 : E)] fun x : E ↦ x :=
    hF_bigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hF_deriv_zero : HasFDerivAt F (0 : E →L[ℝ] G) 0 := by
    apply HasFDerivAt.of_isLittleO
    simpa [hF_zero] using hF_littleO
  exact hF_deriv_zero.fderiv

/-- A convenient form of `coneTip_contDiff_one` when smoothness away from the
origin has already been proved from an explicit formula.

In this version Lean uses `fderiv ℝ F` as the derivative field.  Thus the
application only has to bound that derivative linearly away from zero; its
value at zero and its continuity there are supplied by the cone-tip argument.
-/
theorem coneTip_contDiff_one_of_smooth_off_zero
    (F : E → G)
    (C₀ C₁ : ℝ)
    (hF_zero : F 0 = 0)
    (hF_bound : ∀ x, ‖F x‖ ≤ C₀ * ‖x‖ ^ 2)
    (hF_smooth_off_zero : ContDiffOn ℝ ⊤ F ({0} : Set E)ᶜ)
    (hF_fderiv_bound : ∀ x ≠ 0, ‖fderiv ℝ F x‖ ≤ C₁ * ‖x‖) :
    ContDiff ℝ 1 F := by
  have hF_fderiv_zero : fderiv ℝ F 0 = 0 :=
    coneTip_fderiv_zero F hF_zero C₀ hF_bound
  apply coneTip_contDiff_one F (fderiv ℝ F) C₀ C₁ hF_zero hF_bound
  · exact hF_fderiv_zero
  · intro x
    by_cases hx : x = 0
    · simp [hx, hF_fderiv_zero]
    · exact hF_fderiv_bound x hx
  · exact hF_smooth_off_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  · intro x hx
    have hx' : x ∈ ({0} : Set E)ᶜ := by simpa
    have hdiffWithin : DifferentiableWithinAt ℝ F ({0} : Set E)ᶜ x :=
      hF_smooth_off_zero.differentiableOn (by simp) x hx'
    exact (hdiffWithin.differentiableAt
      (isOpen_compl_singleton.mem_nhds hx')).hasFDerivAt

end

end HomogeneousObstruction
