import HomogeneousObstruction.HomogeneousConeApplication
import HomogeneousObstruction.StabilityCertificatePolarLie

/-!
# Manuscript proof of main theorem item (2)

This module assembles the public theorem from the proof route used in the
manuscript.  The order and regularity properties are obtained from the polar
bounds and the homogeneous unit-circle cone argument.  The Lie identity uses
the active polar chain rule and polar dynamics.
-/

namespace HomogeneousObstruction

open Filter Set

noncomputable section

/-- Positive definiteness deduced from the manuscript's polar lower bound. -/
theorem stabilityCertificate_positiveDefinite_via_polar :
    FunctionPositiveDefinite stabilityCertificate := by
  refine ⟨stabilityCertificate_zero, ?_⟩
  intro z hz
  have hlower := (stabilityCertificate_bounds_via_polar z).1
  exact lt_of_lt_of_le
    (mul_pos (Real.exp_pos _) (radiusSquared_pos hz)) hlower

/-- Radial unboundedness deduced from the manuscript's polar lower bound. -/
theorem stabilityCertificate_radiallyUnbounded_via_polar :
    RadiallyUnbounded stabilityCertificate := by
  have hlower :
      Tendsto (fun z : Point ↦ Real.exp (-5) * radiusSquared z)
        (cocompact Point) atTop :=
    radiusSquared_tendsto_atTop.const_mul_atTop (Real.exp_pos _)
  exact Filter.tendsto_atTop_mono' _
    (Filter.Eventually.of_forall fun z ↦
      (stabilityCertificate_bounds_via_polar z).1) hlower

/-- Strict negativity obtained from the polar Lie identity and polar
positivity, with no appeal to the auxiliary Cartesian Lie calculation. -/
theorem functionLieDerivative_stabilityCertificate_neg_via_polar
    {z : Point} (hz : z ≠ 0) :
    functionLieDerivative stabilityCertificate z < 0 := by
  rw [functionLieDerivative_stabilityCertificate_polar hz]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (radiusSquared_pos hz))
    (stabilityCertificate_positiveDefinite_via_polar.2 z hz)

/-- Main theorem item (2), following the manuscript proof path.

Positive definiteness and radial unboundedness use (2.8), homogeneity uses the
polar formula, global `C¹` regularity uses the homogeneous unit-circle
specialization of the cone-tip lemma, and the final identity uses the active
polar chain rule and polar dynamics. -/
theorem mainTheorem_item2 :
    FunctionPositiveDefinite stabilityCertificate ∧
    RadiallyUnbounded stabilityCertificate ∧
    TwoHomogeneous stabilityCertificate ∧
    ContDiff ℝ 1 stabilityCertificate ∧
    ContDiffOn ℝ ⊤ stabilityCertificate ({0} : Set Point)ᶜ ∧
    ∀ z : Point, z ≠ 0 →
      functionLieDerivative stabilityCertificate z =
          -2 * radiusSquared z * stabilityCertificate z ∧
        functionLieDerivative stabilityCertificate z < 0 := by
  refine ⟨stabilityCertificate_positiveDefinite_via_polar,
    stabilityCertificate_radiallyUnbounded_via_polar,
    stabilityCertificate_twoHomogeneous_via_polar,
    stabilityCertificate_contDiff_one_via_homogeneous_cone,
    stabilityCertificate_contDiffOn_compl_zero, ?_⟩
  intro z hz
  exact ⟨functionLieDerivative_stabilityCertificate_polar hz,
    functionLieDerivative_stabilityCertificate_neg_via_polar hz⟩

end

end HomogeneousObstruction
