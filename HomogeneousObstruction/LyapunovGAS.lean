import HomogeneousObstruction.StabilityCertificateManuscript
import HomogeneousObstruction.LyapunovDirectMethod

/-!
# Global asymptotic stability from the explicit certificate

This file makes the textbook Lyapunov conclusion used after item (2) of the
main theorem precise.  ODE existence is deliberately isolated in the
predicate `ForwardComplete`: assuming forward completeness, the certificate
bounds and its exact Lie-derivative identity prove Lyapunov stability and
global attractivity for every forward trajectory.

The norm below is the Euclidean norm used in the manuscript.  This is stated
explicitly because the function-space norm inherited by `Point = Fin 2 → ℝ`
is the sup norm.
-/

namespace HomogeneousObstruction

open Set

noncomputable section

/-- Euclidean distance, expressed using `euclideanNorm`. -/
def euclideanDistance (z w : Point) : ℝ := euclideanNorm (z - w)

@[simp] theorem euclideanDistance_zero_right (z : Point) :
    euclideanDistance z 0 = euclideanNorm z := by
  simp [euclideanDistance]

/-- Lyapunov stability in the Euclidean norm used by the manuscript. -/
abbrev LyapunovStable (F : Point → Point) (zEquil : Point) : Prop :=
  LyapunovStableWith euclideanDistance F zEquil

/-- Global attractivity in the Euclidean norm used by the manuscript. -/
abbrev GloballyAttractive (F : Point → Point) (zEquil : Point) : Prop :=
  GloballyAttractiveWith euclideanDistance F zEquil

/-- Global asymptotic stability in the Euclidean norm used by the manuscript. -/
abbrev GloballyAsymptoticallyStable (F : Point → Point) (zEquil : Point) : Prop :=
  GloballyAsymptoticallyStableWith euclideanDistance F zEquil

@[simp] theorem fieldValue_zero : fieldValue (0 : Point) = 0 := by
  funext i
  fin_cases i <;> simp [fieldValue]

/-- The exact certificate identity, including the origin. -/
theorem functionLieDerivative_stabilityCertificate_all (z : Point) :
    functionLieDerivative stabilityCertificate z =
      -2 * radiusSquared z * stabilityCertificate z := by
  by_cases hz : z = 0
  · subst z
    simp [functionLieDerivative]
  · exact functionLieDerivative_stabilityCertificate_polar hz

theorem stabilityCertificate_nonneg (z : Point) :
    0 ≤ stabilityCertificate z := by
  exact mul_nonneg (radiusSquared_nonneg z) (le_of_lt (Real.exp_pos _))

/-- Along a forward trajectory, the certificate satisfies the scalar
differential identity displayed in the manuscript. -/
theorem stabilityCertificate_comp_hasDerivAt
    {γ : ℝ → Point} {z₀ : Point}
    (hγ : IsForwardTrajectory fieldValue γ z₀) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => stabilityCertificate (γ s))
      (-2 * radiusSquared (γ t) * stabilityCertificate (γ t)) t := by
  have hγt : HasDerivAt γ (fieldValue (γ t)) t :=
    (hγ.2 t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)
  have hH : HasFDerivAt stabilityCertificate
      (fderiv ℝ stabilityCertificate (γ t)) (γ t) :=
    (stabilityCertificate_contDiff_one_via_homogeneous_cone.differentiable
      (by norm_num) (γ t)).hasFDerivAt
  have hcomp := hH.comp_hasDerivAt t hγt
  convert hcomp using 1
  rw [← functionLieDerivative,
    functionLieDerivative_stabilityCertificate_all]

/-- The certificate is nonincreasing along every forward trajectory. -/
theorem stabilityCertificate_comp_antitoneOn
    {γ : ℝ → Point} {z₀ : Point}
    (hγ : IsForwardTrajectory fieldValue γ z₀) :
    AntitoneOn (fun t => stabilityCertificate (γ t)) (Ici 0) := by
  let h : ℝ → ℝ := fun t => stabilityCertificate (γ t)
  have hhcont : ContinuousOn h (Ici 0) :=
    stabilityCertificate_contDiff_one_via_homogeneous_cone.continuous.comp_continuousOn
      hγ.2.continuousOn
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hhcont
  · intro t ht
    have htpos : 0 < t := by simpa [interior_Ici] using ht
    exact (stabilityCertificate_comp_hasDerivAt hγ htpos).hasDerivWithinAt
  · intro t ht
    have hnonneg := stabilityCertificate_nonneg (γ t)
    have hrs := radiusSquared_nonneg (γ t)
    nlinarith

private theorem exp_five_mul_exp_neg_five :
    Real.exp 5 * Real.exp (-5) = 1 := by
  rw [← Real.exp_add]
  norm_num

/-- The explicit certificate bounds give Lyapunov stability directly. -/
theorem lyapunovStable_fieldValue : LyapunovStable fieldValue 0 := by
  apply lyapunovStableWith_of_quadratic_bounds
    euclideanDistance fieldValue 0 stabilityCertificate (b := Real.exp 5)
  · exact Real.exp_pos 5
  · intro z
    simp only [euclideanDistance_zero_right]
    exact euclideanNorm_nonneg z
  · intro z
    simp only [euclideanDistance_zero_right, euclideanNorm_sq]
    have hlower := (stabilityCertificate_bounds_via_polar z).1
    calc
      radiusSquared z =
          Real.exp 5 * (Real.exp (-5) * radiusSquared z) := by
        rw [← mul_assoc, exp_five_mul_exp_neg_five, one_mul]
      _ ≤ Real.exp 5 * stabilityCertificate z :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_pos 5).le
  · intro z
    simpa only [euclideanDistance_zero_right, euclideanNorm_sq] using
      (stabilityCertificate_bounds_via_polar z).2
  · intro z₀ γ hγ
    exact stabilityCertificate_comp_antitoneOn hγ

/-- Above a positive certificate level `η`, the scalar derivative is bounded
above by the fixed negative number `-2 exp(-5) η²`. -/
private theorem stabilityCertificate_derivative_le_level
    {z : Point} {η : ℝ} (hη : 0 ≤ η)
    (hlevel : η ≤ stabilityCertificate z) :
    -2 * radiusSquared z * stabilityCertificate z ≤
      -2 * Real.exp (-5) * η ^ 2 := by
  have ha : 0 < Real.exp (-5) := Real.exp_pos _
  have hupper := (stabilityCertificate_bounds_via_polar z).2
  have hcancel : Real.exp (-5) * Real.exp 5 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have haH_le_radius :
      Real.exp (-5) * stabilityCertificate z ≤ radiusSquared z := by
    have hmul := mul_le_mul_of_nonneg_left hupper ha.le
    calc
      Real.exp (-5) * stabilityCertificate z ≤
          Real.exp (-5) * (Real.exp 5 * radiusSquared z) := hmul
      _ = radiusSquared z := by rw [← mul_assoc, hcancel, one_mul]
  have haη_le_radius : Real.exp (-5) * η ≤ radiusSquared z :=
    le_trans (mul_le_mul_of_nonneg_left hlevel ha.le) haH_le_radius
  have hproduct : Real.exp (-5) * η ^ 2 ≤
      radiusSquared z * stabilityCertificate z := by
    calc
      Real.exp (-5) * η ^ 2 = (Real.exp (-5) * η) * η := by ring_nf
      _ ≤ radiusSquared z * stabilityCertificate z :=
        mul_le_mul haη_le_radius hlevel hη (radiusSquared_nonneg z)
  nlinarith

/-- Every positive certificate level is reached in finite forward time and,
by monotonicity, remains an upper bound thereafter. -/
private theorem stabilityCertificate_eventually_lt
    {γ : ℝ → Point} {z₀ : Point}
    (hγ : IsForwardTrajectory fieldValue γ z₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → stabilityCertificate (γ t) < η := by
  let h : ℝ → ℝ := fun t => stabilityCertificate (γ t)
  let d : ℝ := 2 * Real.exp (-5) * η ^ 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hcont : ContinuousOn h (Ici 0) :=
    stabilityCertificate_contDiff_one_via_homogeneous_cone.continuous.comp_continuousOn
      hγ.2.continuousOn
  have hanti : AntitoneOn h (Ici 0) :=
    stabilityCertificate_comp_antitoneOn hγ
  apply eventually_lt_of_antitoneOn_of_hasDerivAt_le hcont hanti
    (fun t _ ↦ stabilityCertificate_nonneg (γ t)) hd
  intro t ht hlevel
  refine ⟨-2 * radiusSquared (γ t) * stabilityCertificate (γ t), ?_, ?_⟩
  · simpa only [h] using stabilityCertificate_comp_hasDerivAt hγ ht
  · have hbound := stabilityCertificate_derivative_le_level hη.le hlevel
    simpa [d] using hbound

/-- The explicit certificate makes the origin globally attractive for every
forward trajectory. -/
theorem globallyAttractive_fieldValue : GloballyAttractive fieldValue 0 := by
  apply globallyAttractiveWith_of_lower_quadratic_of_eventually_lt
    euclideanDistance fieldValue 0 stabilityCertificate (c := Real.exp (-5))
  · exact Real.exp_pos (-5)
  · intro z
    simp only [euclideanDistance_zero_right]
    exact euclideanNorm_nonneg z
  · intro z
    simpa only [euclideanDistance_zero_right, euclideanNorm_sq] using
      (stabilityCertificate_bounds_via_polar z).1
  · intro z₀ γ hγ η hη
    exact stabilityCertificate_eventually_lt hγ hη

/-- The textbook conclusion used in the manuscript: once forward existence
for the cubic ODE is supplied, the explicit strict, radially unbounded
certificate proves global asymptotic stability of the origin. -/
theorem globallyAsymptoticallyStable_fieldValue_of_forwardComplete
    (hcomplete : ForwardComplete fieldValue) :
    GloballyAsymptoticallyStable fieldValue 0 := by
  exact ⟨fieldValue_zero, hcomplete,
    lyapunovStable_fieldValue, globallyAttractive_fieldValue⟩

end

end HomogeneousObstruction
