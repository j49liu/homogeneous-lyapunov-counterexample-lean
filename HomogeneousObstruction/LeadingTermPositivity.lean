import HomogeneousObstruction.Degree

namespace HomogeneousObstruction

open MvPolynomial

noncomputable section

/-!
# Positivity of the first nonzero homogeneous Taylor term

This file formalizes the integrating-factor step in the proof of main theorem
item (4).  A nonzero, nonnegative homogeneous polynomial of positive degree
whose Lie derivative is nonpositive cannot vanish away from the origin.
-/

/-- Every nonzero point of `ℝ²` is a nonzero real multiple of a point in the
standard trigonometric parametrization of the unit circle. -/
theorem exists_ne_zero_smul_circlePoint {z : Point} (hz : z ≠ 0) :
    ∃ a theta : ℝ, a ≠ 0 ∧ z = a • circlePoint theta := by
  by_cases hx : z 0 = 0
  · have hy : z 1 ≠ 0 := by
      intro hy
      apply hz
      funext i
      fin_cases i <;> simp [hx, hy]
    refine ⟨z 1, Real.pi / 2, hy, ?_⟩
    funext i
    fin_cases i
    · simp [circlePoint, hx]
    · simp [circlePoint]
  · let theta : ℝ := Real.arctan (z 1 / z 0)
    have hcos : Real.cos theta ≠ 0 := by
      exact (Real.cos_arctan_pos (z 1 / z 0)).ne'
    refine ⟨z 0 / Real.cos theta, theta, div_ne_zero hx hcos, ?_⟩
    funext i
    fin_cases i
    · simp [circlePoint, hcos]
    · simp only [Pi.smul_apply, smul_eq_mul]
      change z 1 = (z 0 / Real.cos theta) * Real.sin theta
      rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.tan_eq_sin_div_cos]
      dsimp [theta]
      rw [Real.tan_arctan]
      field_simp [hx]

/-- A positive-degree homogeneous polynomial which vanishes on the unit circle
is the zero polynomial. -/
theorem homogeneous_eq_zero_of_circleTrace_eq_zero
    {P : BivariatePolynomial} {m : ℕ} (hhom : P.IsHomogeneous m)
    (hm : 0 < m) (htrace : ∀ theta : ℝ, circleTrace P theta = 0) :
    P = 0 := by
  apply MvPolynomial.funext
  intro z
  by_cases hz : z = 0
  · subst z
    have hscale := evalAt_smul_of_isHomogeneous hhom 0 (circlePoint 0)
    simp [hm.ne'] at hscale
    simpa [evalAt] using hscale
  · obtain ⟨a, theta, _ha, rfl⟩ := exists_ne_zero_smul_circlePoint hz
    change evalAt P (a • circlePoint theta) = evalAt 0 (a • circlePoint theta)
    rw [evalAt_smul_of_isHomogeneous hhom,
      show evalAt P (circlePoint theta) = 0 by exact htrace theta, mul_zero]
    simp [evalAt]

/-- An explicit antiderivative of
`m * (-1 + 5 cos (2 theta))`, used to evaluate the integral in the
manuscript's integrating factor. -/
def leadingIntegratingExponent (m : ℕ) (theta : ℝ) : ℝ :=
  (m : ℝ) * (-theta + (5 / 2 : ℝ) * Real.sin (2 * theta))

/-- The manuscript's basepoint-normalized integrating-factor transform.  The
exponent is the displayed integral from `theta0` to `theta`, evaluated with
the explicit antiderivative above. -/
def leadingIntegratingTransform
    (m : ℕ) (p : ℝ → ℝ) (theta0 theta : ℝ) : ℝ :=
  Real.exp
      (leadingIntegratingExponent m theta - leadingIntegratingExponent m theta0) *
    p theta

theorem leadingIntegratingExponent_hasDerivAt (m : ℕ) (theta : ℝ) :
    HasDerivAt (leadingIntegratingExponent m)
      ((m : ℝ) * radialCoefficient theta) theta := by
  have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 theta := by
    simpa using (hasDerivAt_id theta).const_mul 2
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
      (2 * Real.cos (2 * theta)) theta := by
    convert (Real.hasDerivAt_sin (2 * theta)).comp theta hinner using 1
    ring
  have hsum : HasDerivAt
      (fun x : ℝ => -x + (5 / 2 : ℝ) * Real.sin (2 * x))
      (-1 + (5 / 2 : ℝ) * (2 * Real.cos (2 * theta))) theta :=
    (hasDerivAt_id theta).neg.add (hsin.const_mul (5 / 2 : ℝ))
  convert hsum.const_mul (m : ℝ) using 1
  rw [radialCoefficient]
  ring

/-- Evaluation of the integral appearing literally in the manuscript's
integrating factor. -/
theorem integral_radialCoefficient_eq_exponent_sub
    (m : ℕ) (theta0 theta : ℝ) :
    (∫ s in theta0..theta, (m : ℝ) * radialCoefficient s) =
      leadingIntegratingExponent m theta - leadingIntegratingExponent m theta0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s _
    exact leadingIntegratingExponent_hasDerivAt m s
  · have hcont : Continuous (fun s : ℝ ↦ (m : ℝ) * radialCoefficient s) := by
      unfold radialCoefficient
      fun_prop
    exact hcont.intervalIntegrable _ _

/-- Product-rule calculation behind the manuscript's integrating-factor
argument. -/
theorem leadingIntegratingTransform_hasDerivAt
    (m : ℕ) (P : BivariatePolynomial) (theta0 theta : ℝ) :
    HasDerivAt (leadingIntegratingTransform m (circleTrace P) theta0)
      (Real.exp
          (leadingIntegratingExponent m theta - leadingIntegratingExponent m theta0) *
        (circleTraceDerivative P theta +
          (m : ℝ) * radialCoefficient theta * circleTrace P theta)) theta := by
  have hexp :=
    ((leadingIntegratingExponent_hasDerivAt m theta).sub_const
      (leadingIntegratingExponent m theta0)).exp
  have hp := circleTrace_hasDerivAt P theta
  convert hexp.mul hp using 1
  · ring

/-- The manuscript's integrating-factor zero-propagation argument.  If a
nonnegative periodic circle trace satisfies the angular differential
inequality and has one zero, it vanishes identically. -/
theorem circleTrace_eq_zero_of_angular_inequality_of_exists_zero
    (P : BivariatePolynomial) (m : ℕ)
    (hnonneg : ∀ theta : ℝ, 0 ≤ circleTrace P theta)
    (hangular : ∀ theta : ℝ,
      circleTraceDerivative P theta +
        (m : ℝ) * radialCoefficient theta * circleTrace P theta ≤ 0)
    {theta0 : ℝ} (hzero : circleTrace P theta0 = 0) :
    ∀ theta : ℝ, circleTrace P theta = 0 := by
  let F := leadingIntegratingTransform m (circleTrace P) theta0
  have hFderiv (theta : ℝ) : HasDerivAt F
      (Real.exp
          (leadingIntegratingExponent m theta - leadingIntegratingExponent m theta0) *
        (circleTraceDerivative P theta +
          (m : ℝ) * radialCoefficient theta * circleTrace P theta)) theta :=
    leadingIntegratingTransform_hasDerivAt m P theta0 theta
  have hFderiv_nonpos (theta : ℝ) :
      Real.exp
          (leadingIntegratingExponent m theta - leadingIntegratingExponent m theta0) *
        (circleTraceDerivative P theta +
          (m : ℝ) * radialCoefficient theta * circleTrace P theta) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hangular theta)
  have hanti : Antitone F :=
    antitone_of_hasDerivAt_nonpos hFderiv hFderiv_nonpos
  have hFzero : F theta0 = 0 := by simp [F, leadingIntegratingTransform, hzero]
  intro theta
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((theta0 - theta) / (2 * Real.pi))
  have hshift : theta0 ≤ theta + (n : ℝ) * (2 * Real.pi) := by
    have hn' := (div_lt_iff₀ Real.two_pi_pos).mp hn
    linarith
  have hF_nonneg : 0 ≤ F (theta + (n : ℝ) * (2 * Real.pi)) := by
    exact mul_nonneg (Real.exp_pos _).le (hnonneg _)
  have hF_nonpos : F (theta + (n : ℝ) * (2 * Real.pi)) ≤ 0 := by
    simpa [hFzero] using hanti hshift
  have hF_shift : F (theta + (n : ℝ) * (2 * Real.pi)) = 0 :=
    le_antisymm hF_nonpos hF_nonneg
  have hp_shift : circleTrace P (theta + (n : ℝ) * (2 * Real.pi)) = 0 := by
    have hexp : Real.exp
        (leadingIntegratingExponent m (theta + (n : ℝ) * (2 * Real.pi)) -
          leadingIntegratingExponent m theta0) ≠ 0 :=
      (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp (show
      Real.exp
          (leadingIntegratingExponent m (theta + (n : ℝ) * (2 * Real.pi)) -
            leadingIntegratingExponent m theta0) *
        circleTrace P (theta + (n : ℝ) * (2 * Real.pi)) = 0 by
          simpa [F, leadingIntegratingTransform] using hF_shift)).resolve_left hexp
  have hperiod := (circleTrace_periodic P).nat_mul n theta
  simpa only [Nat.cast_ofNat] using hperiod.symm.trans hp_shift

/-- The leading-term positivity statement used in item (4): the first nonzero
homogeneous Taylor term is positive definite once ray positivity and the
leading Lie inequality have been extracted from the analytic hypotheses. -/
theorem positiveDefinite_of_nonnegative_of_lieNonpositive
    {P : BivariatePolynomial} {m : ℕ}
    (hhom : P.IsHomogeneous m) (hm : 0 < m) (hP_ne : P ≠ 0)
    (hnonneg : ∀ z : Point, 0 ≤ evalAt P z)
    (hlie : LieNonpositive P) :
    PositiveDefinite P := by
  have hangular (theta : ℝ) :
      circleTraceDerivative P theta +
        (m : ℝ) * radialCoefficient theta * circleTrace P theta ≤ 0 := by
    simpa [lieDerivative_on_circle hhom theta] using hlie (circlePoint theta)
  have htrace_nonneg (theta : ℝ) : 0 ≤ circleTrace P theta :=
    hnonneg (circlePoint theta)
  have htrace_pos (theta : ℝ) : 0 < circleTrace P theta := by
    apply lt_of_le_of_ne (htrace_nonneg theta)
    intro hnot
    have hzero : circleTrace P theta = 0 := hnot.symm
    apply hP_ne
    exact homogeneous_eq_zero_of_circleTrace_eq_zero hhom hm
      (circleTrace_eq_zero_of_angular_inequality_of_exists_zero P m
        htrace_nonneg hangular hzero)
  constructor
  · have hscale := evalAt_smul_of_isHomogeneous hhom 0 (circlePoint 0)
    simpa [hm.ne'] using hscale
  · intro z hz
    obtain ⟨a, theta, ha, rfl⟩ := exists_ne_zero_smul_circlePoint hz
    rw [evalAt_smul_of_isHomogeneous hhom]
    have hne : a ^ m * circleTrace P theta ≠ 0 :=
      mul_ne_zero (pow_ne_zero m ha) (htrace_pos theta).ne'
    have hnonneg' := hnonneg (a • circlePoint theta)
    rw [evalAt_smul_of_isHomogeneous hhom] at hnonneg'
    exact lt_of_le_of_ne hnonneg' (Ne.symm hne)

end

end HomogeneousObstruction
