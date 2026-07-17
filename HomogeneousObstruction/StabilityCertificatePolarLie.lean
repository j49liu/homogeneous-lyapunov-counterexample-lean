import HomogeneousObstruction.StabilityCertificateCalculus

/-!
# Polar proof of the Lie-derivative identity

This module gives the active polar-coordinate calculation in the manuscript.
It is deliberately independent of the Cartesian proof of
`functionLieDerivative_stabilityCertificate`: an arbitrary nonzero Cartesian
point is represented as `polarPoint r θ`, the vector field is decomposed into
the radial and angular coordinate directions, and the polar formula for the
certificate is differentiated along the resulting coordinate curve.  The
last step is exactly the manuscript's logarithmic-rate cancellation.
-/

namespace HomogeneousObstruction

noncomputable section

/-- Regard a Cartesian point as a complex number. -/
def pointComplex (z : Point) : ℂ := ⟨z 0, z 1⟩

@[simp] theorem pointComplex_re (z : Point) : (pointComplex z).re = z 0 := rfl

@[simp] theorem pointComplex_im (z : Point) : (pointComplex z).im = z 1 := rfl

/-- The nonnegative radius attached to a Cartesian point. -/
def pointRadius (z : Point) : ℝ := ‖pointComplex z‖

/-- The principal polar angle attached to a Cartesian point. -/
def pointAngle (z : Point) : ℝ := (pointComplex z).arg

theorem pointComplex_ne_zero {z : Point} (hz : z ≠ 0) : pointComplex z ≠ 0 := by
  intro hc
  apply hz
  funext i
  fin_cases i
  · have := congrArg Complex.re hc
    simpa using this
  · have := congrArg Complex.im hc
    simpa using this

/-- Every Cartesian point is represented by its complex norm and argument.
The statement includes the origin because the radius then vanishes. -/
theorem point_eq_polar (z : Point) :
    z = polarPoint (pointRadius z) (pointAngle z) := by
  funext i
  fin_cases i
  · change z 0 = ‖pointComplex z‖ * Real.cos (pointComplex z).arg
    exact (Complex.norm_mul_cos_arg (pointComplex z)).symm
  · change z 1 = ‖pointComplex z‖ * Real.sin (pointComplex z).arg
    exact (Complex.norm_mul_sin_arg (pointComplex z)).symm

/-- Squaring the polar radius recovers the manuscript's `x²+y²`. -/
theorem pointRadius_sq (z : Point) : pointRadius z ^ 2 = radiusSquared z := by
  rw [pointRadius, Complex.sq_norm]
  simp only [Complex.normSq_apply, pointComplex_re, pointComplex_im, radiusSquared]
  ring_nf

theorem pointRadius_ne_zero {z : Point} (hz : z ≠ 0) : pointRadius z ≠ 0 := by
  exact norm_ne_zero_iff.mpr (pointComplex_ne_zero hz)

/-- The global quadratic bounds (2.8), transported from polar coordinates by
the norm/argument representation of an arbitrary Cartesian point. -/
theorem stabilityCertificate_bounds_via_polar (z : Point) :
    Real.exp (-5) * radiusSquared z ≤ stabilityCertificate z ∧
      stabilityCertificate z ≤ Real.exp 5 * radiusSquared z := by
  have h := stabilityCertificate_polar_bounds (pointRadius z) (pointAngle z)
  rw [← point_eq_polar z, pointRadius_sq] at h
  exact h

/-- Two-homogeneity read directly from the polar formula for `H`. -/
theorem stabilityCertificate_twoHomogeneous_via_polar :
    TwoHomogeneous stabilityCertificate := by
  intro a ha z
  let r : ℝ := pointRadius z
  let θ : ℝ := pointAngle z
  have hzpolar : z = polarPoint r θ := by
    simpa [r, θ] using point_eq_polar z
  calc
    stabilityCertificate (a • z) =
        stabilityCertificate (polarPoint (a * r) θ) := by
      congr 1
      rw [hzpolar]
      funext i
      fin_cases i <;> simp [polarPoint] <;> ring
    _ = (a * r) ^ 2 * Real.exp (-5 * Real.sin (2 * θ)) :=
      stabilityCertificate_polar _ _
    _ = a ^ 2 *
        (r ^ 2 * Real.exp (-5 * Real.sin (2 * θ))) := by ring
    _ = a ^ 2 * stabilityCertificate z := by
      rw [hzpolar, stabilityCertificate_polar]

/-- The radial velocity obtained by projecting the Cartesian field onto the
radial unit vector, i.e. the first formula in (2.3) of the manuscript. -/
private def polarRadialVelocity (r θ : ℝ) : ℝ :=
  (polarPoint r θ 0 * evalAt field₁ (polarPoint r θ) +
      polarPoint r θ 1 * evalAt field₂ (polarPoint r θ)) / r

/-- The angular velocity obtained from the oriented angular component, i.e.
the second formula in (2.3) of the manuscript. -/
private def polarAngularVelocity (r θ : ℝ) : ℝ :=
  (polarPoint r θ 0 * evalAt field₂ (polarPoint r θ) -
      polarPoint r θ 1 * evalAt field₁ (polarPoint r θ)) / r ^ 2

private theorem polarRadialVelocity_eq {r θ : ℝ} (hr : r ≠ 0) :
    polarRadialVelocity r θ = r ^ 3 * radialCoefficient θ := by
  exact radial_velocity_polar hr

private theorem polarAngularVelocity_eq {r θ : ℝ} (hr : r ≠ 0) :
    polarAngularVelocity r θ = r ^ 2 := by
  exact angular_velocity_polar hr

/-- Solving the radial/angular velocity equations for the Cartesian field
gives the coordinate-basis decomposition
`f = rdot e_r + r thetadot e_θ`. -/
private theorem fieldValue_polar_decomposition {r θ : ℝ} (hr : r ≠ 0) :
    fieldValue (polarPoint r θ) =
      polarRadialVelocity r θ • circlePoint θ +
        (r * polarAngularVelocity r θ) • circleTangent θ := by
  rw [polarRadialVelocity_eq hr, polarAngularVelocity_eq hr]
  funext i
  fin_cases i
  · change evalAt field₁ (polarPoint r θ) =
      (r ^ 3 * radialCoefficient θ) * Real.cos θ +
        (r * r ^ 2) * (-Real.sin θ)
    rw [evalAt_field₁_polarPoint, field₁_on_circle]
    ring_nf
  · change evalAt field₂ (polarPoint r θ) =
      (r ^ 3 * radialCoefficient θ) * Real.sin θ +
        (r * r ^ 2) * Real.cos θ
    rw [evalAt_field₂_polarPoint, field₂_on_circle]
    ring_nf

/-- The first-order polar-coordinate curve with prescribed radial and angular
velocities. -/
private def polarVelocityCurve (r θ rdot thetadot t : ℝ) : Point :=
  polarPoint (r + t * rdot) (θ + t * thetadot)

/-- Chain rule for the polar parametrisation along a line in `(r,θ)`-space. -/
private theorem polarVelocityCurve_hasDerivAt (r θ rdot thetadot : ℝ) :
    HasDerivAt (polarVelocityCurve r θ rdot thetadot)
      (rdot • circlePoint θ + (r * thetadot) • circleTangent θ) 0 := by
  rw [hasDerivAt_pi]
  intro i
  have hrline : HasDerivAt (fun t : ℝ => r + t * rdot) rdot 0 := by
    convert (hasDerivAt_const (x := 0) (c := r)).add
      ((hasDerivAt_id 0).mul_const rdot) using 1
    all_goals simp
  have htline : HasDerivAt (fun t : ℝ => θ + t * thetadot) thetadot 0 := by
    convert (hasDerivAt_const (x := 0) (c := θ)).add
      ((hasDerivAt_id 0).mul_const thetadot) using 1
    all_goals simp
  fin_cases i
  · have hcos : HasDerivAt (fun t : ℝ => Real.cos (θ + t * thetadot))
        (-Real.sin θ * thetadot) 0 := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_cos (θ + 0 * thetadot)).comp 0 htline
    convert hrline.mul hcos using 1
    simp [circlePoint, circleTangent]
    ring_nf
  · have hsin : HasDerivAt (fun t : ℝ => Real.sin (θ + t * thetadot))
        (Real.cos θ * thetadot) 0 := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (θ + 0 * thetadot)).comp 0 htline
    convert hrline.mul hsin using 1
    simp [circlePoint, circleTangent]
    ring_nf

/-- Differentiating `H(r,θ) = r² exp (-5 sin (2θ))` along a polar coordinate
line gives `H (2 rdot/r - 10 cos(2θ) thetadot)`.  This is the polar chain-rule
line displayed in the proof of item (2). -/
private theorem stabilityCertificate_polarVelocityCurve_hasDerivAt
    {r θ rdot thetadot : ℝ} (hr : r ≠ 0) :
    HasDerivAt
      (fun t => stabilityCertificate (polarVelocityCurve r θ rdot thetadot t))
      (stabilityCertificate (polarPoint r θ) *
        (2 * rdot / r - 10 * Real.cos (2 * θ) * thetadot)) 0 := by
  have hrline : HasDerivAt (fun t : ℝ => r + t * rdot) rdot 0 := by
    convert (hasDerivAt_const (x := 0) (c := r)).add
      ((hasDerivAt_id 0).mul_const rdot) using 1
    all_goals simp
  have htline : HasDerivAt (fun t : ℝ => θ + t * thetadot) thetadot 0 := by
    convert (hasDerivAt_const (x := 0) (c := θ)).add
      ((hasDerivAt_id 0).mul_const thetadot) using 1
    all_goals simp
  have htwo : HasDerivAt (fun t : ℝ => 2 * (θ + t * thetadot))
      (2 * thetadot) 0 := htline.const_mul 2
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * (θ + t * thetadot)))
      (Real.cos (2 * θ) * (2 * thetadot)) 0 :=
    by simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (2 * (θ + 0 * thetadot))).comp 0 htwo
  have hang : HasDerivAt (fun t : ℝ => -5 * Real.sin (2 * (θ + t * thetadot)))
      (-5 * (Real.cos (2 * θ) * (2 * thetadot))) 0 := hsin.const_mul (-5)
  have hexp := hang.exp
  have hsq := hrline.pow 2
  have hproduct := hsq.mul hexp
  have hraw : HasDerivAt
      (fun t => (r + t * rdot) ^ 2 *
        Real.exp (-5 * Real.sin (2 * (θ + t * thetadot))))
      (2 * r * rdot * Real.exp (-5 * Real.sin (2 * θ)) +
        r ^ 2 * (Real.exp (-5 * Real.sin (2 * θ)) *
          (-10 * Real.cos (2 * θ) * thetadot))) 0 := by
    convert hproduct using 1
    norm_num [Pi.pow_apply]
    left
    ring_nf
  rw [show (fun t => stabilityCertificate (polarVelocityCurve r θ rdot thetadot t)) =
      (fun t => (r + t * rdot) ^ 2 *
        Real.exp (-5 * Real.sin (2 * (θ + t * thetadot)))) by
    funext t
    exact stabilityCertificate_polar _ _]
  convert hraw using 1
  field_simp [hr]
  rw [stabilityCertificate_polar]
  ring_nf

/-- Manuscript-faithful polar proof of the exact Lie-derivative identity.

Unlike `functionLieDerivative_stabilityCertificate`, this proof performs no
Cartesian differentiation/algebra for the identity.  It represents `z` by
`(r,θ)`, differentiates the active polar coordinate curve whose tangent is
the vector field, and closes with
`stabilityCertificate_logarithmic_rate_from_field`.
-/
theorem functionLieDerivative_stabilityCertificate_polar {z : Point} (hz : z ≠ 0) :
    functionLieDerivative stabilityCertificate z =
      -2 * radiusSquared z * stabilityCertificate z := by
  let r : ℝ := pointRadius z
  let θ : ℝ := pointAngle z
  have hr : r ≠ 0 := by simpa [r] using pointRadius_ne_zero hz
  have hzpolar : polarPoint r θ = z := by
    simpa [r, θ] using (point_eq_polar z).symm
  let rdot : ℝ := polarRadialVelocity r θ
  let thetadot : ℝ := polarAngularVelocity r θ
  let γ : ℝ → Point := polarVelocityCurve r θ rdot thetadot
  have hfield : fieldValue z =
      rdot • circlePoint θ + (r * thetadot) • circleTangent θ := by
    rw [← hzpolar]
    simpa [rdot, thetadot] using fieldValue_polar_decomposition hr
  have hγzero : γ 0 = z := by
    rw [← hzpolar]
    simp [γ, polarVelocityCurve]
  have hγ : HasDerivAt γ (fieldValue z) 0 := by
    rw [hfield]
    exact polarVelocityCurve_hasDerivAt r θ rdot thetadot
  have hchain : HasDerivAt (stabilityCertificate ∘ γ)
      (fderiv ℝ stabilityCertificate z (fieldValue z)) 0 := by
    have hdiff : DifferentiableAt ℝ stabilityCertificate z :=
      (stabilityCertificate_contDiffAt hz).differentiableAt (by simp)
    have hdiffγ : DifferentiableAt ℝ stabilityCertificate (γ 0) := by
      simpa [hγzero] using hdiff
    have := hdiffγ.hasFDerivAt.comp_hasDerivAt 0 hγ
    simpa [hγzero] using this
  have hpolar : HasDerivAt (stabilityCertificate ∘ γ)
      (stabilityCertificate z *
        (2 * rdot / r - 10 * Real.cos (2 * θ) * thetadot)) 0 := by
    have h := stabilityCertificate_polarVelocityCurve_hasDerivAt
      (r := r) (θ := θ) (rdot := rdot) (thetadot := thetadot) hr
    simpa [γ, Function.comp_def, hzpolar] using h
  have hderiv := hchain.unique hpolar
  have hlog :
      2 * rdot / r - 10 * Real.cos (2 * θ) * thetadot = -2 * r ^ 2 := by
    simpa [rdot, thetadot, polarRadialVelocity, polarAngularVelocity] using
      stabilityCertificate_logarithmic_rate_from_field (r := r) (θ := θ) hr
  rw [functionLieDerivative, hderiv, hlog]
  rw [← hzpolar, radiusSquared_polarPoint]
  ring_nf

end

end HomogeneousObstruction
