import HomogeneousObstruction.Basic

namespace HomogeneousObstruction

open Filter

noncomputable section

/-!
# The explicit Lyapunov certificate

This file begins the formalization of item (2) of the main theorem in the
paper.  It records the algebraic, order, and growth properties of

`H(x,y) = (x^2+y^2) exp (-10xy/(x^2+y^2))`.

The formula is used at every point.  Lean's convention `0⁻¹ = 0` makes its
value at the origin equal to zero, exactly as required by the separate origin
clause in the paper.
-/

/-- The square of the Euclidean radius in Cartesian coordinates. -/
def radiusSquared (z : Point) : ℝ := z 0 ^ 2 + z 1 ^ 2

/-- Positive definiteness for a real-valued function, including its value at
the origin. -/
def FunctionPositiveDefinite (V : Point → ℝ) : Prop :=
  V 0 = 0 ∧ ∀ z : Point, z ≠ 0 → 0 < V z

/-- The paper's condition `V(z) → ∞` as `‖z‖ → ∞`.  Since `Point` is a
finite-dimensional real normed space, its cocompact filter is precisely the
filter of points escaping every norm-bounded set. -/
def RadiallyUnbounded (V : Point → ℝ) : Prop :=
  Tendsto V (cocompact Point) atTop

/-- Homogeneity of degree two, with the paper's convention that the scaling
factor is positive. -/
def TwoHomogeneous (V : Point → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ z : Point, V (a • z) = a ^ 2 * V z

/-- The explicit certificate `H` from item (2) of the main theorem.  The same
expression also gives the stipulated value `H(0,0)=0`, because division by
zero is zero in Lean and the leading factor is `radiusSquared 0 = 0`. -/
def stabilityCertificate (z : Point) : ℝ :=
  radiusSquared z * Real.exp (-10 * z 0 * z 1 / radiusSquared z)

/-- Cartesian point with polar data `(r, θ)`.  Negative radii are allowed in
this algebraic parametrisation; the manuscript only uses `r > 0`. -/
def polarPoint (r θ : ℝ) : Point := r • circlePoint θ

@[simp] theorem polarPoint_zero (r θ : ℝ) : polarPoint r θ 0 = r * Real.cos θ := by
  simp [polarPoint]

@[simp] theorem polarPoint_one (r θ : ℝ) : polarPoint r θ 1 = r * Real.sin θ := by
  simp [polarPoint]

/-- The Cartesian squared radius agrees with `r²` in polar coordinates. -/
@[simp] theorem radiusSquared_polarPoint (r θ : ℝ) :
    radiusSquared (polarPoint r θ) = r ^ 2 := by
  simp only [radiusSquared, polarPoint_zero, polarPoint_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Equation (2.7) of the manuscript: the explicit Cartesian formula for
`H` has angular profile `exp (-5 sin (2θ))`. -/
theorem stabilityCertificate_polar (r θ : ℝ) :
    stabilityCertificate (polarPoint r θ) =
      r ^ 2 * Real.exp (-5 * Real.sin (2 * θ)) := by
  by_cases hr : r = 0
  · subst r
    simp [polarPoint, stabilityCertificate, radiusSquared]
  · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have hxy : polarPoint r θ 0 * polarPoint r θ 1 =
        r ^ 2 * (Real.cos θ * Real.sin θ) := by
      simp only [polarPoint_zero, polarPoint_one]
      ring
    have hexponent :
        -10 * polarPoint r θ 0 * polarPoint r θ 1 /
            r ^ 2 =
          -5 * Real.sin (2 * θ) := by
      calc
        -10 * polarPoint r θ 0 * polarPoint r θ 1 / r ^ 2 =
            -10 * (polarPoint r θ 0 * polarPoint r θ 1) / r ^ 2 := by ring
        _ = -10 * (r ^ 2 * (Real.cos θ * Real.sin θ)) / r ^ 2 := by rw [hxy]
        _ = -5 * Real.sin (2 * θ) := by
          rw [Real.sin_two_mul]
          field_simp
          ring
    simp only [stabilityCertificate, radiusSquared_polarPoint]
    rw [hexponent]

/-- Equation (2.8), proved from the polar angular profile exactly as displayed
in the manuscript. -/
theorem stabilityCertificate_polar_bounds (r θ : ℝ) :
    Real.exp (-5) * r ^ 2 ≤ stabilityCertificate (polarPoint r θ) ∧
      stabilityCertificate (polarPoint r θ) ≤ Real.exp 5 * r ^ 2 := by
  rw [stabilityCertificate_polar]
  have hlower : -5 ≤ -5 * Real.sin (2 * θ) := by
    nlinarith [Real.sin_le_one (2 * θ)]
  have hupper : -5 * Real.sin (2 * θ) ≤ 5 := by
    nlinarith [Real.neg_one_le_sin (2 * θ)]
  constructor
  · have hexp := Real.exp_le_exp.mpr hlower
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hexp (sq_nonneg r)
  · have hexp := Real.exp_le_exp.mpr hupper
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hexp (sq_nonneg r)

/-- Cubic scaling of the first field component along a polar ray. -/
theorem evalAt_field₁_polarPoint (r θ : ℝ) :
    evalAt field₁ (polarPoint r θ) =
      r ^ 3 * evalAt field₁ (circlePoint θ) := by
  rw [evalAt_field₁, evalAt_field₁]
  simp only [polarPoint_zero, polarPoint_one, circlePoint_zero, circlePoint_one]
  ring

/-- Cubic scaling of the second field component along a polar ray. -/
theorem evalAt_field₂_polarPoint (r θ : ℝ) :
    evalAt field₂ (polarPoint r θ) =
      r ^ 3 * evalAt field₂ (circlePoint θ) := by
  rw [evalAt_field₂, evalAt_field₂]
  simp only [polarPoint_zero, polarPoint_one, circlePoint_zero, circlePoint_one]
  ring

/-- Equation (2.4) of the manuscript in polar coordinates. -/
theorem radial_field_polar (r θ : ℝ) :
    polarPoint r θ 0 * evalAt field₁ (polarPoint r θ) +
        polarPoint r θ 1 * evalAt field₂ (polarPoint r θ) =
      r ^ 4 * radialCoefficient θ := by
  rw [evalAt_field₁_polarPoint, evalAt_field₂_polarPoint]
  simp only [polarPoint_zero, polarPoint_one]
  calc
    r * Real.cos θ * (r ^ 3 * evalAt field₁ (circlePoint θ)) +
        r * Real.sin θ * (r ^ 3 * evalAt field₂ (circlePoint θ)) =
      r ^ 4 * (Real.cos θ * evalAt field₁ (circlePoint θ) +
        Real.sin θ * evalAt field₂ (circlePoint θ)) := by ring
    _ = r ^ 4 * radialCoefficient θ := by rw [radial_field_on_circle]

/-- Equation (2.5) of the manuscript in polar coordinates. -/
theorem angular_field_polar (r θ : ℝ) :
    polarPoint r θ 0 * evalAt field₂ (polarPoint r θ) -
        polarPoint r θ 1 * evalAt field₁ (polarPoint r θ) =
      r ^ 4 := by
  rw [evalAt_field₁_polarPoint, evalAt_field₂_polarPoint]
  simp only [polarPoint_zero, polarPoint_one]
  calc
    r * Real.cos θ * (r ^ 3 * evalAt field₂ (circlePoint θ)) -
        r * Real.sin θ * (r ^ 3 * evalAt field₁ (circlePoint θ)) =
      r ^ 4 * (Real.cos θ * evalAt field₂ (circlePoint θ) -
        Real.sin θ * evalAt field₁ (circlePoint θ)) := by ring
    _ = r ^ 4 := by rw [angular_field_on_circle, mul_one]

/-- The radial equation `ṙ = r³(-1+5 cos(2θ))` in (2.6). -/
theorem radial_velocity_polar {r θ : ℝ} (hr : r ≠ 0) :
    (polarPoint r θ 0 * evalAt field₁ (polarPoint r θ) +
        polarPoint r θ 1 * evalAt field₂ (polarPoint r θ)) / r =
      r ^ 3 * radialCoefficient θ := by
  rw [radial_field_polar]
  field_simp

/-- The angular equation `θ̇ = r²` in (2.6). -/
theorem angular_velocity_polar {r θ : ℝ} (hr : r ≠ 0) :
    (polarPoint r θ 0 * evalAt field₂ (polarPoint r θ) -
        polarPoint r θ 1 * evalAt field₁ (polarPoint r θ)) / r ^ 2 =
      r ^ 2 := by
  rw [angular_field_polar]
  field_simp

/-- The three-line logarithmic-rate cancellation displayed after (2.8):
substituting the polar system into `2 ṙ/r - 10 cos(2θ) θ̇` gives `-2r²`. -/
theorem stabilityCertificate_logarithmic_rate {r θ : ℝ} (hr : r ≠ 0) :
    2 * (r ^ 3 * radialCoefficient θ) / r -
        10 * Real.cos (2 * θ) * r ^ 2 =
      -2 * r ^ 2 := by
  simp only [radialCoefficient]
  field_simp
  ring

/-- The same logarithmic-rate calculation with the Cartesian field inserted
through the two general polar-velocity formulas (2.3). -/
theorem stabilityCertificate_logarithmic_rate_from_field {r θ : ℝ} (hr : r ≠ 0) :
    2 *
        ((polarPoint r θ 0 * evalAt field₁ (polarPoint r θ) +
            polarPoint r θ 1 * evalAt field₂ (polarPoint r θ)) / r) / r -
      10 * Real.cos (2 * θ) *
        ((polarPoint r θ 0 * evalAt field₂ (polarPoint r θ) -
            polarPoint r θ 1 * evalAt field₁ (polarPoint r θ)) / r ^ 2) =
      -2 * r ^ 2 := by
  rw [radial_velocity_polar hr, angular_velocity_polar hr]
  exact stabilityCertificate_logarithmic_rate hr

theorem radiusSquared_nonneg (z : Point) : 0 ≤ radiusSquared z := by
  simp only [radiusSquared]
  positivity

@[simp] theorem radiusSquared_eq_zero_iff (z : Point) : radiusSquared z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hx : z 0 = 0 := by
      simp only [radiusSquared] at h
      nlinarith [sq_nonneg (z 1)]
    have hy : z 1 = 0 := by
      simp only [radiusSquared] at h
      nlinarith [sq_nonneg (z 0)]
    funext i
    fin_cases i <;> simp [hx, hy]
  · rintro rfl
    simp [radiusSquared]

theorem radiusSquared_pos {z : Point} (hz : z ≠ 0) : 0 < radiusSquared z := by
  exact lt_of_le_of_ne (radiusSquared_nonneg z) (Ne.symm (mt (radiusSquared_eq_zero_iff z).mp hz))

/-- The Euclidean norm used throughout the manuscript.  `Point` is
implemented as a finite function type, whose inherited mathlib norm is the
sup norm, so the manuscript's `sqrt (x²+y²)` is named explicitly. -/
def euclideanNorm (z : Point) : ℝ :=
  Real.sqrt (radiusSquared z)

@[simp] theorem euclideanNorm_zero : euclideanNorm 0 = 0 := by
  simp [euclideanNorm, radiusSquared]

theorem euclideanNorm_nonneg (z : Point) : 0 ≤ euclideanNorm z :=
  Real.sqrt_nonneg _

theorem euclideanNorm_pos {z : Point} (hz : z ≠ 0) : 0 < euclideanNorm z := by
  exact Real.sqrt_pos.2 (radiusSquared_pos hz)

@[simp] theorem euclideanNorm_pos_iff (z : Point) :
    0 < euclideanNorm z ↔ z ≠ 0 := by
  constructor
  · intro h hz
    subst z
    simp at h
  · exact euclideanNorm_pos

theorem euclideanNorm_continuous : Continuous euclideanNorm := by
  unfold euclideanNorm radiusSquared
  fun_prop

@[simp] theorem euclideanNorm_sq (z : Point) :
    euclideanNorm z ^ 2 = radiusSquared z := by
  exact Real.sq_sqrt (radiusSquared_nonneg z)

@[simp] theorem euclideanNorm_eq_zero_iff (z : Point) :
    euclideanNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [euclideanNorm, Real.sqrt_eq_zero'] at h
    exact (radiusSquared_eq_zero_iff z).mp
      (le_antisymm h (radiusSquared_nonneg z))
  · rintro rfl
    exact euclideanNorm_zero

@[simp] theorem radiusSquared_smul (a : ℝ) (z : Point) :
    radiusSquared (a • z) = a ^ 2 * radiusSquared z := by
  simp only [radiusSquared, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem stabilityCertificate_zero : stabilityCertificate 0 = 0 := by
  simp [stabilityCertificate, radiusSquared]

/-- The elementary estimate `-5 ≤ -10xy/(x²+y²) ≤ 5`. -/
theorem stabilityCertificate_exponent_bounds {z : Point} (hz : z ≠ 0) :
    -5 ≤ -10 * z 0 * z 1 / radiusSquared z ∧
      -10 * z 0 * z 1 / radiusSquared z ≤ 5 := by
  have hrs : 0 < radiusSquared z := radiusSquared_pos hz
  have hxy_upper : 2 * z 0 * z 1 ≤ radiusSquared z := by
    simp only [radiusSquared]
    nlinarith [sq_nonneg (z 0 - z 1)]
  have hxy_lower : -radiusSquared z ≤ 2 * z 0 * z 1 := by
    simp only [radiusSquared]
    nlinarith [sq_nonneg (z 0 + z 1)]
  constructor
  · rw [le_div_iff₀ hrs]
    nlinarith
  · rw [div_le_iff₀ hrs]
    nlinarith

/-- The lower bound in equation (2.8) of the paper. -/
theorem stabilityCertificate_lower_bound (z : Point) :
    Real.exp (-5) * radiusSquared z ≤ stabilityCertificate z := by
  by_cases hz : z = 0
  · subst z
    simp [radiusSquared]
  · have hexp := Real.exp_le_exp.mpr (stabilityCertificate_exponent_bounds hz).1
    have hmul := mul_le_mul_of_nonneg_left hexp (radiusSquared_nonneg z)
    simpa only [stabilityCertificate, mul_comm] using hmul

/-- The upper bound in equation (2.8) of the paper. -/
theorem stabilityCertificate_upper_bound (z : Point) :
    stabilityCertificate z ≤ Real.exp 5 * radiusSquared z := by
  by_cases hz : z = 0
  · subst z
    simp [radiusSquared]
  · have hexp := Real.exp_le_exp.mpr (stabilityCertificate_exponent_bounds hz).2
    have hmul := mul_le_mul_of_nonneg_left hexp (radiusSquared_nonneg z)
    simpa only [stabilityCertificate, mul_comm] using hmul

/-- Strict positivity of `H` away from the origin. -/
theorem stabilityCertificate_pos {z : Point} (hz : z ≠ 0) :
    0 < stabilityCertificate z := by
  exact mul_pos (radiusSquared_pos hz) (Real.exp_pos _)

/-- The explicit certificate is positive definite. -/
theorem stabilityCertificate_positiveDefinite :
    FunctionPositiveDefinite stabilityCertificate := by
  exact ⟨stabilityCertificate_zero, fun _ hz ↦ stabilityCertificate_pos hz⟩

/-- Comparison of the paper's Euclidean radius with the ambient sup norm.
This is used only to express radial unboundedness with the standard cocompact
filter; the sharp constant is irrelevant. -/
theorem half_norm_sq_le_radiusSquared (z : Point) :
    (1 / 2 : ℝ) * ‖z‖ ^ 2 ≤ radiusSquared z := by
  have hnorm : ‖z‖ ≤ |z 0| + |z 1| := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · simp only [Real.norm_eq_abs]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · simp only [Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hnorm_sq : ‖z‖ ^ 2 ≤ (|z 0| + |z 1|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hnorm 2
  have habs_sq : (|z 0| + |z 1|) ^ 2 ≤ 2 * radiusSquared z := by
    simp only [radiusSquared]
    nlinarith [sq_nonneg (|z 0| - |z 1|), sq_abs (z 0), sq_abs (z 1)]
  nlinarith

/-- The squared Euclidean radius tends to infinity as the point escapes to
infinity. -/
theorem radiusSquared_tendsto_atTop :
    Tendsto radiusSquared (cocompact Point) atTop := by
  have hnorm : Tendsto (fun z : Point ↦ ‖z‖) (cocompact Point) atTop :=
    tendsto_norm_cocompact_atTop
  have hnormSq : Tendsto (fun z : Point ↦ ‖z‖ ^ 2) (cocompact Point) atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnorm
  have hhalf :
      Tendsto (fun z : Point ↦ (1 / 2 : ℝ) * ‖z‖ ^ 2) (cocompact Point) atTop :=
    hnormSq.const_mul_atTop (by norm_num)
  exact Filter.tendsto_atTop_mono' _
    (Filter.Eventually.of_forall half_norm_sq_le_radiusSquared) hhalf

/-- The explicit certificate is radially unbounded. -/
theorem stabilityCertificate_radiallyUnbounded :
    RadiallyUnbounded stabilityCertificate := by
  have hlower :
      Tendsto (fun z : Point ↦ Real.exp (-5) * radiusSquared z)
        (cocompact Point) atTop :=
    radiusSquared_tendsto_atTop.const_mul_atTop (Real.exp_pos _)
  exact Filter.tendsto_atTop_mono' _
    (Filter.Eventually.of_forall stabilityCertificate_lower_bound) hlower

/-- The explicit certificate is homogeneous of degree two. -/
theorem stabilityCertificate_twoHomogeneous :
    TwoHomogeneous stabilityCertificate := by
  intro a ha z
  have ha0 : a ≠ 0 := ne_of_gt ha
  by_cases hz : z = 0
  · subst z
    simp
  · have hrs0 : radiusSquared z ≠ 0 :=
      mt (radiusSquared_eq_zero_iff z).mp hz
    have hquot :
        -10 * (a • z) 0 * (a • z) 1 / radiusSquared (a • z) =
          -10 * z 0 * z 1 / radiusSquared z := by
      simp only [radiusSquared_smul, Pi.smul_apply, smul_eq_mul]
      field_simp
    unfold stabilityCertificate
    rw [hquot, radiusSquared_smul]
    ring

end

end HomogeneousObstruction
