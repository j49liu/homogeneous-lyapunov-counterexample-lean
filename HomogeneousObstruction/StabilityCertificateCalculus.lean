import HomogeneousObstruction.StabilityCertificate
import HomogeneousObstruction.ConeTipRegularity

/-!
# Calculus of the explicit Lyapunov certificate

This file verifies the regularity and Lie-derivative assertions for the
certificate `stabilityCertificate` from main theorem item (2).  Away from the
origin the calculation is ordinary differentiation of the displayed Cartesian
formula.  At the origin we apply the quadratic cone-tip lemma, as in the paper.
-/

namespace HomogeneousObstruction

open Set

noncomputable section

/-- The polynomial vector field evaluated as a function on `Point`. -/
def fieldValue (z : Point) : Point :=
  ![evalAt field₁ z, evalAt field₂ z]

/-- The function-level Lie derivative, defined using the Fréchet derivative. -/
def functionLieDerivative (V : Point → ℝ) (z : Point) : ℝ :=
  fderiv ℝ V z (fieldValue z)

/-- The manuscript's radial polynomial identity, in function-valued form. -/
theorem fieldValue_radial_identity (z : Point) :
    z 0 * fieldValue z 0 + z 1 * fieldValue z 1 =
      4 * z 0 ^ 4 - 2 * z 0 ^ 2 * z 1 ^ 2 - 6 * z 1 ^ 4 := by
  simpa [fieldValue] using radial_field_identity z

/-- The manuscript's angular polynomial identity, in function-valued form. -/
theorem fieldValue_angular_identity (z : Point) :
    z 0 * fieldValue z 1 - z 1 * fieldValue z 0 = radiusSquared z ^ 2 := by
  simpa [fieldValue, radiusSquared] using angular_field_identity z

theorem radiusSquared_ne_zero {z : Point} (hz : z ≠ 0) : radiusSquared z ≠ 0 :=
  mt (radiusSquared_eq_zero_iff z).mp hz

/-- The explicit certificate is smooth away from the origin. -/
theorem stabilityCertificate_contDiffAt {z : Point} (hz : z ≠ 0) :
    ContDiffAt ℝ ⊤ stabilityCertificate z := by
  have hr : radiusSquared z ≠ 0 := radiusSquared_ne_zero hz
  have hR : ContDiffAt ℝ ⊤ radiusSquared z := by
    unfold radiusSquared
    fun_prop
  have hnum :
      ContDiffAt ℝ ⊤ (fun w : Point => -10 * w 0 * w 1) z := by
    fun_prop
  exact hR.mul ((hnum.div hR hr).exp)

/-- The `C^∞(ℝ² \ {0})` assertion in main theorem item (2). -/
theorem stabilityCertificate_contDiffOn_compl_zero :
    ContDiffOn ℝ ⊤ stabilityCertificate ({0} : Set Point)ᶜ := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact (stabilityCertificate_contDiffAt hz0).contDiffWithinAt

/-- The affine line through `z` in direction `v`. -/
private def affineLine (z v : Point) (t : ℝ) : Point :=
  fun i => z i + t * v i

private theorem affineLine_hasDerivAt (z v : Point) :
    HasDerivAt (affineLine z v) v 0 := by
  rw [hasDerivAt_pi]
  intro i
  convert (hasDerivAt_const (x := 0) (c := z i)).add
    ((hasDerivAt_id 0).mul_const (v i)) using 1
  simp

@[simp] private theorem affineLine_zero (z v : Point) : affineLine z v 0 = z := by
  funext i
  simp [affineLine]

private theorem radiusSquared_affineLine_hasDerivAt (z v : Point) :
    HasDerivAt (fun t => radiusSquared (affineLine z v t))
      (2 * z 0 * v 0 + 2 * z 1 * v 1) 0 := by
  have hx : HasDerivAt (fun t => affineLine z v t 0) (v 0) 0 :=
    hasDerivAt_pi.mp (affineLine_hasDerivAt z v) 0
  have hy : HasDerivAt (fun t => affineLine z v t 1) (v 1) 0 :=
    hasDerivAt_pi.mp (affineLine_hasDerivAt z v) 1
  convert (hx.pow 2).add (hy.pow 2) using 1
  simp [affineLine]

private theorem coordinateProduct_affineLine_hasDerivAt (z v : Point) :
    HasDerivAt (fun t => affineLine z v t 0 * affineLine z v t 1)
      (v 0 * z 1 + z 0 * v 1) 0 := by
  have hx := hasDerivAt_pi.mp (affineLine_hasDerivAt z v) 0
  have hy := hasDerivAt_pi.mp (affineLine_hasDerivAt z v) 1
  convert hx.mul hy using 1
  simp [affineLine]

private theorem stabilityCertificate_affineLine_hasDerivAt
    {z v : Point} (hz : z ≠ 0) :
    HasDerivAt (fun t => stabilityCertificate (affineLine z v t))
      (Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        ((2 * z 0 * v 0 + 2 * z 1 * v 1) +
          radiusSquared z *
            (-10 * (((v 0 * z 1 + z 0 * v 1) * radiusSquared z -
              (z 0 * z 1) * (2 * z 0 * v 0 + 2 * z 1 * v 1)) /
                radiusSquared z ^ 2)))) 0 := by
  have hR := radiusSquared_affineLine_hasDerivAt z v
  have hU := coordinateProduct_affineLine_hasDerivAt z v
  have hQ :=
    (((hasDerivAt_const (x := 0) (c := (-10 : ℝ))).mul hU).div hR (by
      rw [affineLine_zero]
      exact radiusSquared_ne_zero hz))
  have hE := hQ.exp
  rw [affineLine_zero] at hQ hE
  convert hR.mul hE using 1
  · funext t
    unfold stabilityCertificate
    congr 2
    dsimp
    ring
  · simp [affineLine]
    ring_nf

theorem fderiv_stabilityCertificate_apply {z : Point} (hz : z ≠ 0) (v : Point) :
    fderiv ℝ stabilityCertificate z v =
      Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        ((2 * z 0 * v 0 + 2 * z 1 * v 1) +
          radiusSquared z *
            (-10 * (((v 0 * z 1 + z 0 * v 1) * radiusSquared z -
              (z 0 * z 1) * (2 * z 0 * v 0 + 2 * z 1 * v 1)) /
                radiusSquared z ^ 2))) := by
  have hoff : DifferentiableAt ℝ stabilityCertificate (affineLine z v 0) := by
    rw [affineLine_zero]
    exact (stabilityCertificate_contDiffAt hz).differentiableAt (by simp)
  have hcomp := hoff.hasFDerivAt.comp_hasDerivAt 0 (affineLine_hasDerivAt z v)
  have hcalc := stabilityCertificate_affineLine_hasDerivAt (v := v) hz
  have heq := hcomp.unique hcalc
  rw [affineLine_zero] at heq
  simpa [Function.comp_def] using heq

/-- First Cartesian component of the gradient of `stabilityCertificate`. -/
def stabilityCertificateGradientX (z : Point) : ℝ :=
  Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
    (2 * z 0 + radiusSquared z *
      (-10 * ((z 1 * radiusSquared z - (z 0 * z 1) * (2 * z 0)) /
        radiusSquared z ^ 2)))

/-- Second Cartesian component of the gradient of `stabilityCertificate`. -/
def stabilityCertificateGradientY (z : Point) : ℝ :=
  Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
    (2 * z 1 + radiusSquared z *
      (-10 * ((z 0 * radiusSquared z - (z 0 * z 1) * (2 * z 1)) /
        radiusSquared z ^ 2)))

/-- The gradient bundled as a continuous linear functional. -/
def stabilityCertificateGradient (z : Point) : Point →L[ℝ] ℝ :=
  stabilityCertificateGradientX z • ContinuousLinearMap.proj 0 +
    stabilityCertificateGradientY z • ContinuousLinearMap.proj 1

@[simp] theorem stabilityCertificateGradient_apply (z v : Point) :
    stabilityCertificateGradient z v =
      stabilityCertificateGradientX z * v 0 + stabilityCertificateGradientY z * v 1 := by
  simp [stabilityCertificateGradient]

theorem fderiv_stabilityCertificate {z : Point} (hz : z ≠ 0) :
    fderiv ℝ stabilityCertificate z = stabilityCertificateGradient z := by
  ext v
  rw [fderiv_stabilityCertificate_apply hz, stabilityCertificateGradient_apply]
  simp only [stabilityCertificateGradientX, stabilityCertificateGradientY]
  ring

theorem stabilityCertificate_hasFDerivAt {z : Point} (hz : z ≠ 0) :
    HasFDerivAt stabilityCertificate (stabilityCertificateGradient z) z := by
  rw [← fderiv_stabilityCertificate hz]
  exact ((stabilityCertificate_contDiffAt hz).differentiableAt (by simp)).hasFDerivAt

theorem stabilityCertificateGradientX_eq {z : Point} (hz : z ≠ 0) :
    stabilityCertificateGradientX z =
      Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        (2 * z 0 + 10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z) := by
  have hr := radiusSquared_ne_zero hz
  simp only [stabilityCertificateGradientX]
  field_simp [hr]
  simp only [radiusSquared]
  ring

theorem stabilityCertificateGradientY_eq {z : Point} (hz : z ≠ 0) :
    stabilityCertificateGradientY z =
      Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        (2 * z 1 - 10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z) := by
  have hr := radiusSquared_ne_zero hz
  simp only [stabilityCertificateGradientY]
  field_simp [hr]
  simp only [radiusSquared]
  ring

private theorem abs_coordinate_le_norm (z : Point) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i

private theorem abs_sq_sub_sq_le_radiusSquared (z : Point) :
    |z 0 ^ 2 - z 1 ^ 2| ≤ radiusSquared z := by
  calc
    |z 0 ^ 2 - z 1 ^ 2| ≤ |z 0 ^ 2| + |z 1 ^ 2| := abs_sub _ _
    _ = radiusSquared z := by simp [radiusSquared]

private theorem abs_sq_sub_sq_div_radiusSquared_le_one
    {z : Point} (hz : z ≠ 0) :
    |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤ 1 := by
  have hr : 0 < radiusSquared z := radiusSquared_pos hz
  rw [abs_div, abs_of_pos hr, div_le_one hr]
  exact abs_sq_sub_sq_le_radiusSquared z

private theorem stabilityCertificateGradientX_abs_bound
    {z : Point} (hz : z ≠ 0) :
    |stabilityCertificateGradientX z| ≤ 12 * Real.exp 5 * ‖z‖ := by
  rw [stabilityCertificateGradientX_eq hz, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-10 * z 0 * z 1 / radiusSquared z) ≤ Real.exp 5 :=
    Real.exp_le_exp.mpr (stabilityCertificate_exponent_bounds hz).2
  have hx := abs_coordinate_le_norm z 0
  have hy := abs_coordinate_le_norm z 1
  have hratio := abs_sq_sub_sq_div_radiusSquared_le_one hz
  have hterm :
      |10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| =
        10 * |z 1| * |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := by
    rw [show 10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z =
      (10 * z 1) * ((z 0 ^ 2 - z 1 ^ 2) / radiusSquared z) by ring]
    simp
  have hinner :
      |2 * z 0 + 10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤
        12 * ‖z‖ := by
    calc
      _ ≤ |2 * z 0| +
          |10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := abs_add_le _ _
      _ = 2 * |z 0| + 10 * |z 1| *
          |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := by
        rw [hterm]
        simp
      _ ≤ 12 * ‖z‖ := by
        have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
        have hxy : 10 * |z 1| *
            |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤ 10 * ‖z‖ := by
          calc
            _ ≤ 10 * |z 1| * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ ≤ 10 * ‖z‖ := by nlinarith
        nlinarith
  calc
    Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        |2 * z 0 + 10 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤
      Real.exp 5 * (12 * ‖z‖) :=
        mul_le_mul hexp hinner (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    _ = 12 * Real.exp 5 * ‖z‖ := by ring

private theorem stabilityCertificateGradientY_abs_bound
    {z : Point} (hz : z ≠ 0) :
    |stabilityCertificateGradientY z| ≤ 12 * Real.exp 5 * ‖z‖ := by
  rw [stabilityCertificateGradientY_eq hz, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-10 * z 0 * z 1 / radiusSquared z) ≤ Real.exp 5 :=
    Real.exp_le_exp.mpr (stabilityCertificate_exponent_bounds hz).2
  have hx := abs_coordinate_le_norm z 0
  have hy := abs_coordinate_le_norm z 1
  have hratio := abs_sq_sub_sq_div_radiusSquared_le_one hz
  have hterm :
      |10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| =
        10 * |z 0| * |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := by
    rw [show 10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z =
      (10 * z 0) * ((z 0 ^ 2 - z 1 ^ 2) / radiusSquared z) by ring]
    simp
  have hinner :
      |2 * z 1 - 10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤
        12 * ‖z‖ := by
    calc
      _ ≤ |2 * z 1| +
          |10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := abs_sub _ _
      _ = 2 * |z 1| + 10 * |z 0| *
          |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| := by
        rw [hterm]
        simp
      _ ≤ 12 * ‖z‖ := by
        have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
        have hxy : 10 * |z 0| *
            |(z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤ 10 * ‖z‖ := by
          calc
            _ ≤ 10 * |z 0| * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ ≤ 10 * ‖z‖ := by nlinarith
        nlinarith
  calc
    Real.exp (-10 * z 0 * z 1 / radiusSquared z) *
        |2 * z 1 - 10 * z 0 * (z 0 ^ 2 - z 1 ^ 2) / radiusSquared z| ≤
      Real.exp 5 * (12 * ‖z‖) :=
        mul_le_mul hexp hinner (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    _ = 12 * Real.exp 5 * ‖z‖ := by ring

/-- The derivative is linearly bounded at the quadratic cone tip. -/
theorem fderiv_stabilityCertificate_norm_bound {z : Point} (hz : z ≠ 0) :
    ‖fderiv ℝ stabilityCertificate z‖ ≤ 24 * Real.exp 5 * ‖z‖ := by
  rw [fderiv_stabilityCertificate hz]
  apply (stabilityCertificateGradient z).opNorm_le_bound
  · positivity
  · intro v
    rw [stabilityCertificateGradient_apply]
    simp only [Real.norm_eq_abs]
    calc
      |stabilityCertificateGradientX z * v 0 +
          stabilityCertificateGradientY z * v 1| ≤
        |stabilityCertificateGradientX z| * |v 0| +
          |stabilityCertificateGradientY z| * |v 1| := by
            simpa only [abs_mul] using abs_add_le
              (stabilityCertificateGradientX z * v 0)
              (stabilityCertificateGradientY z * v 1)
      _ ≤ (12 * Real.exp 5 * ‖z‖) * ‖v‖ +
          (12 * Real.exp 5 * ‖z‖) * ‖v‖ := by
        gcongr
        · exact stabilityCertificateGradientX_abs_bound hz
        · exact abs_coordinate_le_norm v 0
        · exact stabilityCertificateGradientY_abs_bound hz
        · exact abs_coordinate_le_norm v 1
      _ = (24 * Real.exp 5 * ‖z‖) * ‖v‖ := by ring

private theorem radiusSquared_le_two_norm_sq (z : Point) :
    radiusSquared z ≤ 2 * ‖z‖ ^ 2 := by
  have hx := abs_coordinate_le_norm z 0
  have hy := abs_coordinate_le_norm z 1
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg z
  have hx2 : z 0 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hnorm (abs_nonneg (z 0))),
      sq_abs (z 0)]
  have hy2 : z 1 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hnorm (abs_nonneg (z 1))),
      sq_abs (z 1)]
  simp only [radiusSquared]
  linarith

private theorem stabilityCertificate_quadratic_norm_bound (z : Point) :
    ‖stabilityCertificate z‖ ≤ (2 * Real.exp 5) * ‖z‖ ^ 2 := by
  have hnonneg : 0 ≤ stabilityCertificate z :=
    mul_nonneg (radiusSquared_nonneg z) (le_of_lt (Real.exp_pos _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    stabilityCertificate z ≤ Real.exp 5 * radiusSquared z :=
      stabilityCertificate_upper_bound z
    _ ≤ Real.exp 5 * (2 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (radiusSquared_le_two_norm_sq z)
        (le_of_lt (Real.exp_pos _))
    _ = (2 * Real.exp 5) * ‖z‖ ^ 2 := by ring

/-- The global `C¹(ℝ²)` assertion in main theorem item (2). -/
theorem stabilityCertificate_contDiff_one :
    ContDiff ℝ 1 stabilityCertificate := by
  apply coneTip_contDiff_one_of_smooth_off_zero stabilityCertificate
    (2 * Real.exp 5) (24 * Real.exp 5)
  · exact stabilityCertificate_zero
  · exact stabilityCertificate_quadratic_norm_bound
  · exact stabilityCertificate_contDiffOn_compl_zero
  · intro z hz
    exact fderiv_stabilityCertificate_norm_bound hz

/-- The exact identity `L_f H = -2 (x²+y²) H` away from the origin. -/
theorem functionLieDerivative_stabilityCertificate {z : Point} (hz : z ≠ 0) :
    functionLieDerivative stabilityCertificate z =
      -2 * radiusSquared z * stabilityCertificate z := by
  rw [functionLieDerivative, fderiv_stabilityCertificate_apply hz]
  have hr := radiusSquared_ne_zero hz
  have hrad := fieldValue_radial_identity z
  have hang := fieldValue_angular_identity z
  have hrad_polar :
      z 0 * fieldValue z 0 + z 1 * fieldValue z 1 =
        radiusSquared z *
          (-radiusSquared z + 5 * (z 0 ^ 2 - z 1 ^ 2)) := by
    rw [hrad]
    simp only [radiusSquared]
    ring
  have hmixed :
      (fieldValue z 0 * z 1 + z 0 * fieldValue z 1) * radiusSquared z -
          (z 0 * z 1) *
            (2 * z 0 * fieldValue z 0 + 2 * z 1 * fieldValue z 1) =
        (z 0 ^ 2 - z 1 ^ 2) *
          (z 0 * fieldValue z 1 - z 1 * fieldValue z 0) := by
    simp only [radiusSquared]
    ring
  have hbracket :
      (2 * z 0 * fieldValue z 0 + 2 * z 1 * fieldValue z 1) +
          radiusSquared z *
            (-10 *
              (((fieldValue z 0 * z 1 + z 0 * fieldValue z 1) * radiusSquared z -
                  (z 0 * z 1) *
                    (2 * z 0 * fieldValue z 0 + 2 * z 1 * fieldValue z 1)) /
                radiusSquared z ^ 2)) =
        -2 * radiusSquared z ^ 2 := by
    rw [hmixed, hang]
    have hrad_twice :
        2 * z 0 * fieldValue z 0 + 2 * z 1 * fieldValue z 1 =
          2 * (radiusSquared z *
            (-radiusSquared z + 5 * (z 0 ^ 2 - z 1 ^ 2))) := by
      rw [← hrad_polar]
      ring
    rw [hrad_twice]
    field_simp [hr]
    ring
  simp only [stabilityCertificate]
  rw [hbracket]
  ring

/-- Strict decrease of the certificate away from the origin. -/
theorem functionLieDerivative_stabilityCertificate_neg {z : Point} (hz : z ≠ 0) :
    functionLieDerivative stabilityCertificate z < 0 := by
  rw [functionLieDerivative_stabilityCertificate hz]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (radiusSquared_pos hz))
    (stabilityCertificate_pos hz)

/-- An auxiliary assembly of item (2) from the direct Cartesian derivative
and cone bounds.  The public `mainTheorem_item2` is assembled in
`StabilityCertificateManuscript.lean` from the manuscript's active polar and
homogeneous-unit-circle proofs. -/
theorem mainTheorem_item2_cartesian_auxiliary :
    FunctionPositiveDefinite stabilityCertificate ∧
    RadiallyUnbounded stabilityCertificate ∧
    TwoHomogeneous stabilityCertificate ∧
    ContDiff ℝ 1 stabilityCertificate ∧
    ContDiffOn ℝ ⊤ stabilityCertificate ({0} : Set Point)ᶜ ∧
    ∀ z : Point, z ≠ 0 →
      functionLieDerivative stabilityCertificate z =
          -2 * radiusSquared z * stabilityCertificate z ∧
        functionLieDerivative stabilityCertificate z < 0 := by
  refine ⟨stabilityCertificate_positiveDefinite,
    stabilityCertificate_radiallyUnbounded,
    stabilityCertificate_twoHomogeneous,
    stabilityCertificate_contDiff_one,
    stabilityCertificate_contDiffOn_compl_zero, ?_⟩
  intro z hz
  exact ⟨functionLieDerivative_stabilityCertificate hz,
    functionLieDerivative_stabilityCertificate_neg hz⟩

end

end HomogeneousObstruction
