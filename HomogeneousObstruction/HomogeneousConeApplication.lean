import HomogeneousObstruction.StabilityCertificatePolarLie

/-!
# The homogeneous cone-tip argument for the explicit certificate

This file gives the manuscript-level `k = 2` application of the generic
cone-tip lemma.  Its derivative estimate is obtained from degree-one
homogeneity and boundedness on the Euclidean unit circle, rather than from a
global Cartesian estimate on the two displayed gradient components.
-/

namespace HomogeneousObstruction

open Set

noncomputable section

/-- The Euclidean unit circle, expressed with the manuscript's squared
radius. -/
def euclideanUnitCircle : Set Point := {z | radiusSquared z = 1}

/-- The Euclidean unit circle is compact.  This is the compact angular
cross-section used in the paper's proof of the cone-tip lemma. -/
theorem euclideanUnitCircle_isCompact : IsCompact euclideanUnitCircle := by
  apply (isCompact_closedBall (0 : Point) 1).of_isClosed_subset
  · exact isClosed_eq (by
      unfold radiusSquared
      fun_prop) continuous_const
  · intro z hz
    have hrs : radiusSquared z = 1 := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i
    · simp only [Real.norm_eq_abs]
      change |z 0| ≤ 1
      have hy := sq_nonneg (z 1)
      have hxabs := sq_abs (z 0)
      simp only [radiusSquared] at hrs
      nlinarith [abs_nonneg (z 0)]
    · simp only [Real.norm_eq_abs]
      change |z 1| ≤ 1
      have hx := sq_nonneg (z 0)
      have hyabs := sq_abs (z 1)
      simp only [radiusSquared] at hrs
      nlinarith [abs_nonneg (z 1)]

theorem euclideanUnitCircle_nonempty : euclideanUnitCircle.Nonempty := by
  refine ⟨![1, 0], ?_⟩
  simp [euclideanUnitCircle, radiusSquared]

theorem euclideanUnitCircle_subset_compl_zero :
    euclideanUnitCircle ⊆ ({0} : Set Point)ᶜ := by
  intro z hz
  simp only [mem_compl_iff, mem_singleton_iff]
  intro hz0
  subst z
  simp [euclideanUnitCircle, radiusSquared] at hz

/-- Differentiating quadratic homogeneity shows that the derivative is
homogeneous of degree one.  This is the derivative-scaling step in the
manuscript's proof, derived here from `TwoHomogeneous` rather than from the
explicit Cartesian gradient estimate. -/
theorem fderiv_stabilityCertificate_pos_smul
    (a : ℝ) (ha : 0 < a) (z : Point) :
    fderiv ℝ stabilityCertificate (a • z) =
      a • fderiv ℝ stabilityCertificate z := by
  have hfun :
      (fun w : Point ↦ stabilityCertificate (a • w)) =
        (a ^ 2) • stabilityCertificate := by
    funext w
    simpa only [Pi.smul_apply, smul_eq_mul] using
      stabilityCertificate_twoHomogeneous_via_polar a ha w
  have hderiv := congrArg (fun F : Point → ℝ ↦ fderiv ℝ F z) hfun
  change fderiv ℝ (fun w : Point ↦ stabilityCertificate (a • w)) z =
    fderiv ℝ ((a ^ 2) • stabilityCertificate) z at hderiv
  rw [fderiv_comp_smul] at hderiv
  have hright :
      fderiv ℝ ((a ^ 2) • stabilityCertificate) z =
        (a ^ 2) • fderiv ℝ stabilityCertificate z := by
    simpa only [Pi.smul_apply] using
      congrFun (fderiv_const_smul_field (𝕜 := ℝ)
        (f := stabilityCertificate) (a ^ 2)) z
  rw [hright] at hderiv
  ext v
  have hv := congrArg (fun L : Point →L[ℝ] ℝ ↦ L v) hderiv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv ⊢
  apply (mul_left_cancel₀ (ne_of_gt ha))
  simpa only [pow_two, mul_assoc] using hv

/-- The norm of the off-origin derivative attains a finite maximum on the
Euclidean unit circle.  This is the compactness step that supplies the
otherwise-unspecified angular constant in the manuscript. -/
theorem exists_euclideanUnitCircle_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ euclideanUnitCircle,
        ‖fderiv ℝ stabilityCertificate z‖ ≤ C := by
  have hDcont_compl :
      ContinuousOn (fderiv ℝ stabilityCertificate) ({0} : Set Point)ᶜ :=
    stabilityCertificate_contDiffOn_compl_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  have hnorm_cont :
      ContinuousOn (fun z : Point ↦ ‖fderiv ℝ stabilityCertificate z‖)
        euclideanUnitCircle :=
    (hDcont_compl.mono euclideanUnitCircle_subset_compl_zero).norm
  obtain ⟨u, hu, hmax⟩ :=
    euclideanUnitCircle_isCompact.exists_isMaxOn
      euclideanUnitCircle_nonempty hnorm_cont
  exact ⟨‖fderiv ℝ stabilityCertificate u‖, norm_nonneg _,
    fun z hz ↦ hmax hz⟩

/-- Normalizing a nonzero point by its Euclidean radius lands on the unit
circle. -/
theorem inv_euclideanNorm_smul_mem_unitCircle
    {z : Point} (hz : z ≠ 0) :
    (euclideanNorm z)⁻¹ • z ∈ euclideanUnitCircle := by
  have hr : euclideanNorm z ≠ 0 := ne_of_gt (euclideanNorm_pos hz)
  simp only [euclideanUnitCircle, mem_setOf_eq, radiusSquared_smul]
  rw [← euclideanNorm_sq z]
  field_simp

/-- A point is its Euclidean radius times its unit-circle normalization. -/
theorem euclideanNorm_smul_inv_euclideanNorm_smul
    {z : Point} (hz : z ≠ 0) :
    euclideanNorm z • ((euclideanNorm z)⁻¹ • z) = z := by
  have hr : euclideanNorm z ≠ 0 := ne_of_gt (euclideanNorm_pos hz)
  rw [smul_smul]
  simp [hr]

private theorem coordinate_abs_le_norm (z : Point) (i : Fin 2) :
    |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i

/-- Equivalence of the manuscript's Euclidean radius with the ambient product
norm, in the one direction needed to transport the unit-circle derivative
bound.  The non-sharp constant `2` keeps the cone-tip estimate elementary. -/
theorem euclideanNorm_le_two_norm (z : Point) :
    euclideanNorm z ≤ 2 * ‖z‖ := by
  have hx := coordinate_abs_le_norm z 0
  have hy := coordinate_abs_le_norm z 1
  have hx_sq : z 0 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_abs (z 0), abs_nonneg (z 0), norm_nonneg z]
  have hy_sq : z 1 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_abs (z 1), abs_nonneg (z 1), norm_nonneg z]
  have hr_sq := euclideanNorm_sq z
  have hr_nonneg := euclideanNorm_nonneg z
  simp only [radiusSquared] at hr_sq
  nlinarith [norm_nonneg z]

/-- Transporting the compact unit-circle maximum along Euclidean rays gives
the linear derivative estimate required at a quadratic cone tip. -/
theorem exists_fderiv_stabilityCertificate_linear_bound_from_unitCircle :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : Point, z ≠ 0 →
        ‖fderiv ℝ stabilityCertificate z‖ ≤ C * ‖z‖ := by
  obtain ⟨M, hM_nonneg, hM⟩ :=
    exists_euclideanUnitCircle_fderiv_bound
  refine ⟨2 * M, mul_nonneg (by norm_num) hM_nonneg, ?_⟩
  intro z hz
  let u : Point := (euclideanNorm z)⁻¹ • z
  have hu : u ∈ euclideanUnitCircle := by
    simpa only [u] using inv_euclideanNorm_smul_mem_unitCircle hz
  have hr_pos : 0 < euclideanNorm z := euclideanNorm_pos hz
  have hz_ray : euclideanNorm z • u = z := by
    simpa only [u] using euclideanNorm_smul_inv_euclideanNorm_smul hz
  have hscale :=
    fderiv_stabilityCertificate_pos_smul (euclideanNorm z) hr_pos u
  rw [hz_ray] at hscale
  calc
    ‖fderiv ℝ stabilityCertificate z‖ =
        ‖euclideanNorm z • fderiv ℝ stabilityCertificate u‖ := by
      rw [hscale]
    _ = euclideanNorm z * ‖fderiv ℝ stabilityCertificate u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr_pos]
    _ ≤ euclideanNorm z * M :=
      mul_le_mul_of_nonneg_left (hM u hu) (le_of_lt hr_pos)
    _ ≤ (2 * ‖z‖) * M :=
      mul_le_mul_of_nonneg_right (euclideanNorm_le_two_norm z) hM_nonneg
    _ = (2 * M) * ‖z‖ := by ring

private theorem radiusSquared_le_two_norm_sq_from_coordinates (z : Point) :
    radiusSquared z ≤ 2 * ‖z‖ ^ 2 := by
  have hx := coordinate_abs_le_norm z 0
  have hy := coordinate_abs_le_norm z 1
  have hx_sq : z 0 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_abs (z 0), abs_nonneg (z 0), norm_nonneg z]
  have hy_sq : z 1 ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_abs (z 1), abs_nonneg (z 1), norm_nonneg z]
  simp only [radiusSquared]
  linarith

/-- The quadratic function estimate used in the `k = 2` cone-tip lemma. -/
theorem stabilityCertificate_quadratic_norm_bound_for_cone (z : Point) :
    ‖stabilityCertificate z‖ ≤
      (2 * Real.exp 5) * ‖z‖ ^ 2 := by
  have hnonneg : 0 ≤ stabilityCertificate z := by
    unfold stabilityCertificate
    exact mul_nonneg (radiusSquared_nonneg z) (le_of_lt (Real.exp_pos _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    stabilityCertificate z ≤ Real.exp 5 * radiusSquared z :=
      (stabilityCertificate_bounds_via_polar z).2
    _ ≤ Real.exp 5 * (2 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (radiusSquared_le_two_norm_sq_from_coordinates z)
        (le_of_lt (Real.exp_pos _))
    _ = (2 * Real.exp 5) * ‖z‖ ^ 2 := by ring

/-- Global `C¹` regularity proved by the manuscript's homogeneous cone-tip
argument: compactness bounds the derivative on the Euclidean unit circle,
degree-one homogeneity transports the bound to every ray, and
`coneTip_contDiff_one` extends the derivative continuously by zero. -/
theorem stabilityCertificate_contDiff_one_via_homogeneous_cone :
    ContDiff ℝ 1 stabilityCertificate := by
  obtain ⟨C, _hC_nonneg, hD_bound_off⟩ :=
    exists_fderiv_stabilityCertificate_linear_bound_from_unitCircle
  have hD_zero : fderiv ℝ stabilityCertificate 0 = 0 :=
    coneTip_fderiv_zero stabilityCertificate stabilityCertificate_zero
      (2 * Real.exp 5) stabilityCertificate_quadratic_norm_bound_for_cone
  apply coneTip_contDiff_one stabilityCertificate
    (fderiv ℝ stabilityCertificate) (2 * Real.exp 5) C
  · exact stabilityCertificate_zero
  · exact stabilityCertificate_quadratic_norm_bound_for_cone
  · exact hD_zero
  · intro z
    by_cases hz : z = 0
    · subst z
      simp [hD_zero]
    · exact hD_bound_off z hz
  · exact stabilityCertificate_contDiffOn_compl_zero.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)
  · intro z hz
    exact ((stabilityCertificate_contDiffAt hz).differentiableAt
      (by simp)).hasFDerivAt

end

end HomogeneousObstruction
