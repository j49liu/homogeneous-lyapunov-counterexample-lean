import HomogeneousObstruction.StabilityCertificateManuscript
import HomogeneousObstruction.LocalAnalyticCalculus

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

theorem euclideanNorm_nonneg (z : Point) : 0 ≤ euclideanNorm z :=
  Real.sqrt_nonneg _

@[simp] theorem euclideanNorm_sq (z : Point) :
    euclideanNorm z ^ 2 = radiusSquared z := by
  exact Real.sq_sqrt (radiusSquared_nonneg z)

@[simp] theorem euclideanNorm_eq_zero_iff (z : Point) : euclideanNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [euclideanNorm, Real.sqrt_eq_zero'] at h
    exact (radiusSquared_eq_zero_iff z).mp
      (le_antisymm h (radiusSquared_nonneg z))
  · rintro rfl
    exact euclideanNorm_zero

@[simp] theorem euclideanDistance_zero_right (z : Point) :
    euclideanDistance z 0 = euclideanNorm z := by
  simp [euclideanDistance]

/-- A trajectory beginning at `z₀` and solving the autonomous ODE for all
nonnegative times.  Values at negative times are immaterial. -/
def IsForwardTrajectory (F : Point → Point) (γ : ℝ → Point) (z₀ : Point) : Prop :=
  γ 0 = z₀ ∧ IsIntegralCurveOn γ (fun _ => F) (Ici 0)

/-- Every initial state admits a trajectory on the whole forward time ray. -/
def ForwardComplete (F : Point → Point) : Prop :=
  ∀ z₀ : Point, ∃ γ : ℝ → Point, IsForwardTrajectory F γ z₀

/-- Lyapunov stability in the Euclidean norm, quantified over every forward
trajectory of the vector field. -/
def LyapunovStable (F : Point → Point) (zEquil : Point) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z₀ : Point, euclideanDistance z₀ zEquil < δ →
        ∀ γ : ℝ → Point, IsForwardTrajectory F γ z₀ →
          ∀ t : ℝ, 0 ≤ t → euclideanDistance (γ t) zEquil < ε

/-- Global attractivity in epsilon--time form, again quantified over every
forward trajectory. -/
def GloballyAttractive (F : Point → Point) (zEquil : Point) : Prop :=
  ∀ z₀ : Point, ∀ γ : ℝ → Point, IsForwardTrajectory F γ z₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → euclideanDistance (γ t) zEquil < ε

/-- Global asymptotic stability: equilibrium, forward completeness,
Lyapunov stability, and global attractivity. -/
def GloballyAsymptoticallyStable (F : Point → Point) (zEquil : Point) : Prop :=
  F zEquil = 0 ∧ ForwardComplete F ∧
    LyapunovStable F zEquil ∧ GloballyAttractive F zEquil

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
    (stabilityCertificate_contDiff_one.differentiable (by norm_num) (γ t)).hasFDerivAt
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
    stabilityCertificate_contDiff_one.continuous.comp_continuousOn hγ.2.continuousOn
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
  intro ε hε
  let b : ℝ := Real.exp 5
  have hb : 0 < b := Real.exp_pos 5
  refine ⟨ε / b, div_pos hε hb, ?_⟩
  intro z₀ hz₀ γ hγ t ht
  simp only [euclideanDistance_zero_right] at hz₀ ⊢
  have hanti := stabilityCertificate_comp_antitoneOn hγ
  have hHt_le_H0 : stabilityCertificate (γ t) ≤ stabilityCertificate z₀ := by
    rw [← hγ.1]
    exact hanti (by simp) ht ht
  have hlower := stabilityCertificate_lower_bound (γ t)
  have hupper := stabilityCertificate_upper_bound z₀
  have hcancel : b * Real.exp (-5) = 1 := by
    exact exp_five_mul_exp_neg_five
  have hradius_le :
      radiusSquared (γ t) ≤ b ^ 2 * radiusSquared z₀ := by
    calc
      radiusSquared (γ t) =
          b * (Real.exp (-5) * radiusSquared (γ t)) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ b * stabilityCertificate (γ t) :=
        mul_le_mul_of_nonneg_left hlower hb.le
      _ ≤ b * stabilityCertificate z₀ :=
        mul_le_mul_of_nonneg_left hHt_le_H0 hb.le
      _ ≤ b * (b * radiusSquared z₀) :=
        mul_le_mul_of_nonneg_left hupper hb.le
      _ = b ^ 2 * radiusSquared z₀ := by ring_nf
  have hnorm_sq :
      euclideanNorm (γ t) ^ 2 ≤ b ^ 2 * euclideanNorm z₀ ^ 2 := by
    simpa using hradius_le
  have hb_norm_lt : b * euclideanNorm z₀ < ε := by
    have := (lt_div_iff₀ hb).mp hz₀
    simpa [mul_comm] using this
  have hb_norm_nonneg : 0 ≤ b * euclideanNorm z₀ :=
    mul_nonneg hb.le (euclideanNorm_nonneg z₀)
  have hsq_lt : (b * euclideanNorm z₀) ^ 2 < ε ^ 2 :=
    (sq_lt_sq₀ hb_norm_nonneg hε.le).mpr hb_norm_lt
  have htarget_sq : euclideanNorm (γ t) ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt hnorm_sq ?_
    simpa [mul_pow] using hsq_lt
  exact (sq_lt_sq₀ (euclideanNorm_nonneg (γ t)) hε.le).mp htarget_sq

/-- Above a positive certificate level `η`, the scalar derivative is bounded
above by the fixed negative number `-2 exp(-5) η²`. -/
private theorem stabilityCertificate_derivative_le_level
    {z : Point} {η : ℝ} (hη : 0 ≤ η)
    (hlevel : η ≤ stabilityCertificate z) :
    -2 * radiusSquared z * stabilityCertificate z ≤
      -2 * Real.exp (-5) * η ^ 2 := by
  have ha : 0 < Real.exp (-5) := Real.exp_pos _
  have hupper := stabilityCertificate_upper_bound z
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
  let T : ℝ := h 0 / d + 1
  have hh0 : 0 ≤ h 0 := stabilityCertificate_nonneg (γ 0)
  have hTpos : 0 < T := by
    dsimp [T]
    have : 0 ≤ h 0 / d := div_nonneg hh0 hd.le
    linarith
  have hanti : AntitoneOn h (Ici 0) :=
    stabilityCertificate_comp_antitoneOn hγ
  have hTlt : h T < η := by
    by_contra hnot
    have hηT : η ≤ h T := le_of_not_gt hnot
    let q : ℝ → ℝ := fun t => h t + d * t
    have hhcontIci : ContinuousOn h (Ici 0) :=
      stabilityCertificate_contDiff_one.continuous.comp_continuousOn
        hγ.2.continuousOn
    have hhcontIcc : ContinuousOn h (Icc 0 T) :=
      hhcontIci.mono (fun t ht => ht.1)
    have hqcont : ContinuousOn q (Icc 0 T) := by
      have hlinear : ContinuousOn (fun t : ℝ => d * t) (Icc 0 T) := by
        fun_prop
      exact hhcontIcc.add hlinear
    have hqanti : AntitoneOn q (Icc 0 T) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hqcont
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by simpa [interior_Icc] using ht
        have hhderiv := stabilityCertificate_comp_hasDerivAt hγ htIoo.1
        have hlinderiv : HasDerivAt (fun s : ℝ => d * s) d t := by
          simpa using (hasDerivAt_id t).const_mul d
        exact (hhderiv.add hlinderiv).hasDerivWithinAt
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by simpa [interior_Icc] using ht
        have hT_le_ht : h T ≤ h t :=
          hanti htIoo.1.le hTpos.le htIoo.2.le
        have hηt : η ≤ h t := le_trans hηT hT_le_ht
        have hbound := stabilityCertificate_derivative_le_level hη.le hηt
        change -2 * radiusSquared (γ t) * stabilityCertificate (γ t) + d ≤ 0
        dsimp [d]
        linarith
    have hq0T : q T ≤ q 0 :=
      hqanti ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩ hTpos.le
    have hdT : d * T = h 0 + d := by
      dsimp [T]
      field_simp [ne_of_gt hd]
    have hnegative : h T < 0 := by
      dsimp [q] at hq0T
      rw [hdT] at hq0T
      have hdpos := hd
      linarith
    exact (not_lt_of_ge (stabilityCertificate_nonneg (γ T))) hnegative
  refine ⟨T, hTpos.le, ?_⟩
  intro t hTt
  have htle : h t ≤ h T :=
    hanti hTpos.le (le_trans hTpos.le hTt) hTt
  exact lt_of_le_of_lt htle hTlt

/-- The explicit certificate makes the origin globally attractive for every
forward trajectory. -/
theorem globallyAttractive_fieldValue : GloballyAttractive fieldValue 0 := by
  intro z₀ γ hγ ε hε
  let η : ℝ := Real.exp (-5) * ε ^ 2
  have hη : 0 < η := mul_pos (Real.exp_pos _) (sq_pos_of_pos hε)
  obtain ⟨T, hT, hafter⟩ := stabilityCertificate_eventually_lt hγ hη
  refine ⟨T, hT, ?_⟩
  intro t hTt
  simp only [euclideanDistance_zero_right]
  have hHlt : stabilityCertificate (γ t) < η := hafter t hTt
  have hlower := stabilityCertificate_lower_bound (γ t)
  have hscaled :
      Real.exp (-5) * radiusSquared (γ t) <
        Real.exp (-5) * ε ^ 2 := lt_of_le_of_lt hlower hHlt
  have hradius_lt : radiusSquared (γ t) < ε ^ 2 :=
    lt_of_mul_lt_mul_left hscaled (Real.exp_pos (-5)).le
  have hnorm_sq : euclideanNorm (γ t) ^ 2 < ε ^ 2 := by
    simpa using hradius_lt
  exact (sq_lt_sq₀ (euclideanNorm_nonneg (γ t)) hε.le).mp hnorm_sq

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
