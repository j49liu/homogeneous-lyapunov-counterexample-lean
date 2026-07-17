import HomogeneousObstruction.LyapunovGAS
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Forward completeness of the cubic field

This file supplies the ODE continuation step needed for main theorem item (1).
Mathlib contains Picard--Lindelof existence and Gronwall uniqueness, but not the
standard continuation theorem saying that a bounded trajectory of a locally
Lipschitz vector field exists for all forward time.

We use the usual cutoff proof.  For each initial point, multiply the vector
field by a smooth nonnegative bump which is one on a sufficiently large ball.
The cutoff field is bounded and globally Lipschitz, hence has a global integral
curve.  The Lyapunov function is nonincreasing along this cutoff curve, so the
curve never reaches the region where the cutoff differs from one.  Its forward
half is therefore an integral curve of the original cubic field.
-/

namespace HomogeneousObstruction

open Filter Function Metric Set
open scoped Topology NNReal

noncomputable section

/-! ## A bounded globally Lipschitz field has global integral curves -/

/-- A family of compatible solutions on all symmetric bounded intervals can
be patched into a global integral curve.  This is the ordinary normed-space
counterpart of mathlib's manifold `UniformTime` construction. -/
theorem exists_global_integralCurve_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsIntegralCurve γ (fun _ ↦ f) := by
  have hlocal : ∀ a : ℝ, 0 < a → ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t ∈ Icc (-a) a,
        HasDerivWithinAt γ (f (γ t)) (Icc (-a) a) t := by
    intro a ha
    let t₀ : Icc (-a) a := ⟨0, by constructor <;> linarith⟩
    let A : ℝ≥0 := L * ⟨a, ha.le⟩
    have hPL : IsPicardLindelof (fun _ ↦ f) t₀ x₀ A 0 L K := by
      apply IsPicardLindelof.of_time_independent
      · intro x hx
        exact hL x
      · exact hK.lipschitzOnWith
      · change (L : ℝ) * max (a - 0) (0 - -a) ≤ (A : ℝ) - 0
        simp only [sub_zero, zero_sub, neg_neg, max_self]
        rfl
    simpa [t₀] using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let α : ℝ → ℝ → E := fun a ↦
    if ha : 0 < a then Classical.choose (hlocal a ha) else fun _ ↦ x₀
  have hα0 (a : ℝ) (ha : 0 < a) : α a 0 = x₀ := by
    simp only [α, dif_pos ha]
    exact (Classical.choose_spec (hlocal a ha)).1
  have hα (a : ℝ) (ha : 0 < a) : ∀ t ∈ Icc (-a) a,
      HasDerivWithinAt (α a) (f (α a t)) (Icc (-a) a) t := by
    simp only [α, dif_pos ha]
    exact (Classical.choose_spec (hlocal a ha)).2
  have hα_open (a : ℝ) (ha : 0 < a) :
      ∀ t ∈ Ioo (-a) a, HasDerivAt (α a) (f (α a t)) t := by
    intro t ht
    exact (hα a ha t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hcompat {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (α a) (α b) (Ioo (-a) a) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ ↦ f) (s := fun _ ↦ (univ : Set E))
      (K := K) (t₀ := 0)
    · intro t ht
      exact hK.lipschitzOnWith
    · exact ⟨by linarith, ha⟩
    · intro t ht
      exact ⟨hα_open a ha t ht, mem_univ _⟩
    · intro t ht
      have htb : t ∈ Ioo (-b) b :=
        ⟨lt_of_le_of_lt (neg_le_neg hab) ht.1, lt_of_lt_of_le ht.2 hab⟩
      exact ⟨hα_open b (lt_of_lt_of_le ha hab) t htb, mem_univ _⟩
    · rw [hα0 a ha, hα0 b (lt_of_lt_of_le ha hab)]
  let γ : ℝ → E := fun t ↦ α (|t| + 1) t
  refine ⟨γ, by simp [γ, hα0], ?_⟩
  intro t
  let a : ℝ := |t| + 1
  have ha : 0 < a := by positivity
  have ht : t ∈ Ioo (-a) a := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one |t|
  have heq : γ =ᶠ[𝓝 t] α a := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-a) a, Ioo_mem_nhds ht.1 ht.2, ?_⟩
    intro s hs
    change α (|s| + 1) s = α a s
    by_cases hle : |s| + 1 ≤ a
    · exact hcompat (by positivity) hle
        (by rw [mem_Ioo, ← abs_lt]; exact lt_add_one |s|)
    · exact (hcompat ha (le_of_not_ge hle)
        (by simpa [abs_lt] using hs)).symm
  exact (hα_open a ha t ht).congr_of_eventuallyEq heq

/-! ## Smooth compact cutoffs are globally Lipschitz -/

/-- A point on the segment from an inner point to an outer point meets the
sphere.  This elementary lemma is used only to pass from a Lipschitz estimate
on the support ball to a global estimate. -/
private theorem exists_segment_norm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {x y : E} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
    ∃ u ∈ Icc (0 : ℝ) 1, ‖(1 - u) • x + u • y‖ = R := by
  let q : ℝ → ℝ := fun u ↦ ‖(1 - u) • x + u • y‖
  have hq : Continuous q := by
    unfold q
    fun_prop
  have hR : R ∈ Icc (q 0) (q 1) := by
    simpa [q] using ⟨hx, hy⟩
  obtain ⟨u, hu, huR⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hq.continuousOn hR)
  exact ⟨u, hu, huR⟩

/-- A map that is Lipschitz on a closed ball and vanishes on and outside its
boundary is globally Lipschitz with the same constant. -/
theorem lipschitzWith_of_lipschitzOn_closedBall_of_zero_outside
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {R : ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K g (closedBall (0 : E) R))
    (hzero : ∀ x, R ≤ ‖x‖ → g x = 0) : LipschitzWith K g := by
  have hcross {x y : E} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
      dist (g x) (g y) ≤ (K : ℝ) * dist x y := by
    obtain ⟨u, hu, hzu⟩ := exists_segment_norm_eq hx hy
    let z : E := (1 - u) • x + u • y
    have hzmem : z ∈ closedBall (0 : E) R := by
      simp [mem_closedBall, dist_zero_right, z, hzu]
    have hxmem : x ∈ closedBall (0 : E) R := by
      simpa [mem_closedBall, dist_zero_right]
    have hgz : g z = 0 := hzero z (by simp [z, hzu])
    have hgy : g y = 0 := hzero y hy
    calc
      dist (g x) (g y) = dist (g x) (g z) := by rw [hgz, hgy]
      _ ≤ (K : ℝ) * dist x z := hK.dist_le_mul x hxmem z hzmem
      _ ≤ (K : ℝ) * dist x y := by
        gcongr
        rw [dist_eq_norm, dist_eq_norm]
        have hxy : x - z = u • (x - y) := by
          simp only [z]
          module
        rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hu.2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total ‖x‖ R with hx | hx
  · rcases le_total ‖y‖ R with hy | hy
    · exact hK.dist_le_mul x (by simpa [mem_closedBall, dist_zero_right]) y
        (by simpa [mem_closedBall, dist_zero_right])
    · exact hcross hx hy
  · rcases le_total ‖y‖ R with hy | hy
    · simpa only [dist_comm] using hcross hy hx
    · rw [hzero x hx, hzero y hy, dist_zero]
      simpa using mul_nonneg K.coe_nonneg (dist_nonneg : 0 ≤ dist x y)

/-- The explicit polynomial field is smooth. -/
theorem fieldValue_contDiff : ContDiff ℝ ⊤ fieldValue := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [fieldValue, evalAt_field₁, evalAt_field₂] <;> fun_prop

/-- Multiply the cubic field by a compactly supported smooth bump. -/
def cutoffField (b : ContDiffBump (0 : Point)) (z : Point) : Point :=
  b z • fieldValue z

theorem cutoffField_contDiff (b : ContDiffBump (0 : Point)) :
    ContDiff ℝ 1 (cutoffField b) := by
  have hb : ContDiff ℝ 1 (b : Point → ℝ) := b.contDiff (n := 1)
  have hf : ContDiff ℝ 1 fieldValue := fieldValue_contDiff.of_le (by norm_num)
  simpa [cutoffField, Pi.smul_apply] using hb.smul hf

theorem cutoffField_hasCompactSupport (b : ContDiffBump (0 : Point)) :
    HasCompactSupport (cutoffField b) := by
  apply b.hasCompactSupport.mono
  intro z hz
  show b z ≠ 0
  intro hb
  apply hz
  simp [cutoffField, hb]

theorem cutoffField_bounded (b : ContDiffBump (0 : Point)) :
    ∃ L : ℝ≥0, ∀ z, ‖cutoffField b z‖ ≤ L := by
  obtain ⟨C, hC⟩ :=
    (cutoffField_hasCompactSupport b).exists_bound_of_continuous
      (cutoffField_contDiff b).continuous
  have hC0 : 0 ≤ C := (norm_nonneg (cutoffField b 0)).trans (hC 0)
  exact ⟨⟨C, hC0⟩, hC⟩

theorem cutoffField_lipschitz (b : ContDiffBump (0 : Point)) :
    ∃ K : ℝ≥0, LipschitzWith K (cutoffField b) := by
  have hlocal : LocallyLipschitz (cutoffField b) :=
    ((cutoffField_contDiff b).of_le (by norm_num)).locallyLipschitz
  obtain ⟨K, hK⟩ := hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Point) b.rOut)
  refine ⟨K, lipschitzWith_of_lipschitzOn_closedBall_of_zero_outside hK ?_⟩
  intro z hz
  rw [cutoffField, b.zero_of_le_dist]
  · exact zero_smul _ _
  · simpa [dist_zero_right]

theorem cutoffField_exists_global_integralCurve
    (b : ContDiffBump (0 : Point)) (z₀ : Point) :
    ∃ γ : ℝ → Point, γ 0 = z₀ ∧
      IsIntegralCurve γ (fun _ ↦ cutoffField b) := by
  obtain ⟨K, hK⟩ := cutoffField_lipschitz b
  obtain ⟨L, hL⟩ := cutoffField_bounded b
  exact exists_global_integralCurve_of_lipschitz_bounded (cutoffField b) hK hL z₀

/-! ## The Lyapunov cutoff never activates in forward time -/

/-- A bump whose inner ball is large enough to contain the full Lyapunov
sublevel set through `z₀`.  The deliberately generous radius avoids square
roots in the continuation argument.  The bump uses `Point`'s ambient sup
norm; the explicit comparison with `radiusSquared` below bridges this to the
Euclidean norm used in the GAS statement. -/
def trajectoryCutoff (z₀ : Point) : ContDiffBump (0 : Point) where
  rIn := 2 * Real.exp 5 * stabilityCertificate z₀ + 1
  rOut := 2 * Real.exp 5 * stabilityCertificate z₀ + 2
  rIn_pos := by
    have hH := stabilityCertificate_nonneg z₀
    have he := Real.exp_pos 5
    nlinarith
  rIn_lt_rOut := by linarith

private theorem cutoff_certificate_comp_hasDerivAt
    (b : ContDiffBump (0 : Point)) {γ : ℝ → Point}
    (hγ : IsIntegralCurve γ (fun _ ↦ cutoffField b)) (t : ℝ) :
    HasDerivAt (fun s ↦ stabilityCertificate (γ s))
      (b (γ t) *
        (-2 * radiusSquared (γ t) * stabilityCertificate (γ t))) t := by
  have hH : HasFDerivAt stabilityCertificate
      (fderiv ℝ stabilityCertificate (γ t)) (γ t) :=
    (stabilityCertificate_contDiff_one_via_homogeneous_cone.differentiable
      (by norm_num) (γ t)).hasFDerivAt
  have hγt : HasDerivAt γ (cutoffField b (γ t)) t := by
    simpa using hγ t
  have hvalue :
    fderiv ℝ stabilityCertificate (γ t) (cutoffField b (γ t)) =
        b (γ t) *
          (-2 * radiusSquared (γ t) * stabilityCertificate (γ t)) := by
    calc
      fderiv ℝ stabilityCertificate (γ t) (cutoffField b (γ t)) =
          b (γ t) * functionLieDerivative stabilityCertificate (γ t) := by
        simp only [cutoffField, functionLieDerivative, map_smul, smul_eq_mul]
      _ = b (γ t) *
          (-2 * radiusSquared (γ t) * stabilityCertificate (γ t)) := by
        rw [functionLieDerivative_stabilityCertificate_all]
  rw [← hvalue]
  simpa only [Function.comp_def] using hH.comp_hasDerivAt t hγt

private theorem cutoff_certificate_comp_antitone
    (b : ContDiffBump (0 : Point)) {γ : ℝ → Point}
    (hγ : IsIntegralCurve γ (fun _ ↦ cutoffField b)) :
    Antitone (fun t ↦ stabilityCertificate (γ t)) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t ↦ cutoff_certificate_comp_hasDerivAt b hγ t)
  intro t
  have hb := b.nonneg' (γ t)
  have hr := radiusSquared_nonneg (γ t)
  have hH := stabilityCertificate_nonneg (γ t)
  have hprod : 0 ≤ b (γ t) *
      (radiusSquared (γ t) * stabilityCertificate (γ t)) := by positivity
  calc
    b (γ t) * (-2 * radiusSquared (γ t) * stabilityCertificate (γ t)) =
        -2 * (b (γ t) *
          (radiusSquared (γ t) * stabilityCertificate (γ t))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) hprod

/-- Along the cutoff trajectory starting at `z₀`, the cutoff is identically
one at every nonnegative time. -/
theorem trajectoryCutoff_eq_one
    {z₀ : Point} {γ : ℝ → Point}
    (hγ0 : γ 0 = z₀)
    (hγ : IsIntegralCurve γ (fun _ ↦ cutoffField (trajectoryCutoff z₀)))
    {t : ℝ} (ht : 0 ≤ t) : trajectoryCutoff z₀ (γ t) = 1 := by
  let b := trajectoryCutoff z₀
  have hanti := cutoff_certificate_comp_antitone b hγ
  have hHt : stabilityCertificate (γ t) ≤ stabilityCertificate z₀ := by
    rw [← hγ0]
    exact hanti ht
  have hlower := (stabilityCertificate_bounds_via_polar (γ t)).1
  have hexp : 0 < Real.exp 5 := Real.exp_pos _
  have hcancel : Real.exp 5 * Real.exp (-5) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hradius : radiusSquared (γ t) ≤
      Real.exp 5 * stabilityCertificate z₀ := by
    calc
      radiusSquared (γ t) =
          Real.exp 5 * (Real.exp (-5) * radiusSquared (γ t)) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp 5 * stabilityCertificate (γ t) :=
        mul_le_mul_of_nonneg_left hlower hexp.le
      _ ≤ Real.exp 5 * stabilityCertificate z₀ :=
        mul_le_mul_of_nonneg_left hHt hexp.le
  have hhalf := half_norm_sq_le_radiusSquared (γ t)
  have hnormsq : ‖γ t‖ ^ 2 ≤
      2 * Real.exp 5 * stabilityCertificate z₀ := by nlinarith
  have hA : 0 ≤ 2 * Real.exp 5 * stabilityCertificate z₀ := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _)))
      (stabilityCertificate_nonneg z₀)
  have hnormlt : ‖γ t‖ <
      2 * Real.exp 5 * stabilityCertificate z₀ + 1 := by
    nlinarith [sq_nonneg (‖γ t‖ - (1 / 2 : ℝ))]
  apply b.one_of_mem_closedBall
  simpa [b, trajectoryCutoff, mem_closedBall, dist_zero_right] using hnormlt.le

/-- Every initial condition of the explicit cubic field has a solution on the
whole forward time ray.  The construction uses a smooth compact cutoff only
as a continuation device; the preceding theorem proves that the cutoff never
changes the actual forward trajectory. -/
theorem forwardComplete_fieldValue : ForwardComplete fieldValue := by
  intro z₀
  obtain ⟨γ, hγ0, hγcut⟩ :=
    cutoffField_exists_global_integralCurve (trajectoryCutoff z₀) z₀
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  have hone := trajectoryCutoff_eq_one hγ0 hγcut ht
  have hderiv := (hγcut t).hasDerivWithinAt (s := Ici 0)
  simpa [cutoffField, hone] using hderiv

end

end HomogeneousObstruction
