import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Tactic

/-!
# Reusable definitions and quantitative lemmas for Lyapunov's direct method

This file contains the state-space-independent part of the global asymptotic
stability development.  Stability and attraction are parameterized by a
caller-supplied distance, so applications can use a norm different from the
ambient norm used to implement the state space.
-/

namespace HomogeneousObstruction

open Set

noncomputable section

/-- A trajectory beginning at `z₀` and solving an autonomous ODE for all
nonnegative times.  Values at negative times are immaterial. -/
def IsForwardTrajectory {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (γ : ℝ → E) (z₀ : E) : Prop :=
  γ 0 = z₀ ∧ IsIntegralCurveOn γ (fun _ => F) (Ici 0)

/-- Every initial state admits a trajectory on the whole forward time ray. -/
def ForwardComplete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) : Prop :=
  ∀ z₀ : E, ∃ γ : ℝ → E, IsForwardTrajectory F γ z₀

/-- Lyapunov stability measured by a caller-supplied state-space distance,
quantified over every forward trajectory of the vector field. -/
def LyapunovStableWith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (distance : E → E → ℝ) (F : E → E) (zEquil : E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z₀ : E, distance z₀ zEquil < δ →
        ∀ γ : ℝ → E, IsForwardTrajectory F γ z₀ →
          ∀ t : ℝ, 0 ≤ t → distance (γ t) zEquil < ε

/-- Global attractivity in epsilon--time form, again quantified over every
forward trajectory and measured by a caller-supplied distance. -/
def GloballyAttractiveWith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (distance : E → E → ℝ) (F : E → E) (zEquil : E) : Prop :=
  ∀ z₀ : E, ∀ γ : ℝ → E, IsForwardTrajectory F γ z₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → distance (γ t) zEquil < ε

/-- Global asymptotic stability: equilibrium, forward completeness,
Lyapunov stability, and global attractivity, all for a caller-supplied
distance. -/
def GloballyAsymptoticallyStableWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (distance : E → E → ℝ) (F : E → E) (zEquil : E) : Prop :=
  F zEquil = 0 ∧ ForwardComplete F ∧
    LyapunovStableWith distance F zEquil ∧
      GloballyAttractiveWith distance F zEquil

/-- Quadratic comparison bounds and monotonicity of a Lyapunov function imply
Lyapunov stability, for any caller-supplied nonnegative distance to the
equilibrium. -/
theorem lyapunovStableWith_of_quadratic_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (distance : E → E → ℝ) (F : E → E) (zEquil : E) (V : E → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hdist : ∀ z : E, 0 ≤ distance z zEquil)
    (hlower : ∀ z : E, distance z zEquil ^ 2 ≤ b * V z)
    (hupper : ∀ z : E, V z ≤ b * distance z zEquil ^ 2)
    (hanti : ∀ {z₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ z₀ →
      AntitoneOn (fun t ↦ V (γ t)) (Ici 0)) :
    LyapunovStableWith distance F zEquil := by
  intro ε hε
  refine ⟨ε / b, div_pos hε hb, ?_⟩
  intro z₀ hz₀ γ hγ t ht
  have hVt_le_V0 : V (γ t) ≤ V z₀ := by
    rw [← hγ.1]
    exact hanti hγ (by simp) ht ht
  have hdist_sq :
      distance (γ t) zEquil ^ 2 ≤ b ^ 2 * distance z₀ zEquil ^ 2 := by
    calc
      distance (γ t) zEquil ^ 2 ≤ b * V (γ t) := hlower (γ t)
      _ ≤ b * V z₀ := mul_le_mul_of_nonneg_left hVt_le_V0 hb.le
      _ ≤ b * (b * distance z₀ zEquil ^ 2) :=
        mul_le_mul_of_nonneg_left (hupper z₀) hb.le
      _ = b ^ 2 * distance z₀ zEquil ^ 2 := by ring
  have hb_dist_lt : b * distance z₀ zEquil < ε := by
    simpa [mul_comm] using (lt_div_iff₀ hb).mp hz₀
  have hb_dist_nonneg : 0 ≤ b * distance z₀ zEquil :=
    mul_nonneg hb.le (hdist z₀)
  have hsq_lt : (b * distance z₀ zEquil) ^ 2 < ε ^ 2 :=
    (sq_lt_sq₀ hb_dist_nonneg hε.le).mpr hb_dist_lt
  have htarget_sq : distance (γ t) zEquil ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt hdist_sq ?_
    simpa [mul_pow] using hsq_lt
  exact (sq_lt_sq₀ (hdist (γ t)) hε.le).mp htarget_sq

/-- A positive quadratic lower bound and eventual entry into every positive
Lyapunov sublevel imply global attractivity, for any caller-supplied
nonnegative distance to the equilibrium. -/
theorem globallyAttractiveWith_of_lower_quadratic_of_eventually_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (distance : E → E → ℝ) (F : E → E) (zEquil : E) (V : E → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hdist : ∀ z : E, 0 ≤ distance z zEquil)
    (hlower : ∀ z : E, c * distance z zEquil ^ 2 ≤ V z)
    (heventually : ∀ {z₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ z₀ →
      ∀ η : ℝ, 0 < η →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → V (γ t) < η) :
    GloballyAttractiveWith distance F zEquil := by
  intro z₀ γ hγ ε hε
  obtain ⟨T, hT, hafter⟩ := heventually hγ (c * ε ^ 2)
    (mul_pos hc (sq_pos_of_pos hε))
  refine ⟨T, hT, ?_⟩
  intro t hTt
  have hscaled : c * distance (γ t) zEquil ^ 2 < c * ε ^ 2 :=
    lt_of_le_of_lt (hlower (γ t)) (hafter t hTt)
  have hdist_sq : distance (γ t) zEquil ^ 2 < ε ^ 2 :=
    lt_of_mul_lt_mul_left hscaled hc.le
  exact (sq_lt_sq₀ (hdist (γ t)) hε.le).mp hdist_sq

/-- A nonnegative, nonincreasing scalar quantity must eventually enter every
level above which its derivative has a fixed negative upper bound.  This is
the one-dimensional finite-entry argument in the textbook Lyapunov proof. -/
theorem eventually_lt_of_antitoneOn_of_hasDerivAt_le
    {h : ℝ → ℝ} {d η : ℝ}
    (hcont : ContinuousOn h (Ici 0))
    (hanti : AntitoneOn h (Ici 0))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ h t)
    (hd : 0 < d)
    (hderiv : ∀ t : ℝ, 0 < t → η ≤ h t →
      ∃ h' : ℝ, HasDerivAt h h' t ∧ h' ≤ -d) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → h t < η := by
  let T : ℝ := h 0 / d + 1
  have hTpos : 0 < T := by
    dsimp [T]
    have hquot_nonneg : 0 ≤ h 0 / d :=
      div_nonneg (hnonneg 0 le_rfl) hd.le
    linarith
  have hTlt : h T < η := by
    by_contra hnot
    have hηT : η ≤ h T := le_of_not_gt hnot
    let q : ℝ → ℝ := fun t ↦ h t + d * t
    have hhcontIcc : ContinuousOn h (Icc 0 T) :=
      hcont.mono (fun _ ht ↦ ht.1)
    have hqcont : ContinuousOn q (Icc 0 T) := by
      have hlinear : ContinuousOn (fun t : ℝ ↦ d * t) (Icc 0 T) := by
        fun_prop
      exact hhcontIcc.add hlinear
    have hqanti : AntitoneOn q (Icc 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hqcont
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by
          simpa [interior_Icc] using ht
        obtain ⟨h', hhderiv, _hh'le⟩ :=
          hderiv t htIoo.1
            (le_trans hηT
              (hanti htIoo.1.le hTpos.le htIoo.2.le))
        have hlinderiv : HasDerivAt (fun s : ℝ ↦ d * s) d t := by
          simpa using (hasDerivAt_id t).const_mul d
        exact (hhderiv.add hlinderiv).differentiableAt.differentiableWithinAt
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by
          simpa [interior_Icc] using ht
        obtain ⟨h', hhderiv, hh'le⟩ :=
          hderiv t htIoo.1
            (le_trans hηT
              (hanti htIoo.1.le hTpos.le htIoo.2.le))
        have hlinderiv : HasDerivAt (fun s : ℝ ↦ d * s) d t := by
          simpa using (hasDerivAt_id t).const_mul d
        have hqderiv : HasDerivAt q (h' + d) t :=
          hhderiv.add hlinderiv
        rw [hqderiv.deriv]
        linarith
    have hq0T : q T ≤ q 0 :=
      hqanti ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩ hTpos.le
    have hdT : d * T = h 0 + d := by
      dsimp [T]
      field_simp [ne_of_gt hd]
    have hnegative : h T < 0 := by
      dsimp [q] at hq0T
      rw [hdT] at hq0T
      linarith
    exact (not_lt_of_ge (hnonneg T hTpos.le)) hnegative
  refine ⟨T, hTpos.le, ?_⟩
  intro t hTt
  have htle : h t ≤ h T :=
    hanti hTpos.le (le_trans hTpos.le hTt) hTt
  exact lt_of_le_of_lt htle hTlt

end

end HomogeneousObstruction
