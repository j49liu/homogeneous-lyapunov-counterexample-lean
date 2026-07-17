import HomogeneousObstruction.AnalyticLeadingTerm
import HomogeneousObstruction.LeadingTermPositivity
import HomogeneousObstruction.Obstruction

/-!
# Main theorem item (4): local real-analytic obstruction

The exported statement explicitly quantifies an open neighbourhood `U` of the
origin, requires `V` to be analytic throughout `U`, and requires the Euclidean
ball on which the inequalities are imposed to lie in `U`.  Lean represents a
function on `U` by a total representative `V : Point → ℝ`; every condition is
local to `U`, so values of that representative outside `U` are irrelevant.

The proof follows the manuscript's subsection "Non-existence of Local
Real-Analytic Lyapunov Functions": extract the first nonzero homogeneous
Taylor term, pass the two local inequalities to it along rays, use the
integrating factor to prove that it is positive definite, and contradict main
theorem item (3).
-/

namespace HomogeneousObstruction

noncomputable section

/-- The open Euclidean ball about the origin used in item (4). -/
def euclideanBall (rho : ℝ) : Set Point :=
  {z | euclideanNorm z < rho}

@[simp] theorem mem_euclideanBall {rho : ℝ} {z : Point} :
    z ∈ euclideanBall rho ↔ euclideanNorm z < rho :=
  Iff.rfl

/-- The local conditions displayed in main theorem item (4), including the
radius and its strict positivity. -/
def LocalAnalyticLyapunovConditions (V : Point → ℝ) (ρ : ℝ) : Prop :=
  AnalyticAt ℝ V 0 ∧
    V 0 = 0 ∧
    0 < ρ ∧
    (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) ∧
    (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
      functionLieDerivative V z ≤ 0)

/-- No local real-analytic Lyapunov germ satisfies the displayed conditions
of main theorem item (4). -/
theorem no_localAnalyticLyapunov
    (V : Point → ℝ) (ρ : ℝ) :
    ¬ LocalAnalyticLyapunovConditions V ρ := by
  rintro ⟨hV, hV0, hρ, hpos, hlie⟩
  obtain ⟨m, P, hm, hhom, hP_ne, hnonneg, hLP⟩ :=
    exists_leadingHomogeneousPolynomial hV hV0 hρ hpos hlie
  have hpd : PositiveDefinite P :=
    positiveDefinite_of_nonnegative_of_lieNonpositive
      hhom hm hP_ne hnonneg hLP
  exact no_positiveDefinite_homogeneous_polynomial P ⟨m, hhom⟩ hpd hLP

/-- Germ-level strengthening used internally: analyticity is required only at
the origin.  `AnalyticAt` nevertheless supplies an actual power-series
neighbourhood, and the radius can be shrunk to that neighbourhood. -/
theorem mainTheorem_item4_germ :
    ¬ ∃ (V : Point → ℝ) (ρ : ℝ),
      AnalyticAt ℝ V 0 ∧
        V 0 = 0 ∧
        0 < ρ ∧
        (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) ∧
        (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
          functionLieDerivative V z ≤ 0) := by
  rintro ⟨V, ρ, h⟩
  exact no_localAnalyticLyapunov V ρ h

/-- The neighbourhood-explicit conditions in main theorem item (4).  A total
representative is used for `V`, but only its restriction to `U` is relevant. -/
def LocalAnalyticLyapunovOn
    (U : Set Point) (V : Point → ℝ) (ρ : ℝ) : Prop :=
  IsOpen U ∧
    0 ∈ U ∧
    AnalyticOnNhd ℝ V U ∧
    0 < ρ ∧
    euclideanBall ρ ⊆ U ∧
    V 0 = 0 ∧
    (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) ∧
    (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
      functionLieDerivative V z ≤ 0)

theorem no_localAnalyticLyapunovOn
    (U : Set Point) (V : Point → ℝ) (ρ : ℝ) :
    ¬ LocalAnalyticLyapunovOn U V ρ := by
  rintro ⟨_hU, h0U, hV, hρ, _hball, hV0, hpos, hlie⟩
  exact no_localAnalyticLyapunov V ρ
    ⟨hV 0 h0U, hV0, hρ, hpos, hlie⟩

/-- Main theorem item (4), literally exposing the neighbourhood quantified in
the manuscript: no real-analytic function on any open neighbourhood of the
origin satisfies the three displayed local conditions for any positive
Euclidean radius contained in its domain. -/
theorem mainTheorem_item4 :
    ¬ ∃ (U : Set Point) (V : Point → ℝ) (ρ : ℝ),
      IsOpen U ∧
        0 ∈ U ∧
        AnalyticOnNhd ℝ V U ∧
        0 < ρ ∧
        euclideanBall ρ ⊆ U ∧
        V 0 = 0 ∧
        (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) ∧
        (∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
          functionLieDerivative V z ≤ 0) := by
  rintro ⟨U, V, ρ, h⟩
  exact no_localAnalyticLyapunovOn U V ρ h

#print axioms mainTheorem_item4

end

end HomogeneousObstruction
