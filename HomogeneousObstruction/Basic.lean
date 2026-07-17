import Mathlib

namespace HomogeneousObstruction

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev Point := Fin 2 → ℝ
abbrev BivariatePolynomial := MvPolynomial (Fin 2) ℝ

/-- The first coordinate polynomial. -/
def X₀ : BivariatePolynomial := X 0

/-- The second coordinate polynomial. -/
def X₁ : BivariatePolynomial := X 1

/-- First component of the cubic vector field in (2.1) of the paper. -/
def field₁ : BivariatePolynomial :=
  4 * X₀ ^ 3 - X₀ ^ 2 * X₁ - 6 * X₀ * X₁ ^ 2 - X₁ ^ 3

/-- Second component of the cubic vector field in (2.2) of the paper. -/
def field₂ : BivariatePolynomial :=
  X₀ ^ 3 + 4 * X₀ ^ 2 * X₁ + X₀ * X₁ ^ 2 - 6 * X₁ ^ 3

/-- The explicit cubic vector field from the main theorem. -/
def vectorField : Fin 2 → BivariatePolynomial := ![field₁, field₂]

/-- Evaluation of a bivariate polynomial at a point of `ℝ²`. -/
def evalAt (P : BivariatePolynomial) (z : Point) : ℝ := eval z P

/-- Positive definiteness, including the required value at the origin. -/
def PositiveDefinite (P : BivariatePolynomial) : Prop :=
  evalAt P 0 = 0 ∧ ∀ z : Point, z ≠ 0 → 0 < evalAt P z

/-- A polynomial is homogeneous when it is homogeneous of some (initially unrestricted) degree. -/
def Homogeneous (P : BivariatePolynomial) : Prop :=
  ∃ n : ℕ, P.IsHomogeneous n

/-- Polynomial Lie derivative along the explicit cubic field, defined using `pderiv`. -/
def lieDerivative (P : BivariatePolynomial) : BivariatePolynomial :=
  ∑ i : Fin 2, pderiv i P * vectorField i

/-- The weak Lie-derivative inequality in main theorem item (3), at every point of `ℝ²`. -/
def LieNonpositive (P : BivariatePolynomial) : Prop :=
  ∀ z : Point, evalAt (lieDerivative P) z ≤ 0

@[simp] theorem evalAt_X₀ (z : Point) : evalAt X₀ z = z 0 := by
  simp [evalAt, X₀]

@[simp] theorem evalAt_X₁ (z : Point) : evalAt X₁ z = z 1 := by
  simp [evalAt, X₁]

@[simp] theorem evalAt_field₁ (z : Point) :
    evalAt field₁ z = 4 * z 0 ^ 3 - z 0 ^ 2 * z 1 - 6 * z 0 * z 1 ^ 2 - z 1 ^ 3 := by
  simp [evalAt, field₁, X₀, X₁]

@[simp] theorem evalAt_field₂ (z : Point) :
    evalAt field₂ z = z 0 ^ 3 + 4 * z 0 ^ 2 * z 1 + z 0 * z 1 ^ 2 - 6 * z 1 ^ 3 := by
  simp [evalAt, field₂, X₀, X₁]

theorem field₁_isHomogeneous : field₁.IsHomogeneous 3 := by
  have hx : X₀.IsHomogeneous 1 := by simpa [X₀] using isHomogeneous_X ℝ (0 : Fin 2)
  have hy : X₁.IsHomogeneous 1 := by simpa [X₁] using isHomogeneous_X ℝ (1 : Fin 2)
  have h₁ : (4 * X₀ ^ 3).IsHomogeneous 3 := by
    simpa using (hx.pow 3).C_mul (4 : ℝ)
  have h₂ : (X₀ ^ 2 * X₁).IsHomogeneous 3 := by
    simpa using (hx.pow 2).mul hy
  have h₃ : (6 * X₀ * X₁ ^ 2).IsHomogeneous 3 := by
    simpa [mul_assoc] using (hx.mul (hy.pow 2)).C_mul (6 : ℝ)
  have h₄ : (X₁ ^ 3).IsHomogeneous 3 := by simpa using hy.pow 3
  exact ((h₁.sub h₂).sub h₃).sub h₄

theorem field₂_isHomogeneous : field₂.IsHomogeneous 3 := by
  have hx : X₀.IsHomogeneous 1 := by simpa [X₀] using isHomogeneous_X ℝ (0 : Fin 2)
  have hy : X₁.IsHomogeneous 1 := by simpa [X₁] using isHomogeneous_X ℝ (1 : Fin 2)
  have h₁ : (X₀ ^ 3).IsHomogeneous 3 := by simpa using hx.pow 3
  have h₂ : (4 * X₀ ^ 2 * X₁).IsHomogeneous 3 := by
    simpa [mul_assoc] using ((hx.pow 2).mul hy).C_mul (4 : ℝ)
  have h₃ : (X₀ * X₁ ^ 2).IsHomogeneous 3 := by
    simpa using hx.mul (hy.pow 2)
  have h₄ : (6 * X₁ ^ 3).IsHomogeneous 3 := by
    simpa using (hy.pow 3).C_mul (6 : ℝ)
  exact ((h₁.add h₂).add h₃).sub h₄

theorem vectorField_isHomogeneous (i : Fin 2) : (vectorField i).IsHomogeneous 3 := by
  fin_cases i <;> simp [vectorField, field₁_isHomogeneous, field₂_isHomogeneous]

/-- Analytic chain rule for a bivariate polynomial along a differentiable curve. -/
theorem eval_hasDerivAt (P : BivariatePolynomial)
    (γ : Fin 2 → ℝ → ℝ) (dγ : Fin 2 → ℝ) (t : ℝ)
    (hγ : ∀ i, HasDerivAt (γ i) (dγ i) t) :
    HasDerivAt (fun s => evalAt P (fun i => γ i s))
      (∑ i : Fin 2, evalAt (pderiv i P) (fun j => γ j t) * dγ i) t := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa [evalAt, MvPolynomial.pderiv_C] using hasDerivAt_const (x := t) (c := a)
  | add p q hp hq =>
      simpa [evalAt, map_add, add_mul, Finset.sum_add_distrib] using hp.add hq
  | mul_X p n hp =>
      have hh := hp.mul (hγ n)
      fin_cases n
      all_goals
        convert hh using 1
        · ext s
          simp [evalAt]
        · simp [evalAt, Finset.univ_fin2, add_mul]
          ring

/-- Standard parametrisation of the unit circle. -/
def circlePoint (θ : ℝ) : Point := ![Real.cos θ, Real.sin θ]

@[simp] theorem circlePoint_zero (θ : ℝ) : circlePoint θ 0 = Real.cos θ := by
  simp [circlePoint]

@[simp] theorem circlePoint_one (θ : ℝ) : circlePoint θ 1 = Real.sin θ := by
  simp [circlePoint]

/-- Derivative of `circlePoint`. -/
def circleTangent (θ : ℝ) : Point := ![-Real.sin θ, Real.cos θ]

/-- Restriction of a bivariate polynomial to the unit circle. -/
def circleTrace (P : BivariatePolynomial) (θ : ℝ) : ℝ :=
  evalAt P (circlePoint θ)

/-- Algebraic angular derivative of a circle trace. -/
def circleTraceDerivative (P : BivariatePolynomial) (θ : ℝ) : ℝ :=
  ∑ i : Fin 2, evalAt (pderiv i P) (circlePoint θ) * circleTangent θ i

/-- The radial coefficient `-1 + 5 cos(2θ)` in the polar form of the field. -/
def radialCoefficient (θ : ℝ) : ℝ := -1 + 5 * Real.cos (2 * θ)

theorem circleTrace_hasDerivAt (P : BivariatePolynomial) (θ : ℝ) :
    HasDerivAt (circleTrace P) (circleTraceDerivative P θ) θ := by
  apply eval_hasDerivAt P (fun i t => circlePoint t i) (circleTangent θ) θ
  intro i
  fin_cases i
  · simpa [circlePoint, circleTangent] using Real.hasDerivAt_cos θ
  · simpa [circlePoint, circleTangent] using Real.hasDerivAt_sin θ

theorem circleTrace_differentiable (P : BivariatePolynomial) : Differentiable ℝ (circleTrace P) :=
  fun θ => (circleTrace_hasDerivAt P θ).differentiableAt

theorem circlePoint_ne_zero (θ : ℝ) : circlePoint θ ≠ 0 := by
  intro h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp only [circlePoint_zero, Pi.zero_apply] at h₀
  simp only [circlePoint_one, Pi.zero_apply] at h₁
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem PositiveDefinite.circleTrace_pos {P : BivariatePolynomial}
    (hP : PositiveDefinite P) (θ : ℝ) : 0 < circleTrace P θ :=
  hP.2 (circlePoint θ) (circlePoint_ne_zero θ)

theorem circlePoint_periodic : Function.Periodic circlePoint (2 * Real.pi) := by
  intro θ
  funext i
  fin_cases i
  · exact Real.cos_add_two_pi θ
  · exact Real.sin_add_two_pi θ

theorem circleTrace_periodic (P : BivariatePolynomial) :
    Function.Periodic (circleTrace P) (2 * Real.pi) := by
  intro θ
  simp only [circleTrace, circlePoint_periodic θ]

theorem circleTrace_continuous (P : BivariatePolynomial) : Continuous (circleTrace P) :=
  (circleTrace_differentiable P).continuous

theorem circleTraceDerivative_eq (P : BivariatePolynomial) (θ : ℝ) :
    circleTraceDerivative P θ =
      -Real.sin θ * circleTrace (pderiv 0 P) θ +
        Real.cos θ * circleTrace (pderiv 1 P) θ := by
  simp [circleTraceDerivative, Fin.sum_univ_two, circleTangent, circleTrace]
  ring

theorem circleTraceDerivative_continuous (P : BivariatePolynomial) :
    Continuous (circleTraceDerivative P) := by
  rw [show circleTraceDerivative P = fun θ =>
      -Real.sin θ * circleTrace (pderiv 0 P) θ +
        Real.cos θ * circleTrace (pderiv 1 P) θ by
    funext θ
    exact circleTraceDerivative_eq P θ]
  exact (Real.continuous_sin.neg.mul (circleTrace_continuous _)).add
    (Real.continuous_cos.mul (circleTrace_continuous _))

theorem circleTraceDerivative_periodic (P : BivariatePolynomial) :
    Function.Periodic (circleTraceDerivative P) (2 * Real.pi) := by
  intro θ
  rw [circleTraceDerivative_eq, circleTraceDerivative_eq]
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  rw [circleTrace_periodic (pderiv 0 P) θ, circleTrace_periodic (pderiv 1 P) θ]

/-- Euler's identity evaluated at a point. -/
theorem euler_eval {P : BivariatePolynomial} {n : ℕ} (hP : P.IsHomogeneous n) (z : Point) :
    ∑ i : Fin 2, z i * evalAt (pderiv i P) z = n * evalAt P z := by
  have h := congrArg (eval z) hP.sum_X_mul_pderiv
  simpa [evalAt, map_sum, nsmul_eq_mul] using h

theorem field₁_on_circle (θ : ℝ) :
    evalAt field₁ (circlePoint θ) =
      radialCoefficient θ * Real.cos θ - Real.sin θ := by
  rw [evalAt_field₁]
  simp only [circlePoint, Matrix.cons_val_zero, Matrix.cons_val_one, radialCoefficient,
    Real.cos_two_mul]
  have hunit : 1 - Real.cos θ ^ 2 - Real.sin θ ^ 2 = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    4 * Real.cos θ ^ 3 - Real.cos θ ^ 2 * Real.sin θ -
          6 * Real.cos θ * Real.sin θ ^ 2 - Real.sin θ ^ 3 =
        (-1 + 5 * (2 * Real.cos θ ^ 2 - 1)) * Real.cos θ - Real.sin θ +
          (6 * Real.cos θ + Real.sin θ) *
            (1 - Real.cos θ ^ 2 - Real.sin θ ^ 2) := by ring
    _ = (-1 + 5 * (2 * Real.cos θ ^ 2 - 1)) * Real.cos θ - Real.sin θ := by
      rw [hunit]
      ring

theorem field₂_on_circle (θ : ℝ) :
    evalAt field₂ (circlePoint θ) =
      radialCoefficient θ * Real.sin θ + Real.cos θ := by
  rw [evalAt_field₂]
  simp only [circlePoint, Matrix.cons_val_zero, Matrix.cons_val_one, radialCoefficient,
    Real.cos_two_mul]
  have hunit : Real.cos θ ^ 2 + Real.sin θ ^ 2 - 1 = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    Real.cos θ ^ 3 + 4 * Real.cos θ ^ 2 * Real.sin θ +
          Real.cos θ * Real.sin θ ^ 2 - 6 * Real.sin θ ^ 3 =
        (-1 + 5 * (2 * Real.cos θ ^ 2 - 1)) * Real.sin θ + Real.cos θ +
          (Real.cos θ - 6 * Real.sin θ) *
            (Real.cos θ ^ 2 + Real.sin θ ^ 2 - 1) := by ring
    _ = (-1 + 5 * (2 * Real.cos θ ^ 2 - 1)) * Real.sin θ + Real.cos θ := by
      rw [hunit]
      ring

theorem evalAt_lieDerivative (P : BivariatePolynomial) (z : Point) :
    evalAt (lieDerivative P) z =
      evalAt (pderiv 0 P) z * evalAt field₁ z +
      evalAt (pderiv 1 P) z * evalAt field₂ z := by
  simp [lieDerivative, evalAt, vectorField, Finset.univ_fin2]

/-- Polar identity (4.2) at radius one, obtained from the chain rule and Euler's identity. -/
theorem lieDerivative_on_circle {P : BivariatePolynomial} {n : ℕ}
    (hP : P.IsHomogeneous n) (θ : ℝ) :
    evalAt (lieDerivative P) (circlePoint θ) =
      circleTraceDerivative P θ + n * radialCoefficient θ * circleTrace P θ := by
  rw [evalAt_lieDerivative, field₁_on_circle, field₂_on_circle]
  have he := euler_eval hP (circlePoint θ)
  simp only [Fin.sum_univ_two, circlePoint_zero, circlePoint_one] at he
  simp only [circleTraceDerivative, Fin.sum_univ_two, circleTangent, Matrix.cons_val_zero,
    Matrix.cons_val_one, circleTrace]
  calc
    evalAt ((pderiv 0) P) (circlePoint θ) *
          (radialCoefficient θ * Real.cos θ - Real.sin θ) +
        evalAt ((pderiv 1) P) (circlePoint θ) *
          (radialCoefficient θ * Real.sin θ + Real.cos θ) =
      evalAt ((pderiv 0) P) (circlePoint θ) * (-Real.sin θ) +
        evalAt ((pderiv 1) P) (circlePoint θ) * Real.cos θ +
        radialCoefficient θ *
          (Real.cos θ * evalAt ((pderiv 0) P) (circlePoint θ) +
           Real.sin θ * evalAt ((pderiv 1) P) (circlePoint θ)) := by ring
    _ = evalAt ((pderiv 0) P) (circlePoint θ) * (-Real.sin θ) +
          evalAt ((pderiv 1) P) (circlePoint θ) * Real.cos θ +
          n * radialCoefficient θ * evalAt P (circlePoint θ) := by
      rw [he]
      ring

end

end HomogeneousObstruction
