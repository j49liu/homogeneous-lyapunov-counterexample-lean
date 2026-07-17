import HomogeneousObstruction.StabilityCertificateCalculus

/-!
# Calculus bridges for the local analytic obstruction

This file records two elementary facts used when passing between the
function-level and polynomial formulations of the vector field.  The first is
the cubic scaling of the explicit homogeneous field.  The second identifies
the Fréchet-derivative definition of the function-level Lie derivative with
the `MvPolynomial.pderiv` definition for a polynomial function.
-/

namespace HomogeneousObstruction

noncomputable section

/-- The Euclidean norm used by the manuscript.  `Point` is implemented as a
finite function type, whose inherited mathlib norm is the product norm, so we
name the manuscript's `sqrt (x²+y²)` explicitly in the item-(4) statement. -/
def euclideanNorm (z : Point) : ℝ :=
  Real.sqrt (radiusSquared z)

@[simp] theorem euclideanNorm_zero : euclideanNorm 0 = 0 := by
  simp [euclideanNorm, radiusSquared]

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

/-- The evaluated cubic vector field scales with degree three. -/
theorem fieldValue_smul (a : ℝ) (z : Point) :
    fieldValue (a • z) = a ^ 3 • fieldValue z := by
  funext i
  fin_cases i
  · change evalAt field₁ (a • z) = a ^ 3 * evalAt field₁ z
    simp only [evalAt_field₁, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · change evalAt field₂ (a • z) = a ^ 3 * evalAt field₂ z
    simp only [evalAt_field₂, Pi.smul_apply, smul_eq_mul]
    ring_nf

/-- Evaluation of a multivariate polynomial is Fréchet differentiable. -/
private theorem evalAt_differentiable (P : BivariatePolynomial) :
    Differentiable ℝ (fun z : Point => evalAt P z) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [evalAt]
  | add P Q hP hQ =>
      simpa [evalAt] using hP.add hQ
  | mul_X P i hP =>
      simpa [evalAt] using hP.mul (differentiable_apply i)

/-- The affine line through `z` in direction `v`. -/
private def polynomialAffineLine (z v : Point) (t : ℝ) : Point :=
  fun i => z i + t * v i

private theorem polynomialAffineLine_hasDerivAt (z v : Point) :
    HasDerivAt (polynomialAffineLine z v) v 0 := by
  rw [hasDerivAt_pi]
  intro i
  convert (hasDerivAt_const (x := 0) (c := z i)).add
    ((hasDerivAt_id 0).mul_const (v i)) using 1
  all_goals simp

@[simp] private theorem polynomialAffineLine_zero (z v : Point) :
    polynomialAffineLine z v 0 = z := by
  funext i
  simp [polynomialAffineLine]

/-- Directional form of the standard gradient formula for a multivariate
polynomial, expressed using `MvPolynomial.pderiv`. -/
theorem fderiv_evalAt_apply (P : BivariatePolynomial) (z v : Point) :
    fderiv ℝ (fun w : Point => evalAt P w) z v =
      ∑ i : Fin 2, evalAt (MvPolynomial.pderiv i P) z * v i := by
  have hoff : DifferentiableAt ℝ (fun w : Point => evalAt P w)
      (polynomialAffineLine z v 0) := by
    rw [polynomialAffineLine_zero]
    exact evalAt_differentiable P z
  have hchain := hoff.hasFDerivAt.comp_hasDerivAt 0
    (polynomialAffineLine_hasDerivAt z v)
  have hdirect := eval_hasDerivAt P
    (fun i t => polynomialAffineLine z v t i) v 0 (by
      intro i
      exact hasDerivAt_pi.mp (polynomialAffineLine_hasDerivAt z v) i)
  have heq := hchain.unique hdirect
  rw [polynomialAffineLine_zero] at heq
  simpa [Function.comp_def] using heq

/-- For a polynomial function, the function-level Lie derivative defined via
the Fréchet derivative agrees exactly with the polynomial Lie derivative
defined via `MvPolynomial.pderiv`. -/
theorem functionLieDerivative_evalAt (P : BivariatePolynomial) (z : Point) :
    functionLieDerivative (fun w : Point => evalAt P w) z =
      evalAt (lieDerivative P) z := by
  rw [functionLieDerivative, fderiv_evalAt_apply, evalAt_lieDerivative]
  simp only [Fin.sum_univ_two, fieldValue, Matrix.cons_val_zero, Matrix.cons_val_one]

end

end HomogeneousObstruction
