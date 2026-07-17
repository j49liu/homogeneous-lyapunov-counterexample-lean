import HomogeneousObstruction.Degree
import HomogeneousObstruction.FejerRiesz

namespace HomogeneousObstruction

open scoped BigOperators ComplexConjugate Polynomial Matrix
open Complex Polynomial MvPolynomial

noncomputable section

/-!
# The half-angle circle polynomial

For a homogeneous polynomial `P` of degree `2 * N`, the paper applies
Fejer--Riesz to the half-angle trace

`q(phi) = P (cos (phi / 2), sin (phi / 2))`.

The ordinary polynomial below is the Laurent numerator associated to `q`:

`P_C ((z + 1) / 2, (z - 1) / (2 I))`.

At `z = exp (I * phi)` it evaluates to `z ^ N * q phi`.  Thus its padded
Laurent centre is `N`, rather than `2 * N` as in the direct circle
substitution.
-/

/-- The half-angle trace `q(phi) = p(phi / 2)` used in Lemma 5.2. -/
def halfAngleTrace (P : BivariatePolynomial) (phi : ℝ) : ℝ :=
  circleTrace P (phi / 2)

/-- The derivative of the half-angle trace. -/
def halfAngleTraceDerivative (P : BivariatePolynomial) (phi : ℝ) : ℝ :=
  circleTraceDerivative P (phi / 2) / 2

@[simp] theorem halfAngleTrace_two_mul (P : BivariatePolynomial) (theta : ℝ) :
    halfAngleTrace P (2 * theta) = circleTrace P theta := by
  simp [halfAngleTrace]

@[simp] theorem halfAngleTraceDerivative_two_mul
    (P : BivariatePolynomial) (theta : ℝ) :
    halfAngleTraceDerivative P (2 * theta) =
      circleTraceDerivative P theta / 2 := by
  simp [halfAngleTraceDerivative]

theorem two_mul_halfAngleTraceDerivative_two_mul
    (P : BivariatePolynomial) (theta : ℝ) :
    2 * halfAngleTraceDerivative P (2 * theta) =
      circleTraceDerivative P theta := by
  rw [halfAngleTraceDerivative_two_mul]
  ring

theorem halfAngleTrace_hasDerivAt (P : BivariatePolynomial) (phi : ℝ) :
    HasDerivAt (halfAngleTrace P) (halfAngleTraceDerivative P phi) phi := by
  have hinner : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) phi := by
    simpa using (hasDerivAt_id phi).div_const (2 : ℝ)
  have h := (circleTrace_hasDerivAt P (phi / 2)).scomp phi hinner
  change HasDerivAt (fun t => circleTrace P (t / 2))
    (circleTraceDerivative P (phi / 2) / 2) phi
  convert h using 1
  ring

theorem halfAngleTrace_continuous (P : BivariatePolynomial) :
    Continuous (halfAngleTrace P) := by
  exact continuous_iff_continuousAt.mpr fun phi =>
    (halfAngleTrace_hasDerivAt P phi).continuousAt

theorem halfAngleTraceDerivative_continuous (P : BivariatePolynomial) :
    Continuous (halfAngleTraceDerivative P) := by
  simpa [halfAngleTraceDerivative] using
    ((circleTraceDerivative_continuous P).comp (by fun_prop)).div_const (2 : ℝ)

theorem PositiveDefinite.halfAngleTrace_pos {P : BivariatePolynomial}
    (hP : PositiveDefinite P) (phi : ℝ) :
    0 < halfAngleTrace P phi := by
  exact hP.circleTrace_pos (phi / 2)

/-- Even homogeneity makes the half-angle trace `2 * pi`-periodic. -/
theorem halfAngleTrace_periodic {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) :
    Function.Periodic (halfAngleTrace P) (2 * Real.pi) := by
  have hp := circleTrace_pi_periodic_of_evenDegree hP
  simpa [halfAngleTrace, mul_comm, mul_left_comm, mul_assoc] using hp.div_const (2 : ℝ)

/-- The derivative of the half-angle trace has the same `2 * pi` period. -/
theorem halfAngleTraceDerivative_periodic {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) :
    Function.Periodic (halfAngleTraceDerivative P) (2 * Real.pi) := by
  intro phi
  have hfun :
      (fun t => halfAngleTrace P (t + 2 * Real.pi)) = halfAngleTrace P := by
    funext t
    exact halfAngleTrace_periodic hP t
  have hshift := (halfAngleTrace_hasDerivAt P (phi + 2 * Real.pi)).comp_add_const
    phi (2 * Real.pi)
  rw [hfun] at hshift
  exact hshift.unique (halfAngleTrace_hasDerivAt P phi)

/-- The numerator `(z + 1) / 2` in the half-angle substitution. -/
def halfAngleCosPolynomial : ℂ[X] :=
  Polynomial.C ((2 : ℂ)⁻¹) * (Polynomial.X + 1)

/-- The numerator `(z - 1) / (2 I)` in the half-angle substitution. -/
def halfAngleSinPolynomial : ℂ[X] :=
  Polynomial.C ((2 * I : ℂ)⁻¹) * (Polynomial.X - 1)

/-- The two polynomial coordinates in the half-angle substitution. -/
def halfAngleSubstitution : Fin 2 → ℂ[X] :=
  ![halfAngleCosPolynomial, halfAngleSinPolynomial]

/-- The cleared ordinary polynomial associated to the half-angle trace. -/
def halfAnglePolynomial (P : BivariatePolynomial) : ℂ[X] :=
  MvPolynomial.eval₂ Polynomial.C halfAngleSubstitution
    (MvPolynomial.map Complex.ofRealHom P)

private theorem halfAngleCosPolynomial_eval_exp_two (theta : ℝ) :
    Polynomial.eval (Complex.exp (((2 * theta : ℝ) : ℂ) * I))
        halfAngleCosPolynomial =
      Complex.exp ((theta : ℂ) * I) * (Real.cos theta : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [halfAngleCosPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im, Real.cos_two_mul,
      Real.sin_two_mul];
    nlinarith [Real.cos_sq_add_sin_sq theta]

private theorem halfAngleSinPolynomial_eval_exp_two (theta : ℝ) :
    Polynomial.eval (Complex.exp (((2 * theta : ℝ) : ℂ) * I))
        halfAngleSinPolynomial =
      Complex.exp ((theta : ℂ) * I) * (Real.sin theta : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [halfAngleSinPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im, Real.cos_two_mul,
      Real.sin_two_mul] <;>
    nlinarith [Real.cos_sq_add_sin_sq theta]

private theorem halfAngleCosPolynomial_eval_exp (phi : ℝ) :
    Polynomial.eval (Complex.exp ((phi : ℂ) * I)) halfAngleCosPolynomial =
      Complex.exp ((((phi / 2 : ℝ) : ℂ)) * I) *
        (Real.cos (phi / 2) : ℂ) := by
  have hphi : 2 * (phi / 2) = phi := by ring
  simpa only [hphi] using halfAngleCosPolynomial_eval_exp_two (phi / 2)

private theorem halfAngleSinPolynomial_eval_exp (phi : ℝ) :
    Polynomial.eval (Complex.exp ((phi : ℂ) * I)) halfAngleSinPolynomial =
      Complex.exp ((((phi / 2 : ℝ) : ℂ)) * I) *
        (Real.sin (phi / 2) : ℂ) := by
  have hphi : 2 * (phi / 2) = phi := by ring
  simpa only [hphi] using halfAngleSinPolynomial_eval_exp_two (phi / 2)

/-- Homogeneous evaluation commutes with complex scalar dilation. -/
private theorem halfAngle_complex_eval_mul_of_isHomogeneous
    {Q : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) (a : ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => a * x i) Q =
      a ^ d * MvPolynomial.eval x Q := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg := hQ.degree_eq_sum_deg_support he
  have hprod : (∏ i ∈ e.support, (a * x i) ^ e i) =
      a ^ d * ∏ i ∈ e.support, x i ^ e i := by
    calc
      (∏ i ∈ e.support, (a * x i) ^ e i) =
          ∏ i ∈ e.support, (a ^ e i * x i ^ e i) := by
            apply Finset.prod_congr rfl
            intro i _
            rw [mul_pow]
      _ = (∏ i ∈ e.support, a ^ e i) *
          ∏ i ∈ e.support, x i ^ e i := by
            rw [Finset.prod_mul_distrib]
      _ = a ^ (∑ i ∈ e.support, e i) *
          ∏ i ∈ e.support, x i ^ e i := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = a ^ d * ∏ i ∈ e.support, x i ^ e i := by rw [← hdeg]
  rw [hprod]
  ring

/-- Evaluation of the paper's half-angle Laurent numerator on the unit
circle. -/
theorem halfAnglePolynomial_eval_exp {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) (phi : ℝ) :
    Polynomial.eval (Complex.exp ((phi : ℂ) * I)) (halfAnglePolynomial P) =
      Complex.exp ((phi : ℂ) * I) ^ N * (halfAngleTrace P phi : ℂ) := by
  let z : ℂ := Complex.exp ((phi : ℂ) * I)
  let u : ℂ := Complex.exp ((((phi / 2 : ℝ) : ℂ)) * I)
  have hu_sq : u ^ 2 = z := by
    dsimp [u, z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu_pow : u ^ (2 * N) = Complex.exp ((phi : ℂ) * I) ^ N := by
    calc
      u ^ (2 * N) = (u ^ 2) ^ N := pow_mul u 2 N
      _ = Complex.exp ((phi : ℂ) * I) ^ N := by rw [hu_sq]
  have hcoeff :
      (((Polynomial.evalRingHom z).comp Polynomial.C).comp Complex.ofRealHom) =
        Complex.ofRealHom := by
    ext r
    simp
  have hscale := halfAngle_complex_eval_mul_of_isHomogeneous
    (hP.map Complex.ofRealHom) u (fun i => (circlePoint (phi / 2) i : ℂ))
  have hmap :
      MvPolynomial.eval (fun i => (circlePoint (phi / 2) i : ℂ))
        (MvPolynomial.map Complex.ofRealHom P) =
          (circleTrace P (phi / 2) : ℂ) := by
    rw [MvPolynomial.eval_map]
    have h := MvPolynomial.eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ)
      (circlePoint (phi / 2)) P
    simpa [MvPolynomial.eval₂_id, Function.comp_def, circleTrace, evalAt] using h.symm
  unfold halfAnglePolynomial
  rw [MvPolynomial.polynomial_eval_eval₂, MvPolynomial.eval₂_map]
  change MvPolynomial.eval₂
      ((((Polynomial.evalRingHom z).comp Polynomial.C).comp Complex.ofRealHom))
      (fun s => Polynomial.eval z (halfAngleSubstitution s)) P = _
  rw [hcoeff]
  have hsub : (fun s => Polynomial.eval z (halfAngleSubstitution s)) =
      (fun i => u * (circlePoint (phi / 2) i : ℂ)) := by
    funext i
    fin_cases i
    · simpa [z, u, halfAngleSubstitution, circlePoint] using
        halfAngleCosPolynomial_eval_exp phi
    · simpa [z, u, halfAngleSubstitution, circlePoint] using
        halfAngleSinPolynomial_eval_exp phi
  rw [hsub]
  rw [← MvPolynomial.eval_map]
  rw [hscale, hmap, hu_pow]
  simp [halfAngleTrace]

/-- Laurent form of `halfAnglePolynomial_eval_exp`, centered at `N`, as in
the paper's half-angle proof. -/
theorem halfAnglePolynomial_laurent_representation
    {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) (phi : ℝ) :
    (halfAngleTrace P phi : ℂ) =
      (Complex.exp ((phi : ℂ) * I))⁻¹ ^ N *
        Polynomial.eval (Complex.exp ((phi : ℂ) * I))
          (halfAnglePolynomial P) := by
  rw [halfAnglePolynomial_eval_exp hP]
  rw [← mul_assoc, ← mul_pow]
  rw [inv_mul_cancel₀ (Complex.exp_ne_zero ((phi : ℂ) * I))]
  simp

/-- Strict positivity of the trace makes the half-angle Laurent numerator
nonzero. -/
theorem halfAnglePolynomial_ne_zero_of_positiveDefinite
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hP : PositiveDefinite P) :
    halfAnglePolynomial P ≠ 0 := by
  intro hzero
  have heval := halfAnglePolynomial_eval_exp hhom 0
  have htrace : (halfAngleTrace P 0 : ℂ) = 0 := by
    simpa [hzero] using heval.symm
  exact (ne_of_gt (hP.halfAngleTrace_pos 0)) (Complex.ofReal_eq_zero.mp htrace)

private lemma halfAngleCosPolynomial_natDegree_le :
    halfAngleCosPolynomial.natDegree ≤ 1 := by
  calc
    halfAngleCosPolynomial.natDegree ≤
        (Polynomial.X + (1 : ℂ[X])).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ max (Polynomial.X : ℂ[X]).natDegree (1 : ℂ[X]).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by simp

private lemma halfAngleSinPolynomial_natDegree_le :
    halfAngleSinPolynomial.natDegree ≤ 1 := by
  calc
    halfAngleSinPolynomial.natDegree ≤
        (Polynomial.X - (1 : ℂ[X])).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ max (Polynomial.X : ℂ[X]).natDegree (1 : ℂ[X]).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 1 := by simp

private lemma halfAngleSubstitution_natDegree_le (i : Fin 2) :
    (halfAngleSubstitution i).natDegree ≤ 1 := by
  fin_cases i
  · exact halfAngleCosPolynomial_natDegree_le
  · exact halfAngleSinPolynomial_natDegree_le

/-- The half-angle Laurent numerator has padded degree at most `2 * N`. -/
theorem halfAnglePolynomial_natDegree_le {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) :
    (halfAnglePolynomial P).natDegree ≤ 2 * N := by
  classical
  rw [halfAnglePolynomial, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  calc
    (Polynomial.C (MvPolynomial.coeff e (MvPolynomial.map Complex.ofRealHom P)) *
        ∏ i ∈ e.support, halfAngleSubstitution i ^ e i).natDegree ≤
        (∏ i ∈ e.support, halfAngleSubstitution i ^ e i).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i ∈ e.support, (halfAngleSubstitution i ^ e i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ e.support, e i := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (halfAngleSubstitution i ^ e i).natDegree ≤
            e i * (halfAngleSubstitution i).natDegree :=
          Polynomial.natDegree_pow_le
        _ ≤ e i * 1 := Nat.mul_le_mul_left (e i) (halfAngleSubstitution_natDegree_le i)
        _ = e i := Nat.mul_one _
    _ = 2 * N := by
      rw [hP.degree_eq_sum_deg_support]
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at he
      apply MvPolynomial.mem_support_iff.mpr
      intro hc
      apply he
      rw [hc, map_zero]

private theorem halfAngleCosPolynomial_map_star :
    halfAngleCosPolynomial.map (starRingEnd ℂ) = halfAngleCosPolynomial := by
  simp [halfAngleCosPolynomial, map_ofNat]

private theorem halfAngleSinPolynomial_map_star :
    halfAngleSinPolynomial.map (starRingEnd ℂ) = -halfAngleSinPolynomial := by
  simp [halfAngleSinPolynomial, map_ofNat]

private theorem halfAngleCosPolynomial_reflect_one :
    halfAngleCosPolynomial.reflect 1 = halfAngleCosPolynomial := by
  rw [halfAngleCosPolynomial, Polynomial.reflect_C_mul, Polynomial.reflect_add]
  simp
  ring

private theorem halfAngleSinPolynomial_reflect_one :
    halfAngleSinPolynomial.reflect 1 = -halfAngleSinPolynomial := by
  rw [halfAngleSinPolynomial, Polynomial.reflect_C_mul, Polynomial.reflect_sub]
  simp
  ring

private theorem halfAngleCosPolynomial_padded_conjReflect :
    (halfAngleCosPolynomial.map (starRingEnd ℂ)).reflect 1 =
      halfAngleCosPolynomial := by
  rw [halfAngleCosPolynomial_map_star, halfAngleCosPolynomial_reflect_one]

private theorem halfAngleSinPolynomial_padded_conjReflect :
    (halfAngleSinPolynomial.map (starRingEnd ℂ)).reflect 1 =
      halfAngleSinPolynomial := by
  rw [halfAngleSinPolynomial_map_star, Polynomial.reflect_neg,
    halfAngleSinPolynomial_reflect_one]
  simp

private theorem halfAngle_paddedConjReflect_pow {p : ℂ[X]} {D : ℕ}
    (hdeg : p.natDegree ≤ D)
    (hself : (p.map (starRingEnd ℂ)).reflect D = p) (k : ℕ) :
    ((p ^ k).map (starRingEnd ℂ)).reflect (D * k) = p ^ k := by
  have hmap : (p.map (starRingEnd ℂ)).natDegree ≤ D :=
    Polynomial.natDegree_map_le.trans hdeg
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : ((p.map (starRingEnd ℂ)) ^ k).natDegree ≤ D * k := by
        calc
          ((p.map (starRingEnd ℂ)) ^ k).natDegree ≤
              k * (p.map (starRingEnd ℂ)).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ k * D := Nat.mul_le_mul_left k hmap
          _ = D * k := Nat.mul_comm _ _
      have ih' :
          ((p.map (starRingEnd ℂ)) ^ k).reflect (D * k) = p ^ k := by
        simpa only [Polynomial.map_pow] using ih
      rw [Polynomial.map_pow, pow_succ, Nat.mul_succ]
      rw [Polynomial.reflect_mul _ _ hpow hmap]
      rw [ih', hself, pow_succ]

private theorem halfAngleSubstitution_product_padded_conjReflect
    (e : Fin 2 →₀ ℕ) :
    ((∏ i, halfAngleSubstitution i ^ e i).map (starRingEnd ℂ)).reflect
        (e 0 + e 1) = ∏ i, halfAngleSubstitution i ^ e i := by
  rw [Fin.prod_univ_two]
  simp only [halfAngleSubstitution, Matrix.cons_val_zero, Matrix.cons_val_one,
    Polynomial.map_mul]
  have hcos :
      (((halfAngleCosPolynomial ^ e 0).map (starRingEnd ℂ))).natDegree ≤
        e 0 := by
    calc
      ((halfAngleCosPolynomial ^ e 0).map (starRingEnd ℂ)).natDegree ≤
          (halfAngleCosPolynomial ^ e 0).natDegree := Polynomial.natDegree_map_le
      _ ≤ e 0 * halfAngleCosPolynomial.natDegree := Polynomial.natDegree_pow_le
      _ ≤ e 0 * 1 := Nat.mul_le_mul_left _ halfAngleCosPolynomial_natDegree_le
      _ = e 0 := Nat.mul_one _
  have hsin :
      (((halfAngleSinPolynomial ^ e 1).map (starRingEnd ℂ))).natDegree ≤
        e 1 := by
    calc
      ((halfAngleSinPolynomial ^ e 1).map (starRingEnd ℂ)).natDegree ≤
          (halfAngleSinPolynomial ^ e 1).natDegree := Polynomial.natDegree_map_le
      _ ≤ e 1 * halfAngleSinPolynomial.natDegree := Polynomial.natDegree_pow_le
      _ ≤ e 1 * 1 := Nat.mul_le_mul_left _ halfAngleSinPolynomial_natDegree_le
      _ = e 1 := Nat.mul_one _
  rw [Polynomial.reflect_mul _ _ hcos hsin]
  simpa using congrArg₂ (fun a b : ℂ[X] => a * b)
    (halfAngle_paddedConjReflect_pow halfAngleCosPolynomial_natDegree_le
      halfAngleCosPolynomial_padded_conjReflect (e 0))
    (halfAngle_paddedConjReflect_pow halfAngleSinPolynomial_natDegree_le
      halfAngleSinPolynomial_padded_conjReflect (e 1))

private theorem halfAngle_reflect_finset_sum {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha → ℂ[X]) (D : ℕ) :
    (∑ a ∈ s, f a).reflect D = ∑ a ∈ s, (f a).reflect D := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Conjugating coefficients and reversing at padded degree `2 * N` fixes
the half-angle Laurent numerator. -/
theorem halfAnglePolynomial_padded_conjReflect
    {P : BivariatePolynomial} {N : ℕ}
    (hP : P.IsHomogeneous (2 * N)) :
    ((halfAnglePolynomial P).map (starRingEnd ℂ)).reflect (2 * N) =
      halfAnglePolynomial P := by
  classical
  unfold halfAnglePolynomial
  rw [MvPolynomial.eval₂_eq']
  rw [MvPolynomial.support_map_of_injective P Complex.ofRealHom.injective]
  simp only [MvPolynomial.coeff_map]
  rw [Polynomial.map_sum]
  rw [halfAngle_reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hsum : 2 * N = e 0 + e 1 := by
    calc
      2 * N = ∑ i ∈ e.support, e i := hP.degree_eq_sum_deg_support he
      _ = e.sum (fun _ n => n) := rfl
      _ = ∑ i, e i := Finsupp.sum_fintype e (fun _ n => n) (by simp)
      _ = e 0 + e 1 := Fin.sum_univ_two e
  rw [Polynomial.map_mul, Polynomial.map_C]
  have hcoeff :
      starRingEnd ℂ (Complex.ofRealHom (MvPolynomial.coeff e P)) =
        Complex.ofRealHom (MvPolynomial.coeff e P) := by
    change starRingEnd ℂ ((MvPolynomial.coeff e P : ℝ) : ℂ) =
      ((MvPolynomial.coeff e P : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  rw [hcoeff]
  rw [Polynomial.reflect_C_mul]
  rw [hsum]
  rw [halfAngleSubstitution_product_padded_conjReflect]

/-- Strict Fejer--Riesz data for the paper's half-angle trace, with factor
count bounded by `N`. -/
theorem strictFejerRiesz_halfAngle
    {P : BivariatePolynomial} {N : ℕ}
    (hhom : P.IsHomogeneous (2 * N)) (hP : PositiveDefinite P) :
    Nonempty (StrictFejerRieszData (halfAngleTrace P) N) := by
  exact strictFejerRiesz_of_padded_selfInversive
    (p := halfAngleTrace P) (D := N) (halfAnglePolynomial P)
    (halfAnglePolynomial_ne_zero_of_positiveDefinite hhom hP)
    (halfAnglePolynomial_natDegree_le hhom)
    (halfAnglePolynomial_padded_conjReflect hhom)
    (halfAnglePolynomial_laurent_representation hhom)
    hP.halfAngleTrace_pos

end

end HomogeneousObstruction
