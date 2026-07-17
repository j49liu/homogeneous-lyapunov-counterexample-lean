import HomogeneousObstruction.Basic

namespace HomogeneousObstruction

open Complex MeasureTheory Set
open scoped Interval Real

noncomputable section

local instance instTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The Fourier coefficient convention used in the paper:
`(2π)⁻¹ ∫₀²ᵖ u(θ) exp (-i n θ) dθ`.

It is defined through mathlib's `fourierCoeffOn`; the theorem
`paperFourierCoeff_eq_integral` below records the convention explicitly. -/
def paperFourierCoeff (u : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos u n

/-- The specialization of `paperFourierCoeff` to a real-valued function. -/
def realPaperFourierCoeff (u : ℝ → ℝ) (n : ℤ) : ℂ :=
  paperFourierCoeff (fun θ ↦ (u θ : ℂ)) n

/-- The normalized average over one `2π`-period. -/
def paperAverage (u : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, u θ

theorem paperFourierCoeff_eq_integral (u : ℝ → ℂ) (n : ℤ) :
    paperFourierCoeff u n =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          u θ * Complex.exp (-Complex.I * (n : ℂ) * (θ : ℂ)) := by
  rw [paperFourierCoeff, fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  change
    fourier (-n) (θ : AddCircle (2 * Real.pi - 0)) * u θ =
      u θ * Complex.exp (-Complex.I * (n : ℂ) * (θ : ℂ))
  rw [fourier_coe_apply]
  rw [mul_comm]
  congr 1
  congr 1
  field_simp [Real.pi_ne_zero]
  simp only [Int.cast_neg]
  norm_cast
  push_cast
  ring

/-- The Fourier-coefficient differentiation rule used in the manuscript.
With the convention exp (-i n θ), differentiating a 2π-periodic function
multiplies its mode n by i n. -/
theorem paperFourierCoeff_derivative
    {u du : ℝ → ℂ} (n : ℤ) (hn : n ≠ 0)
    (hderiv : ∀ θ, HasDerivAt u (du θ) θ)
    (hdu : Continuous du)
    (hperiod : u (2 * Real.pi) = u 0) :
    paperFourierCoeff du n =
      I * (n : ℂ) * paperFourierCoeff u n := by
  have hu : Continuous u :=
    continuous_iff_continuousAt.mpr fun θ => (hderiv θ).continuousAt
  have hparts := fourierCoeffOn_of_hasDeriv_right
    (a := (0 : ℝ)) (b := 2 * Real.pi) Real.two_pi_pos hn
    hu.continuousOn
    (fun θ _ => (hderiv θ).hasDerivWithinAt)
    (hdu.intervalIntegrable (0 : ℝ) (2 * Real.pi))
  rw [hperiod, sub_self, mul_zero, zero_sub] at hparts
  unfold paperFourierCoeff
  rw [hparts]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnC, Real.pi_ne_zero]
  push_cast
  ring

/-- Real-valued specialization of the Fourier differentiation rule. -/
theorem realPaperFourierCoeff_derivative
    {u du : ℝ → ℝ} (n : ℤ) (hn : n ≠ 0)
    (hderiv : ∀ θ, HasDerivAt u (du θ) θ)
    (hdu : Continuous du)
    (hperiod : u (2 * Real.pi) = u 0) :
    realPaperFourierCoeff du n =
      I * (n : ℂ) * realPaperFourierCoeff u n := by
  apply paperFourierCoeff_derivative n hn
  · intro θ
    exact (hderiv θ).ofReal_comp
  · exact Complex.continuous_ofReal.comp hdu
  · exact congrArg Complex.ofReal hperiod

/-- Doubling the angular variable sends Fourier mode one to mode two.  This
records explicitly the change of variables used by the paper's half-angle
substitution, including the `1 / (2π)` normalization. -/
theorem paperFourierCoeff_comp_two
    (u : ℝ → ℂ) (hu : Continuous u)
    (hperiod : Function.Periodic u (2 * Real.pi)) :
    paperFourierCoeff (fun θ : ℝ ↦ u (2 * θ)) 2 = paperFourierCoeff u 1 := by
  rw [paperFourierCoeff_eq_integral, paperFourierCoeff_eq_integral]
  let F : ℝ → ℂ := fun φ ↦ u φ * Complex.exp (-I * (φ : ℂ))
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hexpPeriod :
      Complex.exp (-I * (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
    rw [show -I * (((2 * Real.pi : ℝ) : ℂ)) = -(2 * (Real.pi : ℂ) * I) by
      push_cast
      ring]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hFperiod : Function.Periodic F (2 * Real.pi) := by
    intro φ
    dsimp [F]
    rw [hperiod φ]
    rw [show -I * (((φ + 2 * Real.pi : ℝ) : ℂ)) =
        -I * (φ : ℂ) + -I * (((2 * Real.pi : ℝ) : ℂ)) by
      push_cast
      ring]
    rw [Complex.exp_add, hexpPeriod, mul_one]
  have hFint : ∀ a b : ℝ, IntervalIntegrable F MeasureTheory.volume a b :=
    fun a b ↦ hFcont.intervalIntegrable a b
  have hdouble0 := hFperiod.intervalIntegral_add_zsmul_eq (2 : ℤ) 0 hFint
  have hdouble :
      (∫ φ in (0 : ℝ)..4 * Real.pi, F φ) =
        2 * ∫ φ in (0 : ℝ)..2 * Real.pi, F φ := by
    convert hdouble0 using 1
    · simp
      ring_nf
    · simp
  have hintegrand :
      (fun θ : ℝ ↦
          u (2 * θ) * Complex.exp (-I * (2 : ℂ) * (θ : ℂ))) =
        fun θ : ℝ ↦ F (2 * θ) := by
    funext θ
    dsimp [F]
    congr 2
    push_cast
    ring
  norm_num only [Int.cast_ofNat]
  rw [hintegrand]
  rw [intervalIntegral.integral_comp_mul_left F (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mul_zero]
  rw [show 2 * (2 * Real.pi) = 4 * Real.pi by ring, hdouble]
  change (1 / ((2 : ℂ) * Real.pi)) *
      (((2 : ℝ)⁻¹ : ℝ) •
        (2 * ∫ φ in (0 : ℝ)..2 * Real.pi, F φ)) = _
  simp only [real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  dsimp [F]
  ring_nf

/-- Real-valued specialization of `paperFourierCoeff_comp_two`. -/
theorem realPaperFourierCoeff_comp_two
    (u : ℝ → ℝ) (hu : Continuous u)
    (hperiod : Function.Periodic u (2 * Real.pi)) :
    realPaperFourierCoeff (fun θ : ℝ ↦ u (2 * θ)) 2 =
      realPaperFourierCoeff u 1 := by
  simpa only [realPaperFourierCoeff] using
    paperFourierCoeff_comp_two (fun θ ↦ (u θ : ℂ)) (by fun_prop) (by
      intro θ
      change (u (θ + 2 * Real.pi) : ℂ) = (u θ : ℂ)
      exact congrArg Complex.ofReal (hperiod θ))

theorem realPaperFourierCoeff_zero (u : ℝ → ℝ) :
    realPaperFourierCoeff u 0 = (paperAverage u : ℂ) := by
  rw [realPaperFourierCoeff, paperFourierCoeff_eq_integral]
  simp [paperAverage, intervalIntegral.integral_ofReal]

@[simp] theorem realPaperFourierCoeff_zero_re (u : ℝ → ℝ) :
    (realPaperFourierCoeff u 0).re = paperAverage u := by
  rw [realPaperFourierCoeff_zero]
  simp

theorem paperFourierCoeff_const_mul (u : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    paperFourierCoeff (fun θ ↦ c * u θ) n = c * paperFourierCoeff u n := by
  exact fourierCoeffOn.const_mul u c n Real.two_pi_pos

theorem realPaperFourierCoeff_const_mul (u : ℝ → ℝ) (c : ℝ) (n : ℤ) :
    realPaperFourierCoeff (fun θ ↦ c * u θ) n =
      (c : ℂ) * realPaperFourierCoeff u n := by
  simpa only [realPaperFourierCoeff, Complex.ofReal_mul] using
    paperFourierCoeff_const_mul (fun θ ↦ (u θ : ℂ)) (c : ℂ) n

theorem paperFourierCoeff_add (u v : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v) (n : ℤ) :
    paperFourierCoeff (fun θ ↦ u θ + v θ) n =
      paperFourierCoeff u n + paperFourierCoeff v n := by
  rw [paperFourierCoeff_eq_integral, paperFourierCoeff_eq_integral,
    paperFourierCoeff_eq_integral]
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add]
  · ring
  · exact (hu.mul (by fun_prop)).intervalIntegrable _ _
  · exact (hv.mul (by fun_prop)).intervalIntegrable _ _

theorem realPaperFourierCoeff_add (u v : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (n : ℤ) :
    realPaperFourierCoeff (fun θ ↦ u θ + v θ) n =
      realPaperFourierCoeff u n + realPaperFourierCoeff v n := by
  simpa only [realPaperFourierCoeff, Complex.ofReal_add] using
    paperFourierCoeff_add (fun θ ↦ (u θ : ℂ)) (fun θ ↦ (v θ : ℂ))
      (by fun_prop) (by fun_prop) n

/-- Fourier coefficients commute with finite sums of continuous functions. -/
theorem paperFourierCoeff_finset_sum {J : Type*} [Fintype J]
    (u : J → ℝ → ℂ) (hu : ∀ j, Continuous (u j)) (n : ℤ) :
    paperFourierCoeff (fun theta => ∑ j, u j theta) n =
      ∑ j, paperFourierCoeff (u j) n := by
  simp_rw [paperFourierCoeff_eq_integral, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro j _
    exact ((hu j).mul (by fun_prop)).intervalIntegrable _ _

theorem paperFourierCoeff_sub (u v : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v) (n : ℤ) :
    paperFourierCoeff (fun θ ↦ u θ - v θ) n =
      paperFourierCoeff u n - paperFourierCoeff v n := by
  rw [paperFourierCoeff_eq_integral, paperFourierCoeff_eq_integral,
    paperFourierCoeff_eq_integral]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub]
  · ring
  · exact (hu.mul (by fun_prop)).intervalIntegrable _ _
  · exact (hv.mul (by fun_prop)).intervalIntegrable _ _

theorem realPaperFourierCoeff_sub (u v : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (n : ℤ) :
    realPaperFourierCoeff (fun θ ↦ u θ - v θ) n =
      realPaperFourierCoeff u n - realPaperFourierCoeff v n := by
  simpa only [realPaperFourierCoeff, Complex.ofReal_sub] using
    paperFourierCoeff_sub (fun θ ↦ (u θ : ℂ)) (fun θ ↦ (v θ : ℂ))
      (by fun_prop) (by fun_prop) n

/-- A `2π`-periodic function already defined on `AddCircle (2π)` has the same coefficient
whether it is integrated on the additive circle or over the real interval `[0, 2π]`. -/
theorem paperFourierCoeff_coe_addCircle (F : AddCircle (2 * Real.pi) → ℂ) (n : ℤ) :
    paperFourierCoeff (fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi))) n =
      fourierCoeff (T := 2 * Real.pi) F n := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [paperFourierCoeff]
  have hLift :
      fourierCoeff (T := 2 * Real.pi)
          (AddCircle.liftIoc (2 * Real.pi) 0
            (fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi)))) n =
        fourierCoeffOn Real.two_pi_pos
          (fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi))) n := by
    calc
      _ = fourierCoeffOn (lt_add_of_pos_right 0 (Fact.out : 0 < 2 * Real.pi))
          (fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi))) n :=
        fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
          (fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi))) n
      _ = _ := by
        congr 1
        simp
  rw [← hLift]
  congr 1
  funext x
  change F ((AddCircle.equivIoc (2 * Real.pi) 0 x : ℝ) : AddCircle (2 * Real.pi)) = F x
  rw [AddCircle.coe_equivIoc]

theorem paperFourierCoeff_fourier (k n : ℤ) :
    paperFourierCoeff
        (fun θ : ℝ ↦ fourier k (θ : AddCircle (2 * Real.pi))) n =
      (Pi.single k (1 : ℂ) : ℤ → ℂ) n := by
  rw [paperFourierCoeff_coe_addCircle]
  exact congrFun (fourierCoeff_fourier (T := 2 * Real.pi) k) n

/-- With period `2π`, mathlib's Fourier monomial is exactly `exp(i k θ)`.
This is the sign bridge between the manuscript's displayed finite expansion
and `paperFourierCoeff`, whose kernel is `exp(-i n θ)`. -/
theorem exp_int_mul_I_eq_fourier (k : ℤ) (theta : ℝ) :
    Complex.exp ((k : ℂ) * (theta : ℂ) * I) =
      fourier k (theta : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

theorem paperFourierCoeff_one (n : ℤ) :
    paperFourierCoeff (fun _ : ℝ ↦ (1 : ℂ)) n = if n = 0 then 1 else 0 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [paperFourierCoeff]
  have hLift :
      fourierCoeff (T := 2 * Real.pi)
          (AddCircle.liftIoc (2 * Real.pi) 0 (fun _ : ℝ ↦ (1 : ℂ))) n =
        fourierCoeffOn Real.two_pi_pos (fun _ : ℝ ↦ (1 : ℂ)) n := by
    calc
      _ = fourierCoeffOn (lt_add_of_pos_right 0 (Fact.out : 0 < 2 * Real.pi))
          (fun _ : ℝ ↦ (1 : ℂ)) n :=
        fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
          (fun _ : ℝ ↦ (1 : ℂ)) n
      _ = _ := by
        congr 1
        simp
  rw [← hLift]
  change fourierCoeff (T := 2 * Real.pi) (fun _ : AddCircle (2 * Real.pi) ↦ (1 : ℂ)) n = _
  rw [show (fun _ : AddCircle (2 * Real.pi) ↦ (1 : ℂ)) = fourier 0 by
    funext x
    exact (fourier_zero (x := x)).symm]
  rw [show fourierCoeff (T := 2 * Real.pi) (fourier 0) n =
      (Pi.single 0 (1 : ℂ) : ℤ → ℂ) n by
    exact congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) n]
  simp [Pi.single_apply]

@[simp] theorem realPaperFourierCoeff_one_zero :
    realPaperFourierCoeff (fun _ : ℝ ↦ 1) 0 = 1 := by
  simpa [realPaperFourierCoeff] using paperFourierCoeff_one 0

@[simp] theorem realPaperFourierCoeff_one_two :
    realPaperFourierCoeff (fun _ : ℝ ↦ 1) 2 = 0 := by
  simpa [realPaperFourierCoeff] using paperFourierCoeff_one 2

theorem ofReal_cos_two_eq_fourier (θ : ℝ) :
    (Real.cos (2 * θ) : ℂ) =
      (2 : ℂ)⁻¹ *
        (fourier 2 (θ : AddCircle (2 * Real.pi)) +
          fourier (-2) (θ : AddCircle (2 * Real.pi))) := by
  rw [Complex.ofReal_cos]
  calc
    Complex.cos ((2 * θ : ℝ) : ℂ) =
        (2 : ℂ)⁻¹ *
          (Complex.exp ((((2 * θ : ℝ) : ℂ)) * Complex.I) +
            Complex.exp (-(((2 * θ : ℝ) : ℂ)) * Complex.I)) := by
      rw [← Complex.two_cos]
      field_simp
    _ = _ := by
      rw [fourier_coe_apply, fourier_coe_apply]
      congr 2
      · congr 1
        field_simp [Real.pi_ne_zero]
        norm_cast
        ring
      · congr 1
        field_simp [Real.pi_ne_zero]
        norm_cast
        push_cast
        ring

theorem realPaperFourierCoeff_cos_two (n : ℤ) :
    realPaperFourierCoeff (fun θ : ℝ ↦ Real.cos (2 * θ)) n =
      (2 : ℂ)⁻¹ *
        ((Pi.single 2 (1 : ℂ) : ℤ → ℂ) n +
          (Pi.single (-2) (1 : ℂ) : ℤ → ℂ) n) := by
  rw [realPaperFourierCoeff]
  let F : AddCircle (2 * Real.pi) → ℂ := fun x ↦
    (2 : ℂ)⁻¹ * (fourier 2 x + fourier (-2) x)
  have hfun :
      (fun θ : ℝ ↦ (Real.cos (2 * θ) : ℂ)) =
        fun θ : ℝ ↦ F (θ : AddCircle (2 * Real.pi)) := by
    funext θ
    exact ofReal_cos_two_eq_fourier θ
  rw [hfun, paperFourierCoeff_coe_addCircle F n]
  change fourierCoeff (T := 2 * Real.pi)
      (fun x : AddCircle (2 * Real.pi) ↦ (2 : ℂ)⁻¹ * (fourier 2 x + fourier (-2) x)) n = _
  have hInt (k : ℤ) :
      Integrable (fun x : AddCircle (2 * Real.pi) ↦ fourier k x)
        (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
    simpa using
      (fourier k).continuous.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set (AddCircle (2 * Real.pi))))
  rw [fourierCoeff.const_mul]
  have hAdd :
      (fun x : AddCircle (2 * Real.pi) ↦ fourier 2 x + fourier (-2) x) =
        (fun x : AddCircle (2 * Real.pi) ↦ fourier 2 x) +
          (fun x : AddCircle (2 * Real.pi) ↦ fourier (-2) x) := rfl
  rw [hAdd, fourierCoeff.add (hInt 2) (hInt (-2))]
  have hTwo :
      fourierCoeff (T := 2 * Real.pi) (fun x : AddCircle (2 * Real.pi) ↦ fourier 2 x) n =
        (Pi.single 2 (1 : ℂ) : ℤ → ℂ) n := by
    change fourierCoeff (T := 2 * Real.pi) (fourier 2) n = _
    exact congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 2) n
  have hNegTwo :
      fourierCoeff (T := 2 * Real.pi) (fun x : AddCircle (2 * Real.pi) ↦ fourier (-2) x) n =
        (Pi.single (-2) (1 : ℂ) : ℤ → ℂ) n := by
    change fourierCoeff (T := 2 * Real.pi) (fourier (-2)) n = _
    exact congrFun (fourierCoeff_fourier (T := 2 * Real.pi) (-2)) n
  simp only [Pi.add_apply]
  rw [hTwo, hNegTwo]

@[simp] theorem realPaperFourierCoeff_cos_two_zero :
    realPaperFourierCoeff (fun θ : ℝ ↦ Real.cos (2 * θ)) 0 = 0 := by
  rw [realPaperFourierCoeff_cos_two]
  simp

@[simp] theorem realPaperFourierCoeff_cos_two_two :
    realPaperFourierCoeff (fun θ : ℝ ↦ Real.cos (2 * θ)) 2 = (1 / 2 : ℂ) := by
  rw [realPaperFourierCoeff_cos_two]
  simp

/-- The zeroth coefficient of a logarithmic derivative over a period is zero.  Positivity avoids
any choice of a complex logarithm: this is the ordinary real logarithm and the real FTC. -/
theorem realPaperFourierCoeff_logDerivative_zero
    (p dp : ℝ → ℝ)
    (hp : ∀ θ, 0 < p θ)
    (hderiv : ∀ θ, HasDerivAt p (dp θ) θ)
    (hdp : Continuous dp)
    (hperiod : p (2 * Real.pi) = p 0) :
    realPaperFourierCoeff (fun θ ↦ dp θ / p θ) 0 = 0 := by
  have hpcont : Continuous p := continuous_iff_continuousAt.mpr fun θ ↦ (hderiv θ).continuousAt
  have hquot : Continuous (fun θ ↦ dp θ / p θ) :=
    hdp.div hpcont fun θ ↦ (hp θ).ne'
  have hIntegral :
      (∫ θ in (0 : ℝ)..2 * Real.pi, dp θ / p θ) =
        Real.log (p (2 * Real.pi)) - Real.log (p 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ ↦ Real.log (p θ)) (f' := fun θ ↦ dp θ / p θ)
    · intro θ _
      exact (hderiv θ).log (hp θ).ne'
    · exact hquot.intervalIntegrable _ _
  rw [realPaperFourierCoeff_zero]
  norm_cast
  rw [paperAverage, hIntegral, hperiod, sub_self, mul_zero]

theorem realPaperFourierCoeff_const_mul_logDerivative_zero
    (p dp : ℝ → ℝ) (c : ℝ)
    (hp : ∀ θ, 0 < p θ)
    (hderiv : ∀ θ, HasDerivAt p (dp θ) θ)
    (hdp : Continuous dp)
    (hperiod : p (2 * Real.pi) = p 0) :
    realPaperFourierCoeff (fun θ ↦ c * (dp θ / p θ)) 0 = 0 := by
  rw [realPaperFourierCoeff_const_mul,
    realPaperFourierCoeff_logDerivative_zero p dp hp hderiv hdp hperiod, mul_zero]

theorem norm_realPaperFourierCoeff_le_average (u : ℝ → ℝ)
    (hu : ∀ θ, 0 ≤ u θ) (n : ℤ) :
    ‖realPaperFourierCoeff u n‖ ≤ paperAverage u := by
  rw [realPaperFourierCoeff, paperFourierCoeff_eq_integral]
  have hpi : 0 ≤ (2 * Real.pi : ℝ) := Real.two_pi_pos.le
  have hnorm :
      ‖∫ θ in (0 : ℝ)..2 * Real.pi,
          (u θ : ℂ) * Complex.exp (-Complex.I * (n : ℂ) * (θ : ℂ))‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, u θ := by
    calc
      ‖∫ θ in (0 : ℝ)..2 * Real.pi,
          (u θ : ℂ) * Complex.exp (-Complex.I * (n : ℂ) * (θ : ℂ))‖
          ≤ ∫ θ in (0 : ℝ)..2 * Real.pi,
              ‖(u θ : ℂ) * Complex.exp (-Complex.I * (n : ℂ) * (θ : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hpi
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, u θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only
        rw [norm_mul, Complex.norm_exp]
        simp [Complex.norm_real, hu θ]
  rw [norm_mul]
  simp only [one_div, mul_inv_rev, Complex.norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, norm_ofNat, abs_of_pos Real.pi_pos, ge_iff_le]
  have hscale : Real.pi⁻¹ * (2 : ℝ)⁻¹ = (2 * Real.pi)⁻¹ := by
    field_simp [Real.pi_ne_zero]
  rw [hscale]
  rw [paperAverage, one_div]
  exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hpi)

/-- The elementary Fourier estimate used in the contradiction: a nonnegative real function has
every Fourier coefficient bounded in norm by its zeroth coefficient. -/
theorem norm_realPaperFourierCoeff_le_zero_re (u : ℝ → ℝ)
    (hu : ∀ θ, 0 ≤ u θ) (n : ℤ) :
    ‖realPaperFourierCoeff u n‖ ≤ (realPaperFourierCoeff u 0).re := by
  simpa using norm_realPaperFourierCoeff_le_average u hu n

end

end HomogeneousObstruction
