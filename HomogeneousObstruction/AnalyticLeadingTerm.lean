import HomogeneousObstruction.Degree
import HomogeneousObstruction.LocalAnalyticCalculus
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The first homogeneous Taylor term of a local analytic function

This file formalizes the Taylor-expansion step in the proof of main theorem
item (4).  A coefficient of a Fréchet power series is a continuous
multilinear map.  In two variables its restriction to the diagonal is an
ordinary bivariate homogeneous polynomial; `diagonalPolynomial` gives that
polynomial explicitly in the standard basis.
-/

namespace HomogeneousObstruction

open scoped BigOperators Topology
open MvPolynomial Filter Asymptotics

noncomputable section

/-- The standard coordinate vector in `Point = Fin 2 → ℝ`. -/
def coordinateVector (i : Fin 2) : Point := Pi.single i 1

theorem sum_coordinateVector (z : Point) :
    (∑ i : Fin 2, z i • coordinateVector i) = z := by
  funext j
  fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]

/-- The bivariate polynomial obtained by expanding the diagonal of an
`n`-linear form in the standard basis. -/
def diagonalPolynomial {n : ℕ} (A : Point [×n]→L[ℝ] ℝ) : BivariatePolynomial :=
  ∑ σ : Fin n → Fin 2,
    C (A (fun j ↦ coordinateVector (σ j))) *
      ∏ j : Fin n, X (σ j)

theorem evalAt_diagonalPolynomial {n : ℕ} (A : Point [×n]→L[ℝ] ℝ) (z : Point) :
    evalAt (diagonalPolynomial A) z = A (fun _ ↦ z) := by
  classical
  simp only [diagonalPolynomial, evalAt, map_sum, map_mul, eval_C, eval_prod, eval_X]
  calc
    ∑ σ : Fin n → Fin 2,
        A (fun j ↦ coordinateVector (σ j)) * ∏ j : Fin n, z (σ j) =
        ∑ σ : Fin n → Fin 2,
          A (fun j ↦ z (σ j) • coordinateVector (σ j)) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [ContinuousMultilinearMap.map_smul_univ]
            ring
    _ = A (fun _ ↦ ∑ i : Fin 2, z i • coordinateVector i) := by
      symm
      exact ContinuousMultilinearMap.map_sum A
        (fun _ i ↦ z i • coordinateVector i)
    _ = A (fun _ ↦ z) := by
      apply congrArg A
      funext j
      exact sum_coordinateVector z

theorem diagonalPolynomial_isHomogeneous {n : ℕ} (A : Point [×n]→L[ℝ] ℝ) :
    (diagonalPolynomial A).IsHomogeneous n := by
  classical
  unfold diagonalPolynomial
  apply IsHomogeneous.sum
  intro σ _
  apply IsHomogeneous.C_mul
  convert IsHomogeneous.prod Finset.univ (fun j : Fin n ↦ X (σ j)) (fun _ ↦ 1) ?_ using 1
  · simp
  · intro j _
    exact isHomogeneous_X ℝ (σ j)

theorem diagonalPolynomial_ne_zero {n : ℕ} {A : Point [×n]→L[ℝ] ℝ}
    (hA : ∃ z : Point, A (fun _ ↦ z) ≠ 0) : diagonalPolynomial A ≠ 0 := by
  obtain ⟨z, hz⟩ := hA
  intro hzero
  apply hz
  rw [← evalAt_diagonalPolynomial A z, hzero]
  simp [evalAt]

/-! ## Finite truncations of a Fréchet power series -/

/-- Keep precisely the coefficients of degree strictly less than `N`. -/
def truncateFPowerSeries
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) :
    FormalMultilinearSeries ℝ Point ℝ :=
  fun n ↦ if n < N then p n else 0

@[simp] theorem truncateFPowerSeries_apply_of_lt
    (p : FormalMultilinearSeries ℝ Point ℝ) {N n : ℕ} (hn : n < N) :
    truncateFPowerSeries p N n = p n := by
  simp [truncateFPowerSeries, hn]

@[simp] theorem truncateFPowerSeries_apply_of_le
    (p : FormalMultilinearSeries ℝ Point ℝ) {N n : ℕ} (hn : N ≤ n) :
    truncateFPowerSeries p N n = 0 := by
  simp [truncateFPowerSeries, Nat.not_lt.mpr hn]

theorem truncateFPowerSeries_finite
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) :
    ∀ n, N ≤ n → truncateFPowerSeries p N n = 0 := by
  intro n hn
  exact truncateFPowerSeries_apply_of_le p hn

theorem truncateFPowerSeries_partialSum
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) (z : Point) :
    (truncateFPowerSeries p N).partialSum N z = p.partialSum N z := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  simp [hn]

theorem truncateFPowerSeries_sum
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) (z : Point) :
    (truncateFPowerSeries p N).sum z = p.partialSum N z := by
  rw [(truncateFPowerSeries p N).sum_of_finite
    (truncateFPowerSeries_finite p N)]
  exact truncateFPowerSeries_partialSum p N z

theorem truncateFPowerSeries_hasFPowerSeriesOnBall
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) :
    HasFPowerSeriesOnBall (truncateFPowerSeries p N).sum
      (truncateFPowerSeries p N) 0 ⊤ :=
  ((truncateFPowerSeries p N).hasFiniteFPowerSeriesOnBall_of_finite
    (truncateFPowerSeries_finite p N)).toHasFPowerSeriesOnBall

theorem derivSeries_truncate_eq_of_lt
    (p : FormalMultilinearSeries ℝ Point ℝ) {N n : ℕ} (hn : n < N) :
    (truncateFPowerSeries p (N + 1)).derivSeries n = p.derivSeries n := by
  change
    (continuousMultilinearCurryFin1 ℝ Point ℝ :
      (Point [×1]→L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] ℝ)).compContinuousMultilinearMap
        ((truncateFPowerSeries p (N + 1)).changeOriginSeries 1 n) =
      (continuousMultilinearCurryFin1 ℝ Point ℝ :
        (Point [×1]→L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] ℝ)).compContinuousMultilinearMap
        (p.changeOriginSeries 1 n)
  congr 1
  unfold FormalMultilinearSeries.changeOriginSeries
  apply Finset.sum_congr rfl
  intro s _
  unfold FormalMultilinearSeries.changeOriginSeriesTerm
  rw [truncateFPowerSeries_apply_of_lt]
  omega

theorem derivSeries_partialSum_truncate
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) (z : Point) :
    (truncateFPowerSeries p (N + 1)).derivSeries.partialSum N z =
      p.derivSeries.partialSum N z := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  rw [derivSeries_truncate_eq_of_lt p hn]

/-- Differentiating a finite Taylor polynomial drops its degree by one and
produces the corresponding partial sum of `derivSeries`. -/
theorem fderiv_partialSum_succ
    (p : FormalMultilinearSeries ℝ Point ℝ) (N : ℕ) (z : Point) :
    fderiv ℝ (p.partialSum (N + 1)) z = p.derivSeries.partialSum N z := by
  let q := truncateFPowerSeries p (N + 1)
  have hqfinite : ∀ n, N + 1 ≤ n → q n = 0 := by
    simpa [q] using truncateFPowerSeries_finite p (N + 1)
  have hq := q.hasFiniteFPowerSeriesOnBall_of_finite hqfinite
  have hd := hq.fderiv
  have heq := hd.eq_partialSum z (by simp) N le_rfl
  have hsum : q.sum = p.partialSum (N + 1) := by
    funext w
    exact truncateFPowerSeries_sum p (N + 1) w
  rw [zero_add, hsum] at heq
  calc
    fderiv ℝ (p.partialSum (N + 1)) z = q.derivSeries.partialSum N z := heq
    _ = p.derivSeries.partialSum N z := by
      simpa [q] using derivSeries_partialSum_truncate p N z

/-! ## A first nonzero diagonal coefficient -/

/-- A Taylor coefficient is relevant to the represented analytic function
when its restriction to the diagonal is nonzero. -/
def DiagonalCoefficientNonzero
    (p : FormalMultilinearSeries ℝ Point ℝ) (n : ℕ) : Prop :=
  ∃ z : Point, p n (fun _ ↦ z) ≠ 0

theorem partialSum_succ_eq_diagonal
    {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (z : Point) :
    p.partialSum (m + 1) z = p m (fun _ ↦ z) := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_eq_single m
  · intro n hn hne
    rw [Finset.mem_range] at hn
    exact hprior n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) hne) z
  · simp

theorem partialSum_succ_eq_evalAt_diagonalPolynomial
    {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0) :
    p.partialSum (m + 1) = fun z ↦ evalAt (diagonalPolynomial (p m)) z := by
  funext z
  rw [partialSum_succ_eq_diagonal hprior z, evalAt_diagonalPolynomial]

theorem derivSeries_partialSum_eq_fderiv_diagonalPolynomial
    {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (z : Point) :
    p.derivSeries.partialSum m z =
      fderiv ℝ (fun w ↦ evalAt (diagonalPolynomial (p m)) w) z := by
  rw [← fderiv_partialSum_succ p m z]
  rw [partialSum_succ_eq_evalAt_diagonalPolynomial hprior]

theorem diagonal_apply_smul {n : ℕ} (A : Point [×n]→L[ℝ] ℝ)
    (t : ℝ) (z : Point) :
    A (fun _ ↦ t • z) = t ^ n * A (fun _ ↦ z) := by
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

theorem exists_diagonalCoefficientNonzero
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ}
    (hp : HasFPowerSeriesAt V p 0) (hV : ¬ V =ᶠ[𝓝 0] 0) :
    ∃ n, DiagonalCoefficientNonzero p n := by
  by_contra! hall
  apply hV
  filter_upwards [hp.tendsto_partialSum] with z hz
  have hzero : ∀ N, p.partialSum N z = 0 := by
    intro N
    rw [FormalMultilinearSeries.partialSum]
    apply Finset.sum_eq_zero
    intro n _
    by_contra hn
    exact hall n ⟨z, hn⟩
  have hz' : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (V z)) := by
    simpa [hzero] using hz
  have heq := tendsto_nhds_unique hz' tendsto_const_nhds
  simpa using heq

theorem not_eventuallyEq_zero_of_punctured_pos
    {V : Point → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) :
    ¬ V =ᶠ[𝓝 0] 0 := by
  intro hzero
  have hzero' : ∀ᶠ z in 𝓝[≠] (0 : Point), V z = 0 :=
    hzero.filter_mono inf_le_left
  have hrho0 : ∀ᶠ z in 𝓝 (0 : Point), euclideanNorm z < ρ := by
    have ht := euclideanNorm_continuous.tendsto (0 : Point)
    have hIio : Set.Iio ρ ∈ 𝓝 (euclideanNorm (0 : Point)) := by
      simpa using Iio_mem_nhds hρ
    exact ht hIio
  have hrho : ∀ᶠ z in 𝓝[≠] (0 : Point), euclideanNorm z < ρ :=
    hrho0.filter_mono inf_le_left
  have hne : ∀ᶠ z in 𝓝[≠] (0 : Point), z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz
  have hfalse : ∀ᶠ _z in 𝓝[≠] (0 : Point), False := by
    filter_upwards [hzero', hrho, hne] with z hz hr hz0
    have := hpos z (euclideanNorm_pos hz0) hr
    linarith
  obtain ⟨z, hz⟩ := Filter.Eventually.exists hfalse
  exact hz

/-- The least Taylor degree that is nonzero on the diagonal.  Alternating
multilinear noise is deliberately ignored because it does not contribute to
the analytic function's Taylor expansion. -/
def leadingTaylorDegree
    (p : FormalMultilinearSeries ℝ Point ℝ)
    (h : ∃ n, DiagonalCoefficientNonzero p n) : ℕ :=
  @Nat.find (DiagonalCoefficientNonzero p) (Classical.decPred _) h

theorem leadingTaylorDegree_nonzero
    {p : FormalMultilinearSeries ℝ Point ℝ}
    (h : ∃ n, DiagonalCoefficientNonzero p n) :
    DiagonalCoefficientNonzero p (leadingTaylorDegree p h) :=
  by
    classical
    simpa [leadingTaylorDegree] using Nat.find_spec h

theorem leadingTaylorDegree_prior
    {p : FormalMultilinearSeries ℝ Point ℝ}
    (h : ∃ n, DiagonalCoefficientNonzero p n) :
    ∀ n < leadingTaylorDegree p h, ∀ z : Point,
      p n (fun _ ↦ z) = 0 := by
  classical
  intro n hn z
  by_contra hnz
  have hle := Nat.find_min' h ⟨z, hnz⟩
  exact (Nat.not_le_of_lt hn) (by simpa [leadingTaylorDegree] using hle)

theorem leadingTaylorDegree_pos
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ}
    (hp : HasFPowerSeriesAt V p 0) (hV0 : V 0 = 0)
    (h : ∃ n, DiagonalCoefficientNonzero p n) :
    0 < leadingTaylorDegree p h := by
  classical
  by_contra hm
  have hm0 : leadingTaylorDegree p h = 0 := Nat.eq_zero_of_not_pos hm
  obtain ⟨z, hz⟩ := leadingTaylorDegree_nonzero h
  have hcoeff := hp.coeff_zero (fun _ : Fin 0 ↦ (0 : Point))
  rw [hm0] at hz
  apply hz
  rw [show (fun _ : Fin 0 ↦ z) = (fun _ : Fin 0 ↦ (0 : Point)) from
    Subsingleton.elim _ _]
  simpa [hV0] using hcoeff

/-! ## Ray asymptotics of the leading term -/

theorem isLittleO_along_smul_of_isBigO_norm_pow_succ
    {R : Point → ℝ} {m : ℕ}
    (hR : R =O[𝓝 0] fun z ↦ ‖z‖ ^ (m + 1)) (x : Point) :
    (fun t : ℝ ↦ R (t • x)) =o[𝓝 0] fun t ↦ t ^ m := by
  have hray : Tendsto (fun t : ℝ ↦ t • x) (𝓝 0) (𝓝 (0 : Point)) := by
    simpa using
      (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ x)).tendsto 0
  calc
    (fun t : ℝ ↦ R (t • x)) =O[𝓝 0]
        (fun t ↦ ‖t • x‖ ^ (m + 1)) := by
      simpa only [Function.comp_apply] using hR.comp_tendsto hray
    _ =O[𝓝 0] (fun t : ℝ ↦ t ^ (m + 1)) := by
      refine .of_norm_norm ?_
      simpa [norm_smul, mul_pow, norm_pow, mul_comm] using
        (isBigO_refl (fun t : ℝ ↦ |t| ^ (m + 1)) (𝓝 0)).const_mul_left
          (‖x‖ ^ (m + 1))
    _ =o[𝓝 0] (fun t : ℝ ↦ t ^ m) :=
      isLittleO_pow_pow (Nat.lt_succ_self m)

theorem leadingTerm_ray_tendsto
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hp : HasFPowerSeriesAt V p 0)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (x : Point) :
    Tendsto (fun t : ℝ ↦ V (t • x) / t ^ m) (𝓝[>] 0)
      (𝓝 (p m (fun _ ↦ x))) := by
  have hO := hp.isBigO_sub_partialSum_pow (m + 1)
  simp only [zero_add] at hO
  have hlo := isLittleO_along_smul_of_isBigO_norm_pow_succ hO x
  have hrem :
      (fun t : ℝ ↦ V (t • x) - t ^ m * p m (fun _ ↦ x))
        =o[𝓝 0] fun t ↦ t ^ m := by
    apply hlo.congr'
    · filter_upwards with t
      rw [partialSum_succ_eq_diagonal hprior,
        diagonal_apply_smul]
    · rfl
  have ht0 := hrem.tendsto_div_nhds_zero
  have ht : Tendsto
      (fun t : ℝ ↦
        (V (t • x) - t ^ m * p m (fun _ ↦ x)) / t ^ m)
      (𝓝[>] 0) (𝓝 0) :=
    ht0.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hconst : Tendsto (fun _ : ℝ ↦ p m (fun _ ↦ x)) (𝓝[>] 0)
      (𝓝 (p m (fun _ ↦ x))) := tendsto_const_nhds
  have hadd :
      Tendsto
        (fun t : ℝ ↦
          (V (t • x) - t ^ m * p m (fun _ ↦ x)) / t ^ m +
            p m (fun _ ↦ x))
        (𝓝[>] 0) (𝓝 (p m (fun _ ↦ x))) := by
    simpa using ht.add hconst
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have ht0 : t ≠ 0 := ne_of_gt htpos
  field_simp [ht0]
  ring

theorem leadingTerm_nonnegative_of_local_pos
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ}
    {m : ℕ} {ρ : ℝ}
    (hp : HasFPowerSeriesAt V p 0)
    (hm : 0 < m)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (hρ : 0 < ρ)
    (hpos : ∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z) :
    ∀ x : Point, 0 ≤ evalAt (diagonalPolynomial (p m)) x := by
  intro x
  rw [evalAt_diagonalPolynomial]
  by_cases hx : x = 0
  · subst x
    have hzero : p m (fun _ ↦ (0 : Point)) = 0 :=
      ContinuousMultilinearMap.map_coord_zero (p m)
        (m := fun _ ↦ (0 : Point)) (⟨0, hm⟩ : Fin m) rfl
    simp [hzero]
  · have hlim := leadingTerm_ray_tendsto hp hprior x
    apply ge_of_tendsto hlim
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
    have hsmall0 : ∀ᶠ t : ℝ in 𝓝 0, euclideanNorm (t • x) < ρ := by
      have htend : Tendsto (fun t : ℝ ↦ t • x) (𝓝 0) (𝓝 0) := by
        simpa using
          (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ x)).tendsto 0
      have heuc : Tendsto (fun t : ℝ ↦ euclideanNorm (t • x)) (𝓝 0) (𝓝 0) := by
        simpa using (euclideanNorm_continuous.tendsto (0 : Point)).comp htend
      exact heuc (Iio_mem_nhds hρ)
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, euclideanNorm (t • x) < ρ :=
      hsmall0.filter_mono inf_le_left
    filter_upwards [htpos, hsmall] with t ht hs
    have htx : 0 < euclideanNorm (t • x) :=
      euclideanNorm_pos (smul_ne_zero ht.ne' hx)
    have hV := hpos (t • x) htx hs
    exact div_nonneg hV.le (pow_nonneg ht.le m)

/-! ## Lie-derivative asymptotics -/

theorem fderiv_sub_leadingTerm_isBigO
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hp : HasFPowerSeriesAt V p 0)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0) :
    (fun z ↦
      fderiv ℝ V z -
        fderiv ℝ (fun w ↦ evalAt (diagonalPolynomial (p m)) w) z)
      =O[𝓝 0] fun z ↦ ‖z‖ ^ m := by
  obtain ⟨r, hr⟩ := hp
  have hd : HasFPowerSeriesAt (fderiv ℝ V) p.derivSeries 0 :=
    ⟨r, hr.fderiv⟩
  have hO := hd.isBigO_sub_partialSum_pow m
  simp only [zero_add] at hO
  apply hO.congr'
  · filter_upwards with z
    rw [derivSeries_partialSum_eq_fderiv_diagonalPolynomial hprior]
  · rfl

theorem isBigO_along_smul_of_isBigO_norm_pow
    {E : Type*} [SeminormedAddCommGroup E]
    {R : Point → E} {m : ℕ}
    (hR : R =O[𝓝 0] fun z ↦ ‖z‖ ^ m) (x : Point) :
    (fun t : ℝ ↦ R (t • x)) =O[𝓝 0] fun t ↦ t ^ m := by
  have hray : Tendsto (fun t : ℝ ↦ t • x) (𝓝 0) (𝓝 (0 : Point)) := by
    simpa using
      (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ x)).tendsto 0
  calc
    (fun t : ℝ ↦ R (t • x)) =O[𝓝 0]
        (fun t ↦ ‖t • x‖ ^ m) := by
      simpa only [Function.comp_apply] using hR.comp_tendsto hray
    _ =O[𝓝 0] (fun t : ℝ ↦ t ^ m) := by
      refine .of_norm_right ?_
      simpa [norm_smul, mul_pow, norm_pow, mul_comm] using
        (isBigO_refl (fun t : ℝ ↦ |t| ^ m) (𝓝 0)).const_mul_left (‖x‖ ^ m)

/-- The analytic Lie derivative differs from that of the first homogeneous
Taylor term by `o(t^(m+2))` along each ray, exactly as stated in the
manuscript. -/
theorem lieRemainder_isLittleO
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hp : HasFPowerSeriesAt V p 0)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (x : Point) :
    (fun t : ℝ ↦
      functionLieDerivative V (t • x) -
        evalAt (lieDerivative (diagonalPolynomial (p m))) (t • x))
      =o[𝓝 0] fun t ↦ t ^ (m + 2) := by
  let D : Point → (Point →L[ℝ] ℝ) := fun z ↦
    fderiv ℝ V z -
      fderiv ℝ (fun w ↦ evalAt (diagonalPolynomial (p m)) w) z
  have hD : D =O[𝓝 0] fun z ↦ ‖z‖ ^ m := by
    simpa [D] using fderiv_sub_leadingTerm_isBigO hp hprior
  have hDray : (fun t : ℝ ↦ D (t • x)) =O[𝓝 0] fun t ↦ t ^ m :=
    isBigO_along_smul_of_isBigO_norm_pow hD x
  let ev : (Point →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) (fieldValue x)
  have hev0 : (fun t : ℝ ↦ ev (D (t • x))) =O[𝓝 0]
      (fun t ↦ D (t • x)) := ev.isBigO_comp _ _
  have hev : (fun t : ℝ ↦ D (t • x) (fieldValue x)) =O[𝓝 0]
      fun t ↦ t ^ m := by
    simpa [ev] using hev0.trans hDray
  have hmul := (isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).mul hev
  have hO :
      (fun t : ℝ ↦
        functionLieDerivative V (t • x) -
          evalAt (lieDerivative (diagonalPolynomial (p m))) (t • x))
        =O[𝓝 0] fun t ↦ t ^ (m + 3) := by
    apply hmul.congr'
    · filter_upwards with t
      rw [← functionLieDerivative_evalAt (diagonalPolynomial (p m)) (t • x)]
      simp only [functionLieDerivative, D, ContinuousLinearMap.sub_apply,
        fieldValue_smul, map_smul, smul_eq_mul]
      ring
    · filter_upwards with t
      rw [← pow_add]
      congr 1
      omega
  exact hO.trans_isLittleO (isLittleO_pow_pow (by omega))

theorem leadingLie_ray_tendsto
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ} {m : ℕ}
    (hp : HasFPowerSeriesAt V p 0) (hm : 0 < m)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (x : Point) :
    Tendsto
      (fun t : ℝ ↦ functionLieDerivative V (t • x) / t ^ (m + 2))
      (𝓝[>] 0)
      (𝓝 (evalAt (lieDerivative (diagonalPolynomial (p m))) x)) := by
  let P := diagonalPolynomial (p m)
  have hhom : P.IsHomogeneous m := diagonalPolynomial_isHomogeneous _
  have hliehom : (lieDerivative P).IsHomogeneous (m + 2) :=
    lieDerivative_isHomogeneous hm hhom
  have hrem := lieRemainder_isLittleO hp hprior x
  have ht0 := hrem.tendsto_div_nhds_zero
  have ht : Tendsto
      (fun t : ℝ ↦
        (functionLieDerivative V (t • x) -
          evalAt (lieDerivative P) (t • x)) / t ^ (m + 2))
      (𝓝[>] 0) (𝓝 0) :=
    ht0.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hconst : Tendsto (fun _ : ℝ ↦ evalAt (lieDerivative P) x)
      (𝓝[>] 0) (𝓝 (evalAt (lieDerivative P) x)) := tendsto_const_nhds
  have hadd : Tendsto
      (fun t : ℝ ↦
        (functionLieDerivative V (t • x) -
          evalAt (lieDerivative P) (t • x)) / t ^ (m + 2) +
            evalAt (lieDerivative P) x)
      (𝓝[>] 0) (𝓝 (evalAt (lieDerivative P) x)) := by
    simpa using ht.add hconst
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have htne : t ≠ 0 := ne_of_gt htpos
  rw [evalAt_smul_of_isHomogeneous hliehom]
  field_simp [htne]
  ring

theorem leadingTerm_lieNonpositive_of_local_lie
    {V : Point → ℝ} {p : FormalMultilinearSeries ℝ Point ℝ}
    {m : ℕ} {ρ : ℝ}
    (hp : HasFPowerSeriesAt V p 0)
    (hm : 0 < m)
    (hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0)
    (hρ : 0 < ρ)
    (hlie : ∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
      functionLieDerivative V z ≤ 0) :
    LieNonpositive (diagonalPolynomial (p m)) := by
  let P := diagonalPolynomial (p m)
  have hhom : P.IsHomogeneous m := diagonalPolynomial_isHomogeneous _
  have hliehom : (lieDerivative P).IsHomogeneous (m + 2) :=
    lieDerivative_isHomogeneous hm hhom
  intro x
  by_cases hx : x = 0
  · subst x
    change evalAt (lieDerivative P) 0 ≤ 0
    have hscale := evalAt_smul_of_isHomogeneous hliehom 0 (circlePoint 0)
    have hdeg : m + 2 ≠ 0 := by omega
    rw [zero_smul, zero_pow hdeg, zero_mul] at hscale
    exact hscale.le
  · have hlim := leadingLie_ray_tendsto hp hm hprior x
    apply le_of_tendsto hlim
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
    have hsmall0 : ∀ᶠ t : ℝ in 𝓝 0, euclideanNorm (t • x) < ρ := by
      have htend : Tendsto (fun t : ℝ ↦ t • x) (𝓝 0) (𝓝 0) := by
        simpa using
          (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ x)).tendsto 0
      have heuc : Tendsto (fun t : ℝ ↦ euclideanNorm (t • x)) (𝓝 0) (𝓝 0) := by
        simpa using (euclideanNorm_continuous.tendsto (0 : Point)).comp htend
      exact heuc (Iio_mem_nhds hρ)
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, euclideanNorm (t • x) < ρ :=
      hsmall0.filter_mono inf_le_left
    filter_upwards [htpos, hsmall] with t ht hs
    have htx : 0 < euclideanNorm (t • x) :=
      euclideanNorm_pos (smul_ne_zero ht.ne' hx)
    exact div_nonpos_of_nonpos_of_nonneg (hlie (t • x) htx hs)
      (pow_nonneg ht.le (m + 2))

/-- The first nonzero term `P_m` in the manuscript's Taylor expansion,
together with precisely the four properties established before the
integrating-factor argument. -/
theorem exists_leadingHomogeneousPolynomial
    {V : Point → ℝ} {ρ : ℝ}
    (hV : AnalyticAt ℝ V 0) (hV0 : V 0 = 0) (hρ : 0 < ρ)
    (hpos : ∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ → 0 < V z)
    (hlie : ∀ z : Point, 0 < euclideanNorm z → euclideanNorm z < ρ →
      functionLieDerivative V z ≤ 0) :
    ∃ (m : ℕ) (P : BivariatePolynomial),
      0 < m ∧ P.IsHomogeneous m ∧ P ≠ 0 ∧
        (∀ z : Point, 0 ≤ evalAt P z) ∧ LieNonpositive P := by
  obtain ⟨p, hp⟩ := hV
  have hex : ∃ n, DiagonalCoefficientNonzero p n :=
    exists_diagonalCoefficientNonzero hp
      (not_eventuallyEq_zero_of_punctured_pos hρ hpos)
  let m := leadingTaylorDegree p hex
  let P := diagonalPolynomial (p m)
  have hm : 0 < m := leadingTaylorDegree_pos hp hV0 hex
  have hprior : ∀ n < m, ∀ z : Point, p n (fun _ ↦ z) = 0 :=
    leadingTaylorDegree_prior hex
  have hdiag : DiagonalCoefficientNonzero p m := leadingTaylorDegree_nonzero hex
  have hP_ne : P ≠ 0 := diagonalPolynomial_ne_zero hdiag
  have hhom : P.IsHomogeneous m := diagonalPolynomial_isHomogeneous _
  have hnonneg : ∀ z : Point, 0 ≤ evalAt P z :=
    leadingTerm_nonnegative_of_local_pos hp hm hprior hρ hpos
  have hLP : LieNonpositive P :=
    leadingTerm_lieNonpositive_of_local_lie hp hm hprior hρ hlie
  exact ⟨m, P, hm, hhom, hP_ne, hnonneg, hLP⟩

end

end HomogeneousObstruction
