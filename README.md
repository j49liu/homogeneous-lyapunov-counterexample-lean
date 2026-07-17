# Lean formalization of the homogeneous-polynomial obstruction

This directory formalizes item (3) of the main theorem in
`../TAC_submission.tex`.  It is a Lean 4 project pinned to Lean `v4.30.0` and
mathlib `v4.30.0` (resolved by `lake-manifest.json` to mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`).

Build and audit with:

```sh
lake build
lake env lean HomogeneousObstruction.lean
```

The second command prints the axioms of the final theorem.

## Map from the paper to Lean

- `HomogeneousObstruction/Basic.lean` defines the cubic field `field₁`,
  `field₂`, `vectorField`, bivariate polynomials as
  `MvPolynomial (Fin 2) ℝ`, `Homogeneous`, `PositiveDefinite`, the
  `pderiv`-based `lieDerivative`, `LieNonpositive`, the circle trace, and its
  angular derivative.  `lieDerivative_on_circle` is equation (5.6) of the
  paper, proved from the polynomial chain rule and mathlib's homogeneous Euler
  identity.
- `HomogeneousObstruction/Degree.lean` proves that positive definiteness (with
  `P(0)=0`) forces the homogeneous degree to be positive and even.  The final
  theorem therefore does not assume an even degree.
  `circleTrace_pi_periodic_of_evenDegree` records the corresponding even-mode
  parity of the circle trace explicitly.
- `HomogeneousObstruction/HalfAnglePolynomial.lean` follows the paper by
  defining `q(φ)=p(φ/2)` and constructing its cleared ordinary polynomial
  `Pℂ((z+1)/2,(z-1)/(2i))`.  It proves the exact Laurent representation centered
  at `N`, degree bound `2N`, padded reciprocal-conjugate symmetry, nonzeroness,
  and `2π`-periodicity.  `strictFejerRiesz_halfAngle` supplies the paper's
  factorization with actual factor count `L ≤ N`.
- `HomogeneousObstruction/FejerRiesz.lean` proves the strict Fejer--Riesz lemma
  from reciprocal-conjugate root pairing, including multiplicities and removal
  of endpoint zero coefficients.  `strictFejerRiesz_of_selfInversive` and
  `strictFejerRiesz_of_padded_selfInversive` produce factors with parameters
  strictly inside the unit disk.  `StrictFejerRieszData.spectralFactor` and
  `strictFejerRiesz_polynomial_of_selfInversive` expose the polynomial `Q`, its
  exact factor-count degree, its absence of zeros in the closed unit disk, and
  `q(θ)=|Q(exp(iθ))|²`.
- `HomogeneousObstruction/FourierBasic.lean` defines
  `paperFourierCoeff` with the paper's convention
  `(2π)⁻¹ ∫₀²ᵖ u(θ) exp(-inθ) dθ`.  It proves the normalized integral
  formula, the coefficients of `1` and `cos(2θ)`, the zero mean of a real
  logarithmic derivative, the half-angle rescaling identity
  `widehat{(u ∘ (2·))}_2 = û_1`, and the elementary estimate `|ŵₙ| ≤ ŵ₀`
  for `w ≥ 0`.
- `HomogeneousObstruction/MeanLemmas.lean` supplies the complex circle-average
  identities used instead of geometric-series or logarithm-branch arguments.
- `HomogeneousObstruction/LogBound.lean` proves Lemma 5.2 as
  `logarithmicSecondHarmonicBound`.  The parametric theorem
  `halfAngleNormalizedLogDerivative_fourierCoeff_one_of_factorization` proves
  the paper's exact formula `-(i/N) ∑ αₗ`; the subsequent strict theorem uses
  `L ≤ N` and `|αₗ|<1`, and Fourier rescaling returns to mode two of `p`.
- `HomogeneousObstruction/Obstruction.lean` proves the coefficient
  contradiction parametrically in `fourierContradiction_of_log_bound`, then
  exports `no_positiveDefinite_homogeneous_polynomial` and the literal
  nonexistence statement `mainTheorem_item3`.

## Correspondence with the paper's presentation

The Lean proof now follows the paper's substantive proof route: it passes to
`q(φ)=p(φ/2)`, factors `q` with actual degree `L ≤ N`, obtains
`ĝ₂=-(i/N)∑αₗ`, proves the strict `L/N` bound, and uses the same final Fourier
contradiction.  The paper and Lean now use the same branch-free coefficient
calculation: differentiate the finite factorization, divide by it, and evaluate
the resulting circle averages by the mean-value property for holomorphic
functions.
