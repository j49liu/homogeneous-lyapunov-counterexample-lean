# Lean formalization of the homogeneous-polynomial obstruction

This Lean 4/mathlib project formalizes the homogeneous-polynomial obstruction
proof in:

> Jun Liu and Maxwell Fitzsimmons, *A Globally Asymptotically Stable Planar
> Homogeneous Polynomial Vector Field With No Polynomial Lyapunov Function*.

The manuscript has been submitted to the *IEEE Transactions on Automatic
Control* (IEEE TAC).  The target is item (3) of its main theorem: for the
explicit cubic vector field in the paper, no positive definite homogeneous
polynomial has an everywhere nonpositive Lie derivative.

The project is pinned to Lean `v4.30.0` and mathlib `v4.30.0`; the resolved
mathlib revision is recorded in `lake-manifest.json`.

Build and audit the exported theorem with:

```sh
lake build
lake env lean HomogeneousObstruction.lean
```

The second command runs the manuscript theorem file and prints the axioms of
the final exported theorem.

## Map from the manuscript to Lean

- `HomogeneousObstruction/Basic.lean` encodes the paper's cubic vector field as
  `field₁`, `field₂`, and `vectorField`; represents real bivariate
  polynomials by `MvPolynomial (Fin 2) ℝ`; and defines `Homogeneous`,
  `PositiveDefinite`, the `pderiv`-based `lieDerivative`, and the weak
  Lie-derivative inequality.  Positive definiteness includes both `P(0)=0`
  and strict positivity away from the origin.  `radial_field_identity` and
  `angular_field_identity` are the Cartesian identities used to derive the
  polar system.  `lieNonpositive_iff_awayFromZero` records that the paper's
  away-from-zero formulation is equivalent to the all-points formulation,
  because the Lie derivative vanishes at the origin.

- `HomogeneousObstruction/Degree.lean` proves the homogeneous scaling law and
  the positive, even degree reduction.  In particular, the final theorem does
  not assume in advance that the degree is `2 * N`.  `lieDerivative_polar`
  formalizes the full-radius identity

  ```text
  L_f P(r cos θ, r sin θ)
    = r^(2N+2) (p'(θ) + 2N (-1 + 5 cos(2θ)) p(θ)),
  ```

  while `circleTrace_pi_periodic_of_evenDegree` records the parity used in the
  Fourier argument.

- `HomogeneousObstruction/HalfAnglePolynomial.lean` defines the manuscript's
  half-angle trace `q(φ)=p(φ/2)`.  As a Lean-side algebraic device for
  proving the finite expansion, it constructs the auxiliary Laurent numerator
  `Pℂ((z+1)/2,(z-1)/(2i))` centered at `N`, and proves its degree bound,
  Laurent representation, positivity, periodicity, and nonzeroness.  The
  manuscript's displayed actual-degree polynomial `A_L` is defined in the
  next module.

- `HomogeneousObstruction/ManuscriptFourierDegree.lean` makes the opening of
  the logarithmic second-harmonic lemma explicit.  The theorems
  `halfAngleTrace_finiteFourierExpansion` and
  `circleTrace_evenFourierExpansion` give the finite modes of `q` and the even
  modes of `p`.  `manuscriptHalfAngleFourierDegree` is the actual degree `L`;
  `halfAngleFourierCoefficient_eq_paperFourierCoeff` proves that these
  algebraic coefficients are exactly the integral-defined coefficients under
  the paper's sign and `1/(2π)` convention.  The polynomial
  `manuscriptClearedPolynomial` is precisely
  `A_L(z)=∑_{j=-L}^L c_j z^(j+L)`; its degree, nonzero constant term,
  self-inversiveness, and Laurent representation are proved directly from the
  integral Fourier coefficients and the real-valued symmetry
  `conj(c_j)=c_{-j}`, without the former workaround that replaced `q(φ)` by
  `q(-φ)` and reversed an auxiliary cleared polynomial.  The public
  half-angle expansion is obtained from the displayed even-mode expansion of
  `p`, so both manuscript expansions are on the active proof path.  Strict
  positivity of the zero Fourier coefficient locates the Laurent centre, and
  the support and endpoint theorems prove that the nonzero modes are exactly
  bounded by `-L` and `L`, with `L ≤ N`.  The `...Degree_eq_zero` theorems
  implement the manuscript's separate `L=0` case, proving that `q` and `p`
  are constant and that the normalized derivative vanishes before
  factorization is invoked.  `manuscriptHalfAngleFactorization_of_degree_pos`
  is the handoff for the subsequent `L>0` case.

- `HomogeneousObstruction/FejerRiesz.lean` supplies the shared strict
  Fejér--Riesz machinery and interfaces: reciprocal-conjugate root pairing
  with multiplicities, exclusion of unit-circle roots, separation of inside
  and outside roots, and the product/polynomial data structures with their
  degree, zero-free, and squared-norm consequences.

- `HomogeneousObstruction/ManuscriptFejerRiesz.lean` exposes the intermediate
  objects written in the manuscript.  It defines `manuscriptB` from the roots
  outside the unit disk and `manuscriptBsharp` for `B#`, proves their degree,
  root, and unit-circle identities, and proves the scalar relation
  `A = κ B B#` in `manuscript_exists_kappa_mul_B_Bsharp`.
  `manuscript_strictFejerRiesz_of_selfInversive` then follows the remainder of
  the paper's proof: it proves that `κ` is real and positive, takes
  `Q = sqrt(κ) B`, proves that `Q` has degree `L` and no zero in the closed
  unit disk, and obtains `q=|Q|²`.  The stated theorem
  `manuscript_strict_trigonometric_factorization` separately treats `L=0` as
  immediate, exactly as the paper does, and is invoked by the final proof.
  `manuscript_normalize_strict_trigonometric_factor` then factors that very
  same returned polynomial as `Q = factorConstant · ∏ₗ(1-αₗX)`, with
  exactly `L` parameters `|αₗ|<1`, and derives the squared-norm product and
  `normalized.c=|factorConstant|²` by evaluating this polynomial identity.
  Thus the logarithmic calculation does not use a parallel product
  factorization.

- `HomogeneousObstruction/FourierBasic.lean` fixes the paper's convention

  ```text
  û_j = (1 / (2π)) ∫₀²ᵖ u(θ) exp(-i j θ) dθ,
  ```

  including the sign and normalization.  It proves the coefficients of the
  constant function and `cos(2θ)`, the zero mean of the real logarithmic
  derivative, and the elementary nonnegative-function estimate used for
  `w`.

- `HomogeneousObstruction/LogSeries.lean` formalizes the literal logarithmic
  series step in the manuscript.  It defines the positive- and
  negative-frequency logarithmic series, proves their pointwise identities
  with the corresponding complex-log branches, and proves uniform convergence
  of both the original and differentiated series.  Those named uniform-limit
  theorems are the hypotheses used to justify both termwise differentiation
  and termwise Fourier integration.  `manuscriptG_eq_factor_log_expansion` is
  the displayed expansion of `G=(1/(2N)) log p`, and
  `manuscript_logarithmic_fourier_formula` proves the manuscript's exact
  second-mode formula

  ```text
  ĝ₂ = -(i/N) ∑ αₗ.
  ```

- `HomogeneousObstruction/LogBound.lean` exports the strict estimate
  `logarithmicSecondHarmonicBound`, corresponding to the paper's logarithmic
  second-harmonic lemma.  `HomogeneousObstruction/Obstruction.lean` carries out
  the final `w`-coefficient contradiction and exports
  `no_positiveDefinite_homogeneous_polynomial` and `mainTheorem_item3` in the
  paper's all-points formulation, together with the equivalent punctured
  formulation `mainTheorem_item3_awayFromZero`.

## Integration status

The manuscript-specific files `ManuscriptFourierDegree.lean`,
`ManuscriptFejerRiesz.lean`, and `LogSeries.lean` are all on the transitive
dependency path of `mainTheorem_item3`.  More specifically, the active proof
uses the displayed even-mode and half-angle expansions, the paper-normalized
Fourier coefficients, real coefficient conjugacy, the actual-degree split,
the stated strict trigonometric factorization, the direct `A_L=κBB#`
construction, normalization of that same returned `Q`, the uniform-limit
logarithmic Taylor-series calculation, the strict `L/N` estimate, and the
final Fourier contradiction.  The obsolete `q(-φ)`/auxiliary-polynomial
workaround, padded-symmetry factorization, mean-value argument, and
algebraic-logarithmic-derivative route are not present.  Coefficient
conjugate-reflection remains where the manuscript itself uses the
self-inversive identity and `B#`.
`#print axioms mainTheorem_item3` audits this composed proof, not merely
separate manuscript-facing refinements.
