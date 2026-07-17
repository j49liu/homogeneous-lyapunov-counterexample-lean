# Lean formalization of a Lyapunov certificate and polynomial obstruction

## Overview

This Lean 4/mathlib repository formalizes items (2) and (3) of the main theorem
in the paper [1].  For the explicit cubic vector field studied there, item (2)
constructs the Lyapunov certificate

```text
H(x,y) = (x²+y²) exp(-10xy/(x²+y²)),    H(0,0) = 0,
```

and proves its two-sided quadratic bounds, positive definiteness, radial
unboundedness, positive-scalar 2-homogeneity, global `C¹` regularity,
`C∞` regularity off the origin, and the exact identity

```text
L_f H(x,y) = -2(x²+y²)H(x,y) < 0    for (x,y) ≠ (0,0).
```

Item (3) states that no positive definite homogeneous polynomial has an
everywhere nonpositive Lie derivative.  Its formalization includes the strict
Fejér--Riesz factorization, logarithmic second-harmonic bound, and final
Fourier-coefficient contradiction used to prove that obstruction.

The ODE-level global asymptotic stability assertion in main theorem item (1)
is not formalized in this repository.

## Reference

[1] Jun Liu and Maxwell Fitzsimmons, *A Globally Asymptotically Stable Planar
Homogeneous Polynomial Vector Field With No Polynomial Lyapunov Function*.
Manuscript submitted to the *IEEE Transactions on Automatic Control* (IEEE
TAC).

The project is pinned to Lean `v4.30.0` and mathlib `v4.30.0`; the resolved
mathlib revision is recorded in `lake-manifest.json`.

Build and audit the exported theorems with:

```sh
lake build
lake env lean HomogeneousObstruction.lean
```

The second command runs the top-level theorem file and executes both
`#print axioms mainTheorem_item2` and
`#print axioms mainTheorem_item3`.

## Map from the paper to Lean

- `HomogeneousObstruction/StabilityCertificate.lean` defines the explicit
  certificate `stabilityCertificate`, the squared radius, and the
  function-level notions of positive definiteness, radial unboundedness, and
  positive-scalar 2-homogeneity used in item (2).  It proves

  ```text
  exp(-5)(x²+y²) ≤ H(x,y) ≤ exp(5)(x²+y²),
  ```

  and derives positivity, radial unboundedness, and 2-homogeneity.  It also
  formalizes the manuscript's polar proof bridges: the formula
  `H(r,theta)=r² exp(-5 sin(2theta))`, the radial and angular field identities,
  the equations `rdot=r³(-1+5 cos(2theta))` and `thetadot=r²`, and the displayed
  logarithmic-rate cancellation giving `-2r²`.

- `HomogeneousObstruction/ConeTipRegularity.lean` supplies the cone-tip
  regularity step used for item (2).  It formalizes the `k=2` specialization
  needed here: an `O(norm²)` bound on the function and an `O(norm)` bound on
  its derivative imply differentiability at the origin with zero derivative
  and continuity of the extended derivative.  This is not a formalization of
  the manuscript's more general all-`k` cone-tip lemma.

- `HomogeneousObstruction/StabilityCertificateCalculus.lean` proves that the
  certificate is `C∞` off the origin by differentiating its explicit
  Cartesian formula, and supplies a direct Cartesian proof of global `C¹`
  regularity and of `L_f H=-2(x²+y²)H`.  These calculations provide the
  off-origin smoothness and derivative facts used by the manuscript-facing
  modules, but the direct Cartesian assembly is auxiliary: this file exports
  `mainTheorem_item2_cartesian_auxiliary`, not the canonical item-(2) theorem.

- `HomogeneousObstruction/StabilityCertificatePolarLie.lean` implements the
  active polar-coordinate proof of the Lie-derivative identity.  It represents
  each Cartesian point by the norm and argument of the corresponding complex
  number, transports the certificate bounds and two-homogeneity through that
  representation, and decomposes the vector field into radial and angular
  velocities.  It then differentiates `H` along the resulting polar velocity
  curve and applies the manuscript's logarithmic-rate cancellation to prove
  `functionLieDerivative_stabilityCertificate_polar`.

- `HomogeneousObstruction/HomogeneousConeApplication.lean` implements the
  manuscript's homogeneous cone-tip argument for this certificate.  It
  derives degree-one homogeneity of the derivative from two-homogeneity of
  `H`, bounds that derivative on the compact Euclidean unit circle, transports
  the bound along positive rays, and applies the `k=2` cone-tip result to prove
  `stabilityCertificate_contDiff_one_via_homogeneous_cone`.

- `HomogeneousObstruction/StabilityCertificateManuscript.lean` assembles the
  canonical exported theorem `mainTheorem_item2`.  Its active proof uses the
  polar point representation for the bounds, positivity, radial unboundedness,
  and two-homogeneity; the polar velocity-curve chain rule and logarithmic-rate
  calculation for the exact Lie identity; and derivative homogeneity,
  compactness of the Euclidean unit circle, and the `k=2` cone-tip argument for
  global `C¹` regularity.

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

- `HomogeneousObstruction/ActualFourierDegree.lean` makes the opening of
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

- `HomogeneousObstruction/StrictTrigonometricFactorization.lean` exposes the
  intermediate objects written in the manuscript.  It defines `manuscriptB`
  from the roots
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

The top-level file imports the complete item (2) certificate proof and item
(3) obstruction proof, and audits the exported theorems
`mainTheorem_item2` and `mainTheorem_item3` separately.  For item (2), the
canonical theorem is exported by `StabilityCertificateManuscript.lean`.  Its
active dependency path follows the manuscript architecture: polar
point representation, bounds, and two-homogeneity; the polar velocity-curve
chain rule and logarithmic rate for the Lie identity; and derivative
homogeneity plus compactness of the Euclidean unit circle for the homogeneous
cone-tip argument.  Cartesian calculus remains an auxiliary analytic layer
for off-origin differentiability and smoothness, and its separately assembled
theorem is named `mainTheorem_item2_cartesian_auxiliary`.

The manuscript's general all-`k` cone-tip lemma is not formalized: the Lean
development proves and uses precisely the `k=2` case needed for `H`.  The
ODE-level global asymptotic stability assertion in main theorem item (1) is
also not formalized.

For item (3), the proof-specific files `ActualFourierDegree.lean`,
`StrictTrigonometricFactorization.lean`, and `LogSeries.lean` are all on the
transitive dependency path of `mainTheorem_item3`.  More specifically, the active proof
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

## License

Copyright 2026 Jun Liu.

This project is licensed under the [Apache License 2.0](LICENSE).
