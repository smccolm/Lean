---
title: "A Lean-Verified Derivation of the Complete Elliptic Series for the Perimeter of an Ellipse"
author: "Author Name"
date: "Draft v1"
---

# Abstract

The perimeter of an ellipse is a classical example of a natural geometric quantity whose exact expression is not elementary.  If \(A\) and \(B\) are the semiaxes, with \(A\ge B\ge 0\), the usual reduction gives

$$
P=4A E(e),
\qquad
e=\sqrt{1-\left(\frac{B}{A}\right)^2},
$$

where \(E\) is the complete elliptic integral of the second kind.  This paper gives a self-contained derivation of the corresponding infinite series

$$
P
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n}.
$$

The proof is organized to match a Lean formalization.  It starts from the full-loop parametric arc-length integral, reduces the geometric integral to Legendre's complete elliptic integral \(E\), proves the square-root binomial series needed for the integrand, justifies termwise integration by a uniform domination argument, evaluates the resulting even sine-power integrals by Wallis' recurrence, and treats the endpoint \(e=1\) separately by a Wallis squeeze.  The final statement covers all nonnegative semiaxes \(a,b\) with \(a+b>0\), using \(A=\max(a,b)\) and \(B=\min(a,b)\).  Thus the ordinary ellipse case \(0<B\le A\), the circle case \(A=B\), and the degenerate line-segment case \(B=0\) are handled in one theorem.

# 1. Introduction

The circumference of a circle is elementary, but the circumference of an ellipse is not.  For an ellipse with semiaxes \(A\) and \(B\), the full-loop arc length is obtained from the parametrization

$$
\gamma(\theta)=(A\cos\theta,B\sin\theta),
\qquad
0\le \theta\le 2\pi.
$$

The speed is

$$
\|\gamma'(\theta)\|
=
\sqrt{A^2\sin^2\theta+B^2\cos^2\theta}.
$$

When \(A=B\), integrating this speed gives \(2\pi A\).  When \(0<B<A\), the same integral is no longer elementary and is expressed through the complete elliptic integral of the second kind,

$$
E(k)=\int_0^{\pi/2}\sqrt{1-k^2\sin^2\theta}\,d\theta.
$$

The standard perimeter formula is

$$
P=4A E(e),
\qquad
e=\sqrt{1-\frac{B^2}{A^2}}.
$$

The corresponding power series is

$$
E(k)
=
\frac{\pi}{2}
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{k^{2n}}{1-2n}.
$$

Combining these gives

$$
P
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n}.
$$

The purpose of this paper is not merely to cite this formula.  The purpose is to account for the analytic steps in a form suitable for machine checking.  The natural-language proof therefore follows the same decomposition as the Lean proof.  That decomposition has several advantages.  It separates geometry from analysis, it isolates the scalar binomial-series identity, and it treats the endpoint \(k=1\) without pretending that the open-interval binomial argument applies there.

The main theorem is stated symmetrically in the original semiaxes.  Let

$$
A=\max(a,b),
\qquad
B=\min(a,b),
\qquad
e=\sqrt{1-\left(\frac{B}{A}\right)^2}.
$$

For \(a,b\ge 0\) and \(a+b>0\), one has \(A>0\), \(0\le B\le A\), and \(0\le e\le 1\).  The final result is

$$
P(a,b)
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n}.
$$

This includes three boundary checks that are often a source of mistakes.  If \(a=b=A\), then \(e=0\) and the formula reduces to \(P=2\pi A\).  If \(B=0\), then \(e=1\) and the formula reduces to \(P=4A\).  If \(a\) and \(b\) are interchanged, the expression is unchanged because \(A\) and \(B\) are defined by maximum and minimum.

# 2. Statement of the result

For \(n\in\mathbb{N}\), define

$$
c_n
=
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{1}{1-2n}.
$$

The first coefficients are

$$
c_0=1,\qquad
c_1=-\frac14,\qquad
c_2=-\frac{3}{64},\qquad
c_3=-\frac{5}{256}.
$$

Thus the series begins

$$
E(k)
=
\frac{\pi}{2}
\left(
1-\frac{k^2}{4}
-\frac{3k^4}{64}
-\frac{5k^6}{256}
-\cdots
\right).
$$

The geometric theorem can then be stated as follows.

**Theorem 2.1.**  
Let \(a,b\ge 0\) and \(a+b>0\).  Put

$$
A=\max(a,b),
\qquad
B=\min(a,b),
\qquad
e=\sqrt{1-\left(\frac{B}{A}\right)^2}.
$$

Then the full parametric arc length of the ellipse

$$
\gamma(\theta)=(A\cos\theta,B\sin\theta),
\qquad
0\le \theta\le 2\pi,
$$

is

$$
P(a,b)
=
2\pi A
\sum_{n=0}^{\infty}c_n e^{2n}.
$$

Equivalently,

$$
P(a,b)
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n}.
$$

The Lean theorem corresponding to this statement is named `ellipse_perimeter_series`.  In Lean syntax, the conclusion is expressed as

```lean
ellipseParametricPerimeter a b =
  2 * Real.pi * max a b *
    ∑' n : ℕ,
      ellipticESeriesCoeff n *
        eccentricity (max a b) (min a b) ^ (2 * n)
```

under the hypotheses \(0\le a\), \(0\le b\), and \(0<a+b\).

# 3. From the parametric ellipse to a quadrant integral

Let \(A\ge B\ge 0\).  The full parametric perimeter is

$$
P
=
\int_0^{2\pi}
\sqrt{A^2\sin^2\theta+B^2\cos^2\theta}
\,d\theta.
$$

The integrand is invariant under the usual quadrant symmetries.  Hence the full integral is four times a quadrant integral:

$$
P
=
4
\int_0^{\pi/2}
\sqrt{A^2\sin^2\theta+B^2\cos^2\theta}
\,d\theta.
$$

A convenient reparametrization of the quadrant gives

$$
\int_0^{\pi/2}
\sqrt{A^2\sin^2\theta+B^2\cos^2\theta}
\,d\theta
=
A
\int_0^{\pi/2}
\sqrt{1-e^2\sin^2\phi}
\,d\phi,
$$

where

$$
e^2=1-\left(\frac{B}{A}\right)^2.
$$

Therefore

$$
P=4A E(e),
$$

where

$$
E(e)=\int_0^{\pi/2}\sqrt{1-e^2\sin^2\phi}\,d\phi.
$$

The Lean development keeps this geometry separate from the later series proof.  The final geometric object is the full-loop parametric arc length, and a chain of bridge theorems proves that it agrees with the model perimeter.  In conceptual form, the bridge is

$$
\text{full loop}
=
4\cdot \text{quadrant}
=
4A E(e).
$$

This separation matters because the analytic series proof is naturally a theorem about \(E(k)\), while the final theorem is a theorem about the geometric perimeter.

# 4. The complete elliptic integral and the coefficient sequence

The complete elliptic integral of the second kind is

$$
E(k)
=
\int_0^{\pi/2}
\sqrt{1-k^2\sin^2\theta}
\,d\theta.
$$

For \(0\le k<1\), the integrand can be expanded using the scalar binomial series for \(\sqrt{1-x}\), with \(x=k^2\sin^2\theta\).  The coefficient sequence used throughout the proof is

$$
w_n
=
\frac{(2n)!}{2^{2n}(n!)^2}.
$$

This is the even Wallis coefficient.  The square-root coefficient is

$$
a_n
=
\frac{w_n}{1-2n}.
$$

The elliptic coefficient is

$$
c_n=a_nw_n
=
w_n^2\frac{1}{1-2n}.
$$

The reason two factors of \(w_n\) appear is structural.  One factor comes from the binomial expansion of the square root.  The other factor comes from evaluating the integral of \(\sin^{2n}\theta\) over \([0,\pi/2]\).  This is the main accounting identity:

$$
\int_0^{\pi/2}
a_n k^{2n}\sin^{2n}\theta\,d\theta
=
a_n k^{2n}
\int_0^{\pi/2}
\sin^{2n}\theta\,d\theta
=
\frac{\pi}{2}c_nk^{2n}.
$$

Thus, once termwise integration is justified,

$$
E(k)
=
\frac{\pi}{2}
\sum_{n=0}^{\infty}c_nk^{2n}.
$$

# 5. The scalar binomial series

The scalar analytic core is the identity

$$
\sqrt{1-x}
=
\sum_{n=0}^{\infty}
\binom{1/2}{n}(-x)^n,
\qquad |x|<1.
$$

In the proof, this is represented using the coefficient sequence

$$
a_n=\frac{w_n}{1-2n},
\qquad
w_n=\frac{(2n)!}{2^{2n}(n!)^2}.
$$

The first few terms are

$$
1-\frac{x}{2}-\frac{x^2}{8}-\frac{x^3}{16}-\cdots .
$$

The Lean proof avoids relying on a black-box analytic theorem for this specific identity.  Instead it builds the series

$$
S(x)=\sum_{n=0}^{\infty}a_nx^n
$$

and proves

$$
S(x)=\sqrt{1-x}
\qquad (|x|<1).
$$

The proof has three main parts.

First, the series is absolutely summable for \(|x|<1\).  The recurrence

$$
a_{n+1}
=
\frac{2n-1}{2n+2}a_n
$$

implies the ratio estimate

$$
|a_{n+1}x^{n+1}|
\le
|x|\,|a_nx^n|.
$$

Since \(|x|<1\), the ratio test gives summability.

Second, the square of the sum is computed by the Cauchy product.  Writing

$$
a_nx^n=\binom{1/2}{n}(-x)^n,
$$

one obtains

$$
S(x)^2
=
\sum_{n=0}^{\infty}
\left(
\sum_{i+j=n}
\binom{1/2}{i}\binom{1/2}{j}
\right)(-x)^n.
$$

Vandermonde's identity gives

$$
\sum_{i+j=n}
\binom{1/2}{i}\binom{1/2}{j}
=
\binom{1}{n}.
$$

Therefore

$$
S(x)^2
=
\sum_{n=0}^{\infty}\binom{1}{n}(-x)^n
=
1-x.
$$

Third, the sign is fixed.  The equation \(S(x)^2=1-x\) alone gives \(S(x)=\pm\sqrt{1-x}\).  The proof shows \(S(x)\ge 0\) on \((-1,1)\).  Since \(S(0)=1\), a negative value of \(S(x)\) would force a zero between \(0\) and \(x\) by continuity.  At such a zero \(y\), the identity \(S(y)^2=1-y\) would give \(y=1\), contradicting \(|y|<1\).  Hence \(S(x)\ge 0\), and so

$$
S(x)=\sqrt{1-x}.
$$

This argument is well suited to formalization because it reduces the branch choice for the square root to continuity and the intermediate value theorem, rather than informal sign reasoning.

# 6. Substitution into the elliptic integrand

Let \(|k|<1\).  For \(0\le\theta\le\pi/2\),

$$
0\le k^2\sin^2\theta<1.
$$

Applying the scalar identity with \(x=k^2\sin^2\theta\) gives

$$
\sqrt{1-k^2\sin^2\theta}
=
\sum_{n=0}^{\infty}
a_n k^{2n}\sin^{2n}\theta.
$$

Define

$$
f_n(\theta)
=
a_n k^{2n}\sin^{2n}\theta.
$$

Then

$$
E(k)=\int_0^{\pi/2}\sum_{n=0}^{\infty}f_n(\theta)\,d\theta.
$$

The next step is to justify

$$
\int_0^{\pi/2}\sum_{n=0}^{\infty}f_n(\theta)\,d\theta
=
\sum_{n=0}^{\infty}\int_0^{\pi/2}f_n(\theta)\,d\theta.
$$

This is not a cosmetic step.  It is the point at which convergence and integration interact.  In the formal proof, the interchange is obtained using dominated convergence for interval integrals.

For all \(\theta\),

$$
|\sin\theta|\le 1,
$$

so

$$
|f_n(\theta)|
\le
|a_n|\,|k|^{2n}.
$$

The bounding series

$$
\sum_{n=0}^{\infty}|a_n|\,|k|^{2n}
$$

converges by the same ratio estimate used for the scalar series, because \(|k|^2<1\).  The bound is independent of \(\theta\), and hence it is integrable on the finite interval \([0,\pi/2]\).  This gives a clean dominated-convergence proof of termwise integration.

Therefore

$$
E(k)
=
\sum_{n=0}^{\infty}
a_n k^{2n}
\int_0^{\pi/2}\sin^{2n}\theta\,d\theta.
$$

# 7. Wallis integrals

It remains to evaluate

$$
I_n=\int_0^{\pi/2}\sin^{2n}\theta\,d\theta.
$$

The Wallis recurrence is

$$
I_{n+1}
=
\frac{2n+1}{2n+2}I_n,
\qquad
I_0=\frac{\pi}{2}.
$$

It follows that

$$
I_n
=
\frac{\pi}{2}
\prod_{j=0}^{n-1}
\frac{2j+1}{2j+2}.
$$

The product is exactly

$$
w_n=
\frac{(2n)!}{2^{2n}(n!)^2}.
$$

Thus

$$
I_n=\frac{\pi}{2}w_n.
$$

Substituting into the termwise-integrated expression gives

$$
E(k)
=
\sum_{n=0}^{\infty}
a_nk^{2n}\frac{\pi}{2}w_n
=
\frac{\pi}{2}
\sum_{n=0}^{\infty}
a_nw_nk^{2n}.
$$

Since \(c_n=a_nw_n\),

$$
E(k)
=
\frac{\pi}{2}
\sum_{n=0}^{\infty}
c_nk^{2n}.
$$

This proves the series for \(|k|<1\).

# 8. The endpoint \(k=1\)

The binomial-series argument proves the expansion for \(|k|<1\).  The degenerate ellipse case \(B=0\), however, gives \(e=1\).  The proof therefore handles \(k=1\) separately.

The integral value is direct:

$$
E(1)
=
\int_0^{\pi/2}
\sqrt{1-\sin^2\theta}
\,d\theta.
$$

On \([0,\pi/2]\), \(\cos\theta\ge 0\), so

$$
\sqrt{1-\sin^2\theta}=\cos\theta.
$$

Hence

$$
E(1)=\int_0^{\pi/2}\cos\theta\,d\theta=1.
$$

The series value at \(1\) is more delicate.  The proof shows

$$
\frac{\pi}{2}
\sum_{n=0}^{\infty}c_n
=
1.
$$

For partial sums, define

$$
S_N=\sum_{n=0}^{N}c_n.
$$

The coefficient algebra gives the closed form

$$
S_N=(2N+1)w_N^2.
$$

Thus

$$
\frac{\pi}{2}S_N
=
\frac{\pi}{2}(2N+1)w_N^2.
$$

Wallis' inequalities give the squeeze

$$
1
\le
\frac{\pi}{2}(2N+1)w_N^2
\le
\frac{2N+2}{2N+1}.
$$

The right-hand side tends to \(1\).  Hence

$$
\lim_{N\to\infty}
\frac{\pi}{2}S_N
=
1.
$$

Therefore the series also gives \(E(1)=1\).  This is exactly what is needed for the degenerate semiaxis case \(B=0\), since then

$$
P=4A E(1)=4A.
$$

Geometrically, this agrees with the limiting ellipse, a line segment of length \(2A\) traced forth and back by the parametric loop.

# 9. Completing the perimeter series

Combining the geometric reduction with the elliptic-series theorem gives the result.  For \(A=\max(a,b)\), \(B=\min(a,b)\), and

$$
e=\sqrt{1-\left(\frac{B}{A}\right)^2},
$$

the perimeter is

$$
P(a,b)=4A E(e).
$$

For \(0\le e\le 1\),

$$
E(e)
=
\frac{\pi}{2}
\sum_{n=0}^{\infty}c_ne^{2n}.
$$

Therefore

$$
P(a,b)
=
4A
\cdot
\frac{\pi}{2}
\sum_{n=0}^{\infty}c_ne^{2n}
=
2\pi A
\sum_{n=0}^{\infty}c_ne^{2n}.
$$

Unfolding \(c_n\),

$$
P(a,b)
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n}.
$$

This is the desired series.

# 10. Boundary and consistency checks

The proof includes several checks that are worth stating explicitly.

## 10.1. Circle case

If \(a=b=A>0\), then \(B=A\) and

$$
e=\sqrt{1-\left(\frac{A}{A}\right)^2}=0.
$$

The series becomes

$$
\sum_{n=0}^{\infty}c_ne^{2n}=c_0=1.
$$

Thus

$$
P=2\pi A,
$$

which is the ordinary circumference of a circle.

## 10.2. Degenerate case

If \(A>0\) and \(B=0\), then

$$
e=\sqrt{1-0}=1.
$$

The endpoint result gives

$$
E(1)=1,
$$

and therefore

$$
P=4A.
$$

This matches the full-loop parametrization \((A\cos\theta,0)\), which traverses the interval \([-A,A]\) twice.

## 10.3. Symmetry in the semiaxes

The formula is symmetric in the original inputs \(a\) and \(b\) because it is written using

$$
A=\max(a,b),
\qquad
B=\min(a,b).
$$

Thus the same theorem applies whether the larger semiaxis is originally called \(a\) or \(b\).

## 10.4. Bounds

Since

$$
1\le E(k)\le \frac{\pi}{2}
\qquad
(0\le k\le 1),
$$

the perimeter satisfies

$$
4A\le P(a,b)\le 2\pi A.
$$

The lower endpoint corresponds to the degenerate segment, and the upper endpoint corresponds to the circle.

# 11. Structure of the Lean formalization

The Lean proof mirrors the natural proof above, but every analytic transition is made explicit.  The main objects are as follows.

The geometric endpoint is `ellipseParametricPerimeter`.  This is the full-loop arc-length definition.  The theorem `ellipseParametricPerimeter_eq_ellipsePerimeter` connects the geometric definition to the earlier analytic model.

The theorem `completeEllipticEModulus_eq_trig` proves that the parameter form and the trigonometric form of the complete elliptic integral agree.  This accounts for the substitution \(t=\sin^2\theta\).

The theorem `sqrtOneSubSeriesTarget_of_abs_lt_one` proves the scalar identity

$$
\sqrt{1-x}
=
\sum_{n=0}^{\infty}
\binom{1/2}{n}(-x)^n
$$

for \(|x|<1\).  The proof proceeds through summability, Cauchy products, Vandermonde's identity, and the nonnegativity argument described above.

The theorem `eTrigTermwiseTarget_of_abs_lt_one` justifies termwise integration for \(|k|<1\) by dominated convergence.

The theorem `wallisTarget_all` evaluates the even sine-power integrals.  In mathematical notation, it proves

$$
\int_0^{\pi/2}\sin^{2n}\theta\,d\theta
=
\frac{\pi}{2}
\frac{(2n)!}{2^{2n}(n!)^2}.
$$

The theorem `seriesExpansionTarget_final_clean` combines the scalar binomial identity, termwise integration, and Wallis integral evaluation to prove the elliptic series for \(|k|<1\).

The theorem `completeEllipticESeries_one_eq_one` proves the endpoint value of the series at \(k=1\).  It is separate from the open interval proof.

The theorem `ellipsePerimeterModel_eq_completeEllipticESeries` proves the all-cases model theorem for nonnegative semiaxes.

The final theorem `ellipse_perimeter_series` states the result for the full geometric parametric perimeter:

$$
\operatorname{Perim}(a,b)
=
2\pi\max(a,b)
\sum_{n=0}^{\infty}
c_n
\operatorname{ecc}(\max(a,b),\min(a,b))^{2n}.
$$

The proof is consequently not a single clever calculation.  It is a sequence of bridges, each one small enough to be checked independently.

# 12. Why the formalization matters

The standard derivation of the ellipse perimeter series is short on paper, but it contains several points at which informal exposition can conceal real obligations.

First, the square-root binomial series is only directly valid for \(|x|<1\).  Since \(x=k^2\sin^2\theta\), this covers \(|k|<1\), but not \(k=1\) at \(\theta=\pi/2\).  The endpoint must therefore be handled separately.

Second, termwise integration is not automatic.  It requires a convergence theorem.  The proof uses a dominating summable series independent of \(\theta\), which is a standard and robust way to justify the interchange.

Third, the sign of the square root matters.  Showing \(S(x)^2=1-x\) does not by itself identify \(S(x)\) with the nonnegative square root.  The Lean proof records the necessary nonnegativity argument.

Fourth, the final theorem is geometric, not merely analytic.  A proof of

$$
E(k)
=
\frac{\pi}{2}\sum_{n=0}^{\infty}c_nk^{2n}
$$

does not by itself prove the ellipse perimeter formula.  One still has to connect the full-loop parametric arc length to \(4AE(e)\).  The formalization makes this bridge explicit.

These are exactly the sorts of details that can disappear in a familiar textbook derivation.  A machine-checked proof forces the argument to account for them.

# 13. Conclusion

The perimeter of an ellipse with nonnegative semiaxes \(a,b\), not both zero, admits the series

$$
P(a,b)
=
2\pi A
\sum_{n=0}^{\infty}
\left(
\frac{(2n)!}{2^{2n}(n!)^2}
\right)^2
\frac{e^{2n}}{1-2n},
$$

where

$$
A=\max(a,b),
\qquad
B=\min(a,b),
\qquad
e=\sqrt{1-\left(\frac{B}{A}\right)^2}.
$$

The proof proceeds by reducing the full-loop arc length to \(4AE(e)\), proving the series for \(E(k)\) on \(|k|<1\), and then proving the endpoint \(k=1\) by Wallis partial sums.  The Lean formalization confirms the complete chain from the parametric geometric definition to the infinite series statement.

# Appendix A. Lean theorem map

The final proof can be read through the following dependency map.

1. Geometry:
   - `ellipseFullLoopArcLength_eq_four_mul_quadrant`
   - `ellipseParametricPerimeter_eq_ellipseGeometricPerimeter`
   - `ellipseParametricPerimeter_eq_ellipsePerimeter`

2. Model and elliptic integral:
   - `ellipsePerimeterModel_eq_classicalIntegral_of_nonneg`
   - `completeEllipticEModulus_eq_trig`
   - `ellipsePerimeterModel_eq_four_mul_completeEllipticETrig_of_nonneg`

3. Coefficients:
   - `wallisEvenCoeff`
   - `sqrtOneSubCoeff`
   - `ellipticESeriesCoeff`
   - `ellipticESeriesCoeff_eq_bridge`

4. Scalar binomial series:
   - `sqrtOneSubSeriesSummable_of_abs_lt_one`
   - `sqrtOneSubSeries_sq_eq_one_sub`
   - `sqrtOneSubSeries_nonneg_of_abs_lt_one`
   - `sqrtOneSubSeriesTarget_of_abs_lt_one`

5. Termwise integration:
   - `eTrigBinomialTarget_of_sqrtOneSubSeriesTarget_of_abs_lt_one`
   - `eTrigTermwiseTarget_of_abs_lt_one`

6. Wallis integrals:
   - `wallisRecurrenceTarget_proved`
   - `wallisTarget_all`
   - `integral_eTrigBinomialTerm_eq_scaled_seriesTerm`

7. Open-interval elliptic series:
   - `seriesExpansionTarget_final_clean`

8. Endpoint:
   - `completeEllipticETrig_one`
   - `ellipticESeriesCoeff_partialSum_closed_form`
   - `wallisScaledPartial_squeeze`
   - `completeEllipticESeries_one_eq_one`

9. Public model theorem:
   - `ellipsePerimeterModel_eq_completeEllipticESeries`
   - `ellipsePerimeter_eq_four_mul_tsum_of_nonneg`
   - `ellipsePerimeter_eq_series`

10. Final geometric theorem:
   - `ellipse_perimeter_series`

# References

Abramowitz, Milton, and Irene A. Stegun, eds. *Handbook of Mathematical Functions with Formulas, Graphs, and Mathematical Tables*. National Bureau of Standards, 1964.

de Moura, Leonardo, and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language." In *Automated Deduction, CADE 28*, Lecture Notes in Computer Science 12699, 625-635. Springer, 2021.

NIST Digital Library of Mathematical Functions. "Chapter 19: Elliptic Integrals." Version 1.2.6. National Institute of Standards and Technology. https://dlmf.nist.gov/19

The mathlib Community. "The Lean Mathematical Library." In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 367-381. ACM, 2020.

Whittaker, E. T., and G. N. Watson. *A Course of Modern Analysis*. 4th ed. Cambridge University Press, 1927.
