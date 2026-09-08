## Abstract

We give a rigorous derivation of the classical infinite-series formula for the perimeter of an ellipse. For nonnegative semiaxes \(a\) and \(b\), not both zero, let \(A=\max(a,b)\), \(B=\min(a,b)\), and let

$$
e=\sqrt{1-\left(\frac{B}{A}\right)^2}.
$$

The perimeter is shown to be

$$
P(a,b)=4A\,E(e),
$$

where

$$
E(e)=\int_0^{\pi/2}\sqrt{1-e^2\sin^2\theta}\,d\theta
$$

is the complete elliptic integral of the second kind. We then derive the series representation

$$
E(e)=\frac{\pi}{2}\sum_{n=0}^{\infty}
\left(\frac{(2n)!}{2^{2n}(n!)^2}\right)^2
\frac{e^{2n}}{1-2n},
$$

valid for \(0\le e\le 1\), with the endpoint \(e=1\) handled separately by a Wallis-type limiting argument. The proof proceeds through the generalized binomial expansion of \(\sqrt{1-x}\), uniform domination sufficient for termwise integration on \(0\le e<1\), evaluation of the resulting even-power sine integrals, and a Wallis squeeze at the degenerate endpoint. The result is also formalized in Lean, giving a mechanically checked proof of the full nonnegative-semiaxis statement, including the circular and degenerate cases.
