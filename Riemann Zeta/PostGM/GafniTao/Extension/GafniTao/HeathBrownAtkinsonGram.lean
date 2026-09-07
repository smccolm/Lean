import GafniTao.HeathBrownDivisorSquare
import GafniTao.Pintz2023HalaszGram

/-!
# Bombieri--Halász duality for the exact Atkinson sum

This is the finite Gram-matrix step in Ivić, Lemma 7.1, equations
(7.16)--(7.17).  It is specialized to Heath--Brown's literal alternating
divisor coefficient and Atkinson phase.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The alternating divisor coefficient in Heath--Brown's equation (10). -/
def heathBrownAtkinsonCoefficient (n : Nat) : Complex :=
  (-1 : Complex) ^ n * (heathBrownDivisorCoefficient n : Complex)

/-- The unit vector attached to a height and an Atkinson phase. -/
def heathBrownAtkinsonVector (t : Real) (n : Nat) : Complex :=
  unitaryPhase (heathBrownAtkinsonPhase t n)

/-- The coefficient-one Gram entry for two Atkinson heights. -/
def heathBrownAtkinsonGram (K : Nat) (t u : Real) : Complex :=
  ∑ n ∈ Finset.Ioc K (2 * K),
    unitaryPhase
      (heathBrownAtkinsonPhase u n - heathBrownAtkinsonPhase t n)

theorem norm_heathBrownAtkinsonCoefficient (n : Nat) :
    ‖heathBrownAtkinsonCoefficient n‖ =
      (heathBrownDivisorCoefficient n : Real) := by
  unfold heathBrownAtkinsonCoefficient
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast, one_mul]

theorem heathBrownAtkinsonSum_terminal_eq_coefficient_vector
    (K : Nat) (t : Real) :
    heathBrownAtkinsonSum (K : Real) K t =
      ∑ n ∈ Finset.Ioc K (2 * K),
        heathBrownAtkinsonCoefficient n * heathBrownAtkinsonVector t n := by
  rw [heathBrownAtkinsonSum_nat_terminal]
  apply Finset.sum_congr rfl
  intro n hn
  unfold heathBrownAtkinsonCoefficient heathBrownAtkinsonVector unitaryPhase
  congr 2
  ring

theorem heathBrownAtkinsonGram_eq_vector_gram
    (K : Nat) (t u : Real) :
    heathBrownAtkinsonGram K t u =
      ∑ n ∈ Finset.Ioc K (2 * K),
        conj (heathBrownAtkinsonVector t n) *
          heathBrownAtkinsonVector u n := by
  unfold heathBrownAtkinsonGram heathBrownAtkinsonVector
  apply Finset.sum_congr rfl
  intro n hn
  rw [unitaryPhase_sub]
  ring

/-- The exact finite Bombieri--Halász inequality for the terminal Atkinson
sums.  No analytic estimate has yet been applied to the Gram entries. -/
theorem heathBrownAtkinson_halasz_gram
    {K : Nat} {V : Real} {W : Finset Real} (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : Real) K t‖) :
    ((W.card : Real) * V) ^ (2 : Nat) ≤
      (∑ n ∈ Finset.Ioc K (2 * K),
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat)) *
      ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ := by
  have h := pintz2023_finite_halasz_gram
    (Finset.Ioc K (2 * K)) W V heathBrownAtkinsonCoefficient
    heathBrownAtkinsonVector hV (by
      intro t ht
      rw [← heathBrownAtkinsonSum_terminal_eq_coefficient_vector]
      exact hLarge t ht)
  simpa only [norm_heathBrownAtkinsonCoefficient,
    ← heathBrownAtkinsonGram_eq_vector_gram] using h


end

end GafniTao
