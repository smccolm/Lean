import Tao2026.Asymptotics
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Bertrand

/-!
# Tao's Vinogradov-type prime equidistribution input

This module fixes the literal finite prime sum, logarithmic integral, periodic
weight convention, and uniform estimate used in Theorem 2.5 of Tao's paper.
The cited source is Proposition 1.12 of Matomäki--Radziwiłł--Shao--Tao--
Teräväinen, pinned in `Sources/` as arXiv `2106.03335v1`.

The paper later uses only the specialization `M = N`, `j = 2`.  Both the full
source contract and that specialization are recorded here, together with the
proved implication from the full contract to the specialization.  No analytic
estimate is postulated as an axiom or theorem.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

/-- The primes in a real set `I ⊆ [P,2P]`.  The ambient finite range makes the
sum computationally finite; `mem_primesInScaleSet` proves that under the source
range hypothesis it imposes exactly primality and membership in `I`. -/
noncomputable def primesInScaleSet (P : ℝ) (I : Set ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * P⌋₊ + 1)).filter fun p => p.Prime ∧ (p : ℝ) ∈ I

theorem mem_primesInScaleSet
    {P : ℝ} {I : Set ℝ} (_hP : 2 ≤ P) (hI : I ⊆ Icc P (2 * P)) {p : ℕ} :
    p ∈ primesInScaleSet P I ↔ p.Prime ∧ (p : ℝ) ∈ I := by
  classical
  rw [primesInScaleSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp => hp.2
  · rintro hp
    refine ⟨?_, hp⟩
    have hpTop : (p : ℝ) ≤ 2 * P := (hI hp.2).2
    have hpFloor : p ≤ ⌊2 * P⌋₊ := by
      exact_mod_cast Nat.le_floor hpTop
    omega

/-- The literal finite prime sum in Tao's Theorem 2.5. -/
def primeEquidistributionSum
    (P : ℝ) (I : Set ℝ) (W : ℝ × ℝ → ℂ)
    (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ p ∈ primesInScaleSet P I,
    W (N / (p : ℝ), M / (p : ℝ) ^ j)

/-- The logarithmically weighted Lebesgue integral in Tao's Theorem 2.5. -/
def primeEquidistributionIntegral
    (I : Set ℝ) (W : ℝ × ℝ → ℂ)
    (N M : ℝ) (j : ℕ) : ℂ :=
  ∫ t in I, W (N / t, M / t ^ j) / Real.log t

/-- Coordinate form of `ℤ²`-periodicity. -/
def IsZ2Periodic (W : ℝ × ℝ → ℂ) : Prop :=
  ∀ (x y : ℝ) (m n : ℤ),
    W (x + m, y + n) = W (x, y)

/-- Tao's `C³` norm convention: the sum, for derivative orders zero through
three, of the supremum over `ℝ²` of the iterated Fréchet derivative's operator
norm. -/
def taoC3Norm (W : ℝ × ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range 4,
    sSup {r : ℝ | ∃ x : ℝ × ℝ, r = ‖iteratedFDeriv ℝ i W x‖}

/-- The pointwise size condition denoted
`O(exp(log^(3/2-ε) P))` in the source.  The explicit multiplier records the
otherwise suppressed constant. -/
def VinogradovParameterBound (ε K P T : ℝ) : Prop :=
  |T| ≤ K * Real.exp ((Real.log P) ^ (3 / 2 - ε))

/-- Exact source-facing contract for Tao's Theorem 2.5.  The error constant is
uniform in the interval, derivative exponent, weight, and frequencies.  Its
dependence on `K` makes the constant hidden in the hypotheses explicit. -/
def TaoTheorem25Conclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∀ K : ℝ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : ℝ) (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ),
        2 ≤ P → MeasurableSet I → OrdConnected I → I ⊆ Icc P (2 * P) →
        ContDiff ℝ ⊤ W → IsZ2Periodic W → 1 ≤ j →
        VinogradovParameterBound ε K P N →
        VinogradovParameterBound ε K P M →
        ‖primeEquidistributionSum P I W N M j -
            primeEquidistributionIntegral I W N M j‖ ≤
          C * taoC3Norm W * P / (Real.log P) ^ A

/-- The only specialization of Theorem 2.5 used later in Tao's paper. -/
def TaoTheorem25SpecializedConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∀ K : ℝ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : ℝ) (I : Set ℝ) (W : ℝ × ℝ → ℂ) (N : ℝ),
        2 ≤ P → MeasurableSet I → OrdConnected I → I ⊆ Icc P (2 * P) →
        ContDiff ℝ ⊤ W → IsZ2Periodic W →
        VinogradovParameterBound ε K P N →
        ‖primeEquidistributionSum P I W N N 2 -
            primeEquidistributionIntegral I W N N 2‖ ≤
          C * taoC3Norm W * P / (Real.log P) ^ A

/-- The full source theorem supplies every instance of the specialization
used in Sections 3 and 4. -/
theorem taoTheorem25Specialized_of_full
    (h : TaoTheorem25Conclusion) : TaoTheorem25SpecializedConclusion := by
  intro ε hε A hA K hK
  obtain ⟨C, hC, hbound⟩ := h ε hε A hA K hK
  refine ⟨C, hC, ?_⟩
  intro P I W N hP hImeas hIconn hI hW hWper hN
  exact hbound P I W N N 2 hP hImeas hIconn hI hW hWper (by omega) hN hN

end

end Tao2026
