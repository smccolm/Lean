import GafniTao.HeathBrownBlocks
import GafniTao.FordEquation54Expansion
import GafniTao.FordFiniteAMGM

/-!
# Finite energy identity for Heath-Brown's triangular kernel

The absolutely convergent kernel series is summed over a literal finite
index set.  The result is the nonnegative coefficient-weighted square of
the corresponding exponential sum.  This is the equality used before the
block Cauchy inequality in Heath-Brown Section 3.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

def heathBrownFourierAtom
    (g₁ g₂ : ℕ → ℝ) (rs : ℤ × ℤ) (n : ℕ) : ℂ :=
  fordAdditiveCharacter
    ((rs.1 : ℝ) * g₁ n + (rs.2 : ℝ) * g₂ n)

def heathBrownFrequencyEnergy
    (B C : ℝ) (g₁ g₂ : ℕ → ℝ) (S : Finset ℕ)
    (rs : ℤ × ℤ) : ℝ :=
  heathBrownTriangularFourierCoefficient B C rs.1 rs.2 *
    ‖∑ n ∈ S, heathBrownFourierAtom g₁ g₂ rs n‖ ^ 2

theorem heathBrownFourierAtom_mul_conj
    (g₁ g₂ : ℕ → ℝ) (rs : ℤ × ℤ) (m n : ℕ) :
    heathBrownFourierAtom g₁ g₂ rs m *
        conj (heathBrownFourierAtom g₁ g₂ rs n) =
      fordAdditiveCharacter ((rs.1 : ℝ) * (g₁ m - g₁ n)) *
        fordAdditiveCharacter ((rs.2 : ℝ) * (g₂ m - g₂ n)) := by
  unfold heathBrownFourierAtom
  rw [conj_fordAdditiveCharacter]
  calc
    fordAdditiveCharacter
          ((rs.1 : ℝ) * g₁ m + (rs.2 : ℝ) * g₂ m) *
        fordAdditiveCharacter
          (-((rs.1 : ℝ) * g₁ n + (rs.2 : ℝ) * g₂ n)) =
      fordAdditiveCharacter
        (((rs.1 : ℝ) * g₁ m + (rs.2 : ℝ) * g₂ m) -
          ((rs.1 : ℝ) * g₁ n + (rs.2 : ℝ) * g₂ n)) := by
        rw [← fordAdditiveCharacter_add]
        congr 2
    _ = fordAdditiveCharacter
          ((rs.1 : ℝ) * (g₁ m - g₁ n) +
            (rs.2 : ℝ) * (g₂ m - g₂ n)) := by
        congr 2
        ring_nf
    _ = fordAdditiveCharacter ((rs.1 : ℝ) * (g₁ m - g₁ n)) *
          fordAdditiveCharacter ((rs.2 : ℝ) * (g₂ m - g₂ n)) := by
        rw [fordAdditiveCharacter_add]

theorem hasSum_heathBrownPairKernelFourier
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2)
    (g₁ g₂ : ℕ → ℝ) (m n : ℕ) :
    HasSum
      (fun rs : ℤ × ℤ =>
        (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
          heathBrownFourierAtom g₁ g₂ rs m *
          conj (heathBrownFourierAtom g₁ g₂ rs n))
      (heathBrownTriangularKernel B C
        (g₁ m - g₁ n) (g₂ m - g₂ n) : ℂ) := by
  have hs := hasSum_heathBrownTriangularFourierSeries
    hB hBHalf hC hCHalf (g₁ m - g₁ n) (g₂ m - g₂ n)
  refine HasSum.congr_fun hs ?_
  intro rs
  rw [show
    (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
          heathBrownFourierAtom g₁ g₂ rs m *
          conj (heathBrownFourierAtom g₁ g₂ rs n) =
      (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
        (heathBrownFourierAtom g₁ g₂ rs m *
          conj (heathBrownFourierAtom g₁ g₂ rs n)) by ring_nf]
  rw [heathBrownFourierAtom_mul_conj]
  ring_nf

theorem hasSum_heathBrownFinitePairKernelFourier
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2)
    (g₁ g₂ : ℕ → ℝ) (S : Finset ℕ) :
    HasSum
      (fun rs : ℤ × ℤ =>
        ∑ m ∈ S, ∑ n ∈ S,
          (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
            heathBrownFourierAtom g₁ g₂ rs m *
            conj (heathBrownFourierAtom g₁ g₂ rs n))
      (∑ m ∈ S, ∑ n ∈ S,
        (heathBrownTriangularKernel B C
          (g₁ m - g₁ n) (g₂ m - g₂ n) : ℂ)) := by
  have hn (m : ℕ) :
      HasSum
        (fun rs : ℤ × ℤ =>
          ∑ n ∈ S,
            (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
              heathBrownFourierAtom g₁ g₂ rs m *
              conj (heathBrownFourierAtom g₁ g₂ rs n))
        (∑ n ∈ S, (heathBrownTriangularKernel B C
          (g₁ m - g₁ n) (g₂ m - g₂ n) : ℂ)) := by
    simpa using hasSum_sum (s := S)
      (fun n _hn => hasSum_heathBrownPairKernelFourier
        hB hBHalf hC hCHalf g₁ g₂ m n)
  simpa using hasSum_sum (s := S) (fun m _hm => hn m)

theorem heathBrownFinitePairLatticeTerm_eq_energy
    (B C : ℝ) (g₁ g₂ : ℕ → ℝ) (S : Finset ℕ) (rs : ℤ × ℤ) :
    (∑ m ∈ S, ∑ n ∈ S,
        (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
          heathBrownFourierAtom g₁ g₂ rs m *
          conj (heathBrownFourierAtom g₁ g₂ rs n)) =
      (heathBrownFrequencyEnergy B C g₁ g₂ S rs : ℂ) := by
  let c : ℂ :=
    (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ)
  let Z : ℂ := ∑ n ∈ S, heathBrownFourierAtom g₁ g₂ rs n
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        c * heathBrownFourierAtom g₁ g₂ rs m *
          conj (heathBrownFourierAtom g₁ g₂ rs n)) =
        c * Z * conj Z := by
      change (∑ m ∈ S, ∑ n ∈ S,
          c * heathBrownFourierAtom g₁ g₂ rs m *
            conj (heathBrownFourierAtom g₁ g₂ rs n)) =
        c * (∑ m ∈ S, heathBrownFourierAtom g₁ g₂ rs m) *
          conj (∑ n ∈ S, heathBrownFourierAtom g₁ g₂ rs n)
      rw [map_sum]
      rw [show
        c * (∑ m ∈ S, heathBrownFourierAtom g₁ g₂ rs m) *
              (∑ n ∈ S, conj (heathBrownFourierAtom g₁ g₂ rs n)) =
          c * ((∑ m ∈ S, heathBrownFourierAtom g₁ g₂ rs m) *
              (∑ n ∈ S, conj (heathBrownFourierAtom g₁ g₂ rs n))) by ring_nf]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
      ring_nf
    _ = (heathBrownFrequencyEnergy B C g₁ g₂ S rs : ℂ) := by
      rw [show c * Z * conj Z = c * (Z * conj Z) by ring_nf,
        Complex.mul_conj']
      simp only [c, Z, heathBrownFrequencyEnergy]
      push_cast
      ring_nf

/-- Exact real-valued form of the finite kernel energy identity. -/
theorem hasSum_heathBrownFrequencyEnergy
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2)
    (g₁ g₂ : ℕ → ℝ) (S : Finset ℕ) :
    HasSum (heathBrownFrequencyEnergy B C g₁ g₂ S)
      (∑ m ∈ S, ∑ n ∈ S,
        heathBrownTriangularKernel B C
          (g₁ m - g₁ n) (g₂ m - g₂ n)) := by
  apply Complex.hasSum_ofReal.mp
  convert HasSum.congr_fun
    (hasSum_heathBrownFinitePairKernelFourier
      hB hBHalf hC hCHalf g₁ g₂ S)
    (fun rs => (heathBrownFinitePairLatticeTerm_eq_energy
      B C g₁ g₂ S rs).symm) using 1
  push_cast
  rfl

theorem heathBrownFrequencyEnergy_nonneg
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (g₁ g₂ : ℕ → ℝ) (S : Finset ℕ) (rs : ℤ × ℤ) :
    0 ≤ heathBrownFrequencyEnergy B C g₁ g₂ S rs := by
  exact mul_nonneg
    (heathBrownTriangularFourierCoefficient_nonneg hB hC rs.1 rs.2)
    (sq_nonneg _)

#print axioms heathBrownFourierAtom_mul_conj
#print axioms hasSum_heathBrownPairKernelFourier
#print axioms hasSum_heathBrownFinitePairKernelFourier
#print axioms heathBrownFinitePairLatticeTerm_eq_energy
#print axioms hasSum_heathBrownFrequencyEnergy
#print axioms heathBrownFrequencyEnergy_nonneg

end

end GafniTao
