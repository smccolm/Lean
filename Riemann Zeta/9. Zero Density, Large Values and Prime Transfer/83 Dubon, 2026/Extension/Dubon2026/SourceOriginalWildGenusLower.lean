import Dubon2026.SourceOriginalResidueHurwitz
import Dubon2026.SourceGammaOneArithmeticGenusBound
import Dubon2026.SourceMarkedOriginalWildContributionTwo
import Dubon2026.SourceMarkedOriginalWildContributionThree

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation. The original Hurwitz and cusp bounds
combine with the proved wild different contributions and arithmetic genus bound
to give the reverse genus inequality in characteristics two and three for N > 3.
Every coordinate, local-order and differential premise is discharged by its
native original-field proof. Small levels and tame reverse genus remain separate. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

section
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField A) ℓ]

private theorem original_genus_lower_of_differential_contribution (hℓN : ¬ ℓ ∣ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (hdiff : 7 * ((plusMinus (Gamma1 N)).index : ℤ) ≤
      6 * ∑ᶠ v : {v : Place kk F // 0 < v.ord x}, v.val.ordDifferential (D kk F x)) :
    genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) ≤ genusFF kk F := by
  classical
  letI := (original_positive_j_fiber_finite_and_degree A N ℓ hℓN x hx).1
  have hf : {v : Place kk F | 0 < v.ord x}.Finite :=
    (Set.finite_range (fun v : {v : Place kk F // 0 < v.ord x} => v.val)).subset
      (fun v hv => ⟨⟨v, hv⟩, rfl⟩)
  have hh := original_hurwitz_differential_cusp_bound A N ℓ hℓN x hx hf.toFinset
    (fun v hv => ((hf.mem_toFinset).mp hv).le)
  have he : {v : Place kk F | 0 < v.ord x} = (hf.toFinset : Set _) := by
    ext v
    exact hf.mem_toFinset.symm
  have hs : (∑ᶠ v : {v : Place kk F // 0 < v.ord x},
      v.val.ordDifferential (D kk F x)) =
      ∑ v ∈ hf.toFinset, v.ordDifferential (D kk F x) := by
    calc
      _ = ∑ᶠ (v : Place kk F) (_ : 0 < v.ord x), v.ordDifferential (D kk F x) :=
        finsum_subtype_eq_finsum_cond
          (f := fun v : Place kk F => v.ordDifferential (D kk F x)) (fun v => 0 < v.ord x)
      _ = _ := by
        change (∑ᶠ v ∈ ({v : Place kk F | 0 < v.ord x} : Set (Place kk F)),
          v.ordDifferential (D kk F x)) = _
        conv_lhs => rw [he]
        rw [finsum_mem_coe_finset]
  rw [hs] at hdiff
  have hg := gamma1_arithmetic_genus_cusp_bound N
  change 12 * genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) +
    6 * Nat.card (CuspCounting.PolePlaces (Gamma1 N)) ≤
      12 + (plusMinus (Gamma1 N)).index at hg
  omega

end

theorem original_genus_lower_of_char_two [CharP (IsLocalRing.ResidueField A) 2] (haway : ¬ 2 ∣ N) (hN : 3 < N) :
    genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) ≤ genusFF kk F := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x : F := ⟨jqModC kk, jqModC_mem_integralRatioField kk (Gamma1 N)⟩
  exact original_genus_lower_of_differential_contribution A N 2 haway x rfl
    (original_char_two_differential_contribution A N haway hN x rfl)

theorem original_genus_lower_of_char_three [CharP (IsLocalRing.ResidueField A) 3] (haway : ¬ 3 ∣ N) (hN : 3 < N) :
    genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) ≤ genusFF kk F := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : F := ⟨jqModC kk, jqModC_mem_integralRatioField kk (Gamma1 N)⟩
  exact original_genus_lower_of_differential_contribution A N 3 haway x rfl
    (original_char_three_differential_contribution A N haway hN x rfl)

end
end Dubon2026.SourceFunctionField.MarkedChart
