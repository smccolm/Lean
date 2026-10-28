from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'SourceSmoothInvariantComparison.lean').read_text(encoding='utf-8')
concl=s[s.index('    ∃ (V :'):s.index(' := by',s.index('    ∃ (V :')))]
concl=concl.replace('Γ','plusMinus (Gamma1 N)')
# Explicit parentheses are necessary where the original subgroup was an atomic argument.
concl=concl.replace(': plusMinus (Gamma1 N)', ': plusMinus (Gamma1 N)')
concl=concl.replace('MulAction.stabilizer (plusMinus (Gamma1 N))','MulAction.stabilizer (plusMinus (Gamma1 N))')
# Replacing an unparenthesized Gamma argument in subtype binders is harmless;
# stabilizer calls in the primary already parenthesize Gamma.
head="""import SourceSmoothInvariantComparison
import Dubon2026.SourceGammaOneDivisorReciprocityData

/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity.
Construct the smooth invariant comparison from the actual degree-zero original
analytic divisor. The exact signed stabilizer formula proves divisibility
and the weighted degree condition. Original orbit representatives, all levels
and actual ramification orders are retained. No smooth comparison function,
logarithmic derivative formula or meromorphic realization is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real Classical ComplexConjugate

theorem analyticRamification_smul_signed (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (γ : plusMinus (Gamma1 N)) (τ : ℍ) :
    analyticRamification hT (γ.val • τ) = analyticRamification hT τ := by
  have h := Nat.card_congr
    (MulAction.stabilizerEquivStabilizer
      (G := plusMinus (Gamma1 N)) (a := τ) (g := γ) rfl).toEquiv
  change Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) =
    Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) (γ.val • τ)) at h
  rw [← two_mul_ramification_eq_stabilizer_card N hT τ,
    ← two_mul_ramification_eq_stabilizer_card N hT (γ.val • τ)] at h
  omega

theorem exists_original_divisor_smooth_comparison (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0) :
    let D := Finsupp.mapDomain (analyticPlace hT) c
    let n : ℍ → ℤ := fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)
    ∃ S : Finset ℍ, (S : Set ℍ) ⊆ c.support ∧
"""
proof=""" := by
  classical
  dsimp only
  let D := Finsupp.mapDomain (analyticPlace hT) c
  let n : ℍ → ℤ := fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)
  obtain ⟨S, hsub, hinj, hcov, hdeg⟩ := exists_degree_zero_reciprocity_data N hT c hc
  refine ⟨S, hsub, ?_⟩
  apply SourceSmoothDivisor.exists_invariant_comparison (plusMinus (Gamma1 N))
    (neg_one_mem_plusMinus (Gamma1 N)) S n
  · intro γ τ
    dsimp only [n]
    rw [analyticRamification_smul_signed N hT γ τ,
      analyticPlace_smul_plusMinus hT γ.property τ]
  · intro τ hτ
    obtain ⟨s, hs, γ, hγ⟩ := hcov τ (fun he => hτ (by simp [n, D, he]))
    exact ⟨s, hs, ⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩, hγ⟩
  · intro s hs t ht hst
    obtain ⟨γ, hγ⟩ := hst
    obtain ⟨δ, hδ⟩ := exists_gamma_smul_eq_of_mem_plusMinus (Gamma1 N) γ.property s
    exact hinj s hs t ht ⟨δ, hδ.trans hγ⟩
  · intro s _
    rw [← two_mul_ramification_eq_stabilizer_card N hT s]
    refine ⟨D (analyticPlace hT s), ?_⟩
    dsimp only [n]
    push_cast
    ring
  · exact hdeg

end
end Dubon2026.SourceFunctionField.GammaOne
"""
with (p/'SourceGammaOneSmoothDivisorComparison.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+concl+proof)
