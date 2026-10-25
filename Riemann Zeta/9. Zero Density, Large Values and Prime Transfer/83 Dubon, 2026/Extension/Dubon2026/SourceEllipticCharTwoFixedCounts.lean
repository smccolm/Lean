import Dubon2026.SourceEllipticCharTwoQuarticFixedCount
import Dubon2026.SourceEllipticCharTwoCubicFixedCount

/-! DUB-17/18 -> characteristic-two weighted exceptional census.
Construct one actual cubic-root parameter and both source automorphisms,
with their exact fixed cyclic-subgroup counts. No root, action-identity,
nonscalar-action or torsion-structure hypothesis remains. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer SourceLevelProjective
noncomputable section

theorem exists_char_two_exceptional_fixed_counts
    (K : Type*) [Field K] [CharP K 2] [DecidableEq K] [IsAlgClosed K]
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ (ω : K) (hω : ω ^ 2 + ω + 1 = 0),
      Nat.card {H : AddSubgroup (ofJ0 K).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
          H.map (stabilizerPointHom (ofJ0 K) (quarticStabilizer ω hω)).toAddMonoidHom = H}
        = nuTwo N ∧
      Nat.card {H : AddSubgroup (ofJ0 K).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧ H.map (cubicPoint ω hω).toAddMonoidHom = H}
        = nuThree N := by
  obtain ⟨ω, hω⟩ := exists_omega (K := K)
  exact ⟨ω, hω, char_two_quartic_fixed_cyclic_count ω hω N hNK,
    char_two_cubic_fixed_cyclic_count ω hω N hNK⟩

end
end Dubon2026.SourceEllipticCharTwo
