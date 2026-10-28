import Dubon2026.SourceGammaOneDiamondCoefficient

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
arithmetic realization -> trivial original diamond after native transfer.
The actual lifted Gamma0 normalizer preserves exactly the range of the
original diagonal-cover homomorphism. This discharges the subgroup equality
needed to consume the inner trace base-change theorem.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (Q N : ℕ) [NeZero N]

theorem sourceGammaOneDiagonalRange_conj (g : Gamma0 (Q * N ^ 2)) :
    (sourceGammaOneDiagonalHom Q N).range.comap
        (MulAut.conj (sourceGammaOneDiamondLift Q N g)).toMonoidHom =
      (sourceGammaOneDiagonalHom Q N).range := by
  ext x
  change (∃ γ, sourceGammaOneDiagonalHom Q N γ =
      sourceGammaOneDiamondLift Q N g * x * (sourceGammaOneDiamondLift Q N g)⁻¹) ↔
    ∃ γ, sourceGammaOneDiagonalHom Q N γ = x
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨sourceGammaOneDiamondConjugation (Q * N ^ 2) g⁻¹ γ, ?_⟩
    rw [sourceGammaOneDiamondLift_conjugation, map_inv, hγ]
    group
  · rintro ⟨γ, rfl⟩
    exact ⟨sourceGammaOneDiamondConjugation (Q * N ^ 2) g γ,
      sourceGammaOneDiamondLift_conjugation Q N g γ⟩

end
end Dubon2026
