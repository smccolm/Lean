import Dubon2026.FiniteCharactersTopologicalGeneration
import Dubon2026.ProfiniteProPQuotientTopology

/-! # Actual topological generators of the original fixed pro-p quotient from original character finiteness -/

namespace Dubon2026

noncomputable section

/-- The genuine continuous projection from the original profinite group to its actual fixed pro-p quotient. -/
def profiniteProPQuotientProjection (p : ℕ) (G : ProfiniteGrp) :
    G →ₜ* profiniteProPQuotient p G := {
  toMonoidHom := QuotientGroup.mk' (profiniteProPKernel p G)
  continuous_toFun := QuotientGroup.continuous_mk }

/-- Original continuous character finiteness passes to the genuine fixed quotient by its actual surjective projection. -/
theorem profiniteProPQuotient_characters_finite (p : ℕ) (G : ProfiniteGrp)
    [Finite (G →ₜ* Multiplicative (ZMod p))] :
    Finite (profiniteProPQuotient p G →ₜ* Multiplicative (ZMod p)) := by
  apply Finite.of_injective
    (fun f : profiniteProPQuotient p G →ₜ* Multiplicative (ZMod p) =>
      f.comp (profiniteProPQuotientProjection p G))
  intro f g hfg
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (profiniteProPKernel p G) x
  exact DFunLike.congr_fun hfg y

/-- Finiteness of the original continuous prime-order characters gives actual topological generators of the genuine fixed common-kernel quotient. -/
theorem profiniteProPQuotient_finitely_generated (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp)
    [Finite (G →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (G ⧸ profiniteProPKernel p G),
      (Subgroup.closure (S : Set (G ⧸ profiniteProPKernel p G))).topologicalClosure = ⊤ := by
  letI := profiniteProPQuotient_characters_finite p G
  apply proP_finitely_generated_of_finite_characters p hp (profiniteProPQuotient p G)
  intro U
  letI : DiscreteTopology (profiniteProPQuotient p G ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  let quotientPrimeGroup := profiniteProPQuotient_continuous_quotient_isPGroup
    (Q := profiniteProPQuotient p G ⧸ U.toSubgroup) p G
  exact quotientPrimeGroup
    (QuotientGroup.mk' U.toSubgroup) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective U.toSubgroup)

end
end Dubon2026
