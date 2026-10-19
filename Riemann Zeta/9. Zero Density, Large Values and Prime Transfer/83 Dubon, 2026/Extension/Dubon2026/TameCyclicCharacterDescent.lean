import Dubon2026.TameCyclicQuotientKernel

/-! The proved tame kernel inclusion supplies a unique actual character
on the fixed quotient. This is the factorization required for the auxiliary
deformation-ring group action on the Dubon Theorem 2.6 dependency chain. -/

namespace Dubon2026

/-- Tame generation, a common killed wild subgroup and the quotient
exponent produce the unique homomorphism on the fixed cyclic quotient. -/
theorem tame_cyclic_quotient_unique_factor
    {G H D : Type*} [Group G] [Group H] [Group D] [Finite D]
    (I W : Subgroup G) [W.Normal] (t : G)
    (hgen : I = W ⊔ Subgroup.zpowers t)
    (ρ : G →* H) (π : G →* D)
    (hWρ : W ≤ ρ.ker) (hWπ : W ≤ π.ker)
    (hπ : I.map π = ⊤) (ht : ρ t ^ Nat.card D = 1) :
    ∃! χ : D →* H, χ.comp (π.comp I.subtype) = ρ.comp I.subtype := by
  let πI := π.comp I.subtype
  let ρI := ρ.comp I.subtype
  have hs : Function.Surjective πI := by
    intro d
    have hd : d ∈ I.map π := hπ.symm ▸ Subgroup.mem_top d
    obtain ⟨g, hg, hd⟩ := hd
    exact ⟨⟨g, hg⟩, hd⟩
  have hk : πI.ker ≤ ρI.ker := by
    intro g hg
    exact tame_cyclic_quotient_kernel I W t hgen ρ π hWρ hWπ hπ ht ⟨g.property, hg⟩
  let χ := πI.liftOfSurjective hs ⟨ρI, hk⟩
  have hc : χ.comp πI = ρI := πI.liftOfRightInverse_comp _ _ _
  refine ⟨χ, hc, ?_⟩
  intro ψ hψ
  apply MonoidHom.ext
  intro d
  obtain ⟨g, rfl⟩ := hs d
  exact (DFunLike.congr_fun hψ g).trans (DFunLike.congr_fun hc g).symm

end Dubon2026
