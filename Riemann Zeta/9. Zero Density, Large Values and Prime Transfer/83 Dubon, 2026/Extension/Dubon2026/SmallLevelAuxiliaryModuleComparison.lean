import Dubon2026.SmallLevelAuxiliaryTrace

/-! # Assembled algebraic comparison for CHT Lemma 3.3.1

DUB-17 needs this comparison for the source's integral unitary automorphic
modules. It derives finite freeness and the trace specialization from the
geometric level conditions. Those conditions and the arithmetic Hecke
summands still require their original unitary-group construction.
-/

namespace Dubon2026

noncomputable section

open scoped BigOperators

/-- Finite freeness and specialization by the original unnormalized weighted trace. -/
theorem smallLevelAuxiliaryModule_comparison
    {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
    (Γ U V : Subgroup G) (hVU : V ≤ U) (ρ : Representation R U W)
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    [(V.subgroupOf U).Normal]
    [Finite (DoubleCoset.Quotient (G := G) Γ U)] [Fintype (U ⧸ V.subgroupOf U)]
    [Module.Finite R W] [Module.Free R W] :
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : G),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall) f)).val g =
          ∑ d : U ⧸ V.subgroupOf U, ρ d.out (f.val (g * (d.out : G))) :=
  ⟨smallLevelAuxiliary_free Γ U V hVU ρ hsmall,
    smallLevelAuxiliary_finite Γ U V hVU ρ hsmall,
    smallLevelAuxiliaryCoinvariantEquiv Γ U V hVU ρ hsmall,
    smallLevelAuxiliaryCoinvariantEquiv_weighted_trace Γ U V hVU ρ hsmall⟩

end
end Dubon2026
