import Dubon2026.UnramifiedLocalNormQuotient

/-! # Original continuous cyclic Galois H2 normalized by actual local-field order -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Actual continuous H2 for the original cyclic Galois unit action is
identified with integer order modulo the extension degree. The displayed
cyclic generator is retained; identification with arithmetic Frobenius is separate. -/
def continuousUnramifiedCyclicGaloisH2OrderEquiv :
    GaloisUnitContinuousH2 (K := K) (Ω := L) ≃ₗ[ℤ] ZMod (Module.finrank K L) :=
  (continuousCyclicGaloisNormQuotientEquiv g hg).symm.trans
    (unramifiedLocalNormQuotientEquiv (K := K) (L := L))

/-- The original cyclic H2 class of a base-field unit is sent to exactly
its original normalized order modulo the actual extension degree. -/
theorem continuousUnramifiedCyclicGaloisH2OrderEquiv_class (u : Additive Kˣ) :
    continuousUnramifiedCyclicGaloisH2OrderEquiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) := by
  rw [← continuousCyclicGaloisNormQuotientEquiv_mk g hg u]
  change unramifiedLocalNormQuotientEquiv
    ((continuousCyclicGaloisNormQuotientEquiv g hg).symm
      (continuousCyclicGaloisNormQuotientEquiv g hg (Submodule.Quotient.mk u))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end
end Dubon2026
