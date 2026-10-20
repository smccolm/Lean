import Dubon2026.SmallLevelAuxiliaryFreeness

/-! Nonzeroness of the actual weighted automorphic function space from
nonzero original coefficients and proved smallness. Existing exact
double-coset coordinate equivalences are reused. This does not assert
nonzeroness after localization at a prescribed Hecke ideal.
-/

namespace Dubon2026
noncomputable section

variable {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
  [Nontrivial W]

/-- Nonzero original coefficients give nonzero actual automorphic forms at every small level. -/
theorem smallLevelAutomorphic_nontrivial (Γ U : Subgroup G) (ρ : Representation R U W)
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1) :
    Nontrivial (algebraicAutomorphicForms Γ U ρ) :=
  (smallLevelAutomorphicEvaluation Γ U ρ hsmall).toEquiv.nontrivial

/-- The actual lower-level auxiliary forms are nonzero, using their original quotient coordinates and the same original nonzero coefficients. -/
theorem smallLevelAuxiliary_nontrivial (Γ U V : Subgroup G) (hVU : V ≤ U)
    (ρ : Representation R U W)
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    [(V.subgroupOf U).Normal] :
    Nontrivial (algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) :=
  (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall).toEquiv.nontrivial

end
end Dubon2026
