import Dubon2026.AuxiliaryRegularCoordinates

/-! # Finite freeness of the actual small-level auxiliary function space

This proves the algebraic finite-freeness assertion of CHT Lemma 3.3.1 from
finite arithmetic double cosets, trivial arithmetic stabilizers and a finite
free weight lattice. Its level-quotient action is the original weighted right
translation. The unitary arithmetic construction and Hecke summands remain
separate DUB-17 obligations.
-/

namespace Dubon2026

noncomputable section

variable {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
variable (Γ U V : Subgroup G) (hVU : V ≤ U) (ρ : Representation R U W)
variable (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
variable [(V.subgroupOf U).Normal]
variable [Finite (DoubleCoset.Quotient (G := G) Γ U)] [Finite (U ⧸ V.subgroupOf U)]
variable [Module.Finite R W] [Module.Free R W]

/-- The genuine auxiliary forms are free over their full level-quotient group algebra. -/
theorem smallLevelAuxiliary_free :
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).asModule := by
  let b := Module.Free.chooseBasis R W
  letI := auxiliaryRegularModule_free
    (D := U ⧸ V.subgroupOf U) (J := DoubleCoset.Quotient (G := G) Γ U) b
  exact auxiliaryRepresentationModule_free
    (R := R) (D := U ⧸ V.subgroupOf U)
    (X := algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
    (Y := DoubleCoset.Quotient (G := G) Γ U → U ⧸ V.subgroupOf U → W)
    (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall)
    quotientRightTranslation (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall)
    (auxiliaryAutomorphicAction_evaluation Γ U V hVU ρ hsmall)

omit [Module.Free R W] in
/-- Finite arithmetic double cosets and finite weight coefficients give finite generation. -/
theorem smallLevelAuxiliary_finite :
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hsmall).asModule := by
  letI : Module.Finite R (algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) :=
    Module.Finite.equiv (smallLevelAuxiliaryEvaluation Γ U V hVU ρ hsmall).symm
  exact Module.Finite.of_restrictScalars_finite R _ _

end
end Dubon2026
