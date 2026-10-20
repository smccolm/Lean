import Dubon2026.TraceCoefficientStrictConjugacy
import Dubon2026.FixedResidualFramedUniversality
import Dubon2026.OriginalAdicTraceRepresentationDescent
import Dubon2026.OriginalAdicCompleteLocalCompactness
import Dubon2026.TrueResidueScalarExtension

/-! Equal traces of actual continuous lifts with absolutely irreducible
residual representation imply strict conjugacy. Existing framed universality
and genuine trace descent supply the conjugator needed for DUB-17's CM
polarization descent; no matrix-algebra automorphism theorem is postulated. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {ι O A L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
  [t : TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Two actual continuous lifts of the same absolutely irreducible residual
representation with identical whole-group traces differ by an actual change
of basis reducing to the identity. -/
theorem originalResidual_trace_eq_strictlyConjugate
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S))
    (τ₁ τ₂ : H →ₜ* GeneralLinearGroup ι A)
    (h₁ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ₁.toMonoidHom = σ)
    (h₂ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ₂.toMonoidHom = σ)
    (htrace : ∀ x, Matrix.trace (τ₁ x).val = Matrix.trace (τ₂ x).val) (i₀ : ι) :
    MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
      τ₁.toMonoidHom τ₂.toMonoidHom := by
  change t = (IsLocalRing.maximalIdeal A).adicTopology at hA
  subst t
  letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
  letI : T2Space A := originalAdicCompleteLocal_t2Space rfl
  let R := FixedResidualFramedCoefficientRing p H σ hσ S
  letI : IsLocalRing R := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
  have hd := fixedResidualFramedCoefficientRing_localData p H σ hσ S
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hd.2.1
  let eR := fixedResidualFramedCoefficientResidueEquiv p H σ hσ S
  let υ := fixedResidualFramedUniversalRepresentation p H σ hσ S hS
  let υc : H →ₜ* GeneralLinearGroup ι R :=
    ⟨υ, fixedResidualFramedUniversalRepresentation_continuous p H σ hσ S hS⟩
  letI : Algebra (IsLocalRing.ResidueField R) L :=
    ((algebraMap (IsLocalRing.ResidueField O) L).comp eR.toRingHom).toAlgebra
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp υ))) := by
    rw [trueResidueScalarExtension_eq eR υ σ
      (fixedResidualFramedUniversalRepresentation_residue p H σ hσ S hS)]
    infer_instance
  obtain ⟨ω, hω⟩ := originalAdicContinuousTraceRepresentationDescent_exists
    (L := L) hd.2.2 eR υc i₀
  have hωred := matrixStrictlyConjugate_comp_reduction (IsLocalRing.residue R)
    eR.toRingHom _ _ hω
  let E := fixedResidualFramedFiberEquiv rfl eA p hp H σ hσ S hS
  have he (τ : OriginalContinuousFramedFiber eA H σ) :
      (GeneralLinearGroup.map (E.symm τ).val.toRingHom).comp υ = τ.val.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg (fun z : OriginalContinuousFramedFiber eA H σ => z.val x)
      (E.apply_symm_apply τ)
  let f := E.symm ⟨τ₁, h₁⟩
  let g := E.symm ⟨τ₂, h₂⟩
  have hef : (GeneralLinearGroup.map f.val.toRingHom).comp υ = τ₁.toMonoidHom := he ⟨τ₁, h₁⟩
  have heg : (GeneralLinearGroup.map g.val.toRingHom).comp υ = τ₂.toMonoidHom := he ⟨τ₂, h₂⟩
  have ht (x : H) : f.val (Matrix.trace (υ x).val) = g.val (Matrix.trace (υ x).val) := by
    have htf := congrArg (fun z : H →* GeneralLinearGroup ι A => Matrix.trace (z x).val) hef
    have htg := congrArg (fun z : H →* GeneralLinearGroup ι A => Matrix.trace (z x).val) heg
    change Matrix.trace ((υ x).val.map f.val) = Matrix.trace (τ₁ x).val at htf
    change Matrix.trace ((υ x).val.map g.val) = Matrix.trace (τ₂ x).val at htg
    rw [← AddMonoidHom.map_trace] at htf htg
    exact htf.trans ((htrace x).trans htg.symm)
  have hc := matrixStrictlyConjugate_of_trace_specializations
    (localCoefficientReduction eR).toRingHom (localCoefficientReduction eA).toRingHom υ
    ω.toMonoidHom hωred f.val g.val f.property.1 g.property.1
    (congrArg AlgHom.toRingHom f.property.2) (congrArg AlgHom.toRingHom g.property.2) ht
  rw [hef, heg] at hc
  exact hc

end
end Dubon2026
