import Dubon2026.ClosedMatrixTraceImage
import Dubon2026.FixedResidualTraceUnframedUniversality
import Dubon2026.OriginalAdicCompleteLocalCompactness

/-! The trace algebra of an actual continuous lift is a quotient of the
existing universal trace ring. This removes its Noetherianity assumption
before the polarized CM trace comparison required by DUB-17. -/

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

/-- The actual closed trace algebra of a continuous lift with absolutely
irreducible residual representation is Noetherian, using the proved finite
profinite presentation and the existing universal trace ring. -/
theorem originalResidualTraceAlgebra_isNoetherian
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
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (i₀ : ι) :
    IsNoetherianRing (closedMatrixTraceAlgebra (O := O) τ.toMonoidHom) := by
  change t = (IsLocalRing.maximalIdeal A).adicTopology at hA
  subst t
  letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
  letI : T2Space A := originalAdicCompleteLocal_t2Space rfl
  let R := FixedResidualFramedCoefficientRing p H σ hσ S
  letI : IsLocalRing R := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
  have hd := fixedResidualFramedCoefficientRing_localData p H σ hσ S
  letI : IsNoetherianRing R := hd.1
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hd.2.1
  let eR := fixedResidualFramedCoefficientResidueEquiv p H σ hσ S
  letI : Finite (IsLocalRing.ResidueField R) :=
    Finite.of_equiv (IsLocalRing.ResidueField O) eR.toEquiv.symm
  letI : CompactSpace R := originalAdicCompleteLocal_compactSpace hd.2.2
  let υ := fixedResidualFramedUniversalRepresentation p H σ hσ S hS
  obtain ⟨hlocal, hnoeth, _htop, _hcomplete, _hclass⟩ :=
    fixedResidualTraceUnframedUniversality_exists (L := L) p hp H σ hσ S hS i₀
  letI : IsLocalRing (closedMatrixTraceAlgebra (O := O) υ) := hlocal
  letI : IsNoetherianRing (closedMatrixTraceAlgebra (O := O) υ) := hnoeth
  let E := fixedResidualFramedFiberEquiv rfl eA p hp H σ hσ S hS
  let f := E.symm ⟨τ, hτ⟩
  have he : (GeneralLinearGroup.map f.val.toRingHom).comp υ = τ.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    have h := congrArg (fun x : OriginalContinuousFramedFiber eA H σ => x.val g)
      (E.apply_symm_apply ⟨τ, hτ⟩)
    exact h
  have hn := closedMatrixTraceAlgebra_isNoetherian_of_map υ f.val f.property.1
  rw [he] at hn
  exact hn

end
end Dubon2026
