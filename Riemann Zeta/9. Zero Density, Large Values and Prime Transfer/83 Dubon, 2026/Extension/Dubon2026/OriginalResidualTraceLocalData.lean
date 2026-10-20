import Dubon2026.ClosedMatrixTraceImage
import Dubon2026.CompactLocalCoefficientImage
import Dubon2026.FixedResidualTraceUnframedUniversality
import Dubon2026.OriginalAdicCompleteLocalCompactness

/-! Locality, Noetherianity and actual maximal-adic completeness of the
trace algebra of a whole continuous lift. The existing universal trace
ring supplies a continuous surjection onto the original trace algebra,
as required before DUB-17's CM polarization descent. -/

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

/-- The actual trace algebra of the whole lift is complete local and
Noetherian in its inherited topology, which is its own maximal-adic topology. -/
theorem originalResidualTraceAlgebra_localData
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
    let T := closedMatrixTraceAlgebra (O := O) τ.toMonoidHom
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal T) T := by
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
  let U := closedMatrixTraceAlgebra (O := O) υ
  letI : IsTopologicalRing U := inferInstanceAs (IsTopologicalRing U.toSubring)
  obtain ⟨hlocalU, hnoethU, htopU, _hcompleteU, _hclass⟩ :=
    fixedResidualTraceUnframedUniversality_exists (L := L) p hp H σ hσ S hS i₀
  letI : IsLocalRing U := hlocalU
  letI : IsNoetherianRing U := hnoethU
  letI : CompactSpace U := isCompact_iff_compactSpace.mp
    (isClosed_closedMatrixTraceAlgebra υ).isCompact
  let E := fixedResidualFramedFiberEquiv rfl eA p hp H σ hσ S hS
  let f := E.symm ⟨τ, hτ⟩
  have he : (GeneralLinearGroup.map f.val.toRingHom).comp υ = τ.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    exact congrArg (fun x : OriginalContinuousFramedFiber eA H σ => x.val g)
      (E.apply_symm_apply ⟨τ, hτ⟩)
  let T := closedMatrixTraceAlgebra (O := O) τ.toMonoidHom
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  let hlocalT := originalAdicCoefficientSubalgebra_isLocalRing rfl eA T
    (isClosed_closedMatrixTraceAlgebra τ.toMonoidHom)
  letI : IsLocalRing T := hlocalT
  have himage : U.map f.val = T := by
    rw [closedMatrixTraceAlgebra_map υ f.val f.property.1, he]
  let g : U →ₐ[O] T := (f.val.comp U.val).codRestrict T (fun x => by
    change f.val x.val ∈ T
    rw [← himage]
    exact ⟨x.val, x.property, rfl⟩)
  have hg : Continuous g := (f.property.1.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective g := by
    intro y
    have hy : y.val ∈ U.map f.val := himage.symm ▸ y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨hlocalT, isNoetherianRing_of_surjective _ _ g.toRingHom hs,
    compactLocalCoefficientImage_isAdic htopU g.toRingHom hg hs,
    compactLocalCoefficientImage_isAdicComplete htopU g.toRingHom hg hs⟩

end
end Dubon2026
