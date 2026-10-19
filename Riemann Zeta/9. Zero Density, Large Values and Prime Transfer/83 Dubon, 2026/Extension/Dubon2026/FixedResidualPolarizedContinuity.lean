import Dubon2026.FixedResidualPolarizedResidue
import Dubon2026.PolarizedBlockContinuity

/-! Continuity of the actual polarized representation over its original
coefficient quotient. Compactness and separatedness are derived from its
proved local data, and the faithful topological matrix embedding transfers
the native universal matrix continuity. This closes the continuity input
for the source-compatible framed fiber comparison in DUB-17. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  (p : ℕ) (H : ProfiniteGrp.{u})
  (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The original polarized universal representation is continuous in its actual quotient topology. -/
theorem fixedResidualPolarizedUniversalRepresentation_continuous :
    Continuous (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν) := by
  let R := FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  have hd := fixedResidualPolarizedCoefficientRing_localData p H σ hσ S hS ν hν
  letI : IsNoetherianRing R := hd.1
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hd.2.2
  letI : Finite (IsLocalRing.ResidueField R) := Finite.of_equiv (IsLocalRing.ResidueField O)
    (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν).toEquiv.symm
  letI : T2Space R := originalAdicCompleteLocal_t2Space hd.2.1
  letI : CompactSpace R := originalAdicCompleteLocal_compactSpace hd.2.1
  apply (continuous_polarized_iff_block _).mpr
  have he : (fun g => polarizedBlockRepresentation
      (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g)) =
      GeneralLinearGroup.map (fixedResidualPolarizedCoefficientMap p H σ hσ S hS ν).toRingHom ∘
        fixedResidualFramedUniversalRepresentation p H (polarizedBlockRepresentation.comp σ) hσ S hS :=
    funext (fixedResidualPolarizedUniversalRepresentation_block p H σ hσ S hS ν hν)
  rw [he]
  apply Continuous.comp ?_
    (fixedResidualFramedUniversalRepresentation_continuous p H
      (polarizedBlockRepresentation.comp σ) hσ S hS)
  unfold fixedResidualPolarizedCoefficientMap
    FixedResidualPolarizedCoefficientRing fixedResidualPolarizedCommRing
    fixedResidualPolarizedTopologicalSpace
  apply Units.continuous_map
  apply continuous_matrix
  intro i j
  exact (QuotientRing.isOpenQuotientMap_mk _).continuous.comp (continuous_apply_apply i j)

end
end Dubon2026
