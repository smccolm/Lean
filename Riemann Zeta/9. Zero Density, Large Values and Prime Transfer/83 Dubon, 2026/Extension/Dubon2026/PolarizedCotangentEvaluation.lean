import Dubon2026.PolarizedCotangentCocyclePoints
import Dubon2026.PolarizedFirstOrderMatrixCoordinate
import Dubon2026.FixedResidualPolarizedEvaluation

/-! The cotangent comparison evaluates the actual universal polarized
matrix entries. This is the original coefficient-evaluation bridge needed
to prove residue-field linearity before using tangent dimensions in the
DUB-17 source Selmer comparison. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
  (H : ProfiniteGrp) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hσ : Continuous (polarizedBlockRepresentation.comp σ))
  (S : Finset (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ))
  (hS : Function.Surjective (profiniteGeneratorPresentation
    (originalResidualProfiniteGroup p H (polarizedBlockRepresentation.comp σ) hσ) S))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The original cotangent cocycle is the matrix of universal coefficient derivatives times the inverse original residual matrix. -/
theorem fixedResidualPolarizedCotangentCocycleEquiv_evaluation :
    (letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
     ∀ (d : OriginalResidueCotangentMaps
       (fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν)) (g : H),
       (fixedResidualPolarizedCotangentCocycleEquiv p hp H σ hσ S hS ν hν d).val g =
         (Matrix.of fun i j => (d (KaehlerDifferential.D O
           (FixedResidualPolarizedCoefficientRing p H σ hσ S hS ν)
           ((fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g).left.1.val i j))).val.snd) *
           (σ g).left.1.inv) := by
  letI := fixedResidualPolarizedCoefficientRing_isLocal p H σ hσ S hS ν hν
  intro d g
  let k := IsLocalRing.ResidueField O
  letI : WithIdeal (DualNumber k) := ⟨IsLocalRing.maximalIdeal (DualNumber k)⟩
  letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber k)) (DualNumber k) :=
    finiteDualNumber_maximal_isAdicComplete k
  letI : TopologicalSpace (DualNumber k) := (IsLocalRing.maximalIdeal (DualNumber k)).adicTopology
  let eR := fixedResidualPolarizedCoefficientResidueEquiv p H σ hσ S hS ν hν
  have hd := fixedResidualPolarizedCoefficientRing_localData p H σ hσ S hS ν hν
  let f := originalResidueCotangentContinuousFiberEquiv hd.2.1 eR d
  let τ := fixedResidualPolarizedFiberEquiv rfl (relativeDualNumberResidueEquiv O)
    p hp H σ hσ S hS ν hν f
  let T := originalPolarizedDualFiberEquiv H σ ν hν τ
  have ht : T.val.val g = polarizedCoefficientMap f.val.toRingHom
      (fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g) :=
    fixedResidualPolarizedFiberEquiv_evaluation rfl (relativeDualNumberResidueEquiv O)
      p hp H σ hσ S hS ν hν f g
  change polarizedFirstOrderCocycle σ T.val g = _
  rw [polarizedFirstOrderCocycle_matrix_formula]
  apply congrArg (fun M : Matrix ι ι k => M * (σ g).left.1.inv)
  apply Matrix.ext
  intro i j
  change ((T.val.val g).left.1.val i j).snd = _
  rw [ht]
  change (f.val ((fixedResidualPolarizedUniversalRepresentation p H σ hσ S hS ν hν g).left.1.val i j)).snd = _
  rw [originalResidueCotangentContinuousFiberEquiv_apply]
  simp [originalResidueConstantDualLift]

end
end Dubon2026
