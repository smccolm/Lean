import Dubon2026.SourceResidualWittFixedDeterminant
import Dubon2026.ArithmeticFixedDeterminantRepresentation

/-! DUB-17/18 -> arithmetic automorphy -> actual cyclotomic
fixed-determinant deformation problem. Consume the proved residual
determinant and the actual p-adic lift in the existing quotient.
Noetherianity, completeness, exact residue and universal determinant
are derived. A characteristic-zero specialization remains separate. -/
namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]
  (K : Type) [Field K] [Finite K] [CharP K p]
  [TopologicalSpace K] [DiscreteTopology K]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (hpa : (p : 𝓞 ℚ) ∣ a) (j : ℕ)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
  (hσ : Continuous σ)
  (hdet : GeneralLinearGroup.det.comp σ =
    (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j)

/-- Concrete properties of the existing quotient for the genuine cyclotomic determinant. -/
def sourceResidualWittFixedData : Prop :=
  letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
  letI : DiscreteTopology (ResidueField (WittVector p K)) := ⟨rfl⟩
  letI : Finite (ResidueField (WittVector p K)) :=
    (sourceResidualWittCoefficient_localData p K).2.2.2.1
  let σW := sourceResidualWittRepresentation p K σ
  let hσW := sourceResidualWittRepresentation_continuous p K σ hσ
  let δ := sourceArithmeticWittCyclotomicCharacter p K a ^ j
  let hδ := sourceResidualWitt_fixedDeterminant_compatibility p K a hpa j σ hdet
  let R := ArithmeticFixedDeterminantRing a ha p hp.out hpa σW hσW δ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp.out hpa σW hσW δ hδ
  let ρ := arithmeticFixedDeterminantRepresentation a ha p hp.out hpa σW hσW δ
  IsNoetherianRing R ∧ IsAdicComplete (maximalIdeal R) R ∧
    (∀ g, GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).toRingHom
      (GeneralLinearGroup.map (localCoefficientReduction
        (arithmeticFixedDeterminantResidueEquiv a ha p hp.out hpa σW hσW δ hδ)).toRingHom
        (ρ g)) = σ g) ∧
    ∀ g, GeneralLinearGroup.det (ρ g) =
      Units.map (algebraMap (WittVector p K) R).toMonoidHom (δ g)

theorem sourceResidualWittFixed_localData :
    sourceResidualWittFixedData p K a ha hpa j σ hσ hdet := by
  letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
  letI : DiscreteTopology (ResidueField (WittVector p K)) := ⟨rfl⟩
  letI : Finite (ResidueField (WittVector p K)) :=
    (sourceResidualWittCoefficient_localData p K).2.2.2.1
  let σW := sourceResidualWittRepresentation p K σ
  let hσW := sourceResidualWittRepresentation_continuous p K σ hσ
  let δ := sourceArithmeticWittCyclotomicCharacter p K a ^ j
  let hδ := sourceResidualWitt_fixedDeterminant_compatibility p K a hpa j σ hdet
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp.out hpa σW hσW δ hδ
  have hR := arithmeticFixedDeterminantRing_localData a ha p hp.out hpa σW hσW δ hδ
  refine ⟨hR.1, hR.2.1, ?_, ?_⟩
  · intro g
    have hr := DFunLike.congr_fun
      (arithmeticFixedDeterminantRepresentation_residue a ha p hp.out hpa σW hσW δ hδ) g
    change GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).toRingHom
      ((GeneralLinearGroup.map
        (localCoefficientReduction (arithmeticFixedDeterminantResidueEquiv
          a ha p hp.out hpa σW hσW δ hδ)).toRingHom).comp
          (arithmeticFixedDeterminantRepresentation a ha p hp.out hpa σW hσW δ).toMonoidHom g) = _
    rw [hr]
    exact DFunLike.congr_fun (sourceResidualWittRepresentation_original p K σ) g
  · exact arithmeticFixedDeterminantRepresentation_det a ha p hp.out hpa σW hσW δ

end
end Dubon2026
