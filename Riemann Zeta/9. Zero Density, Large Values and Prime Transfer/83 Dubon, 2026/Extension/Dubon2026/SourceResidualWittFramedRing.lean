import Dubon2026.SourceResidualWittRepresentation
import Dubon2026.ArithmeticFramedUniversalRing

/-! DUB-17/18 -> arithmetic automorphy -> the actual residual deformation
problem. The existing arithmetic framed construction consumes the same
finite residual representation over its genuine Witt coefficient ring.
Locality, Noetherianity, completeness and exact original residual
evaluation are proved. This does not assert a characteristic-zero
specialization or a Galois association for the original higher weight. -/
namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- Concrete properties of the existing framed ring, including exact original reduction. -/
def sourceResidualWittFramedData
    (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K p]
    [TopologicalSpace K] [DiscreteTopology K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
    (hσ : Continuous σ) : Prop :=
    letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
    letI : DiscreteTopology (ResidueField (WittVector p K)) := ⟨rfl⟩
    letI : Finite (ResidueField (WittVector p K)) :=
      (sourceResidualWittCoefficient_localData p K).2.2.2.1
    let σW := sourceResidualWittRepresentation p K σ
    let hσW := sourceResidualWittRepresentation_continuous p K σ hσ
    let R := ArithmeticFramedUniversalRing a ha p hp.out hpa σW hσW
    letI := arithmeticFramedUniversalRing_isLocal a ha p hp.out hpa σW hσW
    IsNoetherianRing R ∧ IsAdicComplete (maximalIdeal R) R ∧
      ∀ g, GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).toRingHom
        (GeneralLinearGroup.map
          (localCoefficientReduction (arithmeticFramedUniversalResidueEquiv
            a ha p hp.out hpa σW hσW)).toRingHom
          (arithmeticFramedUniversalRepresentation a ha p hp.out hpa σW hσW g)) = σ g

theorem sourceResidualWittFramed_localData
    (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K p]
    [TopologicalSpace K] [DiscreteTopology K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
    (hσ : Continuous σ) :
    sourceResidualWittFramedData p K a ha hpa σ hσ := by
  letI : TopologicalSpace (ResidueField (WittVector p K)) := ⊥
  letI : DiscreteTopology (ResidueField (WittVector p K)) := ⟨rfl⟩
  letI : Finite (ResidueField (WittVector p K)) :=
    (sourceResidualWittCoefficient_localData p K).2.2.2.1
  let σW := sourceResidualWittRepresentation p K σ
  let hσW := sourceResidualWittRepresentation_continuous p K σ hσ
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp.out hpa σW hσW
  have hdata := arithmeticFramedUniversalRing_localData a ha p hp.out hpa σW hσW
  refine ⟨hdata.1, hdata.2.1, ?_⟩
  intro g
  have he := DFunLike.congr_fun
    (arithmeticFramedUniversalRepresentation_residue a ha p hp.out hpa σW hσW) g
  change GeneralLinearGroup.map (sourceResidualWittResidueEquiv p K).toRingHom
    ((GeneralLinearGroup.map
      (localCoefficientReduction (arithmeticFramedUniversalResidueEquiv
        a ha p hp.out hpa σW hσW)).toRingHom).comp
      (arithmeticFramedUniversalRepresentation a ha p hp.out hpa σW hσW).toMonoidHom g) = _
  rw [he]
  exact DFunLike.congr_fun (sourceResidualWittRepresentation_original p K σ) g

end
end Dubon2026
