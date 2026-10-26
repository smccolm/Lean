import Dubon2026.SourceArithmeticWittCyclotomic
import Dubon2026.SourceResidualWittRepresentation

/-! DUB-17/18 -> arithmetic automorphy -> actual fixed-determinant
deformations. The determinant of the original residual matrices agrees
with the reduction of the genuine p-adic cyclotomic power over Witt
coefficients. Thus determinant compatibility is proved from the already
derived residual determinant, rather than supplied as a new premise. -/
namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

theorem sourceResidualWitt_fixedDeterminant_compatibility
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (K : Type) [Field K] [Finite K] [CharP K p] [TopologicalSpace K]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a) (j : ℕ)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
    (hdet : GeneralLinearGroup.det.comp σ =
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j) :
    ∀ g, GeneralLinearGroup.det (sourceResidualWittRepresentation p K σ g) =
      Units.map (algebraMap (WittVector p K) (ResidueField (WittVector p K)))
        ((sourceArithmeticWittCyclotomicCharacter p K a ^ j) g) := by
  intro g
  let e := sourceResidualWittResidueEquiv p K
  let σW := sourceResidualWittRepresentation p K σ
  apply Units.ext
  apply e.injective
  have hm := DFunLike.congr_fun (sourceResidualWittRepresentation_original p K σ) g
  have hd : e.toRingHom (σW g).val.det = (σ g).val.det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (congrArg Units.val hm)
  change e.toRingHom (σW g).val.det =
    e.toRingHom (residue (WittVector p K)
      (((sourceArithmeticWittCyclotomicCharacter p K a ^ j) g : (WittVector p K)ˣ) : WittVector p K))
  rw [hd]
  have hdetg := congrArg (fun χ => (χ g : K)) hdet
  change (σ g).val.det =
    e.toRingHom (residue (WittVector p K)
      ((sourceArithmeticWittCyclotomicCharacter p K a g : WittVector p K) ^ j))
  rw [map_pow, map_pow]
  change (σ g).val.det =
    (sourceResidualWittResidueEquiv p K
      (residue (WittVector p K)
        (sourceArithmeticWittCyclotomicCharacter p K a g : WittVector p K))) ^ j
  rw [sourceArithmeticWittCyclotomicCharacter_reduction p K a hpa]
  exact hdetg

end
end Dubon2026
