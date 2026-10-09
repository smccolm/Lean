import Dubon2026.FiniteHilbertReferenceExtension
import Dubon2026.AdelicFiniteTensorCore

/-! # Appending actual original local unit references to genuine finite tensors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0)
  (v : Fin (n + 1) → HeightOneSpectrum ℤ)

/-- The genuine finite tensor extension appends the original normalized cusp vector at the new place. -/
def adelicFiniteLocalReferenceExtension :
    AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc) →ₗᵢ[ℂ] AdelicFiniteLocalTensor f v :=
  finiteHilbertReferenceExtension (fun i => adelicLocalInnerCarrier f (v i))
    (adelicLocalUnitReference f (v (Fin.last n))) (adelicLocalUnitReference_norm f hf (v (Fin.last n)))

/-- The original pure local orbit tuple is extended by the identity matrix at the actual new place. -/
theorem adelicFiniteLocalReferenceExtension_family
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) :
    adelicFiniteLocalReferenceExtension f hf v
      (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) g) =
      adelicFiniteLocalTensorFamily f v (Fin.snoc g 1) := by
  have he := finiteHilbertReferenceExtension_pure (fun i => adelicLocalInnerCarrier f (v i))
    (adelicLocalUnitReference f (v (Fin.last n))) (adelicLocalUnitReference_norm f hf (v (Fin.last n)))
    (fun i : Fin n => adelicLocalUnitOrbit f (v i.castSucc) (g i))
  refine he.trans (congrArg (finiteHilbertPureTensor (fun i => adelicLocalInnerCarrier f (v i))) ?_)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, adelicLocalUnitOrbit, map_one, Module.End.one_apply]
  · simp only [Fin.snoc_castSucc]

end
end Dubon2026
