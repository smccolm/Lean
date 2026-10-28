import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place

open scoped Pointwise

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : AlgebraicCurve.Place K F) : AlgebraicCurve.SemilinearAut.ofAlgAut σ • v = σ • v := by
  have hfun : ∀ x : F, AlgebraicCurve.SemilinearAut.ofAlgAut σ • x = σ • x := fun _ => rfl
  apply AlgebraicCurve.Place.toValuationSubring_injective
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [hfun]
