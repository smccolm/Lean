import Dubon2026.SourceIntegerCoefficientExtension
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! DUB-17/18 -> lift the actual primitive projector identities to the
arithmetic Hecke algebra. A proved complex-independent integral basis
makes the literal coefficient extension injective. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {F K A B I : Type*} [Field F] [Field K] [Ring A] [Ring B] [Algebra K B]

theorem integerCoefficientExtension_injective (ι : F →+* K) (φ : A →+* B)
    (b : Module.Basis I ℤ A) (hb : LinearIndependent K (fun i => φ (b i))) :
    Function.Injective (integerCoefficientExtension ι φ) := by
  letI := Algebra.compHom B ι
  letI : IsScalarTower ℤ F B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let ψ : F ⊗[ℤ] A →ₐ[F] B := (AlgHom.liftEquiv ℤ F A B) φ.toIntAlgHom
  have hbF : LinearIndependent F (fun i => φ (b i)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    apply ι.injective
    rw [map_zero]
    exact (linearIndependent_iff'.mp hb) s (fun j => ι (c j)) hc i hi
  have he : ψ.toLinearMap = (b.baseChange F).constr F (fun i => φ (b i)) := by
    apply (b.baseChange F).ext
    intro i
    rw [Module.Basis.constr_basis]
    simp only [Module.Basis.baseChange_apply,
      AlgHom.toLinearMap_apply, ψ, AlgHom.liftEquiv_tmul, one_smul,
      RingHom.toIntAlgHom_apply]
  change Function.Injective ψ.toLinearMap
  rw [he]
  exact (b.baseChange F).injective_constr_of_linearIndependent hbF

end
end Dubon2026
