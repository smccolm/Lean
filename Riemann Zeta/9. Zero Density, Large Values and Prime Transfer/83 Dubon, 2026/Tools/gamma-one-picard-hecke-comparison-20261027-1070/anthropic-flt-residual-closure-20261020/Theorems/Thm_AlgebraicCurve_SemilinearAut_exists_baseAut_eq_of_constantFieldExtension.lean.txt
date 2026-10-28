import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.exists_baseAut_eq_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (τ : K' ≃ₐ[K] K') :
    ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = τ a) ∧
      ∀ y : F, g • algebraMap F F' y = algebraMap F F' y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension.solution
