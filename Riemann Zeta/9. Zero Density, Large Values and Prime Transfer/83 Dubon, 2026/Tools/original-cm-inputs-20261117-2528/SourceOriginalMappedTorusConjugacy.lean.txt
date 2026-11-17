import Dubon2026.FiniteSymmetricAbsoluteIrreducible

/-! DUB-17/18 -> original regular-prime local dimensions. Transport the
actual subfield torus witness into a mapped conjugacy to an original torus.
For the selected route the common subfield is the canonical prime field. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- A literal extended conjugated SL2 torus, with compatible original
coefficients, gives the mapped conjugacy used by the original dimension theorem. -/
theorem original_mapped_torus_conjugacy_of_subfield_lift
    {k F E : Type} [Field k] [Field F] [Field E]
    (j : F →+* E) (φ : k →+* F) (θ : k →+* E) (hcomp : j.comp φ = θ)
    (A : GeneralLinearGroup (Fin 2) F) (B : GeneralLinearGroup (Fin 2) E)
    (u : kˣ) (h : SL(2, k))
    (hA : B * GeneralLinearGroup.map j A * B⁻¹ = GeneralLinearGroup.map θ
      (SpecialLinearGroup.toGL (h * ringSL2UnitDiagonal u * h⁻¹))) :
    IsConj (GeneralLinearGroup.map j A)
      (GeneralLinearGroup.map j (SpecialLinearGroup.toGL
        (ringSL2UnitDiagonal (Units.map φ.toMonoidHom u)))) := by
  have hc₁ : IsConj (GeneralLinearGroup.map j A)
      (GeneralLinearGroup.map θ
        (SpecialLinearGroup.toGL (h * ringSL2UnitDiagonal u * h⁻¹))) :=
    isConj_iff.mpr ⟨B, hA⟩
  have hd : IsConj (ringSL2UnitDiagonal u) (h * ringSL2UnitDiagonal u * h⁻¹) :=
    isConj_iff.mpr ⟨h, rfl⟩
  have hc₂ := (GeneralLinearGroup.map θ).map_isConj (SpecialLinearGroup.toGL.map_isConj hd.symm)
  have hc := hc₁.trans hc₂
  rw [← hcomp, GeneralLinearGroup.map_comp, MonoidHom.comp_apply,
    map_ringSL2UnitDiagonal] at hc
  exact hc

end
end Dubon2026
