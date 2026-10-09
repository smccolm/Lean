import Dubon2026.HeckeCuspBehavior
import Dubon2026.RealGL2Sign

/-! # Holomorphy and genuine cusp vanishing throughout the actual rational slash span -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal complex span of all original rational slash translates of the given cusp form. -/
def rationalCuspSlashSpan : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range (fun r : GeneralLinearGroup (Fin 2) ℚ =>
    (f : ℍ → ℂ) ∣[k] rationalGL2ToReal r))

omit [NeZero N] in
/-- Every function in the actual rational slash span is genuinely holomorphic. -/
theorem rationalCuspSlashSpan_holomorphic (F : ℍ → ℂ) (hF : F ∈ rationalCuspSlashSpan f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨r, rfl⟩ := hF
      exact (ModularFormClass.holo f).slash k (rationalGL2ToReal r)
  | zero => exact mdifferentiable_const
  | add F G hF hG ihF ihG => exact ihF.add ihG
  | smul c F hF ih => exact MDifferentiable.const_smul c ih

/-- Every genuine rational slash combination vanishes at every original arithmetic cusp. -/
theorem rationalCuspSlashSpan_zero_at_cusps (F : ℍ → ℂ) (hF : F ∈ rationalCuspSlashSpan f)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 N).map (mapGL ℝ))) : c.IsZeroAt F k := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨r, rfl⟩ := hF
      exact OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' (rationalMatrix_smul_isCusp r hc))
  | zero => exact (0 : CuspForm ((Gamma0 N).map (mapGL ℝ)) k).zero_at_cusps' hc
  | add F G hF hG ihF ihG => exact ihF.add ihG
  | smul a F hF ih =>
      intro g hg
      rw [ModularForm.smul_slash]
      exact (ih g hg).smul _

end
end Dubon2026
