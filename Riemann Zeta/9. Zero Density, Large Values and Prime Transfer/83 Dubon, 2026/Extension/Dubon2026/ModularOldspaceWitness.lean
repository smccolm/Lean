import Dubon2026.ModularNewspace
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! # A concrete witness for the ordinary-inclusion part of the oldspace

The actual modular discriminant has first Fourier coefficient one. At every
level N>1 its ordinary inclusion is old and is absent from the span of strict
dilations. This checks the distinction without assuming a normalized cusp form
exists and without altering the frozen Dubon source.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The actual level-one discriminant, viewed as a cusp form of level Gamma0(N). -/
def levelDiscriminant (N : ℕ) : CuspForm ((Gamma0 N).map (mapGL ℝ)) 12 :=
  cuspRestrictSubgroup (by
    intro γ hγ
    obtain ⟨δ, _, rfl⟩ := Subgroup.mem_map.mp hγ
    exact ⟨δ, rfl⟩) CuspForm.discriminant

/-- The first Fourier coefficient of the included discriminant remains one. -/
theorem levelDiscriminant_coeff_one (N : ℕ) : cuspCoefficients (levelDiscriminant N) 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

/-- Every higher-level included discriminant is in the full oldspace. -/
theorem levelDiscriminant_mem_oldspace {N : ℕ} (hN : 1 < N) :
    levelDiscriminant N ∈ cuspOldspace N 12 := by
  have he : cuspLevelInclusion (Nat.one_dvd N) 12 (levelDiscriminant 1) =
      levelDiscriminant N := by ext; rfl
  rw [← he]
  exact cuspLevelInclusion_mem_oldspace zero_lt_one hN (Nat.one_dvd N) _

/-- The included discriminant cannot be in the span of strict dilations. -/
theorem levelDiscriminant_not_strictDilationSpan (N : ℕ) :
    levelDiscriminant N ∉ strictCuspDilationSpan N 12 := by
  intro h
  have hz := strictCuspDilationSpan_coeff_one _ h
  rw [levelDiscriminant_coeff_one] at hz
  exact one_ne_zero hz

/-- A concrete weight-12 witness: ordinary inclusion is indispensable at every N>1. -/
theorem weight_twelve_oldspace_ne_strictDilationSpan {N : ℕ} (hN : 1 < N) :
    cuspOldspace N 12 ≠ strictCuspDilationSpan N 12 := by
  intro he
  exact levelDiscriminant_not_strictDilationSpan N (he ▸ levelDiscriminant_mem_oldspace hN)

end
end Dubon2026
