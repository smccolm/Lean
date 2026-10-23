import Dubon2026.SourceModularCoefficientSeparability
import Dubon2026.SourceDifferentialQExpansion
import Dubon2026.SourceDifferentialTranscendence

/-! DUB-17/18 -> original Frobenius/inertia -> residue curve geometry ->
one-dimensional differentials with faithful literal q expansion. The actual
j simple pole proves its derivative nonzero even in characteristic p;
the separating-coordinate theorem supplies spanning. No characteristic-zero
derivative-kernel assertion is transported to characteristic p. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open KaehlerDifferential SourceDifferential

theorem qEuler_jqModC_ne_zero (K : Type*) [Field K] : qEuler K (jqModC K) ≠ 0 := by
  intro h
  have hc := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  have : (-1 : K) = 0 := by
    simpa only [qEuler_coeff, coeff_jqModC_neg_one, Int.cast_neg, Int.cast_one,
      mul_one, HahnSeries.coeff_zero] using hc
  exact neg_ne_zero.mpr one_ne_zero this

theorem D_jCoeff_ne_zero (N : ℕ) (K : Type*) [Field K] :
    D K (modularFunctionFieldCoeff N K) (jCoeff N K) ≠ 0 := by
  intro h
  have he := congrArg (diffQExp (modularFunctionFieldCoeff N K)) h
  rw [diffQExp_D, map_zero] at he
  exact qEuler_jqModC_ne_zero K he

theorem span_D_jCoeff (N : ℕ) [NeZero N] (K : Type*) [Field K] [PerfectField K] :
    Submodule.span (modularFunctionFieldCoeff N K)
      ({D K (modularFunctionFieldCoeff N K) (jCoeff N K)} :
        Set Ω[modularFunctionFieldCoeff N K⁄K]) = ⊤ := by
  haveI := isSeparable_coeff_field N K
  exact span_D_eq_top_of_transcendental K (jCoeff N K) (transcendental_jCoeff N K)

theorem finrank_coeff_differentials (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K] :
    Module.finrank (modularFunctionFieldCoeff N K) Ω[modularFunctionFieldCoeff N K⁄K] = 1 :=
  (finrank_eq_one_iff_of_nonzero _ (D_jCoeff_ne_zero N K)).mpr (span_D_jCoeff N K)

theorem diffQExp_coeff_injective (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K] :
    Function.Injective (diffQExp (modularFunctionFieldCoeff N K)) := by
  let F := modularFunctionFieldCoeff N K
  have hrepr : ∀ ω : Ω[F⁄K], ∃ c : F, ω = c • D K F (jCoeff N K) := by
    intro ω
    have hm : ω ∈ Submodule.span F ({D K F (jCoeff N K)} : Set Ω[F⁄K]) := by
      rw [span_D_jCoeff N K]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, hc.symm⟩
  intro ω₁ ω₂ h
  obtain ⟨c₁, rfl⟩ := hrepr ω₁
  obtain ⟨c₂, rfl⟩ := hrepr ω₂
  rw [diffQExp_smul_D, diffQExp_smul_D] at h
  have hc : c₁ = c₂ := Subtype.ext (mul_right_cancel₀ (qEuler_jqModC_ne_zero K) h)
  rw [hc]

end
end Dubon2026.SourceFunctionField
