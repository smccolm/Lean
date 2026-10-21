import Dubon2026.SourceDifferentialQExpansion
import Dubon2026.SourceDifferentialTranscendence

/-! DUB-17/18 -> original cusp-form lower dimension bound -> injective
expansion of regular differentials. For a Laurent-series intermediate field
separable over one transcendental element, the literal differential expansion
is injective. Transcendence discharges the nonzero-derivative requirement.
SourceOriginalDifferentialInjectivity applies this to the actual original
modular function field with its hypotheses proved.
-/
namespace Dubon2026.SourceDifferential
noncomputable section
open HahnSeries KaehlerDifferential

variable {L : Type*} [Field L] [CharZero L]

theorem qEuler_eq_zero_iff (x : LaurentSeries L) :
    qEuler L x = 0 ↔ x = algebraMap L (LaurentSeries L) (x.coeff 0) := by
  constructor
  · intro h
    rw [algebraMap_laurentSeries_apply_alt]
    ext n
    by_cases hn : n = 0
    · subst hn
      simp
    · have hc := congrArg (fun y : LaurentSeries L => y.coeff n) h
      have he : (n : L) * x.coeff n = 0 := by
        simpa only [qEuler_coeff, coeff_zero] using hc
      rw [(mul_eq_zero.mp he).resolve_left (Int.cast_ne_zero.mpr hn),
        coeff_single_of_ne hn]
  · intro h
    rw [h]
    exact (qEuler L).map_algebraMap _

theorem qEuler_ne_zero_of_transcendental
    (F : IntermediateField L (LaurentSeries L)) (x : F) (hx : Transcendental L x) :
    qEuler L (x : LaurentSeries L) ≠ 0 := by
  intro hz
  have he := (qEuler_eq_zero_iff (x : LaurentSeries L)).mp hz
  have hxC : x = algebraMap L F ((x : LaurentSeries L).coeff 0) := Subtype.ext he
  rw [hxC] at hx
  exact hx (isAlgebraic_algebraMap _)

theorem diffQExp_injective_of_transcendental
    (F : IntermediateField L (LaurentSeries L)) (x : F) (hx : Transcendental L x)
    [Algebra.IsSeparable (IntermediateField.adjoin L ({x} : Set F)) F] :
    Function.Injective (diffQExp F) := by
  have hspan := span_D_eq_top_of_transcendental L x hx
  have hrepr : ∀ ω : Ω[F⁄L], ∃ c : F, ω = c • D L F x := by
    intro ω
    have hm : ω ∈ Submodule.span F ({D L F x} : Set Ω[F⁄L]) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, hc.symm⟩
  intro ω₁ ω₂ h
  obtain ⟨c₁, rfl⟩ := hrepr ω₁
  obtain ⟨c₂, rfl⟩ := hrepr ω₂
  rw [diffQExp_smul_D, diffQExp_smul_D] at h
  have hc : c₁ = c₂ :=
    Subtype.ext (mul_right_cancel₀ (qEuler_ne_zero_of_transcendental F x hx) h)
  rw [hc]

end
end Dubon2026.SourceDifferential
