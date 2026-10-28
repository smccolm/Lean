import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_D_ne_zero

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hbot : Submodule.span F (Set.range (KaehlerDifferential.D K F)) = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨t, rfl⟩; exact h t)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hω hmem
