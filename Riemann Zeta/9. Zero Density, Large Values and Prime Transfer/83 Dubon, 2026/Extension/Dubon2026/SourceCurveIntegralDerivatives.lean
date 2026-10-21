import Dubon2026.SourceCurveUniformizerResidue

/-! DUB-17/18 -> canonical divisors and local differential order formulas.
The cotangent/Nakayama argument generates the integral local differential
module by the actual uniformizer differential. Mapping to the function field
therefore proves that the derivative of every integral local function has an
integral local coefficient. The original consumer derives both finiteness and
residue separability from the proved actual field.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem span_integral_uniformizer_differential :
    Submodule.span v.toValuationSubring {D K v.toValuationSubring v.uniformizerSubring} = ⊤ :=
  v.span_D_uniformizer_eq_top_of_subsingleton
    v.subsingleton_polynomialKaehler_of_isSeparable_of_finite

theorem exists_integral_D_eq_smul_dCoord {f : F} (hf : f ∈ v.toValuationSubring) :
    ∃ g : F, g ∈ v.toValuationSubring ∧ D K F f = g • v.dCoord := by
  have hmem : D K v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) ∈
      Submodule.span v.toValuationSubring {D K v.toValuationSubring v.uniformizerSubring} := by
    rw [v.span_integral_uniformizer_differential]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hmem
  have hpush := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hg
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hpush
  refine ⟨(g : F), g.2, ?_⟩
  change D K F f = (g : F) • D K F (v.uniformizerSubring : F)
  exact (algebraMap_smul F g (D K F (v.uniformizerSubring : F))).trans hpush |>.symm

theorem differentialCoeff_D_mem_of_mem [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {f : F} (hf : f ∈ v.toValuationSubring) :
    v.differentialCoeff (D K F f) ∈ v.toValuationSubring := by
  obtain ⟨g, hg, he⟩ := v.exists_integral_D_eq_smul_dCoord hf
  rwa [v.differentialCoeff_unique he]

theorem ordDifferential_D_nonneg_of_mem [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ordDifferential (D K F f) :=
  v.ord_nonneg_of_mem (v.differentialCoeff_D_mem_of_mem hf)

end
end Dubon2026.SourceCurve.Place
