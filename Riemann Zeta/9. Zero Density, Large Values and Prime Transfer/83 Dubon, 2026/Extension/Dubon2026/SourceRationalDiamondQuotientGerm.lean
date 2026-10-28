import Dubon2026.SourceRationalCuspDiamondImage
import Dubon2026.SourceRationalModularCuspQuotient

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond Galois compatibility. Apply the proved cyclotomic descent to
the two actual normalized cusp images of each rational modular quotient.
Their pointwise identity recovers the original translated quotient, so
no Fricke membership or rational-germ premise remains for that quotient.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceFricke
open scoped MatrixGroups

theorem exists_rational_laurent_translated_ratio (N : ℕ) [NeZero N] {k : ℤ}
    (f h : ModularForm (Gamma1 N) k) (hh : h ≠ 0)
    (pf ph : PowerSeries ℚ)
    (hpf : pf.map (algebraMap ℚ ℂ) = qExpansion 1 f)
    (hph : ph.map (algebraMap ℚ ℂ) = qExpansion 1 h) (g : Gamma0 N) :
    ∃ X : LaurentSeries ℚ,
      CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) X)
        (cuspFunction N (fun τ : ℍ => f (g.val • τ) / h (g.val • τ))) := by
  obtain ⟨m, F, H, pF, pH, hF, hH, _, hratio⟩ :=
    exists_rational_normalized_cusp_quotient N f h hh pf ph hpf hph
  obtain ⟨A, hA⟩ := exists_rational_cuspWeightImage_diamond_laurent
    N ((m : ℤ) * 12) 0 0 m (by ring) F pF hF g
  obtain ⟨B, hB⟩ := exists_rational_cuspWeightImage_diamond_laurent
    N ((m : ℤ) * 12) 0 0 m (by ring) H pH hH g
  refine ⟨A / B, ?_⟩
  rw [map_div₀]
  have he : (cuspWeightImage (Gamma1 N) ((m : ℤ) * 12) 0 0 m F ∘ (g.val • ·)) /
      (cuspWeightImage (Gamma1 N) ((m : ℤ) * 12) 0 0 m H ∘ (g.val • ·)) =
        fun τ : ℍ => f (g.val • τ) / h (g.val • τ) :=
    funext (fun τ => hratio (g.val • τ))
  rw [← he]
  exact hA.cusp_div hB

end
end Dubon2026.SourceFunctionField.GammaOne
