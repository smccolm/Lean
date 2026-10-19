import Dubon2026.AlgebraicLocalDenseInertia
import Dubon2026.OriginalInertiaValuation

/-! Original number-field inertia passes to the same complete local
normed field through a dense compatible embedding. This uses the already
proved valuation congruence on the original field, and supplies the
inertia half of the actual finite-completion comparison required for
Dubon Theorem 2.6's base-support quotient identification. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The original global inertia congruence implies membership in actual
norm inertia for its compatible action on the original local completion.
The valuation comparison preserves the same prime and embedding. -/
theorem originalInertia_mem_normInertia_of_dense_embedding
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) (e : F →+* L) (hd : DenseRange e)
    (hv : (w.valuation F).IsEquiv ((NormedField.valuation (K := L)).comap e))
    (σ : Gal(F/ℚ)) (hσ : σ ∈ w.asIdeal.inertia Gal(F/ℚ))
    (g : Gal(L/K)) (he : ∀ x, g (e x) = e (σ x)) :
    g ∈ algebraicLocalInertia K L := by
  apply algebraicLocal_inertia_of_dense_integer_congruence e hd g
  intro y hy
  have hyv : w.valuation F y ≤ 1 := hv.le_one_iff_le_one.mpr (by exact_mod_cast hy)
  have hs := originalInertia_valuation_sub_lt_one ℚ F w σ hσ y hyv
  have hn := hv.lt_one_iff_lt_one.mp hs
  rw [he, ← map_sub]
  exact_mod_cast hn

end
end Dubon2026
