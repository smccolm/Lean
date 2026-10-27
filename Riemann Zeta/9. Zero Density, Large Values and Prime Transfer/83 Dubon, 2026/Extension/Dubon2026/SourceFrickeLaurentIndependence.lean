import Dubon2026.SourceCuspLaurentLinearRelations
import Dubon2026.SourceFrickeHolomorphicIntegralSpan

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient descent of the original Fricke span. Linear independence of
actual holomorphic cyclotomic Fricke fractions survives extension to the
complex numbers. Their cyclotomic Laurent representations and the existing
coefficient-map independence theorem discharge this descent prerequisite. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem linearIndependent_holomorphic_cyclotomic_fricke_fractions
    {N : ℕ} [NeZero N] {ι : Type} {f : ι → ℍ → ℂ}
    (hf : ∀ i, f i ∈ holomorphicCyclotomicFrickeFractions N)
    (hind : LinearIndependent (kN N) f) : LinearIndependent ℂ f := by
  have hr : ∀ i, ∃ X : LaurentSeries (kN N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N (f i)) := by
    intro i
    obtain ⟨_, a, ha, b, hb, hb0, he⟩ := hf i
    exact exists_cyclotomic_fraction_represents ha hb hb0 he
  choose X hX using hr
  exact linearIndependent_functions_of_laurent_coefficients (by exact_mod_cast NeZero.pos N)
    (fun i => (hf i).1) (fun i => holomorphicCyclotomicFrickeFractions_periodic (hf i)) hX hind

end
end Dubon2026.SourceFricke