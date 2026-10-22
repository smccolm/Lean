import Dubon2026.SourceOriginalDifferentialReadingLinear

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
Finite linear combinations of actual regular differentials have the same
linear combinations of actual path integrals. Local primitive sums and the
proved original differential reading identity derive this law.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem isPrimitiveAlong_sum_smul {n : ℕ} (c : Fin n → ℂ)
    (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    {P Q : Place ℂ F} (γ : Path P Q) (g : Fin n → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong N (b i) γ (g i)) :
    IsPrimitiveAlong N (∑ i, c i • b i) γ (fun t => ∑ i, c i * g i t) := by
  intro t₀
  choose Φ hΦ hgf using fun i => hg i t₀
  refine ⟨fun z => ∑ i, c i * Φ i z, ?_, ?_⟩
  · have hd : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i,
        HasDerivAt (Φ i) (readDifferential N (γ t₀) (b i) z) z := by
      simpa only [placeChart_self] using Filter.eventually_all.mpr hΦ
    rw [placeChart_self]
    filter_upwards [hd, ball_mem_nhds (0 : ℂ) (place_spec N (γ t₀)).1] with z hz hzb
    rw [readDifferential_sum_smul N (γ t₀) c b hb hzb]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hz i).const_mul (c i)
  · filter_upwards [Filter.eventually_all.mpr hgf] with t ht
    simp only [ht]

theorem pathIntegral_sum_smul {n : ℕ} (c : Fin n → ℂ)
    (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral N (∑ i, c i • b i) γ = ∑ i, c i * pathIntegral N (b i) γ := by
  choose g hg using fun i => exists_isPrimitiveAlong N (b i) (hb i) γ
  rw [pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_sum_smul N c b hb γ g hg)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pathIntegral_eq_of_isPrimitiveAlong N (hg i)]
  ring

end
end Dubon2026.SourceFunctionField.OriginalChart
