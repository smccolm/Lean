import TaoTrudgianYang2025.RobertSargosPrimitiveSystem
import TaoTrudgianYang2025.IntegerAffineBandCount

/-! Actual source projections and the cardinality of their narrow affine band. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosFrequencyKey (p : RobertSargosPoint) : ℤ × ℤ × ℤ :=
  (p.d,p.q₁,p.q₂)

def robertSargosCoefficientKey (p : RobertSargosPoint) : ℤ × ℤ × ℤ :=
  (p.r,p.h₁,p.h₂)

theorem robertSargos_keys_injective {p q : RobertSargosPoint}
    (hc : robertSargosCoefficientKey p = robertSargosCoefficientKey q)
    (hf : robertSargosFrequencyKey p = robertSargosFrequencyKey q) : p = q := by
  cases p
  cases q
  simp_all [robertSargosCoefficientKey,robertSargosFrequencyKey]

theorem robertSargos_frequency_image_card_le
    (S : Finset RobertSargosPoint) {D R H Q δ : ℝ}
    (hD : 1 ≤ D) (hR : 0 ≤ R) (hH : 0 < H) (hQ : 1 ≤ Q)
    (hδ : δ ∈ Set.Icc 0 1)
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p)
    (hd : ∀ p ∈ S, |(p.d:ℝ)| ≤ 2*D) :
    ((S.image robertSargosFrequencyKey).card:ℝ) ≤
      25*D*Q*(2*(δ*Q+99*R*Q/H)+1) := by
  have hQp : 0 < Q := by linarith
  have hB : 0 ≤ δ*Q+99*R*Q/H :=
    add_nonneg (mul_nonneg hδ.1 hQp.le) (by positivity)
  apply integer_affine_band_triples_card_le_dyadic _ hD hQ hB
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact hd p hp
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact (hmem p hp).q₁_support.2
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact (hmem p hp).affine_band hH hQp hδ.2

end TaoTrudgianYang2025

