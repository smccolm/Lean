import TaoTrudgianYang2025.RobertSargosPrimitiveProjection

/-! Occupancy-preserving coordinates for actual frequency fibers. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosCoefficientTriple (p : RobertSargosPoint) : ℤ × ℤ × ℤ :=
  (p.h₁,p.h₂,p.r)

def robertSargosFromFrequencyKey (z t : ℤ × ℤ × ℤ) : RobertSargosPoint :=
  ⟨t.2.2,z.2.1,z.2.2,t.1,t.2.1,z.1⟩

theorem robertSargos_from_frequency_coordinates (p : RobertSargosPoint) :
    robertSargosFromFrequencyKey (robertSargosFrequencyKey p)
      (robertSargosCoefficientTriple p) = p := by
  cases p
  rfl

theorem robertSargos_from_fixed_frequency {p : RobertSargosPoint} {z : ℤ × ℤ × ℤ}
    (hz : robertSargosFrequencyKey p = z) :
    robertSargosFromFrequencyKey z (robertSargosCoefficientTriple p) = p := by
  rw [← hz]
  exact robertSargos_from_frequency_coordinates p

theorem robertSargos_frequency_fiber_image_card
    (S : Finset RobertSargosPoint) {z : ℤ × ℤ × ℤ}
    (hfix : ∀ p ∈ S, robertSargosFrequencyKey p = z) :
    (S.image robertSargosCoefficientTriple).card = S.card := by
  classical
  apply Finset.card_image_of_injOn
  intro p hp q hq he
  rw [← robertSargos_from_fixed_frequency (hfix p hp),
    ← robertSargos_from_fixed_frequency (hfix q hq),he]

theorem robertSargos_frequency_fiber_image_valid
    (S : Finset RobertSargosPoint) {R H Q δ : ℝ} {z : ℤ × ℤ × ℤ}
    (hmem : ∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p)
    (hfix : ∀ p ∈ S, robertSargosFrequencyKey p = z) :
    ∀ t ∈ S.image robertSargosCoefficientTriple,
      RobertSargosPrimitiveSystem R H Q δ (robertSargosFromFrequencyKey z t) := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  rw [robertSargos_from_fixed_frequency (hfix p hp)]
  exact hmem p hp

end TaoTrudgianYang2025

