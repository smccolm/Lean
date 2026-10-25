import Dubon2026.SourceOriginalWeilPrincipalShift
import Dubon2026.SourceOriginalWeilSameDivisors

/-! DUB-17/18 -> original Weil pairing descent. Principal changes of
either divisor preserve the pairing, with no assumption on the functions
chosen for the new representatives. All reciprocity and constant-function
inputs are the proved original-field results. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable {n : ℕ} [NeZero n]

theorem pairing_eq_of_isPrincipal_sub_left (d d' : OriginalWeilDatum N L n)
    (hD₂ : d'.D₂ = d.D₂) (hprin : Divisor.IsPrincipal (d'.D₁ - d.D₁)) :
    d'.pairing = d.pairing := by
  obtain ⟨h, hh, hord⟩ := hprin
  let w := d.f₁ * h ^ n
  have hw : w ≠ 0 := mul_ne_zero d.f₁_ne_zero (pow_ne_zero n hh)
  have hordw (v : Place L (modularFunctionFieldOver N L)) : v.ord w = n * d'.D₁ v := by
    dsimp only [w]
    rw [v.ord_mul d.f₁_ne_zero (pow_ne_zero n hh), ← zpow_natCast h n,
      v.ord_zpow, d.ord_f₁, ← hord v, Finsupp.sub_apply]
    ring
  let d'' : OriginalWeilDatum N L n := {
    D₁ := d'.D₁
    D₂ := d.D₂
    f₁ := w
    f₂ := d.f₂
    f₁_ne_zero := hw
    f₂_ne_zero := d.f₂_ne_zero
    ord_f₁ := hordw
    ord_f₂ := d.ord_f₂
    disjoint := fun v => by rw [← hD₂]; exact d'.disjoint v }
  have he : d''.pairing = d.pairing := by
    apply pairing_eq_of_addPrincipalLeft d d'' hh hord
    · change d'.D₁ = d.D₁ + (d'.D₁ - d.D₁)
      abel
    · rfl
    · rfl
    · rfl
  exact (pairing_eq_of_same_divisors d'' d' rfl hD₂).trans he

theorem pairing_eq_of_isPrincipal_sub_right (d d' : OriginalWeilDatum N L n)
    (hD₁ : d'.D₁ = d.D₁) (hprin : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  have he := pairing_eq_of_isPrincipal_sub_left d.symm d'.symm hD₁ hprin
  rw [symm_pairing, symm_pairing] at he
  exact inv_injective he

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum
