import Dubon2026.SourceManinOrbitCount

/-! DUB-17/18 -> exceptional modular-place census. Native finite-order
power enumeration identifies the existing orbit quotient with the two
or three listed cyclic images. A surjective classifier with these fibers
then gives the cardinality of the actual place fiber. -/
namespace Dubon2026.SourceEllipticExceptional
open SourceManin
noncomputable section
variable {X Y : Type*}

theorem orbQ_eq_iff_pow_lt (τ : Equiv.Perm X) (n : ℕ) (hn : 0 < n)
    (hτ : τ ^ n = 1) (S T : X) :
    orbQ τ S = orbQ τ T ↔ ∃ i : ℕ, i < n ∧ T = (τ ^ i) S := by
  classical
  constructor
  · intro he
    obtain ⟨g, hg⟩ := (MulAction.mem_orbit_iff).mp (Quotient.exact he.symm)
    have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hτ⟩
    obtain ⟨i, hi, hiτ⟩ := Finset.mem_image.mp
      (hfin.mem_zpowers_iff_mem_range_orderOf.mp g.property)
    refine ⟨i, (Finset.mem_range.mp hi).trans_le
      (Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hτ)), ?_⟩
    rw [hiτ]
    exact hg.symm
  · rintro ⟨i, _hi, rfl⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨⟨τ ^ i, Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) i⟩, rfl⟩

theorem orbQ_eq_iff_two (τ : Equiv.Perm X) (hτ : τ ^ 2 = 1) (S T : X) :
    orbQ τ S = orbQ τ T ↔ T = S ∨ T = τ S := by
  rw [orbQ_eq_iff_pow_lt τ 2 (by norm_num) hτ]
  constructor
  · rintro ⟨i, hi, he⟩
    interval_cases i
    · exact Or.inl he
    · exact Or.inr he
  · rintro (he | he)
    · exact ⟨0, by norm_num, he⟩
    · exact ⟨1, by norm_num, he⟩

theorem orbQ_eq_iff_three (τ : Equiv.Perm X) (hτ : τ ^ 3 = 1) (S T : X) :
    orbQ τ S = orbQ τ T ↔ T = S ∨ T = τ S ∨ T = τ (τ S) := by
  rw [orbQ_eq_iff_pow_lt τ 3 (by norm_num) hτ]
  constructor
  · rintro ⟨i, hi, he⟩
    interval_cases i
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · rintro (he | he | he)
    · exact ⟨0, by norm_num, he⟩
    · exact ⟨1, by norm_num, he⟩
    · exact ⟨2, by norm_num, he⟩

theorem classifier_card_eq_orbits (τ : Equiv.Perm X)
    (f : X → Y) (hf : Function.Surjective f)
    (he : ∀ S T, f S = f T ↔ orbQ τ S = orbQ τ T) :
    Nat.card Y = Nat.card (Orb τ) := by
  let g : Orb τ → Y := Quotient.lift f (fun S T h => (he S T).mpr (Quotient.sound h))
  symm
  apply Nat.card_eq_of_bijective g
  constructor
  · rintro ⟨S⟩ ⟨T⟩ h
    exact (he S T).mp h
  · intro y
    obtain ⟨S, hS⟩ := hf y
    exact ⟨orbQ τ S, hS⟩

end
end Dubon2026.SourceEllipticExceptional
