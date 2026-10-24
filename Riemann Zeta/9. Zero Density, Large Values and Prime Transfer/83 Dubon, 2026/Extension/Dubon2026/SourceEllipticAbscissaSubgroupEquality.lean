import Dubon2026.SourceEllipticCyclicAbscissae

/-! For the successive actual cyclic quotients in the DUB-17/18 inertia
census, image subgroup compatibility only needs abscissa compatibility.
The existing same-abscissa lemma identifies the two points up to sign;
both signs belong to every additive subgroup. This avoids an unnecessary
comparison of quotient ordinate formulas. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- Inclusion of the actual finite abscissa sets implies inclusion of subgroups. -/
theorem subgroup_le_of_cyclicAbscissae_subset
    (H J : AddSubgroup W.toAffine.Point) [Finite H] [Finite J]
    (h : cyclicAbscissae W H ⊆ cyclicAbscissae W J) : H ≤ J := by
  intro P hPH
  by_cases hP : P = 0
  · simpa only [hP] using J.zero_mem
  · have hx := h ((mem_cyclicAbscissae W H _).mpr ⟨P, hPH, hP, rfl⟩)
    obtain ⟨Q, hQJ, hQ, hxQ⟩ := (mem_cyclicAbscissae W J _).mp hx
    rcases eq_or_eq_neg_of_xco_eq hP hQ hxQ.symm with he | he
    · rw [he]
      exact hQJ
    · rw [he]
      exact J.neg_mem hQJ

/-- The full finite subgroup is determined by its actual nonzero abscissae. -/
theorem cyclicAbscissae_eq_iff
    (H J : AddSubgroup W.toAffine.Point) [Finite H] [Finite J] :
    cyclicAbscissae W H = cyclicAbscissae W J ↔ H = J := by
  constructor
  · intro h
    exact le_antisymm (subgroup_le_of_cyclicAbscissae_subset W H J h.subset)
      (subgroup_le_of_cyclicAbscissae_subset W J H h.symm.subset)
  · rintro rfl
    rfl

/-- Exact zero fibers and nonzero abscissae determine the actual finite subgroup image. -/
theorem subgroup_map_eq_of_nonzero_abscissae
    {G : Type*} [AddGroup G] (J : AddSubgroup G) [Finite J]
    (φ ψ : G →+ W.toAffine.Point)
    (hz : ∀ g, φ g = 0 ↔ ψ g = 0)
    (hx : ∀ g, φ g ≠ 0 → (coordsOrZero (φ g)).1 = (coordsOrZero (ψ g)).1) :
    J.map φ = J.map ψ := by
  letI : Finite (J.map φ) := Finite.of_surjective (φ.addSubgroupMap J) (φ.addSubgroupMap_surjective J)
  letI : Finite (J.map ψ) := Finite.of_surjective (ψ.addSubgroupMap J) (ψ.addSubgroupMap_surjective J)
  apply (cyclicAbscissae_eq_iff W _ _).mp
  ext x
  rw [mem_cyclicAbscissae, mem_cyclicAbscissae]
  constructor
  · rintro ⟨P, ⟨g, hg, rfl⟩, hP, hPx⟩
    refine ⟨ψ g, ⟨g, hg, rfl⟩, fun he => hP ((hz g).mpr he), ?_⟩
    exact (hx g hP).symm.trans hPx
  · rintro ⟨P, ⟨g, hg, rfl⟩, hP, hPx⟩
    have hφ : φ g ≠ 0 := fun he => hP ((hz g).mp he)
    exact ⟨φ g, ⟨g, hg, rfl⟩, hφ, (hx g hφ).trans hPx⟩

end
end Dubon2026.SourceEllipticVelu
