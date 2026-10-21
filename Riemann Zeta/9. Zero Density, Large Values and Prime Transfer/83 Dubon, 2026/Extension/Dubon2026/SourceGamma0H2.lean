import Dubon2026.SourceGammaFourFree
import Dubon2026.SourceGammaFourIndex
import Dubon2026.SourceFreeGroupH2

/-! Actual Gamma0 H2 vanishes after inverting six.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective native H1 coefficient maps -> this H2 vanishing.
The original Gamma 4 intersection is proved free, its actual index divides
48, and the existing native finite-index cohomology trace completes the
argument. No freeness, index bound or vanishing certificate is supplied.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- Native H2 of every original Gamma0 coefficient representation vanishes
when six is invertible. Actual subgroup freeness and the finite index bound
are derived from the original integral matrices. -/
theorem sourceGamma0H2_subsingleton {R : Type} [CommRing R] (Q : ℕ)
    (h6 : IsUnit (6 : R)) (A : Rep R (Gamma0 Q)) :
    Subsingleton (groupCohomology A 2) := by
  let S := (Gamma 4).subgroupOf (Gamma0 Q)
  letI : IsFreeGroup S := sourceGammaFour_subgroup_free Q
  have hd : S.index ∣ 48 := sourceGammaFour_subgroup_index_dvd_48 Q
  letI : S.FiniteIndex := ⟨by
    intro hzero
    rw [hzero, zero_dvd_iff] at hd
    norm_num at hd⟩
  have h2 : IsUnit (2 : R) :=
    isUnit_of_mul_isUnit_left (show IsUnit ((2 : R) * 3) by norm_num; exact h6)
  have h48 : IsUnit ((48 : ℕ) : R) := by
    have he : ((48 : ℕ) : R) = 6 * (2 * (2 * 2)) := by norm_num
    rw [he]
    exact h6.mul (h2.mul (h2.mul h2))
  have hi : IsUnit (S.index : R) := by
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul] at h48
    exact isUnit_of_mul_isUnit_left h48
  exact sourceFreeFiniteIndexH2_subsingleton S hi A

end
end Dubon2026
