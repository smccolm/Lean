import Dubon2026.HeckeLowerCosets
import Dubon2026.ModularDegeneracy

/-! The exact original level-raising index from the existing lower-coset transversal.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level raising from Q to Q*p -> injective restriction in characteristic p.
The existing lower representatives give the index p+1 directly, avoiding
the external Atkin involution construction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- Literal inclusion of the original congruence group at the multiplied level. -/
def sourceGamma0LevelInclusion (Q p : ℕ) : Gamma0 (Q * p) →* Gamma0 Q :=
  Subgroup.inclusion (Gamma0_le_of_dvd (dvd_mul_right Q p))

/-- At coprime levels the already constructed lower Hecke subgroup is the
actual group at level Q*p inside Gamma0 Q. -/
theorem sourceGamma0LevelSubgroup_eq_lower {Q p : ℕ} (hpQ : Nat.Coprime p Q) :
    (Gamma0 (Q * p)).subgroupOf (Gamma0 Q) = heckeLowerSubgroup Q p := by
  ext g
  change g.val ∈ Gamma0 (Q * p) ↔ ((g.val 1 0 : ℤ) : ZMod p) = 0
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd, Int.natCast_dvd]
  have hQ : Q ∣ (g.val 1 0 : ℤ).natAbs := by
    have h := g.property
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] at h
    exact h
  exact ⟨fun h => (dvd_mul_left p Q).trans h,
    fun h => hpQ.symm.mul_dvd_of_dvd_of_dvd hQ h⟩

/-- The exact level-raising index is p+1, obtained from the existing explicit
lower-congruence transversal. -/
theorem sourceGamma0LevelSubgroup_index {Q p : ℕ} (hp : p.Prime) (hpQ : Nat.Coprime p Q) :
    ((Gamma0 (Q * p)).subgroupOf (Gamma0 Q)).index = p + 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [sourceGamma0LevelSubgroup_eq_lower hpQ, Subgroup.index,
    ← Nat.card_congr (heckeLowerCosetEquiv hp hpQ)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

end
end Dubon2026
