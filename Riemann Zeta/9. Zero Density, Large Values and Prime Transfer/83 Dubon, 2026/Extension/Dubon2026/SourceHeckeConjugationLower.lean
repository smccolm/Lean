import Dubon2026.SourceHeckeProductConjugation

/-! The existing diagonal conjugation covers the actual lower subgroup.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> full H1 Hecke commutativity -> product-coset parametrization.
Reuse the proved integral determinant calculation and original level condition.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckePrimeReindex
open scoped MatrixGroups

/-- Every actual lower-subgroup matrix at a good index is the literal diagonal
conjugate of an actual upper-subgroup matrix. -/
theorem sourceIntegralHeckeConjugate_exists_lower {Q p : ℕ} [NeZero p]
    (hpQ : Nat.Coprime p Q) (g : Gamma0 Q) (hg : g ∈ heckeLowerSubgroup Q p) :
    ∃ u : heckeUpperSubgroup Q p, sourceIntegralHeckeConjugate u = g := by
  have hd : (p : ℤ) ∣ g.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hg
  obtain ⟨c, hc⟩ := hd
  let D : SL(2, ℤ) :=
    ⟨!![g.val 0 0, (p : ℤ) * g.val 0 1; c, g.val 1 1],
      lower_div_tau_det_eq_one (sl2z_fin_two_det_eq_one g.val) p c hc⟩
  have hD : D ∈ Gamma0 Q := by
    rw [Gamma0_mem]
    change (c : ZMod Q) = 0
    have hG := Gamma0_mem.mp g.property
    rw [hc, Int.cast_mul, Int.cast_natCast] at hG
    exact (IsUnit.mul_right_eq_zero ((ZMod.isUnit_iff_coprime p Q).mpr hpQ)).mp hG
  have hu : (⟨D, hD⟩ : Gamma0 Q) ∈ heckeUpperSubgroup Q p := by
    rw [sourceHeckeUpper_mem_iff]
    exact dvd_mul_right _ _
  refine ⟨⟨⟨D, hD⟩, hu⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change !![g.val 0 0, ((p : ℤ) * g.val 0 1) / (p : ℤ); c * (p : ℤ), g.val 1 1] =
    g.val.val
  rw [Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne p))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, mul_comm]

/-- At a source prime, the original subgroup homomorphism covers every actual lower-subgroup matrix. -/
theorem sourceHeckeConjugation_exists_lower {Q p : ℕ} [NeZero p] (hp : p.Prime)
    (hpQ : Nat.Coprime p Q) (g : Gamma0 Q) (hg : g ∈ heckeLowerSubgroup Q p) :
    ∃ u : heckeUpperSubgroup Q p, sourceHeckeConjugation hp u = g := by
  obtain ⟨u, hu⟩ := sourceIntegralHeckeConjugate_exists_lower hpQ g hg
  exact ⟨u, (sourceIntegralHeckeConjugate_eq_prime hp u).symm.trans hu⟩

end
end Dubon2026
