import Dubon2026.SourceCurveReductionKummerPower

/-! DUB-17/18 -> Picard torsion injectivity. Existing normalized Kummer
data and a lifted function power make the actual divisor representative
principal. The next modular consumer proves the power-lifting premise. -/
namespace Dubon2026.SourceCurve.ConstantReduction
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem pic0_eq_zero_of_power_lifting [IsAlgClosed (ResidueField A)]
    (R : ConstantReduction A F Fbar)
    (hconst : LSpace (0 : Divisor (ResidueField A) Fbar) =
      LinearMap.range (Algebra.linearMap (ResidueField A) Fbar))
    (m : ℕ) (hm : 0 < m)
    (hlift : ∀ (f : R.integers), (∀ P : Place L F, (m : ℤ) ∣ P.ord (f : F)) →
      ∀ {w : Fbar}, w ≠ 0 → w ^ m = R.residue f → ∃ g : F, g ^ m = (f : F))
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  obtain ⟨D, hDz, f, hf, hDf, w, hw, hwp⟩ :=
    R.exists_residue_power_of_torsion_kernel hconst z m hm hmz hz
  obtain ⟨g, hg⟩ := hlift f (fun P => ⟨D.val P, (hDf P).symm⟩) hw hwp
  have hf0 : (f : F) ≠ 0 := by
    intro he
    have he' : f = 0 := Subtype.ext he
    exact hf (by rw [he', map_zero])
  have hg0 : g ≠ 0 := by
    intro he
    rw [he, zero_pow hm.ne'] at hg
    exact hf0 hg.symm
  have hprincipal : (D : Divisor L F) ∈ Divisor.principal (K := L) (F := F) := by
    refine ⟨g, hg0, fun P => ?_⟩
    apply mul_left_cancel₀ (show (m : ℤ) ≠ 0 by exact_mod_cast hm.ne')
    rw [hDf P, ← hg, ← zpow_natCast, P.ord_zpow]
  rw [← hDz]
  apply (QuotientAddGroup.eq_zero_iff D).mpr
  exact hprincipal

end
end Dubon2026.SourceCurve.ConstantReduction
