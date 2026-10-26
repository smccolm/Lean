import Dubon2026.SourceGammaOneDiagonalHom
import Dubon2026.SourceIntegralHeckeHom

/-! DUB-17/18 -> all-weight adic association -> actual Gamma1 transfer
Hecke compatibility -> derive the group-level base-change hypotheses.
Identify the actual diagonal image by its literal congruences, using
the existing integral inverse conjugation. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- The genuine Gamma1 image is characterized by its exact integral
diagonal, upper-entry and lower-entry congruences. -/
theorem sourceGammaOneCoverImage_mem_iff (Q N : ℕ) [NeZero N] (g : Gamma0 Q) :
    g ∈ (sourceGammaOneDiagonalHom Q N).range ↔
      (g.val 0 0 : ZMod (Q * N ^ 2)) = 1 ∧
      (g.val 1 1 : ZMod (Q * N ^ 2)) = 1 ∧
      (N : ℤ) ∣ g.val 0 1 ∧
      ((g.val 1 0 * (N : ℤ) : ℤ) : ZMod (Q * N ^ 2)) = 0 := by
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨ha, hd, hc⟩ := (Gamma1_mem _ _).mp γ.property
    refine ⟨ha, hd, ⟨γ.val 0 1, rfl⟩, ?_⟩
    have hdiv : (N : ℤ) ∣ γ.val 1 0 :=
      Gamma0_dmul_lower_left_dvd N Q γ.val
        (by simpa only [Nat.mul_comm N Q] using
          sourceGammaOne_le_raisedGammaZero Q N γ.property)
    change (((γ.val 1 0 / (N : ℤ)) * (N : ℤ) : ℤ) : ZMod (Q * N ^ 2)) = 0
    rw [Int.ediv_mul_cancel hdiv]
    exact hc
  · rintro ⟨ha, hd, hb, hc⟩
    let u : heckeUpperSubgroup Q N :=
      ⟨g, (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hb⟩
    have hγ : (sourceIntegralHeckeConjugate u).val ∈ Gamma1 (Q * N ^ 2) := by
      rw [Gamma1_mem]
      exact ⟨ha, hd, hc⟩
    let γ : Gamma1 (Q * N ^ 2) := ⟨(sourceIntegralHeckeConjugate u).val, hγ⟩
    refine ⟨γ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hb' : (N : ℤ) * (g.val 0 1 / (N : ℤ)) = g.val 0 1 :=
      (mul_comm _ _).trans (Int.ediv_mul_cancel hb)
    have hc' : (g.val 1 0 * (N : ℤ)) / (N : ℤ) = g.val 1 0 :=
      Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr (NeZero.ne N))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceGammaOneDiagonalHom, sourceRaisedLevelConjugation,
        sourceRaisedLevelConjugate, levelRaiseConjOfDvd, γ, u,
        sourceIntegralHeckeConjugate, hb', hc']

/-- The actual cover image contains the original principal subgroup at
its exact level, supplying the concrete subgroup used in coprime lifting. -/
theorem sourceGammaOneCoverImage_of_principal (Q N : ℕ) [NeZero N]
    (g : Gamma0 Q) (hg : g.val ∈ Gamma (Q * N ^ 2)) :
    g ∈ (sourceGammaOneDiagonalHom Q N).range := by
  obtain ⟨ha, hb, hc, hd⟩ := Gamma_mem.mp hg
  apply (sourceGammaOneCoverImage_mem_iff Q N g).mpr
  have hNM : (N : ℤ) ∣ ((Q * N ^ 2 : ℕ) : ℤ) := by
    refine ⟨(Q : ℤ) * N, ?_⟩
    push_cast
    ring
  refine ⟨ha, hd, hNM.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb), ?_⟩
  rw [Int.cast_mul, hc, zero_mul]

end
end Dubon2026
