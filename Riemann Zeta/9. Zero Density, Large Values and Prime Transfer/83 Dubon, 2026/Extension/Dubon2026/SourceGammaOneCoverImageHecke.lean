import Dubon2026.SourceGammaOneCoverImage

/-! DUB-17/18 -> all-weight adic association -> Gamma1 transfer/Hecke
compatibility -> the exact subgroup pullback in the native trace square.
Use the proved actual image congruences and good-prime invertibility to
derive preservation in both directions, rather than assume a subgroup square. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- Literal integral Hecke conjugation preserves membership in the actual
Gamma1 cover image in both directions at every coprime nonzero modulus. -/
theorem sourceIntegralHeckeConjugate_mem_gammaOneCover_iff
    (Q N n : ℕ) [NeZero N] [NeZero n] (hcop : Nat.Coprime n (Q * N))
    (u : heckeUpperSubgroup Q n) :
    sourceIntegralHeckeConjugate u ∈ (sourceGammaOneDiagonalHom Q N).range ↔
      u.val ∈ (sourceGammaOneDiagonalHom Q N).range := by
  have hQ := hcop.of_dvd_right (dvd_mul_right Q N)
  have hN := hcop.of_dvd_right (dvd_mul_left N Q)
  have hM : Nat.Coprime n (Q * N ^ 2) := hQ.mul_right (Nat.Coprime.pow_right 2 hN)
  have hnN : IsUnit (n : ZMod N) := (ZMod.isUnit_iff_coprime n N).mpr hN
  have hnM : IsUnit (n : ZMod (Q * N ^ 2)) :=
    (ZMod.isUnit_iff_coprime n (Q * N ^ 2)).mpr hM
  have hb : (u.val.val 0 1 / (n : ℤ)) * (n : ℤ) = u.val.val 0 1 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp u.property)
  have hupper : (N : ℤ) ∣ u.val.val 0 1 / (n : ℤ) ↔ (N : ℤ) ∣ u.val.val 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have he := congrArg (fun z : ℤ => (z : ZMod N)) hb
    dsimp only at he
    rw [Int.cast_mul, Int.cast_natCast] at he
    rw [← he]
    exact hnN.mul_left_eq_zero.symm
  have hlower :
      ((((u.val.val 1 0 * (n : ℤ)) * (N : ℤ) : ℤ)) : ZMod (Q * N ^ 2)) = 0 ↔
        ((u.val.val 1 0 * (N : ℤ) : ℤ) : ZMod (Q * N ^ 2)) = 0 := by
    have he : (u.val.val 1 0 * (n : ℤ)) * (N : ℤ) =
        (u.val.val 1 0 * (N : ℤ)) * (n : ℤ) := by ring
    rw [he, Int.cast_mul, Int.cast_natCast]
    exact hnM.mul_left_eq_zero
  rw [sourceGammaOneCoverImage_mem_iff, sourceGammaOneCoverImage_mem_iff]
  change ((u.val.val 0 0 : ZMod (Q * N ^ 2)) = 1 ∧
      (u.val.val 1 1 : ZMod (Q * N ^ 2)) = 1 ∧
      (N : ℤ) ∣ u.val.val 0 1 / (n : ℤ) ∧
      ((((u.val.val 1 0 * (n : ℤ)) * (N : ℤ) : ℤ)) : ZMod (Q * N ^ 2)) = 0) ↔ _
  rw [hupper, hlower]

/-- The original good-prime conjugation has the same proved two-sided
membership property for the actual Gamma1 image. -/
theorem sourceHeckeConjugation_mem_gammaOneCover_iff
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) (u : heckeUpperSubgroup Q ell) :
    sourceHeckeConjugation hell u ∈ (sourceGammaOneDiagonalHom Q N).range ↔
      u.val ∈ (sourceGammaOneDiagonalHom Q N).range := by
  rw [← sourceIntegralHeckeConjugate_eq_prime]
  exact sourceIntegralHeckeConjugate_mem_gammaOneCover_iff Q N ell hcop u

end
end Dubon2026
