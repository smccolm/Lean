import Dubon2026.SourceGammaOneCoverImageHecke
import Dubon2026.SourcePrincipalCoprimeReduction
import Dubon2026.SourceHeckeConjugationLower
import Dubon2026.SurjectiveCosetEquiv

/-! DUB-17/18 -> original all-weight adic association -> geometric Gamma1
realization -> actual transfer/Hecke compatibility -> discharge the explicit
coset-surjectivity hypothesis of native H1 trace base change. Principal-level
lifting and the proved lower-subgroup image supply genuine representatives. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- The original good-prime Hecke conjugation reaches every coset of the
actual Gamma1 cover image. This is the group hypothesis required by H1
trace base change, proved from coprime principal-level lifting. -/
theorem sourceGammaOneCoverHeckeTraceCoset_surjective
    (Q N ell : ℕ) [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    Function.Surjective (subgroupComapCosetMap (sourceHeckeConjugation hell)
      (sourceGammaOneDiagonalHom Q N).range) := by
  have hQ := hcop.of_dvd_right (dvd_mul_right Q N)
  have hN := hcop.of_dvd_right (dvd_mul_left N Q)
  have hM : Nat.Coprime ell (Q * N ^ 2) := hQ.mul_right (Nat.Coprime.pow_right 2 hN)
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha⟩ := sourcePrincipalReduction_surjective (Q * N ^ 2) ell hM.symm
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ell)) g.val)
    have haQ : a.val ∈ Gamma0 Q := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (Q * N ^ 2)).mp
        (Gamma_mem.mp a.property).2.2.1
      have hdiv : (Q : Int) ∣ ((Q * N ^ 2 : Nat) : Int) := by
        exact_mod_cast (dvd_mul_right Q (N ^ 2))
      exact hdiv.trans hc
    let b : Gamma0 Q := ⟨a.val, haQ⟩
    have hbH : b ∈ (sourceGammaOneDiagonalHom Q N).range :=
      sourceGammaOneCoverImage_of_principal Q N b a.property
    have hb : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ell)) b.val =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ell)) g.val := ha
    have hlow : g * b⁻¹ ∈ heckeLowerSubgroup Q ell := by
      change ((((g.val * b.val⁻¹) 1 0 : ℤ)) : ZMod ell) = 0
      have he : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ell))
          (g.val * b.val⁻¹) = 1 := by
        rw [map_mul, map_inv, hb, mul_inv_cancel]
      exact congrArg (fun z => z 1 0) he
    obtain ⟨u, hu⟩ := sourceHeckeConjugation_exists_lower hell hQ (g * b⁻¹) hlow
    refine ⟨(u : heckeUpperSubgroup Q ell ⧸
      (sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)), ?_⟩
    apply QuotientGroup.eq.mpr
    change (sourceHeckeConjugation hell u)⁻¹ * g ∈
      (sourceGammaOneDiagonalHom Q N).range
    rw [hu]
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hbH

/-- The actual subgroup pulled back by Hecke conjugation is exactly the
ordinary intersection with the upper subgroup, by the proved congruences. -/
theorem sourceGammaOneCoverHeckeTraceSubgroup_eq
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    (sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell) =
      (sourceGammaOneDiagonalHom Q N).range.comap (heckeUpperSubgroup Q ell).subtype := by
  ext u
  exact sourceHeckeConjugation_mem_gammaOneCover_iff Q N ell hell hcop u

end
end Dubon2026
