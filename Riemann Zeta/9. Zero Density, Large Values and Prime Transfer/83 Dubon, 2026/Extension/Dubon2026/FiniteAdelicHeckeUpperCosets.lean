import Dubon2026.GeneralLinearUpperZero
import Dubon2026.IntegralGamma0FiniteResidue
import Dubon2026.HeckeUpperCosets

/-! # Genuine finite-adelic Hecke cosets represented by the original classical matrices -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original finite adelic level subgroup whose actual upper-right residue at the prime is zero. -/
def finiteAdelicHeckeUpper (N p : ℕ) [NeZero p] [Fact p.Prime] : Subgroup (finiteAdeleGL2Gamma0 N) :=
  (gl2UpperZeroSubgroup (ZMod p)).comap (finiteAdelicLevelResidueHom N p)

/-- On original integral Gamma0 matrices, the genuine adelic Hecke subgroup is exactly the classical upper-congruence subgroup. -/
theorem finiteAdelicHeckeUpper_integral_iff (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (γ : Gamma0 N) : integralGamma0FiniteGL2Hom N γ ∈ finiteAdelicHeckeUpper N p ↔
      γ ∈ heckeUpperSubgroup N p := by
  change (finiteAdelicLevelResidueHom N p (integralGamma0FiniteGL2Hom N γ)).val 0 1 = 0 ↔ _
  rw [integralGamma0FiniteGL2Hom_residue]
  rfl

/-- The literal original inverse classical representatives define actual cosets of the full finite-adelic level group. -/
def finiteAdelicHeckeUpperCoset (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (x : Option (ZMod p)) :
    finiteAdeleGL2Gamma0 N ⧸ finiteAdelicHeckeUpper N p :=
  QuotientGroup.mk (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN x))⁻¹

/-- The original p+1 representatives remain distinct in the actual full finite-adelic level quotient. -/
theorem finiteAdelicHeckeUpperCoset_injective (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) : Function.Injective (finiteAdelicHeckeUpperCoset N p hpN) := by
  intro x y h
  apply heckeUpperCoset_injective (Fact.out : p.Prime) hpN
  apply QuotientGroup.eq.mpr
  have hm := QuotientGroup.eq.mp h
  change ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN x))⁻¹)⁻¹ *
    (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN y))⁻¹ ∈ finiteAdelicHeckeUpper N p at hm
  rw [inv_inv, ← map_inv, ← map_mul] at hm
  change ((heckeUpperRepresentative p N hpN x)⁻¹)⁻¹ *
    (heckeUpperRepresentative p N hpN y)⁻¹ ∈ heckeUpperSubgroup N p
  rw [inv_inv]
  exact (finiteAdelicHeckeUpper_integral_iff N p _).mp hm

/-- Every actual finite-adelic level coset has one of the genuine p+1 original classical representatives. -/
theorem finiteAdelicHeckeUpperCoset_surjective (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) : Function.Surjective (finiteAdelicHeckeUpperCoset N p hpN) := by
  intro q
  induction q using Quotient.inductionOn with | h g => ?_
  let M := finiteAdelicLevelResidueHom N p g
  by_cases hd : M.val 1 1 = 0
  · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
    change ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN none))⁻¹)⁻¹ * g ∈
      finiteAdelicHeckeUpper N p
    rw [inv_inv]
    change (finiteAdelicLevelResidueHom N p
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN none) * g)).val 0 1 = 0
    rw [map_mul, integralGamma0FiniteGL2Hom_residue]
    change (GeneralLinearGroup.map (Int.castRingHom (ZMod p))
      (toGL (heckeUpperRepresentative p N hpN none).val) * M).val 0 1 = 0
    simp [heckeUpperRepresentative, heckeBezoutRepresentative, GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two, hd]
  · let x : ZMod p := -M.val 0 1 / M.val 1 1
    refine ⟨some x, QuotientGroup.eq.mpr ?_⟩
    change ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN (some x)))⁻¹)⁻¹ * g ∈
      finiteAdelicHeckeUpper N p
    rw [inv_inv]
    change (finiteAdelicLevelResidueHom N p
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN (some x)) * g)).val 0 1 = 0
    rw [map_mul, integralGamma0FiniteGL2Hom_residue]
    change (GeneralLinearGroup.map (Int.castRingHom (ZMod p))
      (toGL (heckeUpperRepresentative p N hpN (some x)).val) * M).val 0 1 = 0
    simp [heckeUpperRepresentative, heckeUpperTranslation, GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two, x, hd]

/-- The genuine full finite-adelic Hecke quotient is exactly the original finite family of p+1 classical representatives. -/
def finiteAdelicHeckeUpperCosetEquiv (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) : Option (ZMod p) ≃ finiteAdeleGL2Gamma0 N ⧸ finiteAdelicHeckeUpper N p :=
  Equiv.ofBijective (finiteAdelicHeckeUpperCoset N p hpN)
    ⟨finiteAdelicHeckeUpperCoset_injective N p hpN, finiteAdelicHeckeUpperCoset_surjective N p hpN⟩

end
end Dubon2026
