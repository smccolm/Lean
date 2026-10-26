import Dubon2026.SourcePrincipalCoprimeReduction
import Dubon2026.SourceGammaOneCoverHeckeSquare
import Dubon2026.SourceRaisedHeckeCosets

/-! DUB-17/18 -> all-weight adic association -> Gamma1 transfer Hecke
compatibility -> exact finite coset comparison. Principal-level lifting
at coprime moduli supplies actual Gamma1 representatives; the existing
raised-level equivalence then applies to the literal cover map. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup

/-- The literal inclusion into the raised Gamma0 level induces its actual
map of upper-correspondence cosets. -/
def sourceGammaOneRaisedCosetMap (Q N n : ℕ) :
    Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) n →
      Gamma0 (Q * N) ⧸ heckeUpperSubgroup (Q * N) n :=
  Quotient.map' (Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N))
    (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)

/-- The exact inclusion map is injective on these cosets because both
upper subgroups impose the same literal upper-right congruence. -/
theorem sourceGammaOneRaisedCosetMap_injective (Q N n : ℕ) :
    Function.Injective (sourceGammaOneRaisedCosetMap Q N n) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      intro h
      have he : ((Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N) a) :
          Gamma0 (Q * N) ⧸ heckeUpperSubgroup (Q * N) n) =
          (Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N) b) := h
      have hm := QuotientGroup.eq.mp he
      exact QuotientGroup.eq.mpr hm

/-- Coprime principal-level lifting proves that the actual Gamma1 inclusion
reaches every required original raised-level Hecke coset. -/
theorem sourceGammaOneRaisedCosetMap_surjective (Q N n : ℕ)
    [NeZero Q] [NeZero N] [NeZero n] (h : Nat.Coprime n (Q * N ^ 2)) :
    Function.Surjective (sourceGammaOneRaisedCosetMap Q N n) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha⟩ := sourcePrincipalReduction_surjective (Q * N ^ 2) n h.symm
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) g.val)
    have hg := Gamma_mem.mp a.property
    let b : Gamma1 (Q * N ^ 2) :=
      ⟨a.val, (Gamma1_mem _ _).mpr ⟨hg.1, hg.2.2.2, hg.2.2.1⟩⟩
    refine ⟨(b : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) n), ?_⟩
    apply QuotientGroup.eq.mpr
    let j := Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N)
    change ((((j b).val⁻¹ * g.val) 0 1 : ℤ) : ZMod n) = 0
    have hb : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) (j b).val =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) g.val := ha
    have he : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))
        ((j b).val⁻¹ * g.val) = 1 := by
      rw [map_mul, map_inv, hb, inv_mul_cancel]
    have hv := congrArg (fun z => z 0 1) he
    exact hv

/-- The exact Gamma1-to-raised-level map is a bijection of the genuine
finite Hecke cosets at every coprime nonzero modulus. -/
theorem sourceGammaOneRaisedCosetMap_bijective (Q N n : ℕ)
    [NeZero Q] [NeZero N] [NeZero n] (h : Nat.Coprime n (Q * N ^ 2)) :
    Function.Bijective (sourceGammaOneRaisedCosetMap Q N n) :=
  ⟨sourceGammaOneRaisedCosetMap_injective Q N n,
    sourceGammaOneRaisedCosetMap_surjective Q N n h⟩

end
end Dubon2026
