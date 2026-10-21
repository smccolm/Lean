import Dubon2026.SourceGamma0LevelIndex
import Dubon2026.SourceHeckeSubgroupConjugation

/-! Exact original Hecke coset correspondence across the required level change.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> Hecke-compatible level raising. The actual inclusion induces an
injective map of prime-correspondence cosets; the existing p+1 transversal
at each level proves surjectivity without new representative arithmetic.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (Q p ell : ℕ)

/-- Membership in the original upper Hecke subgroup is unchanged by the
literal level inclusion. -/
theorem sourceLevelInclusion_mem_upper (g : Gamma0 (Q * p)) :
    sourceGamma0LevelInclusion Q p g ∈ heckeUpperSubgroup Q ell ↔
      g ∈ heckeUpperSubgroup (Q * p) ell := Iff.rfl

/-- The actual map between Hecke coset spaces induced by level inclusion. -/
def sourceLevelHeckeCosetMap :
    Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell →
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  Quotient.map' (sourceGamma0LevelInclusion Q p) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact (sourceLevelInclusion_mem_upper Q p ell _).mpr hab)

/-- The original level coset map takes the class of a matrix to its literal inclusion. -/
theorem sourceLevelHeckeCosetMap_mk (g : Gamma0 (Q * p)) :
    sourceLevelHeckeCosetMap Q p ell (g : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) =
      (sourceGamma0LevelInclusion Q p g : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := rfl

/-- The exact coset map respects the original action of every matrix at the raised level. -/
theorem sourceLevelHeckeCosetMap_smul (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceLevelHeckeCosetMap Q p ell (g • x) =
      sourceGamma0LevelInclusion Q p g • sourceLevelHeckeCosetMap Q p ell x := by
  induction x using QuotientGroup.induction_on with
  | H x => rfl

/-- The actual level inclusion induces an injective Hecke coset map. -/
theorem sourceLevelHeckeCosetMap_injective :
    Function.Injective (sourceLevelHeckeCosetMap Q p ell) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      intro h
      rw [sourceLevelHeckeCosetMap_mk, sourceLevelHeckeCosetMap_mk, QuotientGroup.eq,
        ← map_inv, ← map_mul, sourceLevelInclusion_mem_upper] at h
      exact QuotientGroup.eq.mpr h

/-- At every prime good at the raised level, the two actual Hecke coset
spaces are bijective under the original level inclusion. -/
theorem sourceLevelHeckeCosetMap_bijective (hell : ell.Prime)
    (hellQp : Nat.Coprime ell (Q * p)) :
    Function.Bijective (sourceLevelHeckeCosetMap Q p ell) := by
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell
  have hellQ : Nat.Coprime ell Q := hellQp.of_dvd_right (dvd_mul_right Q p)
  apply (sourceLevelHeckeCosetMap_injective Q p ell).bijective_of_nat_card_le
  exact le_of_eq ((Nat.card_congr (heckeUpperCosetEquiv hell hellQ)).symm.trans
    (Nat.card_congr (heckeUpperCosetEquiv hell hellQp)))

/-- The genuine Hecke coset equivalence induced by the original level inclusion. -/
def sourceLevelHeckeCosetEquiv (hell : ell.Prime) (hellQp : Nat.Coprime ell (Q * p)) :
    (Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) ≃
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  Equiv.ofBijective _ (sourceLevelHeckeCosetMap_bijective Q p ell hell hellQp)

end
end Dubon2026
