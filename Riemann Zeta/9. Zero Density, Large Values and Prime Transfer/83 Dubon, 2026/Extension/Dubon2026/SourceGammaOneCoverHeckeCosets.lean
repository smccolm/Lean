import Dubon2026.SourceGammaOneRaisedCosets

/-! DUB-17/18 -> all-weight adic association -> Gamma1 geometric Hecke
comparison. Assemble the actual cover's good-prime coset equivalence
from principal-level lifting and the existing raised-level coset theorem. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- The exact diagonal cover map on genuine Hecke cosets. -/
def sourceGammaOneCoverHeckeCosetMap (Q N ell : ℕ) [NeZero N]
    (hcop : Nat.Coprime ell (Q * N)) :
    Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell →
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  sourceRaisedHeckeCosetMap Q N ell hcop ∘ sourceGammaOneRaisedCosetMap Q N ell

/-- The coset map uses the original integral diagonal cover on every
actual matrix representative. -/
theorem sourceGammaOneCoverHeckeCosetMap_mk (Q N ell : ℕ) [NeZero N]
    (hcop : Nat.Coprime ell (Q * N)) (g : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneCoverHeckeCosetMap Q N ell hcop
        (g : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) =
      (sourceGammaOneDiagonalHom Q N g : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := rfl

/-- The actual cover coset map respects the actual original group action. -/
theorem sourceGammaOneCoverHeckeCosetMap_smul (Q N ell : ℕ) [NeZero N]
    (hcop : Nat.Coprime ell (Q * N)) (g : Gamma1 (Q * N ^ 2))
    (x : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceGammaOneCoverHeckeCosetMap Q N ell hcop (g • x) =
      sourceGammaOneDiagonalHom Q N g • sourceGammaOneCoverHeckeCosetMap Q N ell hcop x := by
  induction x using QuotientGroup.induction_on with
  | H x => exact congrArg QuotientGroup.mk (map_mul (sourceGammaOneDiagonalHom Q N) g x)

/-- Every good-prime coset of the original Gamma0 Hecke correspondence has
exactly one coset on the true Gamma1 cover. -/
theorem sourceGammaOneCoverHeckeCosetMap_bijective (Q N ell : ℕ)
    [NeZero Q] [NeZero N] (hell : ell.Prime) (hcop : Nat.Coprime ell (Q * N)) :
    Function.Bijective (sourceGammaOneCoverHeckeCosetMap Q N ell hcop) := by
  letI : NeZero ell := ⟨hell.ne_zero⟩
  have hQ := hcop.of_dvd_right (dvd_mul_right Q N)
  have hN := hcop.of_dvd_right (dvd_mul_left N Q)
  have hM : Nat.Coprime ell (Q * N ^ 2) := hQ.mul_right (Nat.Coprime.pow_right 2 hN)
  exact (sourceRaisedHeckeCosetMap_bijective Q N ell hcop hell).comp
    (sourceGammaOneRaisedCosetMap_bijective Q N ell hM)

/-- The concrete finite equivalence required to compare the actual two
Hecke traces; its map is the original diagonal cover. -/
def sourceGammaOneCoverHeckeCosetEquiv (Q N ell : ℕ)
    [NeZero Q] [NeZero N] (hell : ell.Prime) (hcop : Nat.Coprime ell (Q * N)) :
    (Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) ≃
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  Equiv.ofBijective _ (sourceGammaOneCoverHeckeCosetMap_bijective Q N ell hell hcop)

end
end Dubon2026
