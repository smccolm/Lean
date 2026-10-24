import Dubon2026.SourceEllipticTorsionCardinality
import Dubon2026.SourceCyclicTorsionTransport

/-! The actual specialization reaches every prime-to-characteristic
torsion point once its derived finite Galois source has all N-squared
torsion points. Existing torsion cardinality and native finite injection
arguments supply surjectivity. This removes the lifting assumption needed
for the DUB-17/18 cyclic-subgroup specialization and exceptional fibers. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve
noncomputable section

/-- An actual torsion-domain homomorphism lands in the actual torsion of its target. -/
def torsionTargetMap {G H : Type*} [AddCommGroup G] [AddCommGroup H] (N : ℕ)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ H) :
    Submodule.torsionBy ℤ G (N : ℤ) →+ Submodule.torsionBy ℤ H (N : ℤ) where
  toFun P := ⟨θ P, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, Submodule.smul_torsionBy, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (θ.map_add P Q)

theorem torsionTargetMap_injective {G H : Type*} [AddCommGroup G] [AddCommGroup H] (N : ℕ)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ H) (hθ : Function.Injective θ) :
    Function.Injective (torsionTargetMap N θ) :=
  fun _ _ h => hθ (congrArg Subtype.val h)

theorem torsionTargetMap_surjective_of_full_card
    {G K : Type*} [AddCommGroup G] [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ E₀.toAffine.Point) (hθ : Function.Injective θ)
    (hcard : Nat.card {P : G // N • P = 0} = N ^ 2) :
    Function.Surjective (torsionTargetMap N θ) := by
  let e : {P : G // N • P = 0} ≃ Submodule.torsionBy ℤ G (N : ℤ) :=
    Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  have hgen : Nat.card (Submodule.torsionBy ℤ G (N : ℤ)) = N ^ 2 := by
    rw [← Nat.card_congr e]
    exact hcard
  have hres : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point (N : ℤ)) = N ^ 2 := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      using SourceEllipticTorsion.actual_torsion_cardinality E₀ hNK
  have hN0 : N ≠ 0 := by rintro rfl; exact hNK (Nat.cast_zero)
  letI : Finite (Submodule.torsionBy ℤ E₀.toAffine.Point (N : ℤ)) :=
    Nat.finite_of_card_ne_zero (hres ▸ pow_ne_zero 2 hN0)
  exact ((torsionTargetMap_injective N θ hθ).bijective_of_nat_card_le
    (by rw [hres, hgen])).surjective

theorem torsion_mem_specialization_range
    {G K : Type*} [AddCommGroup G] [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ E₀.toAffine.Point) (hθ : Function.Injective θ)
    (hcard : Nat.card {P : G // N • P = 0} = N ^ 2)
    (Q : E₀.toAffine.Point) (hQ : N • Q = 0) : Q ∈ θ.range := by
  let Q' : Submodule.torsionBy ℤ E₀.toAffine.Point (N : ℤ) :=
    ⟨Q, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hQ⟩
  obtain ⟨P, hP⟩ := torsionTargetMap_surjective_of_full_card E₀ N hNK θ hθ hcard Q'
  exact ⟨P, congrArg Subtype.val hP⟩

end
end Dubon2026.SourceEllipticReduction
