import Dubon2026.SurjectiveCosetEquiv
import Dubon2026.CoinducedCosetTrace
import Dubon2026.OriginalCohomologyTraceNaturality

/-! DUB-17/18 -> all-weight adic association -> genuine Gamma1 Hecke
realization -> surjective-transfer compatibility. Pull back the actual
coinduced functions along the group map, and compare their literal traces
using the existing subgroup-preimage coset map. Coset surjectivity is an
explicit upstream group condition, not a cohomological compatibility premise. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R D G : Type} [CommRing R] [Group D] [Group G]
  (A : Rep.{0} R G) (φ : D →* G) (S : Subgroup G)

/-- The actual restriction of the original group homomorphism to the
literal subgroup preimage. -/
def sourceTracePullbackSubgroupHom : S.comap φ →* S :=
  (φ.comp (S.comap φ).subtype).codRestrict S (fun g => g.property)

/-- Pull back an actual equivariant function by the actual group map.
This is a morphism of the original restricted and coinduced representations. -/
def sourceCoinducedTracePullback :
    Rep.res φ (Rep.coind S.subtype (Rep.res S.subtype A)) ⟶
      Rep.coind (S.comap φ).subtype (Rep.res (S.comap φ).subtype (Rep.res φ A)) :=
  Rep.ofHom {
    toLinearMap := {
      toFun := fun f => ⟨fun d => f.val (φ d), by
        intro t d
        change f.val (φ (t.val * d)) = A.ρ (φ t.val) (f.val (φ d))
        rw [map_mul]
        exact f.property (⟨φ t.val, t.property⟩ : S) (φ d)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    isIntertwining' := by
      intro d
      ext f x
      change f.val (φ x * φ d) = f.val (φ (x * d))
      rw [map_mul] }

/-- Pullback preserves the exact untwisted coefficient values on the
existing genuine subgroup-preimage coset map. -/
theorem sourceCoinducedTracePullback_values
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) (x : D ⧸ S.comap φ) :
    coinducedCosetValues (Rep.res φ A) (S.comap φ)
      ((sourceCoinducedTracePullback A φ S).hom f) x =
      coinducedCosetValues A S f (subgroupComapCosetMap φ S x) := by
  induction x using QuotientGroup.induction_on with
  | H d =>
    change A.ρ (φ d) (f.val (φ d⁻¹)) = A.ρ (φ d) (f.val (φ d)⁻¹)
    rw [map_inv]

/-- Identity evaluation of the actual pullback is the original identity
evaluation, fixing the convention needed in the native Shapiro comparison. -/
theorem sourceCoinducedTracePullback_eval_one
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) :
    ((sourceCoinducedTracePullback A φ S).hom f).val 1 = f.val 1 := by
  change f.val (φ 1) = f.val 1
  rw [map_one]

/-- When every original coset is reached, the native coefficient pullback
commutes with the complete literal finite coset trace. -/
theorem sourceCoinducedTracePullback_trace
    [Fintype (G ⧸ S)] [Fintype (D ⧸ S.comap φ)]
    (hcosets : Function.Surjective (subgroupComapCosetMap φ S)) :
    (Rep.resFunctor φ).map (coinducedCosetTrace A S) =
      sourceCoinducedTracePullback A φ S ≫ coinducedCosetTrace (Rep.res φ A) (S.comap φ) := by
  let e := Equiv.ofBijective (subgroupComapCosetMap φ S)
    ⟨subgroupComapCosetMap_injective φ S, hcosets⟩
  apply Rep.hom_ext
  ext f
  change (∑ q : G ⧸ S, coinducedCosetValues A S f q) =
    ∑ x : D ⧸ S.comap φ, coinducedCosetValues (Rep.res φ A) (S.comap φ)
      ((sourceCoinducedTracePullback A φ S).hom f) x
  calc
    _ = ∑ x : D ⧸ S.comap φ, coinducedCosetValues A S f
        (subgroupComapCosetMap φ S x) :=
      (Equiv.sum_comp e (coinducedCosetValues A S f)).symm
    _ = _ := Finset.sum_congr rfl (fun x _ =>
      (sourceCoinducedTracePullback_values A φ S f x).symm)

end
end Dubon2026
