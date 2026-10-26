import Dubon2026.SourceCoinducedTowerFunctions

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> trace composition. Reindex the
entire coefficient sum by Mathlib's actual quotient-coset decomposition. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  (A : Rep.{0} R G) (S T : Subgroup G) (hST : S ≤ T)

/-- Every actual nested coset value agrees with the corresponding
flattened value under the genuine quotient-product equivalence. -/
theorem sourceCoinducedTowerTrace_values
    (f : Rep.coind T.subtype
      (Rep.coind (S.subgroupOf T).subtype
        (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))))
    (q : G ⧸ T) (x : T ⧸ S.subgroupOf T) :
    coinducedCosetValues A S ((sourceCoinducedTowerFlatten A S T hST).hom f)
      ((Subgroup.quotientEquivProdOfLE hST).symm (q, x)) =
      A.ρ q.out (coinducedCosetValues (Rep.res T.subtype A) (S.subgroupOf T)
        (f.val q.out⁻¹) x) := by
  induction x using QuotientGroup.induction_on with
  | H t =>
    change A.ρ (q.out * t.val) ((f.val (q.out * t.val)⁻¹).val 1) =
      A.ρ q.out (A.ρ t.val ((f.val q.out⁻¹).val t⁻¹))
    have hf := congrArg (fun z : Rep.coind (S.subgroupOf T).subtype
      (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)) => z.val 1)
      (f.property t⁻¹ q.out⁻¹)
    change (f.val (t.val⁻¹ * q.out⁻¹)).val 1 = (f.val q.out⁻¹).val (1 * t⁻¹) at hf
    rw [one_mul] at hf
    rw [mul_inv_rev, hf, map_mul, Module.End.mul_apply]

/-- The complete literal trace of the flattened coefficient function is
exactly the nested original coefficient trace. -/
theorem sourceCoinducedTowerTrace_comp
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (T ⧸ S.subgroupOf T)] :
    sourceCoinducedTowerFlatten A S T hST ≫ coinducedCosetTrace A S =
      (Rep.coindFunctor R T.subtype).map
        (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T)) ≫
          coinducedCosetTrace A T := by
  apply Rep.hom_ext
  ext f
  let fT := ((Rep.coindFunctor R T.subtype).map
    (coinducedCosetTrace (Rep.res T.subtype A) (S.subgroupOf T))).hom f
  have hval (q : G ⧸ T) :
      coinducedCosetValues A T fT q =
        A.ρ q.out (∑ x : T ⧸ S.subgroupOf T,
          coinducedCosetValues (Rep.res T.subtype A) (S.subgroupOf T)
            (f.val q.out⁻¹) x) :=
    congrArg (coinducedCosetValues A T fT) (Quotient.out_eq' q).symm
  change (∑ z : G ⧸ S, coinducedCosetValues A S
      ((sourceCoinducedTowerFlatten A S T hST).hom f) z) =
    ∑ q : G ⧸ T, coinducedCosetValues A T fT q
  simp_rw [hval]
  calc
    _ = ∑ z : (G ⧸ T) × (T ⧸ S.subgroupOf T),
        coinducedCosetValues A S ((sourceCoinducedTowerFlatten A S T hST).hom f)
          ((Subgroup.quotientEquivProdOfLE hST).symm z) :=
      (Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hST).symm
        (coinducedCosetValues A S ((sourceCoinducedTowerFlatten A S T hST).hom f))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q _
      rw [map_sum]
      exact Finset.sum_congr rfl (fun x _ => sourceCoinducedTowerTrace_values A S T hST f q x)

end
end Dubon2026
