import Dubon2026.AdelicDistinctPlaceCoefficients
import Dubon2026.AdelicFiniteFamilyFactorization

/-! # Exact original finite-place coefficient factorization with an arbitrary genuine complementary translate -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- A finite family of distinct genuine good-place translates factors from every original full complementary translate in the normalized cusp coefficient. -/
theorem adelicNormalizedCuspCoefficient_distinct_place_product_mul (l : List AdelicPlaceMatrix)
    (hgood : ∀ x ∈ l, IsGoodAdelicPlace N x.1)
    (hdistinct : l.Pairwise (fun x y => x.1 ≠ y.1))
    (a : RationalAdelicGL2) (ha : ∀ x ∈ l, adelicPlaceGL2Hom x.1 a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm ((l.map adelicPlaceMatrixEmbedding).prod * a) =
      (l.map (fun x => adelicNormalizedCuspCoefficient F.toCuspForm (adelicPlaceMatrixEmbedding x))).prod *
        adelicNormalizedCuspCoefficient F.toCuspForm a := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_mul]
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp hdistinct
    have heval : adelicPlaceGL2Hom x.1 ((l.map adelicPlaceMatrixEmbedding).prod * a) = 1 := by
      rw [map_mul, adelicPlaceGL2Hom_list_product x.1 l hx, ha x List.mem_cons_self, one_mul]
    have he := adelicNormalizedCuspCoefficient_good_local_mul F x.1
      (hgood x List.mem_cons_self) x.2 ((l.map adelicPlaceMatrixEmbedding).prod * a) heval
    change adelicNormalizedCuspCoefficient F.toCuspForm
      (adelicPlaceMatrixEmbedding x * ((l.map adelicPlaceMatrixEmbedding).prod * a)) =
        adelicNormalizedCuspCoefficient F.toCuspForm (adelicPlaceMatrixEmbedding x) *
          adelicNormalizedCuspCoefficient F.toCuspForm ((l.map adelicPlaceMatrixEmbedding).prod * a) at he
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, he,
      ih (fun y hy => hgood y (List.mem_cons_of_mem x hy)) hl
        (fun y hy => ha y (List.mem_cons_of_mem x hy)), mul_assoc]

end
end Dubon2026
