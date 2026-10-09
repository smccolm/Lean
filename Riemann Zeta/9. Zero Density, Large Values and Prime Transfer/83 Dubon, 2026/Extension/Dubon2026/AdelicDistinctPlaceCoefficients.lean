import Dubon2026.AdelicNormalizedCoefficientFactor

/-! # Exact original coefficient products across finitely many distinct genuine good places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- An actual good place is the genuine prime place of a prime coprime to the original level. -/
def IsGoodAdelicPlace (N : ℕ) (v : HeightOneSpectrum ℤ) : Prop :=
  ∃ (p : ℕ) (hp : p.Prime), p.Coprime N ∧ v = rationalPrimePlace p hp

/-- A genuine local matrix together with its actual finite place. -/
abbrev AdelicPlaceMatrix := Σ v : HeightOneSpectrum ℤ, GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)

/-- The original full adelic insertion of a genuine place-indexed local matrix. -/
def adelicPlaceMatrixEmbedding (a : AdelicPlaceMatrix) : RationalAdelicGL2 :=
  rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 a.1 a.2)

/-- A finite ordered product supported at other actual places has the identity original coordinate at the specified place. -/
theorem adelicPlaceGL2Hom_list_product (v : HeightOneSpectrum ℤ) (l : List AdelicPlaceMatrix)
    (hl : ∀ a ∈ l, v ≠ a.1) :
    adelicPlaceGL2Hom v (l.map adelicPlaceMatrixEmbedding).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    have ha := adelicPlaceGL2Hom_local_ne v a.1 (hl a (List.mem_cons_self)) a.2
    change adelicPlaceGL2Hom v (adelicPlaceMatrixEmbedding a) = 1 at ha
    rw [ha, ih (fun b hb => hl b (List.mem_cons_of_mem a hb)), one_mul]

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The proved original local coefficient factorization applies to each genuine good place, with the prime and coprimality obligations discharged from its actual arithmetic definition. -/
theorem adelicNormalizedCuspCoefficient_good_local_mul (v : HeightOneSpectrum ℤ)
    (hv : IsGoodAdelicPlace N v) (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom v a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g) * a) =
      adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) *
        adelicNormalizedCuspCoefficient F.toCuspForm a := by
  obtain ⟨p, hp, hpN, rfl⟩ := hv
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact adelicNormalizedCuspCoefficient_local_mul F hpN g a ha

/-- For every finite family of distinct genuine good places, the normalized original adelic cusp coefficient is exactly the product of its original local coefficients. -/
theorem adelicNormalizedCuspCoefficient_distinct_place_product (l : List AdelicPlaceMatrix)
    (hgood : ∀ a ∈ l, IsGoodAdelicPlace N a.1)
    (hdistinct : l.Pairwise (fun a b => a.1 ≠ b.1)) :
    adelicNormalizedCuspCoefficient F.toCuspForm (l.map adelicPlaceMatrixEmbedding).prod =
      (l.map (fun a => adelicNormalizedCuspCoefficient F.toCuspForm (adelicPlaceMatrixEmbedding a))).prod := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using
      adelicNormalizedCuspCoefficient_one F.toCuspForm (primitiveCuspForm_ne_zero F)
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hdistinct
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    have he := adelicNormalizedCuspCoefficient_good_local_mul F a.1
      (hgood a List.mem_cons_self) a.2 (l.map adelicPlaceMatrixEmbedding).prod
      (adelicPlaceGL2Hom_list_product a.1 l ha)
    change adelicNormalizedCuspCoefficient F.toCuspForm
      (adelicPlaceMatrixEmbedding a * (l.map adelicPlaceMatrixEmbedding).prod) = _ at he
    rw [he, ih (fun b hb => hgood b (List.mem_cons_of_mem a hb)) hl]
    rfl

end
end Dubon2026
