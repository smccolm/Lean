import Dubon2026.AdelicEveryFiniteMixedCoefficient
import Dubon2026.AdelicFiniteTupleCoefficients

/-! # Actual finite tuple coefficient factorization including all bad places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The normalized original cusp coefficient of a genuine finite tuple and full complement is the product of its actual local coefficients and original complementary coefficient. -/
theorem adelicNormalizedCuspCoefficient_every_finite_tuple_mul
    (hk : 0 < k)
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : ∀ i, adelicPlaceGL2Hom (v i) a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFinitePlaceProduct v hv g * a) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm a := by
  classical
  let l := (Finset.univ : Finset I).toList
  let t : I → AdelicPlaceMatrix := fun i => ⟨v i, g i⟩
  have hd : (l.map t).Pairwise (fun x y => x.1 ≠ y.1) := by
    apply List.pairwise_map.mpr
    exact (Finset.nodup_toList (Finset.univ : Finset I)).imp (fun hij => hv.ne hij)
  have ha' : ∀ x ∈ l.map t, adelicPlaceGL2Hom x.1 a = 1 := by
    rintro _ hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ha i
  have h := adelicNormalizedCuspCoefficient_every_distinct_product_mul F (l.map t) hk hd a ha'
  rw [List.map_map, List.map_map] at h
  have hp := adelicFinitePlaceProduct_eq_list v hv g l (Finset.nodup_toList _)
    (Finset.toList_toFinset _)
  change adelicNormalizedCuspCoefficient F.toCuspForm
    ((l.map (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))).prod * a) =
      (l.map (fun i => adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i))))).prod *
      adelicNormalizedCuspCoefficient F.toCuspForm a at h
  rw [← hp, Finset.prod_map_toList] at h
  exact h

/-- The original full finite-family coordinate equivalence has the exact product of its genuine normalized local and complementary coefficients. -/
theorem adelicNormalizedCuspCoefficient_every_finiteFamilyEquiv
    (hk : 0 < k)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFiniteFamilyEquiv v hv b) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b.1 i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm b.2.val :=
  adelicNormalizedCuspCoefficient_every_finite_tuple_mul v hv F hk b.1 b.2.val
    (adelicFiniteFamilyAwayGroup_place v b.2)

end
end Dubon2026
