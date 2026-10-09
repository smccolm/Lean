import Dubon2026.AdelicFiniteFamilyMixedCoefficient

/-! # Exact coefficient products for the genuine finite tuple of original local groups -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- A genuine finite adelic product equals the literal ordered product over every repetition-free enumeration of its original coordinates. -/
theorem adelicFinitePlaceProduct_eq_list [DecidableEq I]
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (l : List I) (hl : l.Nodup) (hu : l.toFinset = Finset.univ) :
    adelicFinitePlaceProduct v hv g =
      (l.map (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))).prod := by
  let comm : ((Finset.univ : Finset I) : Set I).Pairwise
      (fun i j => Commute
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v j) (g j)))) :=
    fun i _ j _ hij => (finiteAdelicLocalGL2_commute (v i) (v j) (hv.ne hij) (g i) (g j)).map
      rationalAdelicFiniteGL2Embedding
  change Finset.univ.noncommProd
    (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i))) comm = _
  have h := Finset.noncommProd_toFinset l
    (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))
    (fun i _ j _ hij => comm (Finset.mem_univ i) (Finset.mem_univ j) hij) hl
  simpa only [hu] using h

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The normalized original cusp coefficient of a genuine finite tuple and full complement is the product of its actual local coefficients and original complementary coefficient. -/
theorem adelicNormalizedCuspCoefficient_finite_tuple_mul
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : ∀ i, adelicPlaceGL2Hom (v i) a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFinitePlaceProduct v hv g * a) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm a := by
  classical
  let l := (Finset.univ : Finset I).toList
  let t : I → AdelicPlaceMatrix := fun i => ⟨v i, g i⟩
  have hgood' : ∀ x ∈ l.map t, IsGoodAdelicPlace N x.1 := by
    rintro _ hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hgood i
  have hd : (l.map t).Pairwise (fun x y => x.1 ≠ y.1) := by
    apply List.pairwise_map.mpr
    exact (Finset.nodup_toList (Finset.univ : Finset I)).imp (fun hij => hv.ne hij)
  have ha' : ∀ x ∈ l.map t, adelicPlaceGL2Hom x.1 a = 1 := by
    rintro _ hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ha i
  have h := adelicNormalizedCuspCoefficient_distinct_place_product_mul F (l.map t) hgood' hd a ha'
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
theorem adelicNormalizedCuspCoefficient_finiteFamilyEquiv
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicNormalizedCuspCoefficient F.toCuspForm (adelicFiniteFamilyEquiv v hv b) =
      (∏ i, adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b.1 i)))) *
      adelicNormalizedCuspCoefficient F.toCuspForm b.2.val :=
  adelicNormalizedCuspCoefficient_finite_tuple_mul v hv F hgood b.1 b.2.val
    (adelicFiniteFamilyAwayGroup_place v b.2)

end
end Dubon2026
