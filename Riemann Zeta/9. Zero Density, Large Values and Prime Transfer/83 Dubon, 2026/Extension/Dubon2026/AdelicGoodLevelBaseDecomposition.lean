import Dubon2026.AdelicRestrictedTensorBase
import Dubon2026.FiniteAdelicLevelAlmostEverywhere

/-! # Original adelic matrices integral at every good place split into fixed base and true level -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- An original matrix belongs to the fixed base exactly when all its genuine good coordinates are identity. -/
theorem adelicRestrictedBaseGroup_mem_iff (N : ℕ) (a : RationalAdelicGL2) :
    a ∈ adelicRestrictedBaseGroup N ↔ ∀ v, IsGoodAdelicPlace N v → adelicPlaceGL2Hom v a = 1 := by
  constructor
  · intro ha v hv
    exact adelicRestrictedBaseGroup_place ⟨a, ha⟩ v hv
  · intro ha
    funext v
    exact ha v.val v.property

/-- If every good coordinate is genuinely in local level, the original adelic matrix is fixed base times original finite level. -/
theorem adelicGoodLevel_exists_base_mul_level (N : ℕ) [NeZero N] (a : RationalAdelicGL2)
    (ha : ∀ v, IsGoodAdelicPlace N v → adelicPlaceGL2Hom v a ∈ finitePlaceGL2Gamma0 N v) :
    ∃ b : adelicRestrictedBaseGroup N, ∃ u : finiteAdeleGL2Gamma0 N,
      b.val * rationalAdelicFiniteGL2Embedding u.val = a := by
  classical
  obtain ⟨S, hS⟩ := finiteAdeleGL2Gamma0_exists_exceptional_finset N (rationalAdelicGL2RealFiniteEquiv a).2
  let B := S.filter (fun v => ¬ IsGoodAdelicPlace N v)
  let v : B → HeightOneSpectrum ℤ := Subtype.val
  have hv : Function.Injective v := Subtype.val_injective
  let r := adelicFinitePlaceRemoval v hv a
  have hr : (rationalAdelicGL2RealFiniteEquiv r).2 ∈ finiteAdeleGL2Gamma0 N := by
    apply (finiteAdeleGL2Gamma0_iff_places N _).mpr
    intro w
    change adelicPlaceGL2Hom w r ∈ _
    by_cases hw : w ∈ B
    · have he := adelicFinitePlaceRemoval_same v hv (⟨w, hw⟩ : B) a
      change adelicPlaceGL2Hom w r = 1 at he
      rw [he]
      exact (finitePlaceGL2Gamma0 N w).one_mem
    · have hne : ∀ i, w ≠ v i := by
        intro i he
        apply hw
        exact he.symm ▸ i.property
      have he := adelicFinitePlaceRemoval_ne v hv w hne a
      change adelicPlaceGL2Hom w r = adelicPlaceGL2Hom w a at he
      rw [he]
      by_cases hg : IsGoodAdelicPlace N w
      · exact ha w hg
      · have hnS : w ∉ S := by
          intro hwS
          exact hw (Finset.mem_filter.mpr ⟨hwS, hg⟩)
        exact hS w hnS
  let q := adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a)
  let aReal := rationalAdelicGL2RealFiniteEquiv.symm ((rationalAdelicGL2RealFiniteEquiv r).1, 1)
  have hq (w : HeightOneSpectrum ℤ) (hw : IsGoodAdelicPlace N w) : adelicPlaceGL2Hom w q = 1 := by
    apply adelicPlaceGL2Hom_finitePlaceProduct_ne
    intro i he
    have hi := (Finset.mem_filter.mp i.property).2
    apply hi
    change IsGoodAdelicPlace N (v i)
    exact he ▸ hw
  have hReal (w : HeightOneSpectrum ℤ) : adelicPlaceGL2Hom w aReal = 1 := by
    rw [adelicPlaceGL2Hom_apply]
    change GeneralLinearGroup.map (finiteAdelePlace w)
      (rationalAdelicGL2RealFiniteEquiv (rationalAdelicGL2RealFiniteEquiv.symm _)).2 = 1
    rw [rationalAdelicGL2RealFiniteEquiv.apply_symm_apply, map_one]
  have hb : q * aReal ∈ adelicRestrictedBaseGroup N := by
    apply (adelicRestrictedBaseGroup_mem_iff N _).mpr
    intro w hw
    rw [map_mul, hq w hw, hReal w, one_mul]
  refine ⟨⟨q * aReal, hb⟩, ⟨(rationalAdelicGL2RealFiniteEquiv r).2, hr⟩, ?_⟩
  have hrdecomp : aReal * rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv r).2 = r := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [map_mul, rationalAdelicFiniteGL2Embedding_coordinates]
    change rationalAdelicGL2RealFiniteEquiv (rationalAdelicGL2RealFiniteEquiv.symm _) * _ = _
    rw [rationalAdelicGL2RealFiniteEquiv.apply_symm_apply]
    exact Prod.ext (mul_one _) (one_mul _)
  change (q * aReal) * rationalAdelicFiniteGL2Embedding (rationalAdelicGL2RealFiniteEquiv r).2 = a
  rw [mul_assoc, hrdecomp]
  exact adelicFinitePlaceProduct_mul_removal v hv a

end
end Dubon2026
