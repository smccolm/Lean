import Dubon2026.AdelicFiniteTupleCoefficients
import Mathlib.Data.List.FinRange

/-! # Original finite adelic coordinates after appending an identity reference factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original genuine finite adelic product is its literal coordinate-ordered product. -/
theorem adelicFinitePlaceProduct_eq_ofFn {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ)
    (hv : Function.Injective v)
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv g =
      (List.ofFn (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (g i)))).prod := by
  have h := adelicFinitePlaceProduct_eq_list v hv g (List.ofFn id)
    (List.nodup_ofFn.mpr Function.injective_id) (by ext i; simp)
  simpa only [List.map_ofFn, Function.comp_id] using h

/-- Appending an identity at a genuine new place preserves exactly the original finite adelic matrix. -/
theorem adelicFinitePlaceProduct_snoc_one {n : ℕ} (v : Fin (n + 1) → HeightOneSpectrum ℤ)
    (hv : Function.Injective v)
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv (Fin.snoc g 1) =
      adelicFinitePlaceProduct (fun i : Fin n => v i.castSucc) (hv.comp (Fin.castSucc_injective n)) g := by
  rw [adelicFinitePlaceProduct_eq_ofFn, adelicFinitePlaceProduct_eq_ofFn, List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, finiteAdelicLocalGL2_one, map_one, mul_one]

/-- The actual full complement of the extended list is a subgroup of the original shorter complement. -/
theorem adelicFiniteFamilyAwayGroup_init_le {n : ℕ} (v : Fin (n + 1) → HeightOneSpectrum ℤ) :
    adelicFiniteFamilyAwayGroup v ≤ adelicFiniteFamilyAwayGroup (fun i : Fin n => v i.castSucc) := by
  intro a ha
  funext i
  exact congrFun ha i.castSucc

end
end Dubon2026
