import Dubon2026.AdelicFiniteReferenceCoordinates

/-! # Exact original adelic products of adjacent finite coordinate blocks -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {n m : ℕ} (v : Fin (n + m) → HeightOneSpectrum ℤ)

/-- A genuine left block of distinct original places retains its exact distinctness. -/
theorem adelicPlaceFamily_left_injective (hv : Function.Injective v) : Function.Injective (fun i : Fin n => v (Fin.castAdd m i)) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (n + m) => i.val) (hv h))

/-- A genuine right block of distinct original places retains its exact distinctness. -/
theorem adelicPlaceFamily_right_injective (hv : Function.Injective v) : Function.Injective (fun i : Fin m => v (Fin.natAdd n i)) := by
  intro a b h
  exact Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin (n + m) => i.val) (hv h)))

/-- Joining the actual local tuples is exactly multiplication of the original adjacent finite adelic products. -/
theorem adelicFinitePlaceProduct_addCases (hv : Function.Injective v)
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv (Fin.addCases g h) =
      adelicFinitePlaceProduct (fun i : Fin n => v (Fin.castAdd m i)) (adelicPlaceFamily_left_injective v hv) g *
      adelicFinitePlaceProduct (fun j : Fin m => v (Fin.natAdd n j)) (adelicPlaceFamily_right_injective v hv) h := by
  rw [adelicFinitePlaceProduct_eq_ofFn, adelicFinitePlaceProduct_eq_ofFn, adelicFinitePlaceProduct_eq_ofFn]
  have he : (fun i => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (Fin.addCases g h i))) =
      Fin.append
        (fun i : Fin n => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v (Fin.castAdd m i)) (g i)))
        (fun j : Fin m => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v (Fin.natAdd n j)) (h j))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left, Fin.append_left]
    · simp only [Fin.addCases_right, Fin.append_right]
  rw [he, List.ofFn_fin_append, List.prod_append]

end
end Dubon2026
