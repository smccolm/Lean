import Dubon2026.AdelicPlaceComplementCriterion
import Mathlib.GroupTheory.NoncommPiCoprod

/-! # Faithful finite products of original disjoint local groups inside genuine adelic GL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The actual finite product of original local group embeddings, using their proved disjoint-place commutation. -/
def adelicFinitePlaceProduct :
    (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) →* RationalAdelicGL2 :=
  MonoidHom.noncommPiCoprod
    (fun i => rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom (v i)))
    (fun i j hij g h =>
      (finiteAdelicLocalGL2_commute (v i) (v j) (hv.ne hij) g h).map rationalAdelicFiniteGL2Embedding)

/-- A single genuine coordinate in the finite product is exactly its original one-place adelic embedding. -/
theorem adelicFinitePlaceProduct_mulSingle [DecidableEq I] (i : I)
    (g : GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
    adelicFinitePlaceProduct v hv (Pi.mulSingle i g) =
      rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) g) :=
  MonoidHom.noncommPiCoprod_mulSingle
    (fun j => rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom (v j))) i g

/-- Evaluation of the actual finite product at any one of its genuine places recovers exactly that original local matrix. -/
theorem adelicPlaceGL2Hom_finitePlaceProduct (i : I)
    (g : ∀ j, GeneralLinearGroup (Fin 2) ((v j).adicCompletion ℚ)) :
    adelicPlaceGL2Hom (v i) (adelicFinitePlaceProduct v hv g) = g i := by
  classical
  have he : (adelicPlaceGL2Hom (v i)).comp (adelicFinitePlaceProduct v hv) =
      Pi.evalMonoidHom (fun j => GeneralLinearGroup (Fin 2) ((v j).adicCompletion ℚ)) i := by
    apply MonoidHom.pi_ext
    intro j a
    change adelicPlaceGL2Hom (v i) (adelicFinitePlaceProduct v hv (Pi.mulSingle j a)) =
      Pi.mulSingle (M := fun t => GeneralLinearGroup (Fin 2) ((v t).adicCompletion ℚ)) j a i
    rw [adelicFinitePlaceProduct_mulSingle]
    by_cases h : j = i
    · subst j
      rw [Pi.mulSingle_eq_same]
      exact adelicPlaceGL2Hom_local_same (v i) a
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm h)]
      exact adelicPlaceGL2Hom_local_ne (v i) (v j) (hv.ne (Ne.symm h)) a
  exact DFunLike.congr_fun he g

/-- No genuine tuple of distinct-place original local matrices disappears under the finite adelic product embedding. -/
theorem adelicFinitePlaceProduct_injective : Function.Injective (adelicFinitePlaceProduct v hv) := by
  intro g h he
  funext i
  have hi := congrArg (adelicPlaceGL2Hom (v i)) he
  rw [adelicPlaceGL2Hom_finitePlaceProduct, adelicPlaceGL2Hom_finitePlaceProduct] at hi
  exact hi

/-- Every original place outside a finite family sees identity in its genuine finite local product. -/
theorem adelicPlaceGL2Hom_finitePlaceProduct_ne (w : HeightOneSpectrum ℤ)
    (hw : ∀ i, w ≠ v i) (g : ∀ j, GeneralLinearGroup (Fin 2) ((v j).adicCompletion ℚ)) :
    adelicPlaceGL2Hom w (adelicFinitePlaceProduct v hv g) = 1 := by
  classical
  have he : (adelicPlaceGL2Hom w).comp (adelicFinitePlaceProduct v hv) = 1 := by
    apply MonoidHom.pi_ext
    intro i a
    change adelicPlaceGL2Hom w (adelicFinitePlaceProduct v hv (Pi.mulSingle i a)) = 1
    rw [adelicFinitePlaceProduct_mulSingle]
    exact adelicPlaceGL2Hom_local_ne w (v i) (hw i) a
  exact DFunLike.congr_fun he g

/-- Remove exactly the selected genuine finite coordinates from an original full adelic matrix. -/
def adelicFinitePlaceRemoval (a : RationalAdelicGL2) : RationalAdelicGL2 :=
  (adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a))⁻¹ * a

/-- Every selected original local coordinate of the actual finite-family remainder is identity. -/
theorem adelicFinitePlaceRemoval_same (i : I) (a : RationalAdelicGL2) :
    adelicPlaceGL2Hom (v i) (adelicFinitePlaceRemoval v hv a) = 1 := by
  rw [adelicFinitePlaceRemoval, map_mul, map_inv, adelicPlaceGL2Hom_finitePlaceProduct, inv_mul_cancel]

/-- Every unselected original local coordinate survives the actual finite-family removal unchanged. -/
theorem adelicFinitePlaceRemoval_ne (w : HeightOneSpectrum ℤ) (hw : ∀ i, w ≠ v i)
    (a : RationalAdelicGL2) :
    adelicPlaceGL2Hom w (adelicFinitePlaceRemoval v hv a) = adelicPlaceGL2Hom w a := by
  rw [adelicFinitePlaceRemoval, map_mul, map_inv, adelicPlaceGL2Hom_finitePlaceProduct_ne v hv w hw,
    inv_one, one_mul]

/-- The original full adelic matrix factors exactly as its selected actual local coordinates times its genuine remaining-coordinate matrix. -/
theorem adelicFinitePlaceProduct_mul_removal (a : RationalAdelicGL2) :
    adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a) * adelicFinitePlaceRemoval v hv a = a := by
  rw [adelicFinitePlaceRemoval, mul_inv_cancel_left]

end
end Dubon2026
