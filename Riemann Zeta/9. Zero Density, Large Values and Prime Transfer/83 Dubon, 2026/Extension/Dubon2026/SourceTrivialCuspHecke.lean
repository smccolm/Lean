import Dubon2026.SourceCuspHeckeExceptional
import Dubon2026.SourceTrivialCoefficientHecke
import Dubon2026.SourceCorrespondenceOne

/-! The full original Hecke action on cusp evaluation is multiplication by ell+1.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> its actual Eisenstein
eigensystem. The original fixed coset contributes ell and the original
translation cycle contributes one; native coboundary comparison proves
independence of the chosen original representatives.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (Q ell : ℕ) [NeZero ell]
    (hell : ell.Prime) (hellQ : Nat.Coprime ell Q)

private local instance cuspHeckeFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

private theorem chosen_translation_sum
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    (∑ i : Option (ZMod ell),
      z (sourceHeckeConjugation hell (sourceCuspHeckeTransition Q ell hell hellQ i))) =
        ((ell : F) + 1) * z (heckeUpperTranslation Q 1) := by
  let φ := (cocycles₁IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom z
  have hφ (g : Gamma0 Q) : φ (Additive.ofMul g) = z g := rfl
  have hn : z (sourceHeckeConjugation hell
      (sourceCuspHeckeTransition Q ell hell hellQ none)) =
        (ell : F) * z (heckeUpperTranslation Q 1) := by
    rw [sourceCuspHeckeConjugation_none]
    rw [← hφ, ofMul_mul, ofMul_mul, ofMul_pow, ofMul_inv,
      map_add, map_add, map_nsmul, map_neg]
    rw [add_comm (φ (Additive.ofMul (heckeLowerTranslation Q 1))), add_neg_cancel_right]
    exact nsmul_eq_mul ell (z (heckeUpperTranslation Q 1) : F)
  have hs (j : ZMod ell) : z (sourceHeckeConjugation hell
      (sourceCuspHeckeTransition Q ell hell hellQ (some j))) =
        if j = 0 then z (heckeUpperTranslation Q 1) else 0 := by
    rw [sourceCuspHeckeConjugation_some]
    split_ifs
    · rfl
    · exact cocycles₁_map_one z
  rw [Fintype.sum_option, hn, Finset.sum_congr rfl (fun j _ => hs j)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

include hellQ in
/-- The actual full original Hecke cocycle evaluated on the unit translation
is exactly ell+1 times the original evaluation. -/
theorem sourceTrivialCoefficientHecke_translation
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    sourcePrimeHeckeCocycles hell (Rep.trivial F (Gamma0 Q) F) LinearMap.id
        (sourceTrivialCoefficient_intertwine F Q hell) z (heckeUpperTranslation Q 1) =
      ((ell : F) + 1) * z (heckeUpperTranslation Q 1) := by
  obtain ⟨v, hv⟩ := sourceCorrespondenceOne_chosen_sub (Rep.trivial F (Gamma0 Q) F)
    (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell) LinearMap.id
    (sourceTrivialCoefficient_intertwine F Q hell)
    (sourceCuspHeckeRepresentative Q ell hell hellQ)
    (sourceCuspHeckeRepresentative_coset Q ell hell hellQ) z
  have h := congrFun hv (heckeUpperTranslation Q 1)
  change v - v =
    (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      z (sourceHeckeConjugation hell
        (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
          (sourceCuspHeckeRepresentative Q ell hell hellQ)
          (sourceCuspHeckeRepresentative_coset Q ell hell hellQ)
          (heckeUpperTranslation Q 1) q))) -
      sourcePrimeHeckeCocycles hell (Rep.trivial F (Gamma0 Q) F) LinearMap.id
        (sourceTrivialCoefficient_intertwine F Q hell) z (heckeUpperTranslation Q 1) at h
  rw [sub_self, ← (heckeUpperCosetEquiv hell hellQ).sum_comp] at h
  change 0 = (∑ i : Option (ZMod ell),
      z (sourceHeckeConjugation hell (sourceCuspHeckeTransition Q ell hell hellQ i))) - _ at h
  rw [chosen_translation_sum F Q ell hell hellQ z] at h
  exact (sub_eq_zero.mp h.symm).symm

end
end Dubon2026
