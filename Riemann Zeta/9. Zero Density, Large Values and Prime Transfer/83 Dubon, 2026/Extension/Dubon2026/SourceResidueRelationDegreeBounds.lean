import Dubon2026.SourcePrimeResidueRelations

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue-field degree. The prime-power tower needs degree bounds from the
actual specialized monic relation, including removal of a known base-field
root. This is the precise polynomial step shared by the forward and reverse
expansion towers; it assumes neither irreducibility nor their exact degrees. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem aeval_relationAtSeed_of_eval_zero
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (P : Polynomial (Polynomial ℤ)) {s x : LaurentSeries K} (hs : s ∈ F)
    (hr : (relationAtSeed P s).eval x = 0) :
    Polynomial.aeval x (relationAtSeed P (⟨s, hs⟩ : F)) = 0 := by
  rw [← Polynomial.eval_map_algebraMap, relationAtSeed_map]
  exact hr

theorem integral_of_relationAtSeed_root
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (P : Polynomial (Polynomial ℤ)) (hm : P.Monic)
    {s x : LaurentSeries K} (hs : s ∈ F) (hr : (relationAtSeed P s).eval x = 0) :
    IsIntegral F x :=
  ⟨relationAtSeed P (⟨s, hs⟩ : F), hm.map _,
    aeval_relationAtSeed_of_eval_zero F P hs hr⟩

theorem minpoly_degree_le_relationAtSeed
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (P : Polynomial (Polynomial ℤ)) (hm : P.Monic)
    {s x : LaurentSeries K} (hs : s ∈ F) (hr : (relationAtSeed P s).eval x = 0) :
    (minpoly F x).natDegree ≤ P.natDegree := by
  have h := Polynomial.natDegree_le_of_dvd
    (minpoly.dvd F x (aeval_relationAtSeed_of_eval_zero F P hs hr)) (hm.map _).ne_zero
  exact h.trans_eq (hm.natDegree_map _)

theorem minpoly_degree_lt_relation_of_known_root
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (P : Polynomial (Polynomial ℤ)) (hm : P.Monic)
    {s x r : LaurentSeries K} (hs : s ∈ F) (hr : r ∈ F)
    (hrroot : (relationAtSeed P s).eval r = 0)
    (hxroot : (relationAtSeed P s).eval x = 0) (hne : x ≠ r) :
    (minpoly F x).natDegree + 1 ≤ P.natDegree := by
  let Q := relationAtSeed P (⟨s, hs⟩ : F)
  let rF : F := ⟨r, hr⟩
  have hQm : Q.Monic := hm.map _
  have hQr : Q.IsRoot rF := by
    apply (algebraMap F (LaurentSeries K)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map]
    exact hrroot
  let R := Q /ₘ (X - C rF)
  have hfact : (X - C rF) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQr
  have hRm : R.Monic := Polynomial.Monic.of_mul_monic_left
    (Polynomial.monic_X_sub_C rF) (hfact ▸ hQm)
  have hdeg : R.natDegree + 1 = P.natDegree := by
    have hQd : Q.natDegree = P.natDegree := hm.natDegree_map _
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C rF) hRm,
      Polynomial.natDegree_X_sub_C, hQd] at h
    omega
  have hRx : Polynomial.aeval x R = 0 := by
    have h : Polynomial.aeval x ((X - C rF) * R) = 0 :=
      hfact ▸ aeval_relationAtSeed_of_eval_zero F P hs hxroot
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (fun he => hne (sub_eq_zero.mp he))
  have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd F x hRx) hRm.ne_zero
  omega

end
end Dubon2026.SourceFunctionField
