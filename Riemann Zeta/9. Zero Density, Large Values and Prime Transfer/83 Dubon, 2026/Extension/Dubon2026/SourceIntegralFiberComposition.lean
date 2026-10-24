import Dubon2026.SourceIntegralModularCompositionResultant

/-! Specialize the integral composition resultant to the actual product of
fiber polynomials. Native resultant multiplicativity on linear factors
avoids splitting fields and a second roots-multiset argument. The prime
quotient product supplies the input factorization for the DUB-17/18
all-level cyclic-root bijection. Adapted from the Resultant section of
S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j,
anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial
noncomputable section

/-- A proved factorization of the first modular fiber gives the exact product containing the product-level fiber. -/
theorem modularPolynomial_fiber_dvd_product
    {K : Type*} [Field K] (a b : ℕ) [NeZero a] [NeZero b] (x : K)
    {ι : Type*} [Fintype ι] (z : ι → K)
    (hz : relationAtSeed (modularPolynomial a) x = ∏ i, (X - C (z i))) :
    relationAtSeed (modularPolynomial (a * b)) x ∣
      ∏ i, relationAtSeed (modularPolynomial b) (z i) := by
  classical
  let B := Polynomial ℤ[X]
  set f : Polynomial B := (modularPolynomial a).map (Polynomial.C : ℤ[X] →+* B) with hf
  set g : Polynomial B := (modularPolynomial b).eval₂
    (Polynomial.mapRingHom (Int.castRingHom B)) (Polynomial.C Polynomial.X) with hg
  have hdvd : modularPolynomial (a * b) ∣ f.resultant g :=
    modularPolynomial_dvd_compositionResultant a b
  set φ : B →+* Polynomial K := Polynomial.mapRingHom
    (eval₂RingHom (Int.castRingHom K) x) with hφ
  have hev (w : K) : (g.map φ).eval (C w) = relationAtSeed (modularPolynomial b) w := by
    rw [hg, ← coe_mapRingHom, Polynomial.hom_eval₂, ← coe_evalRingHom, Polynomial.hom_eval₂]
    have e1 : (evalRingHom (C w)).comp ((mapRingHom φ).comp (mapRingHom (Int.castRingHom B))) =
        C.comp (eval₂RingHom (Int.castRingHom K) w) :=
      Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [hφ])
    have e2 : (evalRingHom (C w)) ((mapRingHom φ) (C (X : B))) = X := by
      rw [coe_mapRingHom, map_C, coe_evalRingHom, eval_C, hφ, coe_mapRingHom, map_X]
    rw [e1, e2]
    rfl
  have hf' : f.map φ = (relationAtSeed (modularPolynomial a) x).map C := by
    rw [hf, relationAtSeed, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hφ, coe_mapRingHom, map_C]
  have hdegree : (f.map φ).natDegree = f.natDegree :=
    ((modularPolynomial_monic a).map (Polynomial.C : ℤ[X] →+* B)).natDegree_map φ
  have hfactor : f.map φ = ∏ i, (X - C (C (z i) : Polynomial K)) := by
    rw [hf', hz, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
  have hvalue : φ (f.resultant g) = ∏ i, relationAtSeed (modularPolynomial b) (z i) := by
    rw [← resultant_map_map, ← hdegree, hfactor,
      resultant_prod_left _ _ _ _ (by simp) natDegree_map_le]
    apply Finset.prod_congr rfl
    intro i _
    rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ natDegree_map_le, hev]
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨φ q, ?_⟩
  rw [← hvalue, hq, map_mul]
  rfl

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
