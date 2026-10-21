import Dubon2026.SourcePrimePowerCoefficientAction
import Dubon2026.SourceAllDivisorMonicRelations

/-! DUB-17/18 -> numerical modular genus -> exact composite j-map degree
-> prime-power root cycle. Applying the literal q-expansion homomorphism
to the proved prime conjugate product gives exactly the roots needed at
the next prime-power seed. This uses only untwisted seeds; the more general
twisted-slot infrastructure is deferred until a required consumer needs it.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem coeffEmb_qExpand_jq_eq_TS (e : ℕ) [NeZero e] :
    coeffEmb K (qExpand ℚ e jq) = TS K e 1 := by
  rw [TS, qTwist_one_apply, ← coeffEmb_jq K]
  exact coeffMap_qExpand (algebraMap ℚ K) e jq

theorem prime_product_expanded (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] :
    relationAtSeed P (qExpand K (e * p) (coeffEmb K jq)) =
      (X - C (TS K (e * (p * p)) 1)) *
        ∏ b ∈ Finset.range p, (X - C (TS K e (ζ ^ b))) := by
  have hc : (qExpand K e).comp
      (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (e * p) (coeffEmb K jq)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rw [show coeffEmb K (qExpand ℚ p jq) = qExpand K p (coeffEmb K jq) from
      coeffMap_qExpand (algebraMap ℚ K) p jq, qExpand_qExpand]
  have h := congrArg (Polynomial.map (qExpand K e)) hP
  rw [Polynomial.map_map, hc] at h
  change relationAtSeed P _ = _ at h
  rw [h, phiProd_conj_eq, Polynomial.map_mul, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    qExpand_TS, Nat.mul_one]

theorem prime_product_expanded_roots (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] :
    (relationAtSeed P (qExpand K (e * p) (coeffEmb K jq))).roots =
      TS K (e * (p * p)) 1 ::ₘ
        (Multiset.range p).map (fun b => TS K e (ζ ^ b)) := by
  classical
  rw [prime_product_expanded p ζ P hP e]
  have hne : (X - C (TS K (e * (p * p)) 1)) *
      ∏ b ∈ Finset.range p, (X - C (TS K e (ζ ^ b))) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val]
  have hm : (Multiset.range p).map (fun b => X - C (TS K e (ζ ^ b))) =
      ((Multiset.range p).map (fun b => TS K e (ζ ^ b))).map (fun x => X - C x) := by
    rw [Multiset.map_map]
    rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

omit [Algebra ℚ K] in
theorem prime_expanded_root_list_nodup (p : ℕ) [hp : Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (e : ℕ) [NeZero e] :
    (TS K (e * (p * p)) 1 ::ₘ
      (Multiset.range p).map (fun b => TS K e (ζ ^ b))).Nodup := by
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · rintro h
    obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp h
    have he := (TS_injective hb).1
    have he0 := Nat.pos_of_ne_zero (NeZero.ne e)
    have hp2 := hp.out.two_le
    have hpp : 1 = p * p := Nat.eq_of_mul_eq_mul_left he0 (by simpa only [mul_one] using he)
    have hp4 := Nat.mul_le_mul hp2 hp2
    omega
  · refine (Multiset.nodup_range p).map_on fun b hb b' hb' hbb' => ?_
    rw [Multiset.mem_range] at hb hb'
    have hu := (TS_injective hbb').2
    exact (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_inj hb hb' hu

end
end Dubon2026.SourceFunctionField
