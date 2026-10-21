import Dubon2026.SourcePrimeTwistedProduct

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> original next-series nonmembership -> extending a field embedding to a
non-distinguished twisted root. The literal prime product splits and has
distinct roots. These facts let the non-linear minimal polynomial supply
one of the required twisted roots without assuming an embedding extension.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem prime_twisted_product_splits (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] (u : Kˣ) :
    (relationAtSeed P (TS K (e * p) (u ^ p))).Splits := by
  rw [prime_product_twisted_expanded p ζ P hP e u]
  exact (Polynomial.Splits.X_sub_C _).mul
    (Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _)

theorem prime_twisted_product_roots (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] (u : Kˣ) :
    (relationAtSeed P (TS K (e * p) (u ^ p))).roots =
      TS K (e * (p * p)) (u ^ (p * p)) ::ₘ
        (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) := by
  classical
  rw [prime_product_twisted_expanded p ζ P hP e u]
  have hne : (X - C (TS K (e * (p * p)) (u ^ (p * p)))) *
      ∏ b ∈ Finset.range p, (X - C (TS K e (u * ζ ^ b))) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val]
  have hm : (Multiset.range p).map (fun b => X - C (TS K e (u * ζ ^ b))) =
      ((Multiset.range p).map (fun b => TS K e (u * ζ ^ b))).map (fun x => X - C x) := by
    rw [Multiset.map_map]
    rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem prime_twisted_product_roots_nodup (p : ℕ) [hp : Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (e : ℕ) [NeZero e] (u : Kˣ) :
    (relationAtSeed P (TS K (e * p) (u ^ p))).roots.Nodup := by
  rw [prime_twisted_product_roots p ζ P hP e u]
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · rintro h
    obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp h
    have he := (TS_injective hb).1
    have he0 := Nat.pos_of_ne_zero (NeZero.ne e)
    have hpp : 1 = p * p := Nat.eq_of_mul_eq_mul_left he0 (by simpa only [mul_one] using he)
    have hp4 := Nat.mul_le_mul hp.out.two_le hp.out.two_le
    omega
  · refine (Multiset.nodup_range p).map_on fun b hb b' hb' hbb' => ?_
    rw [Multiset.mem_range] at hb hb'
    have hu := mul_left_cancel (TS_injective hbb').2
    exact (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_inj hb hb' hu

end
end Dubon2026.SourceFunctionField
