import Dubon2026.SourcePrimeConjugateBaseChange

/-! DUB-17/18 -> numerical modular genus -> all-level exact degree
-> original next-series nonmembership. The root-spreading argument needs
the same prime relation at primitive roots taken from a larger root system.
Native nth-root multisets identify all primitive-root enumerations, so the
already proved product can be used at any selected primitive p-th root.
No new coefficient-field embedding package or symmetry premise is needed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K]

theorem primitive_root_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot (ζ : K) N) {p : ℕ} (hpN : p ∣ N) :
    IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd : N / p ≠ 0 := by
    intro h0
    have h := Nat.div_mul_cancel hpN
    rw [h0, zero_mul] at h
    exact hN h.symm
  have h := hζ.pow_of_dvd hd (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

theorem primitive_root_powers_multiset_eq {p : ℕ} (ζ η : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (hη : IsPrimitiveRoot (η : K) p) :
    (Multiset.range p).map (ζ ^ ·) = (Multiset.range p).map (η ^ ·) := by
  apply Multiset.map_injective Units.val_injective
  simp only [Multiset.map_map, Function.comp_def, Units.val_pow_eq_pow_val]
  have h1 := hζ.nthRoots_eq (one_pow p : (1 : K) ^ p = 1)
  have h2 := hη.nthRoots_eq (one_pow p : (1 : K) ^ p = 1)
  simpa only [mul_one] using h1.symm.trans h2

theorem prime_product_eq_of_primitive [Algebra ℚ K]
    (p : ℕ) [Fact p.Prime] (ζ η : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (hη : IsPrimitiveRoot (η : K) p) :
    PhiGen.phiProd p (PhiGen.conj p ζ) = PhiGen.phiProd p (PhiGen.conj p η) := by
  rw [phiProd_conj_eq, phiProd_conj_eq]
  congr 1
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod,
    Finset.range_val]
  have h := congrArg (fun l : Multiset Kˣ =>
    (l.map (fun u => X - C (TS K 1 u))).prod) (primitive_root_powers_multiset_eq ζ η hζ hη)
  simpa only [Multiset.map_map, Function.comp_def] using h

theorem exists_prime_product_at_root [Algebra ℚ K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] (η : Kˣ) (hη : IsPrimitiveRoot (η : K) p) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
        PhiGen.phiProd p (PhiGen.conj p η) := by
  obtain ⟨ζ, P, hζ, hm, hd, he⟩ := exists_prime_product_algClosed p K
  exact ⟨P, hm, hd, he.trans (prime_product_eq_of_primitive p ζ η hζ hη)⟩

end
end Dubon2026.SourceFunctionField
