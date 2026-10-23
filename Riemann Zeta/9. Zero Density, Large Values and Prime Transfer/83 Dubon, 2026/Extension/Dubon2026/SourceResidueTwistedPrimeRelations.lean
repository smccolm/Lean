import Dubon2026.SourceResiduePrimePolynomialRoots
import Dubon2026.SourcePrimePowerCoefficientAction

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree and generation -> prime relation intersections. Transport the
already proved actual root list by literal twist and expansion. Native split
polynomial root transport preserves multiplicity and distinctness. Twisted
seeds are needed for lower-level conjugates in the coprime nonmembership
argument; untwisted seeds give the two-prime generation step. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem relationAtSeed_twist_expansion
    {K : Type*} [Field K] (P : Polynomial (Polynomial ℤ))
    (p e : ℕ) [NeZero p] [NeZero e] (u : Kˣ) :
    (relationAtSeed P (qExpand K p (jqModC K))).map ((qExpand K e).comp (qTwist u)) =
      relationAtSeed P (TS K (e * p) (u ^ p)) := by
  rw [relationAtSeed_map]
  congr 1
  change qExpand K e (qTwist u (qExpand K p (jqModC K))) = _
  rw [qTwist_qExpand, qExpand_qExpand, zpow_natCast]
  rfl

theorem exists_residue_prime_twisted_relations
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      ∀ (e : ℕ) [NeZero e] (u : Kˣ),
        (relationAtSeed P (TS K (e * p) (u ^ p))).roots =
          TS K (e * (p * p)) (u ^ (p * p)) ::ₘ
            (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) ∧
        (relationAtSeed P (TS K (e * p) (u ^ p))).Splits ∧
        (relationAtSeed P (TS K (e * p) (u ^ p))).roots.Nodup := by
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations_coeff p
  have hf := (hrel K p).1
  have hr : (relationAtSeed P (qExpand K p (jqModC K))).eval (jqModC K) = 0 := by
    simpa only [one_mul, qExpand_one_apply] using (hrel K 1).2
  have hs := residue_prime_polynomial_splits K p ζ hζ P hm hd hf hr
  have hroots := residue_prime_polynomial_roots K p ζ hζ P hm hd hf hr
  have hnd : (relationAtSeed P (qExpand K p (jqModC K))).roots.Nodup := by
    rw [hroots]
    exact roots_phiProd_conj_nodup p ζ hζ
  refine ⟨P, hm, hd, fun e _ u => ?_⟩
  let H := (qExpand K e).comp (qTwist u)
  have hmap := relationAtSeed_twist_expansion P p e u
  have hmroots := hs.roots_map H
  rw [hmap] at hmroots
  refine ⟨?_, ?_, ?_⟩
  · rw [hmroots, hroots, Multiset.map_cons, Multiset.map_map]
    simp only [Function.comp_def, H, RingHom.comp_apply, qTwist_TS, qExpand_TS,
      zpow_natCast, pow_one, mul_one]
  · rw [← hmap]
    exact hs.map H
  · rw [hmroots]
    exact Multiset.Nodup.map H.injective hnd

theorem residue_prime_root_iff_of_root_list
    {K : Type*} [Field K] (p e : ℕ) [NeZero p] [NeZero e]
    (ζ u : Kˣ) (P : Polynomial (Polynomial ℤ)) (hm : P.Monic)
    (hr : (relationAtSeed P (TS K (e * p) (u ^ p))).roots =
      TS K (e * (p * p)) (u ^ (p * p)) ::ₘ
        (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)))
    (y : LaurentSeries K) :
    (relationAtSeed P (TS K (e * p) (u ^ p))).eval y = 0 ↔
      y = TS K (e * (p * p)) (u ^ (p * p)) ∨
        ∃ b < p, y = TS K e (u * ζ ^ b) := by
  have hm' : (relationAtSeed P (TS K (e * p) (u ^ p))).Monic := hm.map _
  rw [← Polynomial.IsRoot.def, ← Polynomial.mem_roots hm'.ne_zero, hr]
  simp only [Multiset.mem_cons, Multiset.mem_map, Multiset.mem_range, eq_comm]

end
end Dubon2026.SourceFunctionField
