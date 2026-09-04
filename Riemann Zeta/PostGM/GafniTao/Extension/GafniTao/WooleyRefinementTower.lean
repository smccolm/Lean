import GafniTao.WooleySection7IntegratedRefinement

/-!
# Exact towers of residue-class refinements

The source passage from (7.22) to (7.23) uses two exact finite partitions:
`zeta mod p^H` parametrizes the classes above `xi mod p^a`, and refining
first to `a+H` and then to `b'` is the same as refining directly to `b'`.
This file records those statements without cardinality loss.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal lift `kappa = p^a zeta + xi` used in Section 7. -/
def wooleyResidueLift (p a H : ℕ) (xi : ZMod (p ^ a))
    (zeta : ZMod (p ^ H)) : ZMod (p ^ (a + H)) :=
  ((p ^ a) * zeta.val + xi.val : ℕ)

theorem wooleyResidueLift_eq_section7
    (p a H : ℕ) (xi : ZMod (p ^ a)) (zeta : ZMod (p ^ H)) :
    wooleyResidueLift p a H xi zeta =
      ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
        ZMod (p ^ (a + H))) := by
  norm_cast

theorem wooleyResidueLift_mem
    {p a H : ℕ} [NeZero p] (xi : ZMod (p ^ a))
    (zeta : ZMod (p ^ H)) :
    wooleyResidueLift p a H xi zeta ∈
      wooleyResidueRefinementFiber p a (a + H) (Nat.le_add_right a H) xi := by
  simp only [wooleyResidueRefinementFiber, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  unfold wooleyResidueLift
  rw [ZMod.val_natCast]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p (Nat.le_add_right a H))]
  simp [Nat.add_mod, Nat.mod_eq_of_lt xi.val_lt]

theorem wooleyResidueLift_injective
    {p a H : ℕ} [NeZero p] (xi : ZMod (p ^ a)) :
    Function.Injective (wooleyResidueLift p a H xi) := by
  intro zeta1 zeta2 heq
  have hmod :
      p ^ a * zeta1.val + xi.val ≡ p ^ a * zeta2.val + xi.val
        [MOD p ^ (a + H)] := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
  have hmul : p ^ a * zeta1.val ≡ p ^ a * zeta2.val
      [MOD p ^ (a + H)] := hmod.add_right_cancel' xi.val
  rw [pow_add] at hmul
  have hzmod : zeta1.val ≡ zeta2.val [MOD p ^ H] :=
    Nat.ModEq.mul_left_cancel' (pow_ne_zero a (NeZero.ne p)) hmul
  apply ZMod.val_injective
  exact Nat.ModEq.eq_of_lt_of_lt hzmod zeta1.val_lt zeta2.val_lt

/-- The source's `zeta` parameterization is a bijection onto the refinement
fiber above `xi`. -/
def wooleyResidueLiftEquiv
    (p a H : ℕ) [NeZero p] (xi : ZMod (p ^ a)) :
    ZMod (p ^ H) ≃
      {z // z ∈ wooleyResidueRefinementFiber p a (a + H)
        (Nat.le_add_right a H) xi} := by
  let f : ZMod (p ^ H) →
      {z // z ∈ wooleyResidueRefinementFiber p a (a + H)
        (Nat.le_add_right a H) xi} := fun zeta =>
    ⟨wooleyResidueLift p a H xi zeta, wooleyResidueLift_mem xi zeta⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact wooleyResidueLift_injective xi (congrArg Subtype.val hxy)
  have hcard : Fintype.card (ZMod (p ^ H)) =
      Fintype.card {z // z ∈ wooleyResidueRefinementFiber p a (a + H)
        (Nat.le_add_right a H) xi} := by
    rw [ZMod.card, Fintype.card_coe]
    rw [wooleyResidueRefinementFiber_card]
    simp
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

/-- Exact sum form of the `zeta` parameterization. -/
theorem wooley_sum_residueLift
    {p a H : ℕ} [NeZero p] (xi : ZMod (p ^ a))
    (F : ZMod (p ^ (a + H)) → ℝ) :
    ∑ zeta : ZMod (p ^ H), F (wooleyResidueLift p a H xi zeta) =
      ∑ kappa ∈ wooleyResidueRefinementFiber p a (a + H)
          (Nat.le_add_right a H) xi, F kappa := by
  let e := wooleyResidueLiftEquiv p a H xi
  calc
    ∑ zeta : ZMod (p ^ H), F (wooleyResidueLift p a H xi zeta) =
        ∑ z : {z // z ∈ wooleyResidueRefinementFiber p a (a + H)
            (Nat.le_add_right a H) xi}, F z.1 := by
      exact e.sum_comp (fun z => F z.1)
    _ = ∑ kappa ∈ wooleyResidueRefinementFiber p a (a + H)
          (Nat.le_add_right a H) xi, F kappa := by
      exact (Finset.sum_subtype _ (fun _ => Iff.rfl) F).symm

theorem wooley_castHom_tower
    {p a m b : ℕ} [NeZero p] (ham : a ≤ m) (hmb : m ≤ b)
    (z : ZMod (p ^ b)) :
    ZMod.castHom (pow_dvd_pow p (ham.trans hmb)) (ZMod (p ^ a)) z =
      ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a))
        (ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z) := by
  change (ZMod.castHom (pow_dvd_pow p (ham.trans hmb)) (ZMod (p ^ a))) z =
    ((ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a))).comp
      (ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)))) z
  rw [ZMod.castHom_comp]

/-- Refinement fibers compose without duplication. -/
theorem wooley_sum_refinement_tower
    {p a m b : ℕ} [NeZero p] (ham : a ≤ m) (hmb : m ≤ b)
    (xi : ZMod (p ^ a)) (F : ZMod (p ^ b) → ℝ) :
    ∑ kappa ∈ wooleyResidueRefinementFiber p a m ham xi,
        ∑ z ∈ wooleyResidueRefinementFiber p m b hmb kappa, F z =
      ∑ z ∈ wooleyResidueRefinementFiber p a b (ham.trans hmb) xi, F z := by
  classical
  unfold wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (kappa : ZMod (p ^ m)) :
      (if ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a)) kappa = xi then
          ∑ z : ZMod (p ^ b),
            if ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z = kappa
            then F z else 0
        else 0) =
        ∑ z : ZMod (p ^ b),
          if ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a)) kappa = xi then
            (if ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z = kappa
              then F z else 0)
          else 0 := by
    by_cases hk :
        ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a)) kappa = xi <;>
      simp [hk]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hza :
      ZMod.castHom (pow_dvd_pow p (ham.trans hmb)) (ZMod (p ^ a)) z = xi
  · rw [if_pos hza]
    have hcompose :
        ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a))
            (ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z) = xi := by
      rw [← wooley_castHom_tower ham hmb z]
      exact hza
    rw [Fintype.sum_eq_single
      (ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z)]
    · rw [if_pos hcompose, if_pos rfl]
    · intro kappa hkappa
      by_cases hkm :
          ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a)) kappa = xi
      · rw [if_pos hkm]
        rw [if_neg (fun h => hkappa h.symm)]
      · rw [if_neg hkm]
  · rw [if_neg hza]
    apply Finset.sum_eq_zero
    intro kappa hkappa
    by_cases hkm :
        ZMod.castHom (pow_dvd_pow p ham) (ZMod (p ^ a)) kappa = xi
    · rw [if_pos hkm]
      by_cases hzk :
          ZMod.castHom (pow_dvd_pow p hmb) (ZMod (p ^ m)) z = kappa
      · exfalso
        apply hza
        rw [wooley_castHom_tower ham hmb z, hzk]
        exact hkm
      · rw [if_neg hzk]
    · rw [if_neg hkm]

#print axioms wooleyResidueLift_mem
#print axioms wooleyResidueLift_eq_section7
#print axioms wooleyResidueLift_injective
#print axioms wooley_sum_residueLift
#print axioms wooley_sum_refinement_tower

end

end GafniTao
