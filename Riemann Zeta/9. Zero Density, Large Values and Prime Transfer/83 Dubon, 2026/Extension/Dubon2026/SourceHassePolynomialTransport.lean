import Dubon2026.SourceHasseCoefficientExpansion
import Dubon2026.SourceLaurentRootTwist
import Dubon2026.SourceLaurentTwistMonomials
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> Hasse composition divisibility.
The actual prime orbit factorization and discriminant norm supply the two
identities needed to descend a Laurent identity to a polynomial divisibility.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_closure. Existing j transcendence and coefficient
formulas replace repeated principal-part proofs. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

variable (K : Type*) [Field K]

theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c :=
  algebraMap_laurent_eq_single K c

theorem aeval_jqModC_injective :
    Function.Injective (Polynomial.aeval (jqModC K) : Polynomial K → LaurentSeries K) :=
  transcendental_iff_injective.mp (transcendental_jqModC K)

theorem qExpand_C (N : ℕ) [NeZero N] (c : K) :
    qExpand K N (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, qExpand_single, mul_zero]

theorem qTwist_C (u : Kˣ) (c : K) : qTwist u (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]

theorem qTwist_aeval (u : Kˣ) (x : LaurentSeries K) (P : Polynomial K) :
    qTwist u (Polynomial.aeval x P) = Polynomial.aeval (qTwist u x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun c => by rw [RingHom.comp_apply, algebraMap_eq_C, qTwist_C]

theorem qExpand_aeval (N : ℕ) [NeZero N] (x : LaurentSeries K) (P : Polynomial K) :
    qExpand K N (Polynomial.aeval x P) = Polynomial.aeval (qExpand K N x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun c => by rw [RingHom.comp_apply, algebraMap_eq_C, qExpand_C]

theorem prod_map_sub_comm (s : Multiset K) (x : LaurentSeries K) :
    (s.map fun α => x - algebraMap K (LaurentSeries K) α).prod =
      (-1) ^ Multiset.card s * (s.map fun α => algebraMap K (LaurentSeries K) α - x).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih,
      Multiset.card_cons, pow_succ]
    ring

variable [IsAlgClosed K]

theorem aeval_eq_prod_roots (G : Polynomial K) (x : LaurentSeries K) :
    Polynomial.aeval x G =
      algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots *
        (G.roots.map fun α => algebraMap K (LaurentSeries K) α - x).prod := by
  conv_lhs => rw [(IsAlgClosed.splits G).eq_prod_roots]
  rw [map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map, mul_assoc,
    ← prod_map_sub_comm]
  congr 2
  exact Multiset.map_congr rfl fun α _ => by
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]


end
end Dubon2026.SourceFunctionField
