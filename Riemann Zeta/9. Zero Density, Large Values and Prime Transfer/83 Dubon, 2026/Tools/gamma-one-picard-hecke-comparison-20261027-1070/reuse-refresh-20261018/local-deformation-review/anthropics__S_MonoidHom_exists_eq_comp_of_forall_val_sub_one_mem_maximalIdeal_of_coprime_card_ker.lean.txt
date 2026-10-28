import Mathlib
import Definitions.Def_Deformations_TameDescent
import Theorems.Thm_TaylorWiles_tameDescentChar_comp_eq
import Theorems.Thm_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
import P2M.Util
namespace P2MW.S_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker

set_option autoImplicit false

universe u v w

theorem solution {G : Type u} {Δ : Type v} {R : Type w} [Group G] [Finite G] [Group Δ] [CommRing R] [IsLocalRing R]
    (π : G →* Δ) (hπ : Function.Surjective π) {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hcop : (Nat.card π.ker).Coprime p)
    (ξ : G →* Rˣ) (hξ : ∀ g, (ξ g : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ χ : Δ →* Rˣ, ∀ g, ξ g = χ (π g) := by

  have hn : IsUnit ((Nat.card π.ker : ℕ) : R) := by
    by_contra hnu
    have hmem : ((Nat.card π.ker : ℕ) : R) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime ((Nat.card π.ker : ℕ) : ℤ) (p : ℤ))
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := congrArg (Int.cast : ℤ → R) huv
      push_cast at this
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp)
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h1

  have hker : ∀ g ∈ π.ker, ξ g = 1 := by
    intro g hg
    have hpow : g ^ Nat.card π.ker = 1 := by
      have h := pow_card_eq_one' (G := π.ker) (x := ⟨g, hg⟩)
      exact congrArg Subtype.val h
    exact MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one ξ g (hξ g) hn hpow
  refine ⟨TaylorWiles.tameDescentChar π hπ ξ hker, fun g => ?_⟩
  rw [TaylorWiles.tameDescentChar_comp_eq]
