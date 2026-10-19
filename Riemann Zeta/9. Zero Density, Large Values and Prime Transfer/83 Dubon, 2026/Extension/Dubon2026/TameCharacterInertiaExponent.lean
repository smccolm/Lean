import Dubon2026.DiagonalCharacterFactorization
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! The actual tame character equations bound the whole inertia image,
not just a chosen generator. This is the exponent condition needed to
descend the auxiliary deformation characters to the finite tame quotient
in the local-ring computation for Dubon Theorem 2.6. -/

namespace Dubon2026
open Matrix

/-- The constructed diagonal character family has the same cyclic inertia
image as the original representation, through its injective diagonal map. -/
theorem diagonal_characters_cyclic_inertia
    {G A ι : Type} [Group G] [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Subgroup G) (t : G) (ρ : G →* GeneralLinearGroup ι A)
    (W : GeneralLinearGroup ι A) (χ : G →* (ι → A)ˣ)
    (hχ : ∀ g, diagonal (χ g).val = (MulAut.conj W (ρ g)).val)
    (hI : I.map ρ = Subgroup.zpowers (ρ t)) :
    I.map χ = Subgroup.zpowers (χ t) := by
  let D := Units.map (diagonalRingHom ι A).toMonoidHom
  have hD : Function.Injective D := by
    intro x y h
    apply Units.ext
    funext i
    have hi := congrArg (fun M : GeneralLinearGroup ι A => M.val i i) h
    simpa [D] using hi
  have he : D.comp χ = (MulAut.conj W).toMonoidHom.comp ρ := by
    apply MonoidHom.ext
    intro g
    exact Units.ext (hχ g)
  apply Subgroup.map_injective hD
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hI, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 1
  exact (DFunLike.congr_fun he t).symm

/-- Every actual inertia value satisfies the tame exponent equation once
the constructed cyclic generator does. This supplies the exponent input; the finite tame presentation and
surjectivity of the fixed cyclotomic quotient separately identify its kernel. -/
theorem cyclic_tame_characters_inertia_pow_eq_one
    {G A ι : Type} [Group G] [CommRing A]
    (I : Subgroup G) (t : G) (χ : G →* (ι → A)ˣ)
    (hI : I.map χ = Subgroup.zpowers (χ t))
    (p : ℕ) (hp : 1 ≤ p) (ht : ∀ i, ((χ t).val i)^p = (χ t).val i) :
    ∀ g ∈ I, χ g ^ (p - 1) = 1 := by
  have ht' : χ t ^ p = χ t := by
    apply Units.ext
    funext i
    exact ht i
  have hpow : χ t ^ (p - 1) = 1 := by
    apply mul_right_cancel (b := χ t)
    rw [← pow_succ, Nat.sub_add_cancel hp, one_mul]
    exact ht'
  intro g hg
  have hm : χ g ∈ Subgroup.zpowers (χ t) := hI ▸ Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  obtain ⟨n, hn⟩ := hm
  rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, hpow, one_zpow]

end Dubon2026
