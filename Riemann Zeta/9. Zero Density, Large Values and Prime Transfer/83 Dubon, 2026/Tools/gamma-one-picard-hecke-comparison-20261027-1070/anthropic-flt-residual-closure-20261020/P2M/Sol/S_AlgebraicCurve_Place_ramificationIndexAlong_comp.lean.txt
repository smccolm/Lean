import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_comp

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : Place.ramificationIndexAlong (χ.comp φ) W = Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring
  have hπord : (W.restrictAlong (χ.comp φ) hχφ).ord
      ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) = 1 :=
    (W.restrictAlong (χ.comp φ) hχφ).ord_coe_irreducible hπ
  set f : F := ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) with hf
  have h1 : W.ord ((χ.comp φ) f) = (Place.ramificationIndexAlong (χ.comp φ) W : ℤ) := by
    rw [W.ord_restrictAlong (χ.comp φ) hχφ, hπord, mul_one]
  have h2 : W.ord ((χ.comp φ) f)
      = (Place.ramificationIndexAlong χ W : ℤ)
          * (Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) : ℤ) := by
    rw [AlgHom.comp_apply, W.ord_restrictAlong χ hχ, (W.restrictAlong χ hχ).ord_restrictAlong φ hφ,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ, hπord, mul_one]
  exact_mod_cast h1.symm.trans h2
