import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, W.veluGy (P i).1 (P i).2 = 0) ∧
        ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.solution
