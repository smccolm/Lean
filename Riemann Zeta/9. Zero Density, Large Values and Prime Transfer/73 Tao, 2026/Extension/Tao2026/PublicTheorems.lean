import Tao2026.Theorem17Complete
import Tao2026.Theorem25Complete
import Tao2026.Theorem19And110Complete

/-!
# The four unconditional public theorem contracts

The individual declarations prove precisely the unchanged conclusion
definitions in `PublicStatements`. This combined theorem has no mathematical
hypotheses and provides one audited consumer of all four proof chains.
-/

namespace Tao2026

theorem taoMainTheorems_unconditional :
    TaoTheorem17Conclusion ∧ TaoTheorem18Conclusion ∧
      TaoTheorem19Conclusion ∧ TaoTheorem110Conclusion :=
  ⟨taoTheorem17_unconditional, taoTheorem18_unconditional,
    taoTheorem19_unconditional, taoTheorem110_unconditional⟩

end Tao2026
