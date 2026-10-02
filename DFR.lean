import LeanSpherical.Theorems
-- CDR (Christ-Durcik-Roos, arXiv:2008.10140): the modules containing Theorems 1-4,
-- `Auto.CDR.thm_singint`, `Auto.CDR.thm_anisotp`, `Auto.CDR.thm_maxfct`, `Auto.CDR.thm_patterns`.
import DFR.Auto.CDR.Sec2PreliminaryReductions1Decomposition
import DFR.Auto.CDR.Sec4SmoothCase
import DFR.Auto.CDR.Sec2PreliminaryReductions
import DFR.Auto.CDR.Sec5Applications

/-!
# DFR

This project depends on the formalization in `lean-spherical`.
-/

namespace DFR

-- Dependency smoke test; replace this with the project's formalization.
#check Spherical.eLpNorm_sphericalMaximal_le

end DFR
