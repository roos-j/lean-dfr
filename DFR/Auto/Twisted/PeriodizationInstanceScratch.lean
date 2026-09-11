import Auto.Twisted.Twisted
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace Auto.Twisted

abbrev Circle8InstanceScratch := AddCircle (8 : ℝ)

local instance : Fact (0 < (8 : ℝ)) := ⟨by norm_num⟩

#synth LocallyCompactSpace Circle8InstanceScratch
#synth LocallyCompactSpace (Circle8InstanceScratch × Circle8InstanceScratch)
#synth T2Space (Circle8InstanceScratch × Circle8InstanceScratch)

end Auto.Twisted
