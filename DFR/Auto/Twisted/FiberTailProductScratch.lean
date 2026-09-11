import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped BigOperators Convolution ENNReal

noncomputable section

/-- The three-factor Hölder association used by a one-bad-coordinate term:
one interval tail and the two remaining coordinate maximal factors. -/
theorem scratch_eLpNorm_threefold_product_le
    {p0 p1 p2 r12 r : ENNReal}
    [ENNReal.HolderTriple p1 p2 r12] [ENNReal.HolderTriple p0 r12 r]
    (g0 g1 g2 : E3 → ℝ)
    (hg0 : AEStronglyMeasurable g0 volume)
    (hg1 : AEStronglyMeasurable g1 volume)
    (hg2 : AEStronglyMeasurable g2 volume) :
    eLpNorm (fun x ↦ g0 x * g1 x * g2 x) r volume ≤
      eLpNorm g0 p0 volume * eLpNorm g1 p1 volume * eLpNorm g2 p2 volume := by
  have h12 : eLpNorm (fun x ↦ g1 x * g2 x) r12 volume ≤
      eLpNorm g1 p1 volume * eLpNorm g2 p2 volume := by
    change eLpNorm (g1 * g2) r12 volume ≤ _
    simpa only [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm (μ := volume) hg2 hg1)
  have hm12 : AEStronglyMeasurable (fun x ↦ g1 x * g2 x) volume := hg1.mul hg2
  have h012 : eLpNorm (fun x ↦ g0 x * (g1 x * g2 x)) r volume ≤
      eLpNorm g0 p0 volume * eLpNorm (fun x ↦ g1 x * g2 x) r12 volume := by
    change eLpNorm (g0 * fun x ↦ g1 x * g2 x) r volume ≤ _
    simpa only [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm (μ := volume) hm12 hg0)
  calc
    eLpNorm (fun x ↦ g0 x * g1 x * g2 x) r volume =
        eLpNorm (fun x ↦ g0 x * (g1 x * g2 x)) r volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      ring
    _ ≤ eLpNorm g0 p0 volume * eLpNorm (fun x ↦ g1 x * g2 x) r12 volume := h012
    _ ≤ eLpNorm g0 p0 volume *
        (eLpNorm g1 p1 volume * eLpNorm g2 p2 volume) := by
      gcongr
    _ = eLpNorm g0 p0 volume * eLpNorm g1 p1 volume * eLpNorm g2 p2 volume := by
      ring

/-- The corresponding finite-norm membership statement, with no hidden
association convention in the product. -/
theorem scratch_memLp_threefold_product
    {p0 p1 p2 r12 r : ENNReal}
    [ENNReal.HolderTriple p1 p2 r12] [ENNReal.HolderTriple p0 r12 r]
    (g0 g1 g2 : E3 → ℝ)
    (hg0 : MemLp g0 p0 volume)
    (hg1 : MemLp g1 p1 volume)
    (hg2 : MemLp g2 p2 volume) :
    MemLp (fun x ↦ g0 x * g1 x * g2 x) r volume := by
  have h12 : MemLp (fun x ↦ g1 x * g2 x) r12 volume := hg2.mul' hg1
  have h012 : MemLp (fun x ↦ g0 x * (g1 x * g2 x)) r volume := h12.mul' hg0
  simpa only [mul_assoc] using h012

end
end Twisted
end Auto
