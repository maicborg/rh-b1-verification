import Mathlib

open Real
namespace RFH123S

/-- The density logarithm is within the intended 40 sqrt(u v) budget.
The hypotheses are scalar bounds, not statements about existence of Data. -/
lemma density_budget (u v q H W A L : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (hqlo : sqrt (u / v) ≤ q) (hqhi : q ≤ 2 * sqrt (u / v))
    (hA : log A ≤ 12 * u / q) (hL : log (2 * L) ≤ 2 * v)
    (hH : log (H / W) ≤ 3 * v) (hn : log q ≤ v) :
    log (H / W) + log q + 2 * log A + q * log (2 * L) ≤
      40 * sqrt (u * v) := by
  let z := sqrt (u / v)
  let t := sqrt (u * v)
  have hz : 0 < z := Real.sqrt_pos.2 (by positivity)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hz2 : z ^ 2 = u / v := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = u * v := Real.sq_sqrt (by positivity)
  have hzv : z * v = t := by
    have hsq : (z * v)^2 = t^2 := by
      rw [mul_pow, hz2, ht2]
      field_simp
      <;> ring
    nlinarith [mul_pos hz hv]
  have hut : u = z * t := by
    rw [← hzv, ← mul_assoc, ← pow_two, hz2]
    field_simp
  have hvt : v ≤ t := by
    have hsq : v^2 ≤ t^2 := by
      rw [ht2]
      nlinarith [mul_le_mul_of_nonneg_right hvu hv.le]
    nlinarith
  have hq : 0 < q := hz.trans_le hqlo
  have hA' : log A ≤ 12 * t := hA.trans (by
    apply (div_le_iff₀ hq).2
    rw [hut]
    nlinarith [mul_le_mul_of_nonneg_right hqlo ht.le])
  have hL' : q * log (2 * L) ≤ 4 * t := calc
    _ ≤ q * (2 * v) := mul_le_mul_of_nonneg_left hL hq.le
    _ ≤ (2 * z) * (2 * v) := mul_le_mul_of_nonneg_right hqhi (by positivity)
    _ = _ := by linarith [hzv]
  change log (H / W) + log q + 2 * log A + q * log (2 * L) ≤ 40 * t
  linarith

end RFH123S
