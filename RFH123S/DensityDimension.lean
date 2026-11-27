import Mathlib

open Real
namespace RFH123S

/-- Choose the integer Behrend dimension with the required rounding
bounds and logarithmic loss. -/
lemma exists_density_dimension (u v : ℝ)
    (hu : 4 ≤ u) (hv : 1 ≤ v) (hvu : v ≤ u) (hlog : log u ≤ v) :
    ∃ q : ℕ, 0 < q ∧ sqrt (u / v) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ 2 * sqrt (u / v) ∧ log (q : ℝ) ≤ v := by
  let z := sqrt (u / v)
  have hvp : 0 < v := by linarith
  have hz : 1 ≤ z := by
    calc
      1 = sqrt 1 := by simp
      _ ≤ z := Real.sqrt_le_sqrt ((le_div_iff₀ hvp).2 (by simpa using hvu))
  let q := ⌈z⌉₊
  have hqlo : z ≤ (q : ℝ) := Nat.le_ceil z
  have hqhi : (q : ℝ) ≤ 2 * z := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ z by linarith)
    change (q : ℝ) < z + 1 at h
    linarith
  have hqp : 0 < q := by
    exact_mod_cast (show 0 < (q : ℝ) by linarith)
  have hzupper : z ≤ sqrt u :=
    Real.sqrt_le_sqrt ((div_le_iff₀ hvp).2 (by nlinarith))
  have hs : 2 * sqrt u ≤ u := by
    have hsq := Real.sq_sqrt (show 0 ≤ u by linarith)
    have h2 : 2 ≤ sqrt u := by
      calc
        2 = sqrt 4 := by norm_num
        _ ≤ sqrt u := Real.sqrt_le_sqrt hu
    nlinarith [mul_nonneg (show 0 ≤ sqrt u by positivity) (show 0 ≤ sqrt u - 2 by linarith)]
  have hqu : (q : ℝ) ≤ u := by linarith
  exact ⟨q, hqp, hqlo, hqhi, (Real.log_le_log (by exact_mod_cast hqp) hqu).trans hlog⟩

#print axioms exists_density_dimension
end RFH123S
