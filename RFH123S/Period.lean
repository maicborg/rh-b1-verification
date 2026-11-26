import Mathlib

/-! RFH 123 semplificata: the exact logarithmic cancellation. -/
namespace RFH123S

open Real

lemma log_period (n d c : ℝ) (hn : 0 < n) (hd : 0 < d) (hc : 0 < c) :
    log (2 * π / (n * sqrt d / c)) =
      log (2 * π) - log n - log d / 2 + log c := by
  have hs : 0 < sqrt d := Real.sqrt_pos.2 hd
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hc.ne', Real.log_mul hn.ne' hs.ne',
    Real.log_sqrt hd.le]
  ring

lemma jet_excess (a fac ell W g Q : ℝ) (ha : 0 < a) (hf : 0 < fac)
    (hW : 0 < W) (hg : 0 < g) (hQ : 0 < Q) :
    (log fac - a * log (exp ell * Q / g)) -
      a * (log a - 1 - ell - log W) =
    a * log (W * g / Q) + (log fac - a * log a + a) := by
  rw [Real.log_div (by positivity) hg.ne', Real.log_mul (Real.exp_pos _).ne' hQ.ne',
    Real.log_exp, Real.log_div (by positivity) hQ.ne', Real.log_mul hW.ne' hg.ne']
  ring

lemma level_cancellation (H R h m a K w L eta S : ℝ)
    (hlevel : L = m * (w + K) - K - 15 / 2 * h + eta) :
    H - m * R + a * m * (w + K) + m * S - a * L =
      H - m * R + a * (K + 15 / 2 * h - eta) + m * S := by
  rw [hlevel]
  ring

end RFH123S
