import Mathlib

/-!
# RH-B1: confronto delle soglie di non annullamento

Direzione concettuale del programma RH: Maicol Borghetti (@maicborg).
Formalizzazione assistita: GPT-6.
Questa è un'identità razionale elementare; non è un nuovo teorema RH.
-/

namespace RH_B1

/-- Il semipiano Re(s) > 399/400 è contenuto in Re(s) > 7/8. -/
theorem seven_eighths_lt_zero_free_box_boundary :
    (7 / 8 : ℝ) < 1 - 1 / 400 := by
  norm_num

end RH_B1
