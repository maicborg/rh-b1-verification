/-
RFH V1: final seal, to be compiled only after the actual producers
and the conditional bridge have been certified on the same pinned environment.
No axiom, sorry, terminal upstream theorem, or changed observable.
-/
import RFHProducerInputs
import RFHTopGReduced
import RFHVWinReduced
import Lean.Util.FoldConsts

namespace BorghettiRH

theorem rfh_final : RiemannHypothesis :=
  rfh_of_producer_inputs producer_topG producer_vwin_zeta

end BorghettiRH

#print axioms BorghettiRH.producer_topG
#print axioms BorghettiRH.producer_vwin_zeta
#print axioms BorghettiRH.rfh_final

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let checks : List (Name × List Name × Bool) :=
    [(``BorghettiRH.producer_topG,
      [``BorghettiRH.topG_of_literature], true),
     (``BorghettiRH.producer_vwin_zeta,
      [``BorghettiRH.producer_vwin], true),
     (``BorghettiRH.rfh_final,
      [``BorghettiRH.rfh_of_producer_inputs,
       ``BorghettiRH.producer_topG,
       ``BorghettiRH.producer_vwin_zeta,
       ``BorghettiRH.zeta_core_windows_of_topG,
       ``BorghettiRH.rfh_of_zeta_core_windows,
       ``BorghettiRH.rfh_of_matched_core_windows,
       ``BorghettiRH.normalized_point_of_matched_core,
       ``BorghettiRH.budget_of_normalized_point,
       ``BorghettiRH.due_windows_of_local_budget,
       ``BorghettiRH.rh_of_zeta_windows,
       ``UpperTheory.Top.supplyChi,
       ``QH.pairEx,
       ``BorghettiRH.b2_actual_h78,
       ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re], false)]
  for (root, required, isProducer) in checks do
    let mut seen : Std.HashSet Name := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let ns := n.toString
      if ns.startsWith "UpperTheory.FinalTheorems." ||
         ns == "UpperTheory.Top.zeroFreeAll_of_topG" ||
         ns == "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin" ||
         ns == "UpperTheory.Top.zero_free_all_of_green_v_win" ||
         ns == "UpperTheory.Top.every_character_of_green_v_win" ||
         ns == "sorryAx" ||
         (isProducer && ns == "RiemannHypothesis") then
        throwError m!"Forbidden dependency in {root}: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless ["propext", "Classical.choice", "Quot.sound"].contains ns do
            throwError m!"Nonstandard axiom in {root}: {n}"
        | _ => pure ()
        for dep in ci.type.getUsedConstants do
          if !seen.contains dep then todo := todo.push dep
        if let some v := ci.value? (allowOpaque := true) then
          for dep in v.getUsedConstants do
            if !seen.contains dep then todo := todo.push dep
    for n in required do
      unless seen.contains n do
        throwError m!"Missing actual dependency in {root}: {n}"
      logInfo m!"VERIFIED_FINAL_DEP {root} -> {n}"
    logInfo m!"AUDITED_FINAL_CLOSURE {root} {seen.size}"
