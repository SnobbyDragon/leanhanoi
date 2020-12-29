import hanoiwidget

meta def hanoi_tactic := tactic

namespace hanoi_tactic
  open tactic
  local attribute [reducible] hanoi_tactic
  meta instance : monad hanoi_tactic := infer_instance

  meta def step {α : Type} (m : hanoi_tactic α) : hanoi_tactic unit :=
  tactic.step m

  meta def istep {α} (a b c d : ℕ) (t : hanoi_tactic α) : hanoi_tactic unit :=
  tactic.istep a b c d t

  meta def save_info (p : pos) : hanoi_tactic unit := hanoi_save_info p

  meta instance : interactive.executor hanoi_tactic :=
  { config_type := unit, 
    execute_with := λ n tac, tac
  }

  /- Now that these magic methods are implemented, you can write
    begin [hanoi_tactic]
    ...
    end
   -/

end hanoi_tactic
