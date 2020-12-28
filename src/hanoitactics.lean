import hanoi

open hanoi hanoi.tower
open tactic
open interactive (parse) interactive.types expr
open lean.parser (ident) (tk)

namespace hanoitactics

-- moves curr tower to a new position if valid, otherwise fails
meta def move_disk (s d : tower) : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
    --tactic.trace $ (to_string t₁) ++ "\n" ++ (to_string t₂),
    --tactic.infer_type t₁ >>= tactic.trace,
    tactic.apply `(@fmove' %%t₁ %%t₂ %%(reflect s) %%(reflect d)),
    tactic.applyc ``and.intro,
    -- need to check if valid, then simplify move
    -- tactic.target >>= tactic.trace,
    dunfold_target [``valid_move],
    `[simp only [list.range', false_or, eq_self_iff_true, not_true, ne.def, not_false_iff, and_self, false_and]],
    dunfold_target [``move],
    `[dsimp]} <|> tactic.trace "failed to move disk :("

meta def startgame : tactic unit :=
do { `(game' %%d) ← tactic.target,
    dunfold_target [``game']
   } <|> tactic.trace "not a game"

-- if two towers are the same then we win
meta def endgame : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
     tactic.exact `(@can_get_to'.can_get_to_self' %%t₁)
   }

end hanoitactics