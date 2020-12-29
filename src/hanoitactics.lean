import hanoi

open hanoi hanoi.tower
open tactic

namespace hanoitactics

-- moves curr tower to a new position if valid, otherwise fails
meta def move_disk (s d : tower) : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
    tactic.apply `(@fmove' %%t₁ %%t₂ %%(reflect s) %%(reflect d)),
    tactic.applyc ``and.intro,
    `[simp only [valid_move, list.range', false_or, eq_self_iff_true, not_true, ne.def, not_false_iff, and_self, false_and]],
    `[dsimp [move]]
} <|> tactic.fail "failed to move disk :("

meta def startgame : tactic unit :=
do { `(game' %%d) ← tactic.target,
    dunfold_target [``game']
} <|> tactic.fail "not a game"

-- if two towers are the same then we win
meta def endgame : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
     tactic.exact `(@can_get_to'.can_get_to_self' %%t₁)
} <|> tactic.fail "we haven't won yet"

-- not sure how to get the current position...
meta def get_position : position := position.mk [1,2,3] [] []

end hanoitactics