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

meta def start_game : tactic unit :=
do { `(game' %%d) ← tactic.target,
    dunfold_target [``game']
} <|> tactic.fail "not a game"

-- if two towers are the same then we win
meta def finish_game : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
     tactic.exact `(@can_get_to'.can_get_to_self' %%t₁)
} <|> tactic.fail "we haven't won yet"

-- automatically starts the game if not started
meta def move_disk' (s d : tower) : tactic unit :=
do { start_game,
     move_disk s d
} <|> move_disk s d

meta def get_start_position : tactic position :=
do { `(game' %%d) ← tactic.target,
    d' ← (eval_expr ℕ) d,
    return ⟨list.range' 1 d', [], []⟩
}

meta def get_position : tactic position :=
do { `(can_get_to' { A := %%A, B := %%B, C := %%C} %%t₂) ← tactic.target,
      [A', B', C'] ← list.mmap (eval_expr (list ℕ)) [A, B, C],
      return ⟨A', B', C'⟩
} <|> get_start_position

end hanoitactics