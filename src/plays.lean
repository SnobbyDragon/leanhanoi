import hanoi

open hanoi
open hanoi.tower

namespace hanoitactics
/- PLANS ON HOW TO MAKE GAME PLAYABLE
   maybe make some tactics:
   1) fmove (forward move)
     takes in towers t₁ t₂, move the start position (disk on t₁ to t₂) to a different position p
     ∙ creates subgoal that the move (start tower) t₁ t₂ is valid
     ∙ changes goal to can_get_to p (end tower)
   2) bmove (backward move)
     takes in towers t₁ t₂, move disk on t₂ to t₁ on end position; change the end position to new position p
     ∙ creates subgoal that the move p t₁ t₂ is valid
     ∙ changes goal to can_get_to (start tower) p
   
   instead of having subgoals that the move is valid, what if it auto checks? (errors if not valid)
   THUS we need something to check for us
-/

-- THIS ALL ISN'T FINISHED BC IDK HOW TO WRITE TACTICS

meta def parsepos (e : expr) : tactic (position) :=
do tp ← tactic.infer_type e,
   guard (tp = `(position)),
   

-- checks if a move is valid
meta def checkmove (t : position) (s d : tower) : tactic unit :=
do { sorry
   }
<|> tactic.fail "invalid move!"

-- moves curr tower to a new position if valid, otherwise fails
meta def fmove (s d : tower) : tactic unit :=
do { `(can_get_to' %%t₁ %%t₂) ← tactic.target,
     tactic.trace $ "goal is can_get_to",
     tactic.trace $ (to_string t₁) ++ "\n" ++ (to_string t₂),
     tactic.infer_type t₁ >>= tactic.trace,
     tactic.apply `(fmove' %%s %%d)
   }
   <|> tactic.trace "goal is not can_get_to"
  
-- moves goal tower backward to a new position if valid, otherwise fails
meta def bmove (s d : tower) : tactic unit :=
do { goal ← tactic.target,
     sorry
   }

-- I don't like how ugly it is right now
-- hopefully can have (h : current position) and ⊢ goal position
-- so I suppose fmove will replace h; bmove will change ⊢
meta def startgame : tactic unit :=
do { `(game' %%d) ← tactic.target,
     tactic.trace $ "game with " ++ (to_string d) ++ " disk(s)" }
   <|> tactic.trace "not a game"

-- test on simple case
example : game' 1 :=
begin
  startgame,
  unfold game',
  fmove a b,
end

#reduce game' 1
#eval to_string 1

end hanoitactics

/- messing around to learn tactics -/
namespace tacticplayground

meta def hello : tactic unit := tactic.trace "cat"

#check hello
#eval hello



end tacticplayground
