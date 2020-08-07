import hanoi

open hanoi

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

meta def fmove (s d : tower) : tactic unit := sorry
meta def bmove (s d : tower) : tactic unit := sorry

end hanoitactics

/- messing around to learn tactics -/
namespace tacticplayground

meta def hello : tactic unit := tactic.trace "cat"

#check hello
#eval hello

end tacticplayground
