import hanoi
import hanoiinteractive

open hanoi hanoi.tower
open hanoitactics

namespace testGames

/-
  md a b = move disk from tower a to tower b
  finish_game = check if you're done!
-/

example : game' 1 :=
begin [hanoi_tactic]
  md a b,
  md b c,
  finish_game,
end

example : game' 3 :=
begin [hanoi_tactic]
  md a c,
  md a b,
  md c b,
  md a c,
  md b a,
  md b c,
  md a c,
  finish_game,
end

end testGames