import hanoi
import hanoitactics hanoiwidget

open hanoi hanoi.tower
open hanoitactics

namespace testGames

example : game' 1 :=
begin
  -- start_game,
  md a b,
  md b c,
  finish_game,
end

example : game' 3 :=
begin
  md a c,
  md a b,
  md c a,
end

end testGames