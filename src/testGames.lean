import hanoi
import hanoitactics hanoiwidget

open hanoi hanoi.tower
open hanoitactics

namespace testGames

example : game' 1 :=
begin
  start_game,
  move_disk' a b,
  move_disk' b c,
  finish_game,
end

example : game' 3 :=
begin
  move_disk' a c,
end

end testGames