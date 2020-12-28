import hanoi
import hanoitactics

open hanoi hanoi.tower
open hanoitactics

namespace testGames

example : game' 1 :=
begin
  startgame,
  move_disk a c,
  endgame,
end

end testGames