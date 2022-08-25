-- Level name : Addition mit dem Nachfolger - von links

import natnum.add -- hide
import game.Addition.level_4 --hide
namespace natnum -- hide

/-
Genauso wie wir aus $a+0=a$ nicht direkt $0+a=a$ folgern könnten, können wir
aus $b + $`succ`$(a) =$ `succ`$(b+a)$ nicht `succ`$(a)+b =$ `succ`$(a+b)$
folgern. Wir haben nämlich noch nicht bewiesen, dass die Addition kommutativ ist.
-/

/- Lemma
`succ`$(a)+b = $`succ`$(a+b)$
-/
lemma succ_add (a b: natnum) : succ(a) + b = succ(a + b) :=
begin
  induction b with d hd,
  {rw add_zero,
  rw add_zero,},
  {rw add_succ,
  rw hd,
  rw add_succ,},
end

end natnum -- hide