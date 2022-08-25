-- Level name : Kommutativität der Addition

import natnum.add -- hide
import game.Addition.level_5 --hide
namespace natnum -- hide

/-
Endlich können wir zeigen, dass die Addition kommutativ ist!
-/

/- Lemma
a+b=b+a
-/
lemma add_komm (a b: natnum) : a + b = b + a :=
begin
  induction b with d hd,
  {rw add_zero,
  rw zero_add,},
  {rw add_succ,
  rw hd,
  rw succ_add,},
end

end natnum -- hide