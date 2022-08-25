-- Level name : mul_one

import natnum.mul -- hide
import game.Multiplikation_Extra.level_1 -- hide
namespace natnum -- hide

/-
Du hast zwei optionen für dieses Level. Du kannst mit Induktion starten,
oder du könntest ausnutzen, dass wir gezeigt haben, dass die Multiplikation
Kommutativ ist! 
-/

/- Lemma
a * 1 = a
-/
lemma one_mul (a: natnum) : one*a = a :=
begin
induction a with d hd,
{rw mul_zero,},
{rw mul_succ,
rw hd,
rw succ_eq_add_one,},
end

end natnum -- hide