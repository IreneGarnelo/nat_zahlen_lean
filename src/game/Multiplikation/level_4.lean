-- Level name : Das Distributivgesetz

import natnum.mul -- hide
import game.Multiplikation.level_3 -- hide
namespace natnum -- hide

/-
Das Distributivgesetzt gibt uns an, wie wir mit Ausdrücken umgehen können in denen
Addition und Multiplikation vorkommen.
-/

/- Lemma
$c * (a + b) = c * a + c * b$
-/
lemma distr (a b c : natnum) : c * (a + b) = c * a + c * b :=
begin
induction b with d hd,
{rw add_zero,
rw mul_zero,
rw add_zero,},
{rw add_succ,
rw mul_succ,
rw hd,
rw mul_succ,
rw add_assoz,},
end

end natnum -- hide