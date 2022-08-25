-- Level name : $1$ hoch etwas

import natnum.pow -- hide
import game.Potenzen.level_3 -- hide
namespace natnum -- hide

/-



-/

/- Lemma
$1^a=1$
-/
lemma one_pow (a : natnum) : (one) ^ (a) = one :=
begin
induction a with d hd,
{rw pow_zero,},
{rw pow_succ,
rw mul_one,
rw hd,},
end

end natnum -- hide