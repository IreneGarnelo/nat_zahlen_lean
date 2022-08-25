-- Level name : Potenz einer Potenz

import natnum.pow -- hide
import game.Potenzen.level_6 -- hide
namespace natnum -- hide

/-
Es geht weiter mit noch einem Potenzgesetzt.
-/

/- Lemma
$(a^b)^c = a^{b * c}$
-/
lemma pow_pow (a b c : natnum) : (a ^ b) ^ c = a ^ (b * c) :=
begin
induction c with d hd,
{rw mul_zero,
repeat {rw pow_zero},},
{rw mul_succ,
rw pow_add,
rw pow_succ,
rw hd,},
end

end natnum -- hide