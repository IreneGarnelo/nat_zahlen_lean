-- Level name : Multiplikation mit 1

import natnum.mul -- hide
import game.Multiplikation.level_5 -- hide
namespace natnum -- hide

/-

-/

/- Lemma
$a * 1 = a$
-/
lemma mul_one (a: natnum) : a*one = a :=
begin
rw one_eq_succ_zero,
rw mul_succ,
rw mul_zero,
rw zero_add,
end

end natnum -- hide