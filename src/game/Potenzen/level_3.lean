-- Level name : Hoch $1$ nehmen

import natnum.pow -- hide
import game.Potenzen.level_2 -- hide
namespace natnum -- hide

/-



-/

/- Lemma
$a^1 = a$
-/
lemma pow_one (a : natnum) : (a) ^ (one) = a :=
begin
rw one_eq_succ_zero,
rw pow_succ,
rw pow_zero,
rw one_mul,
end

end natnum -- hide