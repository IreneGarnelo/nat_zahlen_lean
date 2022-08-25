-- Level name : Kommutativität der linken Faktoren

import natnum.mul -- hide
import game.Multiplikation_Extra.level_3 -- hide
namespace natnum -- hide

/-
TODO


-/

/- Lemma
a * 1 = a
-/
lemma mul_left_comm (a b c : natnum) : a * (b * c) = b * (a * c) :=
begin
rw ← mul_assoz b a c,
rw mul_komm b a,
rw mul_assoz a b c,
end

end natnum -- hide