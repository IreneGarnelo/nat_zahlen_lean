-- Level name : Distributivgesetz - von liks

import natnum.mul -- hide
import game.Multiplikation_Extra.level_2 -- hide
namespace natnum -- hide

/-
Wir haben das Distributivgesetzt gezeigt, wir könnten es aber manchmal auch von
links gebrauchen. Um uns in diesen Fällen Schreibarbeit zu sparen, zeigen wir hier,
dass es auch von links gilt. Auch hier kannst du deinen Beweis über Induktion führen
oder Kommutativität ausnutzen. Kannst du beide Wege coden?
-/

/- Lemma
$(a + b) * c = a * c + b * c$
-/
lemma add_mul (a b c: natnum) : (a + b) * c = a * c + b * c :=
begin
induction c with d hd,
{repeat {rw mul_zero},
rw add_zero,},

{rw mul_succ,
rw hd,
repeat {rw mul_succ},
rw add_assoz (a*d) (b*d) (a + b),
rw ← add_assoz (b*d) a b,
rw add_komm (b*d) a,
rw add_assoz a (b*d) b,
rw ← add_assoz (a*d) a (b * d + b),},
end

end natnum -- hide