-- Level name : Kommutativität der Multiplikation

import natnum.mul -- hide
import game.Multiplikation.level_2 -- hide
namespace natnum -- hide

/- 
Die Ergebnisse aus Level 1 und 2 sind genug, um die Kommutativität zu zeigen!
-/

/- Lemma
a * b = b * a
-/
lemma mul_komm (a b : natnum) : a * b = b * a :=
begin
induction b with d hd,
{rw mul_zero,
rw zero_mul,},
{rw mul_succ,
rw hd,
rw succ_mul,},
end

end natnum -- hide

/- Hint :  Kommen dir die Schritte in diesem Beweis bekannt vor?
Wenn du dir den Beweis der Kommutativität der Addition anschaust und dort
das überall "add" mit "mul" ersetzt, hast du einen gültigen Beweis für
Die Kommutativität der Multiplikation!
-/