-- Level name : Multiplikation mit dem Nachfolger - von links

import natnum.mul -- hide
import game.Multiplikation.level_1 --hide
namespace natnum -- hide

/-
Manchmal möchtest du einen Befehl mehrmal hintereinander Ausführen. Wenn du dir
zum Beispiel den Induktionsanfang dieses Levels anschaust, musst du zeigen, dass
`a.succ * zero = a * zero + zero`, du könntest damit anfangen, überall wo mit
$0$ multipliziert wird `rw mul_zero,` anzuwenden. Anstatt den Befehl zweimal
auszuschreiben, kannst du `{repeat {rw mul_zero,},` anwenden. Dann wird LEAN den
Befehl `rw mul_zero,` so oft ausführen, bis es keine Instanz der Form `a+zero` gibt.
-/

/- Lemma
`succ`$(a) * b = a * b + b$
-/
lemma succ_mul (a b : natnum) : succ(a) * b = a * b + b :=
begin
induction b with d hd,
{repeat {rw mul_zero,},
rw add_zero,},
{rw mul_succ,
rw mul_succ,
rw hd,
rw add_succ,
rw add_succ,
rw add_right_komm,
},
end

end natnum -- hide