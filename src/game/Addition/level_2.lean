-- Level name : Die natürliche Zahl 1

import natnum.add -- hide
import game.Addition.level_1 --hide
namespace natnum -- hide

/-
Aus praktischen Gründen möchten wir nun dem Nachfolger von $0$ einen Namen
geben. Diese Zahl nennen wir $1$. Die Aussage `one = succ(zero)` heißt in
LEAN `one_eq_succ_zero`.
-/

/- Hint : Klicke hier um die Definition der Nummer $1$ in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
`def one : natnum := succ zero` <br>
`theorem one_eq_succ_zero : one = succ zero := rfl`
-/

/- 
Nun können wir zeigen, dass der Nachfolger von $a$ gleich $a+1$ ist. 
-/

/- Lemma
`succ`$(a) = a + 1$
-/
lemma succ_eq_add_one (a : natnum) : succ(a) = a + one :=
begin
rw one_eq_succ_zero,
rw add_succ,
rw add_zero,
end

end natnum -- hide