-- Level name : Die Addition

import natnum.add -- hide
import game.Peano.level_1 --hide
namespace natnum -- hide

/-
Man kann die Addition zweier natürlichen Zahlen rekursiv anhand der Peano-Axiome 
definieren.
- Für $a \in \mathbb{N}$ sei $a+0=a$
- Für $a,d \in \mathbb{N}$ sei $a+$`succ`$(d) = $`succ`$(a+d)$

Nach dem Prinzip der Induktion ist dann die Addition für alle Paare von natürlichen
Zahlen definiert.

Die beiden Aussagen, die die Addition definieren, sind in LEAN implementiert und 
haben jeweils den Namen `add_zero` und `add_succ`. Auch diese Aussagen können mit
dem Befehl `rw` verwendet werden. `rw add_zero,` wandelt die Aussage `b+zero` in `b`
um.
-/

/- Hint : Klicke hier um die Definition der Addition der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def add : natnum → natnum → natnum` <br>
`| m 0 := m` <br>
`| m (succ n) := succ (add m n)` <br>

Den beiden definierenden Eigenschaften wird ein Namen gegeben: <br>
`lemma add_zero (m : natnum) : m + zero = m := rfl` <br>
`lemma add_succ (m n : natnum) : m + succ n = succ (m + n) := rfl`
-/

/-
In diesem Level werden wir zeigen, dass Addition mit dem Nachfolger von $0$ (den
wir noch nicht Formal als $1$ eingeführt haben), gleich dem Nachfolger der Zahl ist.
-/

/- Lemma
$a+$`succ`$(0)=$`succ`$(a)$
-/
lemma add_succ_zero (a : natnum) : a + succ(zero) = succ(a) :=
begin
  rw add_succ,
  rw add_zero,
end

end natnum -- hide