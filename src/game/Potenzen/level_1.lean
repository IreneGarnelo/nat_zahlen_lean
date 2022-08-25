-- Level name : Die Potenzierung

import natnum.pow -- hide
import game.Multiplikation_Extra.level_4 -- hide
namespace natnum -- hide

/-
Man kann auch die Potenzierung einer natürlichen Zahlen mit einer anderen 
rekursiv anhand der Peano-Axiome definieren.
- Für $m \in \mathbb{N}$ sei $m^0=1$
- Für $m,n \in \mathbb{N}$ sei $m^{(succ(n))} = m^n*m$

Nach dem Prinzip der Induktion ist dann die Potenzierung für alle Paare von
natürlichen Zahlen definiert.

Die beiden Aussagen, die die Multiplikation definieren, sind in LEAN implementiert und 
haben jeweils den Namen `pow_zero` und `pow_succ`.
-/

/- Hint : Klicke hier um die Definition der Multiplikation der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def pow : natnum → natnum → natnum` <br>
`| m zero := one` <br>
`| m (succ n) := pow m n * m` <br>

Den beiden definierenden Eigenschaften wird ein Namen gegeben: <br>
`lemma pow_zero (m : natnum) : m ^ (zero : natnum) = one := rfl` <br>
`lemma pow_succ (m n : natnum) : m ^ (succ n) = m ^ n * m := rfl`
-/

/-
In diesem Level werden wir zeigen, dass nach Definition gilt, dass $0^0=1$.
-/

/- Lemma
$0^0=1$
-/
lemma zero_pow_zero : (zero) ^ (zero) = one :=
begin
rw pow_zero,
end

end natnum -- hide