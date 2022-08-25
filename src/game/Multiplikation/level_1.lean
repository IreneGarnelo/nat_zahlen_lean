-- Level name : Die Multiplikation

import natnum.mul -- hide
import game.Addition_Extra.level_1 --hide
namespace natnum -- hide

/-
Man kann auch die Multiplikation zweier natürlichen Zahlen rekursiv anhand der 
Peano-Axiome definieren.
- Für $a \in \mathbb{N}$ sei $a*0=0$
- Für $a,d \in \mathbb{N}$ sei $a* $`succ`$(d) = a*d+a$

Nach dem Prinzip der Induktion ist dann die Multiplikation für alle Paare von
natürlichen Zahlen definiert.

Die beiden Aussagen, die die Multiplikation definieren, sind in LEAN implementiert und 
haben jeweils den Namen `mul_zero` und `mul_succ`.
-/

/- Hint : Klicke hier um die Definition der Multiplikation der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def mul : natnum → natnum → natnum` <br>
`| a zero := zero` <br>
`| a (succ d) := mul a d + a` <br>

Den beiden definierenden Eigenschaften wird ein Namen gegeben: <br>
`lemma mul_zero (a : natnum) : a * zero = zero := rfl` <br>
`lemma mul_succ (a d : natnum) : a * (succ d) = a * d + a := rfl`
-/

/-
In diesem Level werden wir zeigen, dass auch die Multiplikation mit $0$ von links $0$ ergibt.
Wir haben die Kommutativität der Multiplikation noch nicht gezeigt.
-/

/- Lemma
$0*a=0$
-/
lemma zero_mul (a: natnum) : zero*a = zero :=
begin
induction a with d hd,
{rw mul_zero,},
{rw mul_succ,
rw hd,
rw add_zero,},
end

end natnum -- hide