-- Level name : Potenzieren als Homomorphismus $⬝∧c: (\mathbb{N}, *) → (\mathbb{N}, *)$

import natnum.pow -- hide
import game.Potenzen.level_5 -- hide
namespace natnum -- hide

/-
Wenn wir das Potenzieren als Abbildung $⬝∧c: (\mathbb{N}, *) → (\mathbb{N}, *)$
auffassen, dann ist $∧$ ebenfalls ein Homomorphismus, da $(a * b)^c = a^c * b^c$. 
Dies ein weiteres der Potenzgesetzte.

Das Potenzieren ist also sowohl im ersten wie auch im zweiten Argument ein
Homomorphismus, aber jeweils bezüglich einer anderen Verknüpfung in der Urbildmenge.
-/

/- Lemma
$(a * b)^c = a^c * b^c$
-/
lemma mul_pow (a b c : natnum) : (a * b) ^ c = a ^ c * b ^ c :=
begin
induction c with d hd,
{repeat {rw pow_zero},
rw mul_one,},
{repeat {rw pow_succ},
rw hd,
rw mul_assoz (a ^ d) (b ^ d) (a * b),
rw ← mul_assoz (b^d) a b,
rw mul_komm (b^d) a,
rw mul_assoz a (b^d) b,
rw ← mul_assoz (a^d) a (b^d*b),
},
end

end natnum -- hide