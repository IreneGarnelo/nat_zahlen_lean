-- Level name : Potenzieren als Homomorphismus $a∧⬝: (\mathbb{N}, +) → (\mathbb{N}, *)$

import natnum.pow -- hide
import game.Potenzen.level_4 -- hide
namespace natnum -- hide

/-
Wenn wir das Potenzieren als Abbildung $a∧⬝: (\mathbb{N}, +) → (\mathbb{N}, *)$
auffassen, dann ist $∧$ ein Homomorphismus, da $a^{b + c} = a^b * a^c$. Dies 
ist eines der Potenzgesetzte.
-/

/- Lemma
$a^{b + c} = a^b * a^c$
-/
lemma pow_add (a b c : natnum) : a ^ (b + c) = a ^ b * a ^ c :=
begin
induction c with d hd,
{rw add_zero,
rw pow_zero,
rw mul_one,},
{rw add_succ,
repeat{rw pow_succ},
rw hd,
rw ← mul_assoz (a^b) (a^d) a,
},

end

end natnum -- hide