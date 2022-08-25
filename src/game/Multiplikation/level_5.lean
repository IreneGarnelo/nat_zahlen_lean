-- Level name : Assoziativität der Multiplikation

import natnum.mul -- hide
import game.Multiplikation.level_4 -- hide
namespace natnum -- hide

/-



-/

/- Lemma
$(a * b) * c = a * (b * c)$
-/
lemma mul_assoz (a b c : natnum) : (a * b) * c = a * (b * c) :=
begin
induction c with d hd,
{repeat {rw mul_zero,},},
{repeat{rw mul_succ},
rw distr,
rw hd,},
end

end natnum -- hide

/- Hint :  Kannst du auch bei der Assoziativität den Beweis aus der Addition einfach übernehmen?
Nein, für diesen Beweis brauchst du nämlich das Distributivgesetzt. Das kommt daher, dass die 
Definition der Multiplikation von der Addition abhängt (`a*succ(d)=a*d+a`).
-/