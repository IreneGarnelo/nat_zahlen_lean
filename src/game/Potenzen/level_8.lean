-- Level name : Erste Binomische Formel

import natnum.pow -- hide
import game.Potenzen.level_7 -- hide
namespace natnum -- hide

/-
Du bist zu dem letzten Level angekommen! Mit allem was wir
bisher bewiesen haben können wir die erste binomische Formel
beweisen. Das wird aber einige Beweisschritte erfordern.

In diesem Level kommt die zwei zum ersten Mal explizit vor. Anstatt
`succ(one)` wollen wir einen Namen einführen: `two`. Zusätzlich möchten wir
benutzen können, dass `two=succ(one)` ist, diese Aussage nennen wir 
`two_eq_succ_one`.
-/

/- Hint : Klicke hier um die Definition von `two` in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def two : natnum := succ(succ(0))` <br>

Dieser Eigenschaften wird ein Namen gegeben: <br>
`theorem two_eq_succ_one : two = succ(succ(zero)) := rfl`
-/

/- Lemma
$(a+b)^2=a^2+2*a*b+b^2$
-/
lemma add_squared (a b : natnum) : (a + b) ^ two = a ^ two + two * a * b + b ^ two:=
begin
rw two_eq_succ_one,
repeat{rw pow_succ},
repeat{rw pow_one},
rw distr,
repeat{rw add_mul},
rw succ_mul,
rw ← one_eq_succ_zero,
repeat {rw pow_zero,},
repeat{rw one_mul,},
repeat{rw add_mul,},
rw mul_komm b a,
rw add_assoz (a*a) (a*b) (a*b + b*b),
rw add_assoz (a*a) (a*b+a*b) (b*b),
rw add_assoz (a*b) (a*b) (b*b),
end

end natnum -- hide