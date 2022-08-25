-- Level name : 0 hoch etwas ergibt 0

import natnum.pow -- hide
import game.Potenzen.level_1 -- hide
namespace natnum -- hide

/-

In diesem Level zeigen wir, dass $0$ hoch jedem Nachfolger einer natürlichen Zahl
$0$ ergibt.

-/

/- Hint :  Wieso folgt daraus nicht $0^0=0$, was ein Widerspruch zu level 1 ist?
In den Peano Axiomen steht, dass $0$ nicht der Nachfolger einer Zahl ist. Deswegen
zeigen wir hier $0^{(succ(a))}=0$ und nicht $0^a=0$. Wir schließen so die $0$ aus.
-/

/- Lemma
$0^{(succ(a))}=0$
-/
lemma zero_pow_succ (a : natnum) : (zero) ^ (succ(a)) = zero :=
begin
rw pow_succ,
rw mul_zero,
end

end natnum -- hide