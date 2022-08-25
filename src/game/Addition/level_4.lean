-- Level name : Assoziativität der Addition

import natnum.add -- hide
import game.Addition.level_3 --hide
namespace natnum -- hide

/-
Nun werden wir die Assoziativität der Addition der natürlichen
Zahlen zeigen. Das bedeutet $(a + b) + c = a + (b + c)$. 
-/

/- Hint : Über welcher der drei Variablen ist ein Induktionsbeweis am sinnvollsten?
Wir haben die Addition mit Rekursion auf die rechte Variable definiert,
es ist also sinnvoll bei dem Imduktionsbeweis über die Variable
$c$ zu induzieren.
-/

/-
Noch eine Bemerkung: LEAN ist linksassoziativ. Das bedeutet, dass für LEAN
$a+b+b$ das gleiche wie $(a+b)+c$ ist.
-/

/- Lemma
$(a + b) + c = a + (b + c)$
-/
lemma add_assoz (a b c : natnum) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  {rw add_zero,
  rw add_zero,},
  {rw add_succ (a+b) d,
  rw add_succ,
  rw add_succ,
  rw hd,},
end

end natnum -- hide