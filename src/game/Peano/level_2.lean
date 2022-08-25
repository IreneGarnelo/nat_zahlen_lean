-- Level name : Die Peano Axiome - Teil 2

-- namespace nat -- hide 

import natnum.definition -- hide
namespace natnum -- hide

/-
Im diesen Level passiert nicht viel. Es dient eher zur Übung von dem gelerntem in
Level 1.

Wir werden aber auch die Gelegenheit nutzen, um uns den `rw` Befehl nochmal
anzuschauen. Wir haben gesehen, dass für die Aussage `h: a = b` der Befehl
`rw h,` in der zu zeigenden Aussage jedes `a` durch ein `b` ersetztz. Aber wie
kann man jedes `b` durch ein `a` ersetzten? Dazu verwendet man den Befehl
`rw ← h,`. Der Pfeil steht sozusagen dafür, dass LEAN die Aussage h von rechts
nach links lesen soll. Du kannst den Pfeil mit \ l (backslash + klein L)
schreiben.

Du kannst das untenstehende Lemma ähnlich wie Level 1 lösen, aber erkennst du
auch einen weiteren Weg?
-/

/- Lemma
Falls `succ`$(a) = b$ und `succ`$(b)= c$ dann `succ`$($`succ`$(a)) = c$
-/
lemma succ_succ (a b c : natnum) (h : succ(a) = b) (g : succ(b) = c): succ(succ(a)) = c :=
begin
rw h,
rw g,
end

end natnum -- hide

/- Hint : Brauchst du Hilfe um einen zweiten Weg zu finden?
In der zu zeigenden Aussage kommt der Term `c` vor, der auch Teil der Aussage
`g` ist. Du kannst also mit `rw ← g,` das `c` in der Aussage ersetzen.
-/