-- Level name : Addition mit 0 - von links

import natnum.add -- hide
import game.Addition.level_2 --hide
namespace natnum -- hide

/-
Nach Definition der Addition gilt: $a+0=a$. Wir haben aber noch nicht bewiesen,
dass die Addition kommutativ ist. Es ist also noch nicht bewiesen, dass auch
$0+a=a$ gilt.

Dies werden wir über Induktion zeigen. Dazu lernen wir den `induction` Befehl in
LEAN. Um einen Induktionsbeweis zu starten, müssen wir `induction a with d hd,`
aufrufen. Dabei ist das $a$ die Variable, über die induziert werden soll, $d$
wird der Name der Variable im Induktionsschritt sein, und `hd` ist die Aussage
der Induktionsvoraussetzung.

Nachdem du den Befehl `induction a with d hd,` eingibst, wirst du in der rechten
Spalte sehen, dass du zwei Beweisziele hast: den Induktionsanfang und die 
Induktionsvoraussetzung. Um den Beweis übersichtlicher zu führen, kannst du
die zwei Teile mit geschweiften Klammern umgeben. Dein Beweis hat dann die Form: <br>
`begin` <br>
  `induction a with d hd,` <br>
  `{},` <br>
  `{},` <br>
`end` <br>
Innerhalb der geschweiften Klammern kannst du dann jeweils den Induktionsanfang und
den Induktionsschritt zeigen.
-/

/- Lemma
$0+a=a$
-/
lemma zero_add (a : natnum) : zero + a = a :=
begin
  induction a with d hd,
  {rw add_zero,},
  {rw add_succ,
  rw hd,},
end

end natnum -- hide