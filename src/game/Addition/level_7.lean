-- Level name : Kommutativität der rechten Summanden

import natnum.add -- hide
import game.Addition.level_6 --hide
namespace natnum -- hide

/-
Das Ziel dieses Levels ist $a+b+c=a+c+b$. Das sieht vielleicht erstmal danach aus,
dass du nur `add_komm,` anwenden muss. Aber LEAN ist links-assoziativ. Das bedeutet,
dass diese Aussage mit Klammern so geschrieben werden kann: $(a+b)+c=(a+c)+b$. Um
dieses Lemma zu zeigen, wirst du also auch die Assozitivität verwenden. Dieses
Lemma wird dir in zukünftigen Beweisen etwas Schreibarbeit sparen.

Noch eine Bemerkung: manchmal gibt es mehr als eine Stelle, an der `rw` etwas
anstellen kann. Wenn du nichts weiteres spezifizierst, wird LEAN die erste dieser
Stellen raussuchen. Wenn du zum Beispile in diesem Level damit anfangen möchtest,
dass du auf der rechten Seite $a+c+b$ zu $a+(c+b)$ umschreibst, wird das nicht mit
dem Befehl `rw add_assoz,` klappen. Dies wird nämlich in der linken Seite der Gleichung
die Assozitivität ausnutzen. Du kannst LEAN konkret angeben an welcher Stelle du die
Änderung möchtest, in diesem Fall: `rw add_assoz a c b,`.
-/

/- Lemma
$a+b+c=a+c+b$
-/
lemma add_right_komm (a b c: natnum) : a + b + c = a + c + b :=
begin
rw add_assoz a b c,
rw add_komm b c,
rw ← add_assoz a c b,
end

end natnum -- hide