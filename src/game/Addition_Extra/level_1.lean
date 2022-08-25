-- Level name : Die succ Abbildung ist kein Homomorphismus

import natnum.add -- hide
import game.Addition.level_7 --hide
namespace natnum -- hide

/-
Für zwei Mengen mit Verknüpfung $(M, $∗$), (N, $⋆$)$ ist eine Abbildung $f: M $→$ N$
ein Homomorphismus, falls $f(m_1)$ ⋆ $f(m_2) = f(m_1$ ∗ $m_2)$ für alle $m_1, m_2$ in M.

Die Abbildung `succ` ist eine Abbildung `succ`$: \mathbb{N}$ → $\mathbb{N}$. Wir haben
auf der Menge der natürlichen Zahlen die Addition als Verknüpfung definiert. Wir werden
nun sehen, dass diese Abbildung kein Homomorphismus bezüglich der Addition ist.
-/

/- Lemma
`succ`$(a) +$ `succ`$(b) =$ `succ`$(a + b) + 1$
-/
lemma succ_non_hom (a b: natnum) : succ(a) + succ(b) = succ(a + b) + one :=
begin
rw add_succ,
rw succ_eq_add_one (a.succ+b),
rw succ_add,
end

end natnum -- hide