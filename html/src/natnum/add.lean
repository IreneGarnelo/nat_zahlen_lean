import natnum.definition

namespace natnum

def add : natnum → natnum → natnum
| m 0 := m
| m (succ n) := succ (add m n)

instance : has_add natnum := ⟨natnum.add⟩

lemma add_zero (m : natnum) : m + zero = m := rfl

lemma add_succ (m n : natnum) : m + succ n = succ (m + n) := rfl

end natnum