import natnum.add

namespace natnum

def mul : natnum → natnum → natnum
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul natnum := ⟨mul⟩
-- notation a * b := mul a b

lemma mul_zero (m : natnum) : m * zero = zero := rfl

lemma mul_succ (m n : natnum) : m * (succ n) = m * n + m := rfl

end natnum