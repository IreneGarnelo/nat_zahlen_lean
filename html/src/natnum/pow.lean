import natnum.mul

namespace natnum

def pow : natnum → natnum → natnum
| m zero := one
| m (succ n) := pow m n * m

instance : has_pow natnum natnum := ⟨pow⟩
-- notation a ^ b := pow a b

lemma pow_zero (m : natnum) : m ^ (zero : natnum) = one := rfl

lemma pow_succ (m n : natnum) : m ^ (succ n) = m ^ n * m := rfl

end natnum