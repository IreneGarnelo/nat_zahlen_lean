@[derive decidable_eq]
inductive natnum
| zero : natnum
| succ (n : natnum) : natnum

namespace natnum

instance : has_zero natnum := ⟨natnum.zero⟩
theorem natnum_zero_eq_zero : natnum.zero = 0 := rfl

def one : natnum := succ 0

def two : natnum := succ(succ(0))

instance : has_one natnum := ⟨natnum.one⟩

theorem one_eq_succ_zero : one = succ zero := rfl

theorem two_eq_succ_one : two = succ(succ(zero)) := rfl

lemma zero_ne_succ (m : natnum) : (zero : natnum) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : natnum} (h : succ m = succ n) : m = n := by cases h; refl

end natnum

attribute [symm] ne.symm