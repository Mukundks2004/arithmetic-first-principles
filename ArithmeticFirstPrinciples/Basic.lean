namespace ArithmeticFirstPrinciples.Basic

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

def myAdd : MyNat → MyNat → MyNat
  | a, .zero => a
  | a, .succ b => MyNat.succ (myAdd a b)

theorem add_zero (a : MyNat) : myAdd a .zero = a := by
  rfl

theorem add_succ (a b : MyNat) : myAdd a (MyNat.succ b) = MyNat.succ (myAdd a b) := by
  rfl

theorem zero_add (a : MyNat) : myAdd .zero a = a := by
  induction a with
  | zero => rfl
  | succ b ih =>
    rw [add_succ, ih]

theorem succ_add (a b : MyNat) : myAdd (MyNat.succ a) b = MyNat.succ (myAdd a b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [add_succ, ih]
    rw [← add_succ]

theorem add_comm (a b : MyNat) : myAdd a b = myAdd b a := by
  induction b with
  | zero =>
    rw [add_zero, zero_add]
  | succ b ih =>
    rw [add_succ, succ_add, ih]

theorem add_assoc (a b c : MyNat) : myAdd (myAdd a b) c = myAdd a (myAdd b c) := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | succ c ih =>
    rw [add_succ, add_succ, add_succ, ih]

end ArithmeticFirstPrinciples.Basic
