import ProvenHashes.Halftime.IntegerNH

namespace ProvenHashes.Halftime
set_option maxHeartbeats 500000

def splitWord {q : ℕ} (x : ZMod (q * q)) : Bool → ZMod q
  | false => x.val
  | true => x.val / q

theorem splitWord_injective {q : ℕ} [NeZero q] : Function.Injective (@splitWord q) := by
  intro x y he
  have hx : x.val / q < q := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne q))).mpr x.val_lt
  have hy : y.val / q < q := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne q))).mpr y.val_lt
  have h0 := congrArg ZMod.val (congrFun he false)
  have h1 := congrArg ZMod.val (congrFun he true)
  simp only [splitWord, ZMod.val_natCast] at h0 h1
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
  apply ZMod.val_injective
  have hxx := Nat.mod_add_div x.val q
  have hyy := Nat.mod_add_div y.val q
  rw [h0, h1] at hxx
  omega

/-- The actual low and high unsigned 32-bit halves of a 64-bit word. -/
def halves32 (x : ZMod (2 ^ 64)) : Bool → ZMod (2 ^ 32) := splitWord (nh32Equiv.symm x)

theorem halves32_injective : Function.Injective halves32 := by
  intro x y he
  exact nh32Equiv.symm.injective (splitWord_injective he)

def packWords {m : ℕ} (x : Fin m → ZMod (2 ^ 64)) : Fin m × Bool → ZMod (2 ^ 32) :=
  fun p => halves32 (x p.1) p.2

theorem packWords_injective {m : ℕ} : Function.Injective (@packWords m) := by
  intro x y he
  funext i
  apply halves32_injective
  funext b
  exact congrFun he (i, b)

/-- Hash the first m child words; carry the last word as the unhashed
accumulator. This is an injective packing of all m+1 input words. -/
def packTree {m : ℕ} (x : Fin (m + 1) → ZMod (2 ^ 64)) :
    (Fin m × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32) :=
  (packWords (fun i => x i.castSucc), nh32Equiv.symm (x (Fin.last m)))

theorem packTree_injective {m : ℕ} : Function.Injective (@packTree m) := by
  intro x y he
  have h0 : (fun i : Fin m => x i.castSucc) = (fun i => y i.castSucc) :=
    packWords_injective (congrArg Prod.fst he)
  have h1 : x (Fin.last m) = y (Fin.last m) := nh32Equiv.symm.injective (congrArg Prod.snd he)
  funext i
  exact Fin.lastCases h1 (fun j => congrFun h0 j) i

end ProvenHashes.Halftime
