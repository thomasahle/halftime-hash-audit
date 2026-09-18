import ProvenHashes.Halftime.IntegerNH
import ProvenHashes.Halftime.EndToEnd

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem uniformProb_inter_conditional {K J : Type*} [Fintype K] [Fintype J]
    (E : K → Prop) (F : K → J → Prop) (a : ℚ≥0)
    (hf : ∀ k, E k → uniformProb (F k) ≤ a) :
    uniformProb (fun k : K × J => E k.1 ∧ F k.1 k.2) ≤ uniformProb E * a := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (fun j => E k ∧ F k j)) ≤ _
  calc
    _ ≤ mean (fun k => a * indicator E k) := by
      apply mean_mono
      intro k
      by_cases he : E k
      · simpa [indicator, he] using hf k he
      · simp [he, indicator, uniformProb]
    _ = _ := by rw [mean_mul, mean_indicator, mul_comm]

/-- Expose one key, retaining the exact probability of the earlier event.
The earlier event is invariant under updates of that key. -/
theorem uniformProb_inter_update {I V O : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Nonempty V] (E : (I → V) → Prop) (f : (I → V) → O) (i : I)
    (hE : ∀ k v, E (Function.update k i v) ↔ E k)
    (hf : ∀ k, Function.Injective (fun v => f (Function.update k i v))) (t : O) :
    uniformProb (fun k => E k ∧ f k = t) ≤ uniformProb E * (1 / Fintype.card V) := by
  classical
  let split := Equiv.funSplitAt i V
  let v₀ : V := Classical.choice inferInstance
  let e : (({j // j ≠ i} → V) × V) ≃ (I → V) :=
    (Equiv.prodComm _ _).trans split.symm
  have hu (r : {j // j ≠ i} → V) (v : V) :
      e (r, v) = Function.update (e (r, v₀)) i v := by
    funext j
    by_cases hj : j = i
    · subst j; simp [e, split]
    · simp [e, split, Function.update, hj]
  have heE (r : {j // j ≠ i} → V) (v : V) : E (e (r, v)) ↔ E (e (r, v₀)) := by
    rw [hu r v]
    exact hE _ _
  have hprob : uniformProb E = uniformProb (fun r => E (e (r, v₀))) := by
    have hfun : (fun p => E (e p)) = (fun p => E (e (p.1, v₀))) := by
      funext p
      exact propext (heE p.1 p.2)
    calc
      _ = uniformProb (fun p => E (e p)) := (uniformProb_equiv e E).symm
      _ = uniformProb (fun p : ({j // j ≠ i} → V) × V => E (e (p.1, v₀))) := congrArg uniformProb hfun
      _ = _ := uniformProb_prod_fst (J := V) (fun r => E (e (r, v₀)))
  have hfun : (fun p => E (e p) ∧ f (e p) = t) =
      (fun p => E (e (p.1, v₀)) ∧ f (e p) = t) := by
    funext p
    exact propext (and_congr_left (fun _ => heE p.1 p.2))
  calc
    _ = uniformProb (fun p => E (e p) ∧ f (e p) = t) :=
      (uniformProb_equiv e (fun k => E k ∧ f k = t)).symm
    _ = uniformProb (fun p : ({j // j ≠ i} → V) × V => E (e (p.1, v₀)) ∧ f (e p) = t) :=
      congrArg uniformProb hfun
    _ ≤ uniformProb (fun r => E (e (r, v₀))) * (1 / Fintype.card V) := by
      apply uniformProb_inter_conditional (fun r => E (e (r, v₀)))
        (fun r v => f (e (r, v)) = t) (1 / Fintype.card V)
      intro r _
      apply uniformProb_of_injective (fun v => f (e (r, v))) _ t
      intro u v huv
      apply hf (e (r, v₀))
      change f (Function.update (e (r, v₀)) i u) = f (Function.update (e (r, v₀)) i v)
      rw [← hu r u, ← hu r v]
      exact huv
    _ = _ := congrArg (fun a : ℚ≥0 => a * (1 / Fintype.card V)) hprob.symm

/-- Triangular key exposure: each output has one injective fresh coordinate
that every preceding output ignores. Derived outputs need not be independent. -/
theorem triangular_adu {I V O : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Nonempty V] (r : ℕ)
    (f : Fin r → (I → V) → O) (pick : Fin r → I)
    (hf : ∀ j k, Function.Injective (fun v => f j (Function.update k (pick j) v)))
    (hp : ∀ i j, i < j → ∀ k v, f i (Function.update k (pick j) v) = f i k)
    (b : Fin r → O) :
    uniformProb (fun k => ∀ j, f j k = b j) ≤ (1 / (Fintype.card V : ℚ≥0)) ^ r := by
  induction r with
  | zero => simp [uniformProb]
  | succ r ih =>
    let E (k : I → V) := ∀ i : Fin r, f i.castSucc k = b i.castSucc
    have he : ∀ k v, E (Function.update k (pick (Fin.last r)) v) ↔ E k := by
      intro k v
      simp only [E, hp _ _ (Fin.castSucc_lt_last _) k v]
    have H := uniformProb_inter_update E (f (Fin.last r)) (pick (Fin.last r)) he (hf _) (b (Fin.last r))
    have hi := ih (fun i => f i.castSucc) (fun i => pick i.castSucc) (fun i => hf i.castSucc)
      (fun i j hij => hp i.castSucc j.castSucc hij) (fun i => b i.castSucc)
    have hev : (fun k => ∀ j, f j k = b j) = (fun k => E k ∧ f (Fin.last r) k = b (Fin.last r)) := by
      funext k
      exact propext Fin.forall_fin_succ'
    rw [hev, pow_succ]
    exact H.trans (mul_le_mul_of_nonneg_right hi (by positivity))

def shiftIndex {n r : ℕ} (i : Fin n) (j : Fin r) : Fin (n + r - 1) := ⟨i.val + j.val, by omega⟩

def shiftEmbedding {n r : ℕ} (j : Fin r) : (Fin n × Bool) ↪ (Fin (n + r - 1) × Bool) :=
  ⟨fun p => (shiftIndex p.1 j, p.2), by
    intro a b he
    have h0 := congrArg (fun p => p.1.val) he
    have h1 := congrArg Prod.snd he
    apply Prod.ext
    · apply Fin.ext; dsimp [shiftIndex] at h0; omega
    · exact h1⟩

/-- Output j shifts the NH key by j whole pairs, so adjacent outputs share
key words. The pool has exactly n+r−1 pairs when n and r are positive. -/
def toeplitzNH {n r : ℕ} (x : Fin n × Bool → ZMod (2 ^ 32))
    (key : Fin (n + r - 1) × Bool → ZMod (2 ^ 32)) (j : Fin r) : ZMod (2 ^ 64) :=
  nh32 x (fun i => key (shiftEmbedding j i))

theorem update_comp_embedding {I J V : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ↪ J) (k : J → V) (i : I) (v : V) :
    (fun j => Function.update k (e i) v (e j)) = Function.update (fun j => k (e j)) i v := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · have he : e j ≠ e i := fun hh => h (e.injective hh)
    simp [Function.update, h, he]

theorem nh_difference_update_injective {q n : ℕ} [NeZero q]
    (x y k : Fin n × Bool → ZMod q) (i : Fin n) (b : Bool) (hi : x (i, b) ≠ y (i, b)) :
    Function.Injective (fun v => nh x (Function.update k (i, !b) v) - nh y (Function.update k (i, !b) v)) := by
  intro u v huv
  cases b
  · simp only [Bool.not_false, nh_update_true] at huv
    apply unsigned_pair_add_injective (x (i, false) + k (i, false)) (y (i, false) + k (i, false))
      (x (i, true)) (y (i, true)) (by simpa using hi)
    linear_combination huv
  · simp only [Bool.not_true, nh_update_false] at huv
    apply unsigned_pair_add_injective (x (i, true) + k (i, true)) (y (i, true) + k (i, true))
      (x (i, false)) (y (i, false)) (by simpa using hi)
    linear_combination huv

theorem toeplitz_update_injective {n r : ℕ}
    (x y : Fin n × Bool → ZMod (2 ^ 32)) (p : Fin n) (b : Bool) (hp : x (p, b) ≠ y (p, b))
    (j : Fin r) (key : Fin (n + r - 1) × Bool → ZMod (2 ^ 32)) :
    Function.Injective (fun v =>
      toeplitzNH x (Function.update key (shiftEmbedding j (p, !b)) v) j -
      toeplitzNH y (Function.update key (shiftEmbedding j (p, !b)) v) j) := by
  intro u v huv
  simp only [toeplitzNH, update_comp_embedding, nh32, ← map_sub] at huv
  exact nh_difference_update_injective x y _ p b hp (nh32Equiv.injective huv)

theorem toeplitz_earlier_ignores_update {n r : ℕ}
    (x y : Fin n × Bool → ZMod (2 ^ 32)) (p : Fin n)
    (hp : ∀ a, p < a → ∀ b, x (a, b) = y (a, b))
    (i j : Fin r) (hij : i < j) (b : Bool)
    (key : Fin (n + r - 1) × Bool → ZMod (2 ^ 32)) (v : ZMod (2 ^ 32)) :
    toeplitzNH x (Function.update key (shiftEmbedding j (p, b)) v) i -
      toeplitzNH y (Function.update key (shiftEmbedding j (p, b)) v) i =
    toeplitzNH x key i - toeplitzNH y key i := by
  simp only [toeplitzNH, nh32, ← map_sub]
  congr 1
  simp only [nh, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : shiftIndex a i = shiftIndex p j
  · have hpa : p < a := by
      have he := congrArg Fin.val ha
      dsimp [shiftIndex] at he
      change i.val < j.val at hij
      change p.val < a.val
      omega
    rw [hp a hpa false, hp a hpa true]
    simp
  · have hfalse : shiftEmbedding i (a, false) ≠ shiftEmbedding j (p, b) :=
      fun he => ha (congrArg Prod.fst he)
    have htrue : shiftEmbedding i (a, true) ≠ shiftEmbedding j (p, b) :=
      fun he => ha (congrArg Prod.fst he)
    simp only [Function.update_of_ne hfalse, Function.update_of_ne htrue]

/-- The shared-key Toeplitz NH family is ε^r difference universal. The last
differing pair exposes a fresh half-word for each successive output. -/
theorem toeplitzNH_adu {n r : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (t : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun key => toeplitzNH x key - toeplitzNH y key = t) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ r := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ∃ b, x (i, b) ≠ y (i, b))
  have hS : S.Nonempty := by
    obtain ⟨⟨i, b⟩, hi⟩ := Function.ne_iff.mp hxy
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hi⟩⟩
  let p := S.max' hS
  have hpS : p ∈ S := Finset.max'_mem S hS
  obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hpS).2
  have hafter (a : Fin n) (ha : p < a) (b : Bool) : x (a, b) = y (a, b) := by
    by_contra hn
    have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hn⟩
    exact (not_le_of_gt ha) (Finset.le_max' S a haS)
  have H := triangular_adu r (fun j key => toeplitzNH x key j - toeplitzNH y key j)
    (fun j => shiftEmbedding j (p, !b))
    (fun j key => toeplitz_update_injective x y p b hb j key)
    (fun i j hij key v => toeplitz_earlier_ignores_update x y p hafter i j hij (!b) key v) t
  simpa only [funext_iff, Pi.sub_apply, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using H

end ProvenHashes.Halftime
