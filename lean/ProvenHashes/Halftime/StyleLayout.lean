import ProvenHashes.Halftime.StyleLanes

namespace ProvenHashes.Halftime
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Restricting an independent uniform table to distinct addresses gives an
independent uniform table on those addresses. Unused entries are integrated out. -/
theorem uniformProb_restrict {I J V : Type*} [Fintype I] [Fintype J] [Fintype V]
    [DecidableEq I] [DecidableEq J] [Nonempty V] (e : I ↪ J) (E : (I → V) → Prop) :
    uniformProb (fun k : J → V => E (fun i => k (e i))) = uniformProb E := by
  classical
  let C := {j : J // j ∉ Set.range e}
  let domain : I ⊕ C ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl C)).trans
      (Equiv.sumCompl (fun j => j ∈ Set.range e))
  let keyEquiv : ((I → V) × (C → V)) ≃ (J → V) :=
    (Equiv.sumArrowEquivProdArrow I C V).symm.trans (Equiv.arrowCongr domain (Equiv.refl V))
  have he (k : (I → V) × (C → V)) : (fun i => keyEquiv k (e i)) = k.1 := by
    funext i
    change keyEquiv k (domain (Sum.inl i)) = k.1 i
    simp [keyEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]
  rw [← uniformProb_equiv keyEquiv]
  simp only [he]
  exact uniformProb_prod_fst E

noncomputable def halves32Equiv : Word64 ≃ (Bool → Word32) :=
  Equiv.ofBijective halves32 ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨halves32_injective, by simp [Word32, Word64]⟩)

noncomputable def keyWordEquiv : XorWord 64 ≃ (Bool → Word32) :=
  (xorWordEquiv 64).trans halves32Equiv

/-- Function-indexed level keys and the recursive forest key representation. -/
def levelKeysEquiv (K : Type*) : (h : ℕ) → (Fin h → K) ≃ LevelKeys K h
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ i => Fin.elim0 i
      left_inv := by intro f; funext i; exact Fin.elim0 i
      right_inv := by intro k; cases k; rfl }
  | h + 1 =>
    { toFun := fun f => (levelKeysEquiv K h (fun i => f i.castSucc), f (Fin.last h))
      invFun := fun k => Fin.lastCases k.2 ((levelKeysEquiv K h).symm k.1)
      left_inv := by
        intro f
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      right_inv := by
        intro k
        apply Prod.ext <;> simp }

abbrev StyleWordIndex (b h roots l : ℕ) :=
  (Fin 7 × Fin 3) ⊕ ((Fin h × (Fin 2 × Fin 7)) ⊕
    (((Fin roots × Fin 2) × Fin b) ⊕ Fin (l + (b + 1) - 1)))

def styleKeyFromWords {b h roots l : ℕ} (k : StyleWordIndex b h roots l → Bool → Word32) :
    StyleKey b h roots l :=
  ((fun s p => k (.inl (s, p.1)) p.2,
    fun c => (levelKeysEquiv _ h (fun j p => k (.inr (.inl (j, c, p.1))) p.2),
      fun p => k (.inr (.inr (.inl (((finProdFinEquiv.symm p.1).1, c),
        (finProdFinEquiv.symm p.1).2)))) p.2)),
    fun p => k (.inr (.inr (.inr p.1))) p.2)

def styleKeyToWords {b h roots l : ℕ} (k : StyleKey b h roots l) :
    StyleWordIndex b h roots l → Bool → Word32
  | .inl (s, t), bit => k.1.1 s (t, bit)
  | .inr (.inl (j, c, v)), bit => (levelKeysEquiv _ h).symm (k.1.2 c).1 j (v, bit)
  | .inr (.inr (.inl ((v, c), lane))), bit => (k.1.2 c).2 (finProdFinEquiv (v, lane), bit)
  | .inr (.inr (.inr p)), bit => k.2 (p, bit)

def styleKeyEquiv (b h roots l : ℕ) :
    (StyleWordIndex b h roots l → Bool → Word32) ≃ StyleKey b h roots l where
  toFun := styleKeyFromWords
  invFun := styleKeyToWords
  left_inv k := by
    funext i bit
    rcases i with ⟨s, t⟩ | (⟨j, c, v⟩ | (⟨⟨v, c⟩, lane⟩ | p)) <;>
      simp only [styleKeyFromWords, styleKeyToWords, Equiv.symm_apply_apply]
  right_inv k := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext c
        apply Prod.ext
        · exact (levelKeysEquiv _ h).apply_symm_apply _
        · funext p
          simp only [styleKeyFromWords, styleKeyToWords, Prod.eta, Equiv.apply_symm_apply]
    · rfl

/-- Actual absolute word addresses, including the fixed nine-level reservation. -/
def styleWordAddressNat {b h roots l : ℕ} : StyleWordIndex b h roots l → ℕ
  | .inl (s, t) => 512 + (finProdFinEquiv (s, t)).val
  | .inr (.inl (j, c, v)) => 533 +
      (finProdFinEquiv (j, finProdFinEquiv (c, v))).val
  | .inr (.inr (.inl ((v, c), lane))) => 659 +
      (finProdFinEquiv (finProdFinEquiv (v, c), lane)).val
  | .inr (.inr (.inr p)) => 659 + roots * 2 * b + p.val

theorem styleWordAddress_ehc {b h roots l : ℕ} (s : Fin 7) (t : Fin 3) :
    @styleWordAddressNat b h roots l (.inl (s, t)) = 512 + 3 * s.val + t.val := by
  change 512 + (t.val + 3 * s.val) = _
  omega

theorem styleWordAddress_tree {b h roots l : ℕ} (j : Fin h) (c : Fin 2) (v : Fin 7) :
    @styleWordAddressNat b h roots l (.inr (.inl (j, c, v))) =
      533 + 14 * j.val + 7 * c.val + v.val := by
  change 533 + ((v.val + 7 * c.val) + (2 * 7) * j.val) = _
  omega

theorem styleWordAddress_final {b h roots l : ℕ} (v : Fin roots) (c : Fin 2) (lane : Fin b) :
    @styleWordAddressNat b h roots l (.inr (.inr (.inl ((v, c), lane)))) =
      659 + b * (2 * v.val + c.val) + lane.val := by
  change 659 + (lane.val + b * (c.val + 2 * v.val)) = _
  ring

theorem styleWordAddress_tail {b h roots l : ℕ} (p : Fin (l + (b + 1) - 1)) :
    @styleWordAddressNat b h roots l (.inr (.inr (.inr p))) =
      659 + 2 * b * roots + p.val := by
  unfold styleWordAddressNat
  ring

theorem styleWordAddressNat_injective {b h roots l : ℕ} (hh : h ≤ 9) :
    Function.Injective (@styleWordAddressNat b h roots l) := by
  intro i j he
  have htree : h * (2 * 7) ≤ 126 := by omega
  rcases i with ⟨s, t⟩ | (⟨lev, c, v⟩ | (⟨⟨v, c⟩, lane⟩ | p)) <;>
    rcases j with ⟨s', t'⟩ | (⟨lev', c', v'⟩ | (⟨⟨v', c'⟩, lane'⟩ | p')) <;>
    simp only [styleWordAddressNat] at he
  all_goals first
    | (have hh := (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).injective
        (Fin.ext (Nat.add_left_cancel he)); cases hh; rfl)
    | (have hh := (finProdFinEquiv : Fin h × Fin (2 * 7) ≃ Fin (h * (2 * 7))).injective
        (Fin.ext (Nat.add_left_cancel he));
       have h0 := congrArg Prod.fst hh;
       have h1 := finProdFinEquiv.injective (congrArg Prod.snd hh);
       cases h0; cases h1; rfl)
    | (have hh := (finProdFinEquiv : Fin (roots * 2) × Fin b ≃ Fin (roots * 2 * b)).injective
        (Fin.ext (Nat.add_left_cancel he));
       have h0 := finProdFinEquiv.injective (congrArg Prod.fst hh);
       have h1 := congrArg Prod.snd hh;
       cases h0; cases h1; rfl)
    | (have hh : p = p' := Fin.ext (Nat.add_left_cancel he); cases hh; rfl)
    | omega

theorem styleWordAddressNat_lt {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b)
    (i : StyleWordIndex b h roots l) : styleWordAddressNat i < 2048 := by
  have htree : h * (2 * 7) ≤ 126 := by omega
  have hfinal : roots * 2 * b ≤ 1024 := by nlinarith
  have htail : roots * 2 * b + (l + (b + 1) - 1) ≤ 1176 := by
    have he : l + (b + 1) - 1 = l + b := by omega
    rw [he]
    have := Nat.mul_le_mul_right b hr
    nlinarith
  rcases i with ⟨s, t⟩ | (⟨j, c, v⟩ | (⟨⟨v, c⟩, lane⟩ | p)) <;>
    simp only [styleWordAddressNat] <;> omega

def styleWordAddress {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b) :
    StyleWordIndex b h roots l ↪ Fin 2048 :=
  ⟨fun i => ⟨styleWordAddressNat i, styleWordAddressNat_lt hb hh hr hl i⟩,
    fun _ _ he => styleWordAddressNat_injective hh (congrArg Fin.val he)⟩

def styleLowerAddress {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b) :
    StyleWordIndex b h roots l ↪ (Fin 8 × Fin 256) :=
  (styleWordAddress hb hh hr hl).trans
    (finProdFinEquiv : Fin 8 × Fin 256 ≃ Fin 2048).symm.toEmbedding

/-- Read the core keys from the same 2048 words that serve as length tables. -/
noncomputable def readStyleKey {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b)
    (key : LowerTableKey) : StyleKey b h roots l :=
  styleKeyEquiv b h roots l (fun i => keyWordEquiv (key (styleLowerAddress hb hh hr hl i)))

theorem readStyleKey_uniform {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b)
    (E : StyleKey b h roots l → Prop) :
    uniformProb (fun key => E (readStyleKey hb hh hr hl key)) = uniformProb E := by
  unfold readStyleKey
  rw [uniformProb_restrict (styleLowerAddress hb hh hr hl)
    (fun k => E (styleKeyEquiv b h roots l (fun i => keyWordEquiv (k i))))]
  exact uniformProb_equiv
    ((Equiv.piCongrRight fun _ => keyWordEquiv).trans (styleKeyEquiv b h roots l)) E

noncomputable def flatStyleCore {b h roots l : ℕ}
    (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b)
    (s : Fin roots → TreeShape 8 h)
    (x : (∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l) (key : LowerTableKey) :
    Fin 2 → Word64 := styleCore s x (readStyleKey hb hh hr hl key)

theorem flatStyleCore_survival {b h roots l : ℕ}
    (hb0 : 0 < b) (hb : b ≤ 8) (hh : h ≤ 9) (hr : roots ≤ 64) (hl : l ≤ 18 * b)
    (s : Fin roots → TreeShape 8 h)
    (x y : (∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l) (hxy : x ≠ y)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => flatStyleCore hb hh hr hl s x key - flatStyleCore hb hh hr hl s y key = target) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  unfold flatStyleCore
  rw [readStyleKey_uniform hb hh hr hl (fun key => styleCore s x key - styleCore s y key = target)]
  exact styleCore_survival hb0 s x y hxy target

end ProvenHashes.Halftime
