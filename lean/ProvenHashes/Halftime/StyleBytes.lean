import ProvenHashes.Halftime.StyleLayout

namespace ProvenHashes.Halftime
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

abbrev Byte := Fin 256

/-- Little-endian loading of eight bytes into one unsigned word. -/
def byteWordEquiv : (Fin 8 → Byte) ≃ Word64 :=
  finFunctionFinEquiv.trans ((finCongr (by norm_num : 256 ^ 8 = 2 ^ 64)).trans
    (ZMod.finEquiv (2 ^ 64)).toEquiv)

def wordBytes (w : Word64) : Fin 8 → Byte := byteWordEquiv.symm w

def signatureBytes (w : Fin 2 → Word64) : Fin 16 → Byte :=
  fun i => wordBytes (w ((finProdFinEquiv : Fin 2 × Fin 8 ≃ Fin 16).symm i).1)
    ((finProdFinEquiv : Fin 2 × Fin 8 ≃ Fin 16).symm i).2

theorem signatureBytes_injective : Function.Injective signatureBytes := by
  intro x y he
  funext c
  apply byteWordEquiv.symm.injective
  funext j
  have hj := congrFun he (finProdFinEquiv (c, j))
  simpa only [signatureBytes, Equiv.symm_apply_apply] using hj

def lengthBytes (n : ℕ) : Fin 8 → Byte := wordBytes (n : Word64)

theorem lengthBytes_injective_below {m n : ℕ} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64)
    (he : lengthBytes m = lengthBytes n) : m = n := by
  have hw := byteWordEquiv.symm.injective he
  have hv := congrArg ZMod.val hw
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] using hv

def zeroPad {n capacity : ℕ} (x : Fin n → Byte) : Fin capacity → Byte :=
  fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0

theorem zeroPad_injective {n capacity : ℕ} (hn : n ≤ capacity) :
    Function.Injective (@zeroPad n capacity) := by
  intro x y he
  funext i
  have hi := congrFun he (i.castLE hn)
  simpa only [zeroPad, Fin.coe_castLE, i.isLt, dif_pos] using hi

def packBytesEquiv (words : ℕ) : (Fin (words * 8) → Byte) ≃ (Fin words → Word64) :=
  (Equiv.arrowCongr (finProdFinEquiv : Fin words × Fin 8 ≃ Fin (words * 8)).symm (Equiv.refl Byte)).trans
    ((Equiv.curry _ _ _).trans (Equiv.piCongrRight fun _ => byteWordEquiv))

def paddedWords {n words : ℕ} (x : Fin n → Byte) : Fin words → Word64 :=
  packBytesEquiv words (zeroPad x)

theorem paddedWords_injective {n words : ℕ} (hn : n ≤ words * 8) :
    Function.Injective (@paddedWords n words) := by
  intro x y he
  exact zeroPad_injective hn ((packBytesEquiv words).injective he)

noncomputable def inputWordEquiv : Word64 ≃ (Bool → XorWord 32) :=
  halves32Equiv.trans (Equiv.piCongrRight fun _ => (xorWordEquiv 32).symm)

noncomputable def leafRawEquiv (b : ℕ) :
    (((Fin 6 × Fin 3) × Fin b) → Word64) ≃ (Fin b → Encode2Input) where
  toFun f lane symbol p := inputWordEquiv (f ((symbol, p.1), lane)) p.2
  invFun x p := inputWordEquiv.symm (fun bit => x p.2 p.1.1 (p.1.2, bit))
  left_inv f := by funext p; exact inputWordEquiv.symm_apply_apply (f p)
  right_inv x := by funext lane symbol p; exact congrFun (inputWordEquiv.apply_symm_apply _) p.2

def leafWordIndex (b : ℕ) : ((Fin 6 × Fin 3) × Fin b) ≃ Fin (18 * b) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin b))).trans finProdFinEquiv

noncomputable def leafWordsEquiv (b : ℕ) : (Fin (18 * b) → Word64) ≃ (Fin b → Encode2Input) :=
  (Equiv.arrowCongr (leafWordIndex b).symm (Equiv.refl Word64)).trans (leafRawEquiv b)

def treeInputEquiv (X : Type*) {f : ℕ} : {h : ℕ} → (s : TreeShape f h) →
    TreeInput X s ≃ (LeafPath s → X)
  | _, .leaf =>
    { toFun := fun x _ => x
      invFun := fun g => g PUnit.unit
      left_inv := fun _ => rfl
      right_inv := by intro g; funext p; cases p; rfl }
  | _, .skip s => treeInputEquiv X s
  | _, .node s =>
    { toFun := fun x p => treeInputEquiv X (s p.1) (x p.1) p.2
      invFun := fun g i => (treeInputEquiv X (s i)).symm (fun p => g ⟨i, p⟩)
      left_inv := by
        intro x
        funext i
        change (treeInputEquiv X (s i)).symm (treeInputEquiv X (s i) (x i)) = x i
        exact (treeInputEquiv X (s i)).symm_apply_apply (x i)
      right_inv := by
        intro g
        funext p
        exact congrFun ((treeInputEquiv X (s p.1)).apply_symm_apply _) p.2 }

def forestInputEquiv (X : Type*) {roots h n : ℕ} (s : Fin roots → TreeShape 8 h)
    (order : (Σ i, LeafPath (s i)) ≃ Fin n) :
    (∀ i, TreeInput X (s i)) ≃ (Fin n → X) where
  toFun x i := treeInputEquiv X (s (order.symm i).1) (x (order.symm i).1) (order.symm i).2
  invFun g i := (treeInputEquiv X (s i)).symm (fun p => g (order ⟨i, p⟩))
  left_inv x := by
    funext i
    change (treeInputEquiv X (s i)).symm
      (fun p => (treeInputEquiv X (s (order.symm (order ⟨i, p⟩)).1))
        (x (order.symm (order ⟨i, p⟩)).1) (order.symm (order ⟨i, p⟩)).2) = x i
    have he : (fun p => (treeInputEquiv X (s (order.symm (order ⟨i, p⟩)).1))
        (x (order.symm (order ⟨i, p⟩)).1) (order.symm (order ⟨i, p⟩)).2) =
        treeInputEquiv X (s i) (x i) := by
      funext p
      rw [order.symm_apply_apply]
    rw [he, Equiv.symm_apply_apply]
  right_inv g := by
    funext i
    simp only [Equiv.apply_symm_apply, Sigma.eta]

noncomputable def prefixWordsEquiv {b h roots n : ℕ} (s : Fin roots → TreeShape 8 h)
    (order : (Σ i, LeafPath (s i)) ≃ Fin n) :
    (Fin (n * (18 * b)) → Word64) ≃ (∀ i, TreeInput (Fin b → Encode2Input) (s i)) :=
  (Equiv.arrowCongr (finProdFinEquiv : Fin n × Fin (18 * b) ≃ Fin (n * (18 * b))).symm
    (Equiv.refl Word64)).trans ((Equiv.curry _ _ _).trans
      ((Equiv.piCongrRight fun _ => leafWordsEquiv b).trans (forestInputEquiv _ s order).symm))

noncomputable def wordPairsEquiv (l : ℕ) : (Fin l → Word64) ≃ PairKey l :=
  (Equiv.piCongrRight fun _ => halves32Equiv).trans (Equiv.curry _ _ _).symm

noncomputable def styleInputEquiv {b h roots n l : ℕ} (s : Fin roots → TreeShape 8 h)
    (order : (Σ i, LeafPath (s i)) ≃ Fin n) :
    (Fin (n * (18 * b) + l) → Word64) ≃
      ((∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Word64)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (prefixWordsEquiv s order) (wordPairsEquiv l)))

/-- Number of complete Encode2 leaves and raw blocks. Even an aligned
remainder receives one additional all-zero block, exactly as in the header. -/
def styleGroups (b bytes : ℕ) : ℕ := bytes / (144 * b)
def styleTailBlocks (b bytes : ℕ) : ℕ := bytes % (144 * b) / (8 * b) + 1
def styleTailWords (b bytes : ℕ) : ℕ := styleTailBlocks b bytes * b

theorem styleTailBlocks_le {b bytes : ℕ} (hb : 0 < b) : styleTailBlocks b bytes ≤ 18 := by
  have hp : 0 < 144 * b := by omega
  have hr := Nat.mod_lt bytes hp
  have he : 144 * b = 18 * (8 * b) := by omega
  have hd : bytes % (144 * b) / (8 * b) < 18 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 8 * b)).mpr
    omega
  exact hd

theorem styleTailWords_le {b bytes : ℕ} (hb : 0 < b) : styleTailWords b bytes ≤ 18 * b :=
  Nat.mul_le_mul_right b (styleTailBlocks_le hb)

theorem style_padding_capacity {b bytes : ℕ} (hb : 0 < b) :
    bytes ≤ (styleGroups b bytes * (18 * b) + styleTailWords b bytes) * 8 := by
  have hm := Nat.mod_add_div bytes (144 * b)
  have hd := Nat.mod_add_div (bytes % (144 * b)) (8 * b)
  have hr := Nat.mod_lt (bytes % (144 * b)) (by omega : 0 < 8 * b)
  unfold styleGroups styleTailWords styleTailBlocks
  nlinarith

noncomputable def parseStyle {b h roots bytes : ℕ} (s : Fin roots → TreeShape 8 h)
    (order : (Σ i, LeafPath (s i)) ≃ Fin (styleGroups b bytes)) (x : Fin bytes → Byte) :
    ((∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey (styleTailWords b bytes)) :=
  styleInputEquiv s order (paddedWords x)

theorem parseStyle_injective {b h roots bytes : ℕ} (hb : 0 < b) (s : Fin roots → TreeShape 8 h)
    (order : (Σ i, LeafPath (s i)) ≃ Fin (styleGroups b bytes)) :
    Function.Injective (parseStyle s order) := by
  intro x y he
  exact paddedWords_injective (style_padding_capacity hb) ((styleInputEquiv s order).injective he)

end ProvenHashes.Halftime
