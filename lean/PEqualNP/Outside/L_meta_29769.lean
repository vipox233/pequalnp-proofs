import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620

open scoped BigOperators RealInnerProductSpace

namespace PEqualNP.Outside.L_meta_29769_aux

private def guardBit (α β δ : Bool) (a b c : Bool) : Bool :=
  let f4 := β
  let f5 := xor β (!α)
  let f6 := xor α a
  let f7 := xor β ((!a) && b)
  let f8 := xor δ ((a == b) && c)
  let u := xor (xor f4 f5) f6
  let v := xor (xor f5 f6) f7
  let w := xor (xor f6 f7) f8
  xor u ((!v) && w)

private def tripleBit (α β δ : Bool) (s : Fin 8) : Bool :=
  guardBit α β δ (s.val.testBit 0) (s.val.testBit 1) (s.val.testBit 2)

private def walshBit (r s : Fin 8) : Bool :=
  xor (xor (r.val.testBit 0 && s.val.testBit 0)
    (r.val.testBit 1 && s.val.testBit 1)) (r.val.testBit 2 && s.val.testBit 2)

private def majorFreq (α β δ : Bool) : Fin 8 :=
  if xor (xor α β) δ then 1 else 2

private def heavyPoint (α β δ : Bool) : Fin 8 :=
  if xor (xor α β) δ then 7 else 3

private def localCoeff (α β δ : Bool) (r : Fin 8) : ℤ :=
  ∑ s : Fin 8, if xor (tripleBit α β δ s) (walshBit r s) then -1 else 1

private def weightedCoeff (α β δ : Bool) (r : Fin 8) : ℤ :=
  ∑ s : Fin 8, (if xor (tripleBit α β δ s) (walshBit r s) then -1 else 1) *
    (if s = heavyPoint α β δ then 3 else 1)

private lemma local_spectrum (α β δ : Bool) (r : Fin 8) :
    (localCoeff α β δ r)^2 = if r = majorFreq α β δ then 36 else 4 := by
  cases α <;> cases β <;> cases δ <;> revert r <;> decide

private lemma local_weighted_spectrum (α β δ : Bool) (r : Fin 8) :
    |weightedCoeff α β δ r| ≤ 4 := by
  cases α <;> cases β <;> cases δ <;> revert r <;> decide

-- The round definitions agree with PEqualNP.Outside.L_meta_25620.
private def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

private def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

private def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k))
    ((constant round).val.testBit (pos % k))

private def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

private def oldFn {k : ℕ} (constant : ℕ → Fin (2^k)) (row key : Fin (2^k)) (p j : ℕ) : Bool :=
  bitFn k constant row.val 0 key.val (p + j)

private def firstFn {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (p j : ℕ) : Bool :=
  bitFn k constant row.val 1 ref.val (p + j)

private def tauFn (old : ℕ → Bool) := xor (xor (old 6) (old 7)) (old 8)

private def alphaFn (old : ℕ → Bool) (inj : Bool) := xor (xor (xor (old 5) (old 6)) (old 7)) inj

private def betaFn (old : ℕ → Bool) (inj : Bool) := xor (tauFn old) inj

private def deltaFn (old : ℕ → Bool) (b d : Bool) := xor (xor (xor (old 7) (old 8)) b) d

private def encodeTriple (a b c : Bool) : Fin 8 :=
  ⟨a.toNat + 2 * b.toNat + 4 * c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

private def codeFn (old u : ℕ → Bool) : Fin 8 :=
  encodeTriple (xor (u 9) (xor (old 7) (old 8))) (xor (u 10) (old 7)) (xor (u 11) (old 8))

private def modelFn (old first : ℕ → Bool) (α β δ : Bool) (s j : ℕ) : Bool :=
  let a := s.testBit 0
  let b := s.testBit 1
  let c := s.testBit 2
  if j = 6 then xor α ((!xor (old 6) (xor (old 7) (old 8))) && a)
  else if j = 7 then xor β ((!a) && b)
  else if j = 8 then xor δ ((a == b) && c)
  else first j

private def nextFn (model : ℕ → Bool) (j : ℕ) (inj : Bool) : Bool :=
  let mix := fun h => xor (xor (model (h-1)) (model h)) (model (h+1))
  xor (xor (mix j) (!(mix (j+1)) && mix (j+2))) inj

private lemma nextFn_guarded (old first : ℕ → Bool) (α β δ inj : Bool) (s : Fin 8)
    (hτ : tauFn old = false) (h45 : xor (first 4) (first 5) = !α) (h4 : first 4 = β) :
    nextFn (modelFn old first α β δ s.val) 5 inj = xor (tripleBit α β δ s) inj := by
  have hτ' : xor (old 6) (xor (old 7) (old 8)) = false := by
    simpa [tauFn, Bool.xor_assoc] using hτ
  have h5 : first 5 = xor β (!α) := by
    rw [h4] at h45
    generalize first 5 = b at h45 ⊢
    cases β <;> cases α <;> cases b <;> simp_all
  simp [nextFn, modelFn, hτ', h4, h5, tripleBit, guardBit]

set_option maxHeartbeats 400000 in
private lemma local_bit_of_guard (k : ℕ) (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref q : Fin (2^k)) (p : ℕ)
    (hpin : ∀ j : Fin 9, oldFn constant row q p j.val = oldFn constant row ref p j.val)
    (hτ : tauFn (oldFn constant row ref p) = false)
    (h45 : xor (firstFn constant row ref p 4) (firstFn constant row ref p 5) =
      !(alphaFn (oldFn constant row ref p) (injectedFn k constant 1 ref.val (p+6))))
    (h4 : firstFn constant row ref p 4 =
      betaFn (oldFn constant row ref p) (injectedFn k constant 1 ref.val (p+7))) :
    let old := oldFn constant row ref p
    let α := alphaFn old (injectedFn k constant 1 ref.val (p+6))
    let β := betaFn old (injectedFn k constant 1 ref.val (p+7))
    let δ := deltaFn old (row.val.testBit ((p+9)%k)) ((constant 1).val.testBit ((p+8)%k))
    bitFn k constant row.val 2 q.val (p+5) = xor
      (tripleBit α β δ (codeFn old (oldFn constant row q p))) (injectedFn k constant 2 ref.val (p+5)) := by
  dsimp only
  let old := oldFn constant row ref p
  let first := firstFn constant row ref p
  let α := alphaFn old (injectedFn k constant 1 ref.val (p+6))
  let β := xor (xor (old 6) (xor (old 7) (old 8))) (injectedFn k constant 1 ref.val (p+7))
  let δ := deltaFn old (row.val.testBit ((p+9)%k)) ((constant 1).val.testBit ((p+8)%k))
  let code := codeFn old (oldFn constant row q p)
  let inj := injectedFn k constant 2 ref.val (p+5)
  have hq : q ∈ (Finset.univ : Finset (Fin (2^k))).filter
      (fun v => (List.range 9).all (fun j => oldFn constant row v p j == old j)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true,
      List.mem_range, beq_iff_eq]
    exact fun j hj => hpin ⟨j,hj⟩
  have hbit := ((PEqualNP.Outside.L_meta_25620 k (by omega) constant hk row ref p).1 q hq).2 (3 : Fin 4)
  change bitFn k constant row.val 2 q.val (p+5) =
    nextFn (modelFn old first α β δ code.val) 5 inj at hbit
  have hb : betaFn old (injectedFn k constant 1 ref.val (p+7)) = β := by
    simp [β, betaFn, tauFn]
  have h4' : first 4 = β := h4.trans hb
  have hnext := nextFn_guarded old first α β δ inj code hτ h45 h4'
  rw [show betaFn (oldFn constant row ref p) (injectedFn k constant 1 ref.val (p+7)) = β from hb]
  exact hbit.trans hnext

-- Rotation and initial-round bit lemmas from PEqualNP.Outside.L_meta_25620.
private lemma rotFn_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsm : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hhi : word.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and, hmod]
  · have hlt : i < s % k := by omega
    have hdec : decide (s % k ≤ i) = false := decide_eq_false (by omega)
    have hmod : (i + k - s % k) % k = i + (k - s % k) := by
      have h1 : i + k - s % k = i + (k - s % k) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hdec, Bool.false_and, Bool.false_or, hmod, Nat.add_comm (k - s % k) i]

private lemma mod_sub_one {k n : ℕ} (hk : 1 ≤ k) :
    (n % k + k - 1 % k) % k = (n + k - 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : n % k < k := Nat.mod_lt n (by omega)
    have hrew : n % k + k - 1 = n % k + (k - 1) := by omega
    have hrew2 : n + k - 1 = n + (k - 1) := by omega
    rw [hrew, hrew2, Nat.mod_add_mod]

private lemma bitFn_zero {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    bitFn k constant row 0 key pos =
      xor (key.testBit ((pos + k - 1) % k)) (row.testBit (pos % k)) := by
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]

private lemma key_testBit_from_bit0 {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    key.testBit (pos % k) =
      xor (bitFn k constant row 0 key (pos + 1)) (row.testBit ((pos + 1) % k)) := by
  have h0 := bitFn_zero hk constant (row := row) hkey (pos + 1)
  have hmod : (pos + 1 + k - 1) % k = pos % k := by
    have : pos + 1 + k - 1 = pos + k := by omega
    rw [this, Nat.add_mod_right]
  rw [hmod] at h0
  rw [h0]
  cases key.testBit (pos % k) <;> cases row.testBit ((pos + 1) % k) <;> rfl

private def keyXor {k : ℕ} (x y : Fin (2^k)) : Fin (2^k) :=
  ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow x.isLt y.isLt⟩

private def initialBits {k : ℕ} (constant : ℕ → Fin (2^k)) (row key : Fin (2^k)) (i : Fin k) : Bool :=
  bitFn k constant row.val 0 key.val i.val

private lemma initialBits_mod {k : ℕ} (hk : 0 < k) (constant : ℕ → Fin (2^k))
    (row key : Fin (2^k)) (p : ℕ) :
    initialBits constant row key ⟨p % k, Nat.mod_lt _ hk⟩ = bitFn k constant row.val 0 key.val p := by
  simp [initialBits, bitFn]

private lemma initialBits_xor {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row x y ref : Fin (2^k)) (i : Fin k) :
    initialBits constant row (keyXor (keyXor x y) ref) i =
      xor (xor (initialBits constant row x i) (initialBits constant row y i))
        (initialBits constant row ref i) := by
  unfold initialBits
  rw [bitFn_zero hk constant (keyXor (keyXor x y) ref).isLt,
    bitFn_zero hk constant x.isLt, bitFn_zero hk constant y.isLt, bitFn_zero hk constant ref.isLt]
  simp only [keyXor, Nat.testBit_xor]
  generalize x.val.testBit ((i.val+k-1)%k) = a
  generalize y.val.testBit ((i.val+k-1)%k) = b
  generalize ref.val.testBit ((i.val+k-1)%k) = c
  generalize row.val.testBit (i.val % k) = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma initialBits_injective {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k)) (row : Fin (2^k)) :
    Function.Injective (initialBits constant row) := by
  intro x y heq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have h := congrFun heq ⟨(i+1) % k, Nat.mod_lt _ (by omega)⟩
    have hk0 : 0 < k := by omega
    rw [initialBits_mod hk0, initialBits_mod hk0] at h
    have hi' : i % k = i := Nat.mod_eq_of_lt hi
    rw [← hi', key_testBit_from_bit0 hk constant (row := row.val) x.isLt,
      key_testBit_from_bit0 hk constant (row := row.val) y.isLt, h]
  · have hp : 2^k ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le hp), Nat.testBit_lt_two_pow (y.isLt.trans_le hp)]

private noncomputable def initialEquiv {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row : Fin (2^k)) : Fin (2^k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (initialBits constant row) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨initialBits_injective hk constant row, by simp⟩

private def fiberFn {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (pin : Finset (Fin k)) :
    Finset (Fin (2^k)) :=
  Finset.univ.filter (fun key => ∀ z ∈ pin, initialBits constant row key z = initialBits constant row ref z)

private lemma xor_mem_fiber {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref x y : Fin (2^k)) (pin : Finset (Fin k))
    (hx : x ∈ fiberFn constant row ref pin) (hy : y ∈ fiberFn constant row ref pin) :
    keyXor (keyXor x y) ref ∈ fiberFn constant row ref pin := by
  simp only [fiberFn, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  intro z hz
  rw [initialBits_xor hk, hx z hz, hy z hz]
  cases initialBits constant row ref z <;> rfl

private def restrictBits {ι : Type*} [DecidableEq ι] (pin : Finset ι) (ref : ι → Bool) :
    {f : ι → Bool // ∀ z ∈ pin, f z = ref z} ≃ ({z : ι // z ∉ pin} → Bool) where
  toFun f z := f.val z.val
  invFun g := ⟨fun z => if hz : z ∈ pin then ref z else g ⟨z,hz⟩, by
    intro z hz
    exact dite_eq_left hz⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ pin
    · simpa [hz] using (f.property z hz).symm
    · simp [hz]
  right_inv g := by
    funext z
    simp [z.property]

private noncomputable def fiberEquiv {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) :
    (fiberFn constant row ref pin : Type) ≃ ({z : Fin k // z ∉ pin} → Bool) :=
  (Equiv.subtypeEquiv (initialEquiv hk constant row) (fun key => by simp [fiberFn, initialEquiv])).trans
    (restrictBits pin (initialBits constant row ref))

private def freeIndex {k m : ℕ} (hk : 0 < k) (starts : Fin m → ℕ) (pin : Finset (Fin k))
    (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) (u : Fin m × Fin 3) :
    {z : Fin k // z ∉ pin} :=
  ⟨⟨(starts u.1+9+u.2.val)%k, Nat.mod_lt _ hk⟩, fun hz => hfree u.1 u.2 _ hz rfl⟩

private lemma freeIndex_injective {k m : ℕ} (hk : 0 < k) (starts : Fin m → ℕ) (pin : Finset (Fin k))
    (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k)) :
    Function.Injective (freeIndex hk starts pin hfree) := by
  intro u v h
  have hj := congrArg (fun z : {z : Fin k // z ∉ pin} => z.val.val) h
  have hup : (u.1, (⟨9+u.2.val, by have := u.2.isLt; omega⟩ : Fin 12)) =
      (v.1, ⟨9+v.2.val, by have := v.2.isLt; omega⟩) := hdist (by simpa [freeIndex, Nat.add_assoc] using hj)
  refine Prod.ext (congrArg (fun z : Fin m × Fin 12 => z.1) hup) ?_
  apply Fin.ext
  have he := congrArg (fun z : Fin m × Fin 12 => z.2.val) hup
  dsimp at he
  omega

private noncomputable def splitBits {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    (κ → Bool) ≃ (ι → Bool) × (((Set.range f)ᶜ : Set κ) → Bool) := by
  classical
  exact (Equiv.arrowCongr
    (((Equiv.ofInjective f hf).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range f))).symm
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private def tripleEquiv : (Fin 3 → Bool) ≃ Fin 8 where
  toFun g := encodeTriple (g 0) (g 1) (g 2)
  invFun s j := s.val.testBit j.val
  left_inv g := by
    funext j
    change (encodeTriple (g 0) (g 1) (g 2)).val.testBit j.val = g j
    generalize ha : g 0 = a
    generalize hb : g 1 = b
    generalize hc : g 2 = c
    fin_cases j
    · change (encodeTriple a b c).val.testBit 0 = g 0
      rw [ha]
      cases a <;> cases b <;> cases c <;> rfl
    · change (encodeTriple a b c).val.testBit 1 = g 1
      rw [hb]
      cases a <;> cases b <;> cases c <;> rfl
    · change (encodeTriple a b c).val.testBit 2 = g 2
      rw [hc]
      cases a <;> cases b <;> cases c <;> rfl
  right_inv s := by revert s; decide

private def xorBits (tag : Fin 3 → Bool) : (Fin 3 → Bool) ≃ (Fin 3 → Bool) where
  toFun f j := xor (f j) (tag j)
  invFun f j := xor (f j) (tag j)
  left_inv f := by
    funext j
    change xor (xor (f j) (tag j)) (tag j) = f j
    cases f j <;> cases tag j <;> rfl
  right_inv f := by
    funext j
    change xor (xor (f j) (tag j)) (tag j) = f j
    cases f j <;> cases tag j <;> rfl

private noncomputable def fiberCoords {k m : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) (starts : Fin m → ℕ)
    (hk0 : 0 < k) (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k))
    (tag : Fin m → Fin 3 → Bool) :
    (fiberFn constant row ref pin : Type) ≃
      (Fin m → Fin 8) × (((Set.range (freeIndex hk0 starts pin hfree))ᶜ : Set _) → Bool) :=
  (fiberEquiv hk constant row ref pin).trans
    ((splitBits _ (freeIndex_injective hk0 starts pin hfree hdist)).trans
      (((Equiv.curry _ _ Bool).trans (Equiv.piCongrRight fun i => (xorBits (tag i)).trans tripleEquiv)).prodCongr
        (Equiv.refl _)))

private lemma fiberCoords_bit {k m : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) (starts : Fin m → ℕ)
    (hk0 : 0 < k) (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k))
    (tag : Fin m → Fin 3 → Bool) (q : fiberFn constant row ref pin) (i : Fin m) (j : Fin 3) :
    ((fiberCoords hk constant row ref pin starts hk0 hfree hdist tag q).1 i).val.testBit j.val =
      xor (oldFn constant row q.val (starts i) (9+j.val)) (tag i j) := by
  let g : Fin 3 → Bool := fun j => xor
    (initialBits constant row q.val (freeIndex hk0 starts pin hfree (i,j)).val) (tag i j)
  change (tripleEquiv.symm (tripleEquiv g)) j = _
  rw [Equiv.symm_apply_apply]
  change xor (initialBits constant row q.val ⟨(starts i+9+j.val)%k, _⟩) (tag i j) = _
  rw [initialBits_mod hk0]
  simp only [oldFn, Nat.add_assoc]

private def codeTag (old : ℕ → Bool) (j : Fin 3) : Bool :=
  if j = 0 then xor (old 7) (old 8) else if j = 1 then old 7 else old 8

private lemma codeFn_bit (old g : ℕ → Bool) (j : Fin 3) :
    (codeFn old g).val.testBit j.val = xor (g (9+j.val)) (codeTag old j) := by
  have h : codeFn old g = tripleEquiv (fun j => xor (g (9+j.val)) (codeTag old j)) := by
    simp [codeFn, tripleEquiv, codeTag]
  rw [h]
  exact congrFun (tripleEquiv.left_inv _) j

private lemma oldFn_xor {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row x y ref : Fin (2^k)) (p j : ℕ) :
    oldFn constant row (keyXor (keyXor x y) ref) p j =
      xor (xor (oldFn constant row x p j) (oldFn constant row y p j))
        (oldFn constant row ref p j) := by
  have hk0 : 0 < k := by omega
  simpa only [initialBits_mod hk0, oldFn] using
    initialBits_xor hk constant row x y ref ⟨(p+j)%k, Nat.mod_lt _ hk0⟩

private lemma fiberCoords_xor {k m : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) (starts : Fin m → ℕ)
    (hk0 : 0 < k) (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k))
    (x y : fiberFn constant row ref pin) (i : Fin m) :
    let old := oldFn constant row ref (starts i)
    let left := fiberCoords hk constant row ref pin starts hk0 hfree hdist
      (fun i => codeTag (oldFn constant row ref (starts i)))
    let right := fiberCoords hk constant row ref pin starts hk0 hfree hdist
      (fun i j => oldFn constant row ref (starts i) (9+j.val))
    codeFn old (oldFn constant row (keyXor (keyXor x.val y.val) ref) (starts i)) =
      keyXor (k := 3) ((left x).1 i) ((right y).1 i) := by
  dsimp only
  apply tripleEquiv.symm.injective
  funext j
  change (codeFn _ _).val.testBit j.val = (keyXor _ _).val.testBit j.val
  rw [codeFn_bit, oldFn_xor hk]
  simp only [keyXor, Nat.testBit_xor, fiberCoords_bit]
  generalize oldFn constant row x.val (starts i) (9+j.val) = a
  generalize oldFn constant row y.val (starts i) (9+j.val) = b
  generalize codeTag (oldFn constant row ref (starts i)) j = d
  generalize oldFn constant row ref (starts i) (9+j.val) = e
  cases a <;> cases b <;> cases d <;> cases e <;> rfl

private lemma width_of_layout {k m : ℕ} (hm : 0 < m) (hk0 : 0 < k) (starts : Fin m → ℕ)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k)) : 12 ≤ k := by
  let base : Fin m := ⟨0, hm⟩
  let f : Fin 12 → Fin k := fun j => ⟨(starts base+j.val)%k, Nat.mod_lt _ hk0⟩
  have hf : Function.Injective f := by
    intro x y h
    have hp : ((base,x) : Fin m × Fin 12) = (base,y) :=
      hdist (congrArg (fun z : Fin k => z.val) h)
    exact congrArg Prod.snd hp
  simpa using Fintype.card_le_of_injective f hf

private lemma local_pin {k m : ℕ} (hk0 : 0 < k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) (starts : Fin m → ℕ)
    (hpin : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k)
    (q : Fin (2^k)) (hq : q ∈ fiberFn constant row ref pin) (i : Fin m) (j : Fin 9) :
    oldFn constant row q (starts i) j.val = oldFn constant row ref (starts i) j.val := by
  obtain ⟨z, hz, he⟩ := hpin i j
  have h := (Finset.mem_filter.mp hq).2 z hz
  have hz' : z = ⟨(starts i+j.val)%k, Nat.mod_lt _ hk0⟩ := Fin.ext he
  rw [hz', initialBits_mod hk0, initialBits_mod hk0] at h
  exact h

section Projection

variable {I J Q E : Type*} [Fintype I] [Fintype J] [Fintype Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem guardedProjection_inner (U : Submodule ℝ E) (v w : E) (hw : w ∈ U) :
    ⟪U.starProjection v, w⟫ = ⟪v, w⟫ := by
  have h := U.starProjection_inner_eq_zero v w hw
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm


private theorem guardedProjection_sum (U : Submodule ℝ E) (b : I → E)
    (hb : Orthonormal ℝ b) :
    ∑ i, ‖U.starProjection (b i)‖ ^ 2 ≤ (Module.finrank ℝ U : ℝ) := by
  let a := stdOrthonormalBasis ℝ U
  have hn (v : E) : ‖U.starProjection v‖ ^ 2 = ∑ j, ⟪(a j : E), v⟫ ^ 2 := by
    rw [Submodule.starProjection_apply, Submodule.norm_coe, ← a.sum_sq_inner_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Submodule.coe_inner, ← Submodule.starProjection_apply,
      real_inner_comm (U.starProjection v) (a j : E),
      guardedProjection_inner _ _ _ (a j).property, real_inner_comm (a j : E) v]
  simp_rw [hn]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin (Module.finrank ℝ U), ‖(a j : E)‖ ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      simp_rw [← real_inner_comm (a j : E)]
      simpa [Real.norm_eq_abs] using
        hb.sum_inner_products_le (s := Finset.univ) (a j : E)
    _ = _ := by simp_rw [Submodule.norm_coe, a.orthonormal.1]; simp

private theorem guardedProjection_norm [DecidableEq I] (U : Submodule ℝ E) (b : I → E)
    (eig : I → ℝ) (coord : I → J → ℝ)
    (hcoord : ∀ i j, (∑ y, coord i y * coord j y) = if i = j then 1 else 0) :
    (∑ y, ‖U.starProjection (∑ i, (eig i * coord i y) • b i)‖ ^ 2) =
      ∑ i, eig i ^ 2 * ‖U.starProjection (b i)‖ ^ 2 := by
  classical
  let p := fun i => U.starProjection (b i)
  have hexp (y : J) :
      ‖U.starProjection (∑ i, (eig i * coord i y) • b i)‖ ^ 2 =
        ∑ i, ∑ j, (coord i y * coord j y) * (eig i * eig j * ⟪p j, p i⟫) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, p]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcoord]
  rw [Finset.sum_eq_single i]
  · simp [p, pow_two]
  · intro j _ hji
    simp [hji.symm]
  · simp

private theorem guardedProjection_corr [DecidableEq I] (b : I → E)
    (hb : Orthonormal ℝ b) (eig : I → ℝ)
    (coord : I → J → ℝ)
    (hcoord : ∀ i j, (∑ y, coord i y * coord j y) = if i = j then 1 else 0)
    (pred : J → E) (gen : Q → E) (coef : Q → J → ℝ)
    (hpred : ∀ y, pred y = ∑ q, coef q y • gen q) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ (∑ i, w i) ≤ Fintype.card Q ∧
      (∑ y, ⟪∑ i, (eig i * coord i y) • b i, pred y⟫) ^ 2 ≤
      (∑ y, ‖pred y‖ ^ 2) * (∑ i, eig i ^ 2 * w i) := by
  classical
  let U := Submodule.span ℝ (Set.range gen)
  let truth : J → E := fun y => ∑ i, (eig i * coord i y) • b i
  refine ⟨fun i => ‖U.starProjection (b i)‖ ^ 2, ?_, ?_, ?_⟩
  · intro i
    refine ⟨sq_nonneg _, ?_⟩
    have h := U.norm_starProjection_apply_le (b i)
    rw [hb.1] at h
    simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr h
  · have hf : Module.finrank ℝ U ≤ Fintype.card Q := finrank_range_le_card gen
    exact (guardedProjection_sum U b hb).trans (by exact_mod_cast hf)
  · have hmem (y : J) : pred y ∈ U := by
      rw [hpred y]
      exact U.sum_mem fun q _ => U.smul_mem _ (Submodule.subset_span ⟨q, rfl⟩)
    have hinner (y : J) := guardedProjection_inner U (truth y) (pred y) (hmem y)
    change (∑ y, ⟪truth y, pred y⟫) ^ 2 ≤
      (∑ y, ‖pred y‖ ^ 2) * (∑ i, eig i ^ 2 * ‖U.starProjection (b i)‖ ^ 2)
    rw [← guardedProjection_norm U b eig coord hcoord]
    simp_rw [← hinner]
    rw [← sq_abs (∑ y, ⟪U.starProjection (truth y), pred y⟫)]
    calc
      _ ≤ (∑ y, ‖pred y‖ * ‖U.starProjection (truth y)‖) ^ 2 := by
        refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_))
        rw [mul_comm]
        exact abs_real_inner_le_norm ..
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end Projection

private def guardedXor8 (a b : Fin 8) : Fin 8 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt⟩

private def guardedCharInt (r x : Fin 8) : ℤ :=
  if walshBit r x then -1 else 1

private noncomputable def guardedChar (r x : Fin 8) : ℝ :=
  (guardedCharInt r x : ℝ)

private theorem guardedChar_eq (r x : Fin 8) :
    guardedChar r x = if walshBit r x then -1 else 1 := by
  cases h : walshBit r x <;> simp [guardedChar, guardedCharInt, h]

private theorem guardedChar_gramInt : ∀ r s : Fin 8,
    (∑ x : Fin 8, guardedCharInt r x * guardedCharInt s x) =
      if r = s then 8 else 0 := by decide

private theorem guardedChar_gram (r s : Fin 8) :
    (∑ x : Fin 8, guardedChar r x * guardedChar s x) =
      if r = s then 8 else 0 := by
  by_cases hrs : r = s
  · simpa [hrs, guardedChar] using congrArg (fun z : ℤ => (z : ℝ))
      (guardedChar_gramInt r s)
  · simpa [hrs, guardedChar] using congrArg (fun z : ℤ => (z : ℝ))
      (guardedChar_gramInt r s)

private theorem guardedChar_invInt : ∀ a b u : Fin 8,
    (∑ r : Fin 8, guardedCharInt r u * guardedCharInt r a * guardedCharInt r b) =
      if u = guardedXor8 a b then 8 else 0 := by decide

private theorem guardedChar_inv (a b u : Fin 8) :
    (∑ r : Fin 8, guardedChar r u * guardedChar r a * guardedChar r b) =
      if u = guardedXor8 a b then 8 else 0 := by
  by_cases h : u = guardedXor8 a b
  · simpa [h, guardedChar] using congrArg (fun z : ℤ => (z : ℝ))
      (guardedChar_invInt a b u)
  · simpa [h, guardedChar] using congrArg (fun z : ℤ => (z : ℝ))
      (guardedChar_invInt a b u)

private theorem guardedLocal_synthesis (f : Fin 8 → ℝ) (a b : Fin 8) :
    (∑ r, (∑ u, f u * guardedChar r u) * guardedChar r a * guardedChar r b) =
      8 * f (guardedXor8 a b) := by
  calc
    _ = ∑ r, ∑ u, f u * (guardedChar r u * guardedChar r a * guardedChar r b) := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => by ring
    _ = ∑ u, f u * (if u = guardedXor8 a b then 8 else 0) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, guardedChar_inv]
    _ = _ := by simp [mul_comm]

private theorem guardedTensor_gram {m : ℕ} (r s : Fin m → Fin 8) :
    (∑ x : Fin m → Fin 8, (∏ i, guardedChar (r i) (x i)) * (∏ i, guardedChar (s i) (x i))) =
      if r = s then (8 : ℝ) ^ m else 0 := by
  classical
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun _ : Fin m => Fin 8)
    (fun i u => guardedChar (r i) u * guardedChar (s i) u)]
  simp only [guardedChar_gram]
  by_cases h : r = s
  · simp [h]
  · rw [ite_eq_right h]
    have hne : ∃ i, r i ≠ s i := by
      by_contra! hne
      exact h (funext hne)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private noncomputable def guardedTensor_coord {m : ℕ} {S : Type*} [Fintype S]
    (r : Fin m → Fin 8) (x : (Fin m → Fin 8) × S) : ℝ :=
  (∏ i, guardedChar (r i) (x.1 i)) / Real.sqrt ((8 : ℝ)^m * (Fintype.card S : ℝ))

private theorem guardedTensor_coord_gram {m : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (r s : Fin m → Fin 8) :
    (∑ x : (Fin m → Fin 8) × S, guardedTensor_coord r x * guardedTensor_coord s x) =
      if r = s then 1 else 0 := by
  classical
  have hs : 0 < (Fintype.card S : ℝ) := by exact_mod_cast (Fintype.card_pos (α := S))
  have hpow : 0 < (8 : ℝ)^m := by positivity
  have hsqrt := Real.sq_sqrt (mul_nonneg hpow.le hs.le)
  simp only [guardedTensor_coord, div_mul_div_comm, ← pow_two, ← Finset.sum_div, hsqrt]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, guardedTensor_gram]
  by_cases hrs : r = s
  · simp [hrs, mul_comm ((8 : ℝ)^m)]
  · simp [hrs]

private noncomputable def guardedTensor_vec {m : ℕ} {S : Type*} [Fintype S]
    (r : Fin m → Fin 8) : EuclideanSpace ℝ ((Fin m → Fin 8) × S) :=
  WithLp.toLp 2 (guardedTensor_coord r)

private theorem guardedTensor_orthonormal {m : ℕ} {S : Type*} [Fintype S] [Nonempty S] :
    Orthonormal ℝ (guardedTensor_vec (m := m) (S := S)) := by
  classical
  rw [orthonormal_iff_ite]
  intro r s
  rw [PiLp.inner_apply]
  simpa [guardedTensor_vec, RCLike.inner_apply, mul_comm] using
    guardedTensor_coord_gram (S := S) r s

private noncomputable def guardedTensor_eig {m : ℕ} (S : Type*) [Fintype S]
    (f : Fin m → Fin 8 → ℝ) (r : Fin m → Fin 8) : ℝ :=
  (Fintype.card S : ℝ) * (∏ i, ∑ u, f i u * guardedChar (r i) u)

private theorem guardedTensor_synthesis {m : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (f : Fin m → Fin 8 → ℝ) (y : (Fin m → Fin 8) × S) :
    (WithLp.toLp 2 (fun x : (Fin m → Fin 8) × S =>
      ∏ i, f i (guardedXor8 (x.1 i) (y.1 i))) : EuclideanSpace ℝ _) =
      ∑ r, (guardedTensor_eig S f r * guardedTensor_coord r y) • guardedTensor_vec r := by
  classical
  let X := (Fin m → Fin 8) × S
  let e := EuclideanSpace.equiv X ℝ
  apply e.injective
  rw [map_sum]
  funext x
  rw [Finset.sum_apply]
  change (∏ i, f i (guardedXor8 (x.1 i) (y.1 i))) =
    ∑ r, (guardedTensor_eig S f r * guardedTensor_coord r y) * guardedTensor_coord r x
  let coeff := fun i r => ∑ u, f i u * guardedChar r u
  have hs : 0 < (Fintype.card S : ℝ) := by exact_mod_cast (Fintype.card_pos (α := S))
  have hpow : 0 < (8 : ℝ)^m := by positivity
  have hsqrt := Real.sq_sqrt (mul_nonneg hpow.le hs.le)
  have hval (r : Fin m → Fin 8) :
      (guardedTensor_eig S f r * guardedTensor_coord r y) * guardedTensor_coord r x =
        (∏ i, coeff i (r i) * guardedChar (r i) (x.1 i) * guardedChar (r i) (y.1 i)) / (8 : ℝ)^m := by
    simp only [guardedTensor_eig, guardedTensor_coord, Finset.prod_mul_distrib, coeff]
    rw [mul_assoc, div_mul_div_comm, ← pow_two, hsqrt]
    field_simp
  simp_rw [hval]
  rw [← Finset.sum_div, ← Fintype.prod_sum (κ := fun _ : Fin m => Fin 8)
    (fun i u => coeff i u * guardedChar u (x.1 i) * guardedChar u (y.1 i))]
  simp_rw [coeff, guardedLocal_synthesis, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

private theorem guardedEuclidean_inner {X : Type*} [Fintype X] (a b : X → ℝ) :
    ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ X), WithLp.toLp 2 b⟫ = ∑ x, a x * b x := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

private theorem guardedTensor_corr {m : ℕ} {S Q : Type*} [Fintype S] [Nonempty S] [Fintype Q]
    (f : Fin m → Fin 8 → ℝ)
    (pred : ((Fin m → Fin 8) × S) → ((Fin m → Fin 8) × S) → ℝ)
    (a b : Q → ((Fin m → Fin 8) × S) → ℝ)
    (hpred : ∀ x y, pred x y = ∑ q, a q x * b q y)
    (hunit : ∀ x y, (pred x y) ^ 2 = 1) :
    ∃ w : (Fin m → Fin 8) → ℝ, (∀ r, 0 ≤ w r ∧ w r ≤ 1) ∧ (∑ r, w r) ≤ Fintype.card Q ∧
      (∑ x, ∑ y, (∏ i, f i (guardedXor8 (x.1 i) (y.1 i))) * pred x y) ^ 2 ≤
        (Fintype.card ((Fin m → Fin 8) × S) : ℝ) ^ 2 * (∑ r, guardedTensor_eig S f r ^ 2 * w r) := by
  classical
  let X := (Fin m → Fin 8) × S
  let predCol : X → EuclideanSpace ℝ X := fun y => WithLp.toLp 2 (fun x => pred x y)
  let gen : Q → EuclideanSpace ℝ X := fun q => WithLp.toLp 2 (a q)
  have hfactors (y : X) : predCol y = ∑ q, (b q y) • gen q := by
    apply (EuclideanSpace.equiv X ℝ).injective
    rw [map_sum]
    funext x
    rw [Finset.sum_apply]
    change pred x y = ∑ q, b q y * a q x
    simpa only [mul_comm] using hpred x y
  obtain ⟨w, hw, hsum, hcorr⟩ := guardedProjection_corr
    (guardedTensor_vec (m := m) (S := S)) guardedTensor_orthonormal
    (guardedTensor_eig S f) (guardedTensor_coord (m := m) (S := S))
    (guardedTensor_coord_gram (S := S)) predCol gen b hfactors
  refine ⟨w, hw, hsum, ?_⟩
  have hnorm (y : X) : ‖predCol y‖ ^ 2 = (Fintype.card X : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [predCol, guardedEuclidean_inner, ← pow_two, hunit]
    simp
  have henergy : (∑ y : X, ‖predCol y‖ ^ 2) = (Fintype.card X : ℝ) ^ 2 := by
    simp [hnorm, nsmul_eq_mul, pow_two]
  rw [henergy] at hcorr
  simp_rw [← guardedTensor_synthesis f, predCol, guardedEuclidean_inner] at hcorr
  rwa [Finset.sum_comm] at hcorr

private theorem guardedTensor_card {m : ℕ} {S : Type*} [Fintype S] :
    (Fintype.card ((Fin m → Fin 8) × S) : ℝ) = (8 : ℝ)^m * (Fintype.card S : ℝ) := by
  simp

private theorem guardedXor8_involutive : ∀ a b : Fin 8,
    guardedXor8 a (guardedXor8 a b) = b := by decide

private def guardedXor8_equiv (a : Fin 8) : Fin 8 ≃ Fin 8 where
  toFun := guardedXor8 a
  invFun := guardedXor8 a
  left_inv := guardedXor8_involutive a
  right_inv := guardedXor8_involutive a

private theorem guardedXor8_sum (a : Fin 8) (w : Fin 8 → ℝ) :
    (∑ b, w (guardedXor8 a b)) = ∑ b, w b :=
  Fintype.sum_equiv (guardedXor8_equiv a) _ _ (fun _ => rfl)

private theorem guardedTensor_row_sum {m : ℕ} {S : Type*} [Fintype S]
    (w : Fin m → Fin 8 → ℝ) (x : (Fin m → Fin 8) × S) :
    (∑ y : (Fin m → Fin 8) × S, ∏ i, w i (guardedXor8 (x.1 i) (y.1 i))) =
      (Fintype.card S : ℝ) * ∏ i, ∑ u, w i u := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (κ := fun _ : Fin m => Fin 8) (fun i u => w i (guardedXor8 (x.1 i) u))]
  simp only [guardedXor8_sum]

private theorem guardedHeavy_weight_sum (heavy : Fin 8) :
    (∑ u : Fin 8, if u = heavy then (3 : ℝ) else 1) = 10 := by
  calc
    _ = ∑ u : Fin 8, (1 + if u = heavy then (2 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      split <;> norm_num
    _ = _ := by norm_num [Finset.sum_add_distrib]

private theorem guardedTensor_heavy_sum {m : Nat} {S : Type*} [Fintype S]
    (heavy : Fin m → Fin 8) :
    (∑ x : (Fin m → Fin 8) × S, ∑ y : (Fin m → Fin 8) × S,
      ∏ i, if guardedXor8 (x.1 i) (y.1 i) = heavy i then (3 : ℝ) else 1) =
      (Fintype.card S : ℝ)^2 * (80 : ℝ)^m := by
  let w : Fin m → Fin 8 → ℝ := fun i u => if u = heavy i then 3 else 1
  change (∑ x : (Fin m → Fin 8) × S, ∑ y : (Fin m → Fin 8) × S,
    ∏ i, w i (guardedXor8 (x.1 i) (y.1 i))) = _
  simp_rw [guardedTensor_row_sum, w, guardedHeavy_weight_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.prod_const,
    Fintype.card_fin, guardedTensor_card]
  rw [show (80 : ℝ)^m = (8 : ℝ)^m * (10 : ℝ)^m by rw [← mul_pow]; norm_num]
  ring

private def guardedLog {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    let q := guardedLog alice speak x y t
    q + (speak t q (if alice t q then x else y)).toNat * 2^t

private theorem guardedLog_foldl {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c : Nat) :
    guardedLog alice speak x y c =
      (List.range c).foldl (fun log t =>
        let v := speak t log (if alice t log then x else y)
        log + (v.toNat <<< t)) 0 := by
  induction c with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.shiftLeft_eq, guardedLog, ih]

private theorem guardedLog_lt {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c : Nat) :
    guardedLog alice speak x y c < 2^c := by
  induction c with
  | zero => simp [guardedLog]
  | succ t ih =>
    rw [guardedLog, Nat.pow_succ]
    have hb := Bool.toNat_le (speak t (guardedLog alice speak x y t)
      (if alice t (guardedLog alice speak x y t) then x else y))
    have hm := Nat.mul_le_mul_right (2^t) hb
    omega

private def guardedAccept {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (side : Bool) (x : X) : Nat → Nat → Prop
  | 0, q => q = 0
  | t+1, q =>
    let prev := q % 2^t
    guardedAccept alice speak side x t prev ∧
      (alice t prev = side → prev + (speak t prev x).toNat * 2^t = q)

private theorem guardedLog_rect {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c q : Nat) :
    guardedLog alice speak x y c = q ↔
      guardedAccept alice speak true x c q ∧
      guardedAccept alice speak false y c q := by
  induction c generalizing q with
  | zero =>
    simp [guardedLog, guardedAccept, eq_comm]
  | succ t ih =>
    let prev := q % 2^t
    have hmod : guardedLog alice speak x y (t+1) % 2^t = guardedLog alice speak x y t := by
      rw [guardedLog, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (guardedLog_lt ..)]
    rw [guardedAccept, guardedAccept]
    change guardedLog alice speak x y (t+1) = q ↔
      (guardedAccept alice speak true x t prev ∧ _) ∧
      (guardedAccept alice speak false y t prev ∧ _)
    constructor
    · intro h
      have hp : guardedLog alice speak x y t = prev := by rw [← hmod, h]
      have ha := (ih prev).mp hp
      rw [guardedLog] at h
      rw [hp] at h
      exact ⟨⟨ha.1, fun ea => by
          change alice t prev = true at ea
          simpa [ea] using h⟩,
        ⟨ha.2, fun eb => by
          change alice t prev = false at eb
          simpa [eb] using h⟩⟩
    · rintro ⟨⟨ha, ea⟩, ⟨hb, eb⟩⟩
      have hp := (ih prev).mpr ⟨ha, hb⟩
      rw [guardedLog, hp]
      cases e : alice t prev with
      | false => simpa [e] using eb e
      | true => simpa [e] using ea e

private theorem guardedLog_factor {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (bob : Nat → X → Bool) (c : Nat)
    (sgn : Bool → ℝ) :
    ∃ a b : Fin (2^c) → X → ℝ,
      ∀ q x y,
        a q x * b q y = if guardedLog alice speak x y c = q then sgn (bob q y) else 0 := by
  classical
  refine ⟨fun q x => if guardedAccept alice speak true x c q then 1 else 0,
    fun q y => if guardedAccept alice speak false y c q then sgn (bob q y) else 0, ?_⟩
  intro q x y
  simp only [guardedLog_rect]
  by_cases ha : guardedAccept alice speak true x c q <;>
    by_cases hb : guardedAccept alice speak false y c q <;> simp [ha, hb]

private theorem guardedLog_sum {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (bob : Nat → X → Bool) (c : Nat)
    (sgn : Bool → ℝ) :
    ∃ a b : Fin (2^c) → X → ℝ, ∀ x y,
      (∑ q, a q x * b q y) =
        sgn (bob ((List.range c).foldl (fun log t =>
          log + ((speak t log (if alice t log then x else y)).toNat <<< t)) 0) y) ∧
      (∑ q, (a q x * b q y)^2) =
        (sgn (bob ((List.range c).foldl (fun log t =>
          log + ((speak t log (if alice t log then x else y)).toNat <<< t)) 0) y))^2 := by
  classical
  obtain ⟨a, b, hab⟩ := guardedLog_factor alice speak bob c sgn
  refine ⟨a, b, fun x y => ?_⟩
  rw [← guardedLog_foldl]
  let q₀ : Fin (2^c) := ⟨guardedLog alice speak x y c, guardedLog_lt ..⟩
  have zero_of_ne (q : Fin (2^c)) (hq : q ≠ q₀) : a q x * b q y = 0 := by
    rw [hab, ite_eq_right]
    exact fun e => hq (Fin.ext e.symm)
  constructor
  · rw [Finset.sum_eq_single q₀ (fun q _ hq => zero_of_ne q hq) (by simp),
        hab, ite_eq_left rfl]
  · rw [Finset.sum_eq_single q₀ (fun q _ hq => by rw [zero_of_ne q hq]; norm_num)
        (by simp), hab, ite_eq_left rfl]

private noncomputable def guardedBoolSign (b : Bool) : ℝ :=
  if b then -1 else 1

private theorem guardedBoolSign_sq (b : Bool) : guardedBoolSign b ^ 2 = 1 := by
  cases b <;> norm_num [guardedBoolSign]

private theorem guardedBoolSign_agree (a b : Bool) :
    (if a = b then (1 : ℝ) else -1) = guardedBoolSign b * guardedBoolSign a := by
  cases a <;> cases b <;> norm_num [guardedBoolSign]

private theorem guardedAveraging_sq {Z : Type*} [Fintype Z] (mass vals : Z → ℝ)
    (hn : ∀ z, 0 ≤ mass z) (hm : (∑ z, mass z) = 1) :
    (∑ z, mass z * vals z) ^ 2 ≤ ∑ z, mass z * vals z ^ 2 := by
  have hsq (z : Z) := Real.sq_sqrt (hn z)
  simpa only [← mul_assoc, ← pow_two (Real.sqrt _), hsq, mul_pow, hm, one_mul] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun z => Real.sqrt (mass z)) (fun z => Real.sqrt (mass z) * vals z)

private theorem guardedAveraging_bound {Z : Type*} [Fintype Z] (mass vals : Z → ℝ)
    (hn : ∀ z, 0 ≤ mass z) (hm : (∑ z, mass z) = 1) (scale bound : ℝ)
    (hscale : 0 ≤ scale) (hbound : ∀ z, scale * vals z ^ 2 ≤ bound) :
    scale * (∑ z, mass z * vals z) ^ 2 ≤ bound := by
  calc
    _ ≤ scale * (∑ z, mass z * vals z ^ 2) :=
      mul_le_mul_of_nonneg_left (guardedAveraging_sq mass vals hn hm) hscale
    _ = ∑ z, mass z * (scale * vals z ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ ∑ z, mass z * bound :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hbound z) (hn z)
    _ = _ := by rw [← Finset.sum_mul, hm, one_mul]

private theorem guardedPublicCoin_corr {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (mass : Z → ℝ) (prob : X → Y → ℝ) (truth : X → Y → Bool) (pred : Z → X → Y → Bool) :
    (∑ x, ∑ y, prob x y * ∑ z, mass z *
      (if pred z x y = truth x y then (1 : ℝ) else -1)) =
    ∑ z, mass z * (∑ x, ∑ y, (prob x y * guardedBoolSign (truth x y)) *
      guardedBoolSign (pred z x y)) := by
  simp_rw [guardedBoolSign_agree, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ y, ∑ z, mass z * ((prob x y * guardedBoolSign (truth x y)) *
      guardedBoolSign (pred z x y)) := by
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ x, ∑ z, ∑ y, mass z * ((prob x y * guardedBoolSign (truth x y)) *
      guardedBoolSign (pred z x y)) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem guardedProbability_minimum {X Y : Type*} [Fintype X] [Fintype Y]
    (prob bias : X → Y → ℝ) (hp : ∀ x y, 0 ≤ prob x y)
    (hsum : (∑ x, ∑ y, prob x y) = 1) (adv : ℝ) (hadv : ∀ x y, adv ≤ bias x y) :
    adv ≤ ∑ x, ∑ y, prob x y * bias x y := by
  calc
    adv = ∑ x, ∑ y, prob x y * adv := by simp_rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hadv x y) (hp x y)

def allocateSlots (cap : Nat → Nat) (budget i : Nat) : Nat :=
  min (cap i) (budget - ∑ j ∈ Finset.range i, cap j)

theorem slots_prefix (cap : Nat → Nat) (budget n : Nat) :
    (∑ i ∈ Finset.range n, allocateSlots cap budget i) =
      min budget (∑ i ∈ Finset.range n, cap i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold allocateSlots
    omega


theorem weighted_majorization (u v w : Nat → ℝ)
    (hPrefix : ∀ n, ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, v i)
    (decreasing : ∀ n, w (n+1) ≤ w n)
    (nonneg : ∀ n, 0 ≤ w n) (n : Nat) :
    ∑ i ∈ Finset.range n, u i * w i ≤ ∑ i ∈ Finset.range n, v i * w i := by
  have strong (j : Nat) :
      (∑ i ∈ Finset.range j, u i * w i) - (∑ i ∈ Finset.range j, v i * w i) ≤
      ((∑ i ∈ Finset.range j, u i) - (∑ i ∈ Finset.range j, v i)) * w j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        _ ≤ ((∑ i ∈ Finset.range (j+1), u i) - (∑ i ∈ Finset.range (j+1), v i)) * w j := by
          simp only [Finset.sum_range_succ]
          linarith only [ih, show
            (((∑ i ∈ Finset.range j, u i) + u j) - ((∑ i ∈ Finset.range j, v i) + v j)) * w j =
              ((∑ i ∈ Finset.range j, u i) - (∑ i ∈ Finset.range j, v i)) * w j +
                (u j * w j - v j * w j) by ring]
        _ ≤ _ := mul_le_mul_of_nonpos_left (decreasing j) (sub_nonpos.mpr (hPrefix (j+1)))
  have hle := (strong n).trans (mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hPrefix n)) (nonneg n))
  exact sub_nonpos.mp hle


theorem weighted_slots (cap : Nat → Nat) (budget : Nat) (mass value : Nat → ℝ)
    (massNonneg : ∀ j, 0 ≤ mass j) (capacity : ∀ j, mass j ≤ cap j)
    (decreasing : ∀ j, value (j+1) ≤ value j) (valuesNonneg : ∀ j, 0 ≤ value j)
    (n : Nat) (total : (∑ j ∈ Finset.range n, mass j) ≤ budget) :
    ∑ j ∈ Finset.range n, mass j * value j ≤
      ∑ j ∈ Finset.range n, (allocateSlots cap budget j : ℝ) * value j := by
  let u := fun j => if j < n then mass j else 0
  have hmaj : ∀ t, (∑ j ∈ Finset.range t, u j) ≤ ∑ j ∈ Finset.range t, (allocateSlots cap budget j : ℝ) := by
    intro t
    have hCap : (∑ j ∈ Finset.range t, u j) ≤ ∑ j ∈ Finset.range t, (cap j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      unfold u
      split
      · exact capacity j
      · positivity
    have hBudget : (∑ j ∈ Finset.range t, u j) ≤ budget := by
      by_cases h : t ≤ n
      · apply le_trans ?_ total
        calc
          _ ≤ ∑ j ∈ Finset.range t, mass j := by
            apply Finset.sum_le_sum
            intro j hj
            have hjn := (Finset.mem_range.mp hj).trans_le h
            simp [u, hjn]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono h) (fun j _ _ => massNonneg j)
      · have ht : n ≤ t := by omega
        apply le_trans ?_ total
        have hm := Finset.sum_subset (Finset.range_mono ht)
          (f := u) (fun j (_ : j ∈ Finset.range t) hj => by
            have hj' : ¬j < n := fun h => hj (Finset.mem_range.mpr h)
            simp [u, hj'])
        rw [← hm]
        apply Finset.sum_le_sum
        intro j hj
        simp [u, Finset.mem_range.mp hj]
    have hc :
        (∑ j ∈ Finset.range t, (allocateSlots cap budget j : ℝ)) =
          min (budget : ℝ) (∑ j ∈ Finset.range t, (cap j : ℝ)) := by
      exact_mod_cast slots_prefix cap budget t
    rw [hc]
    exact le_min hBudget hCap
  have h := weighted_majorization u (fun j => allocateSlots cap budget j) value hmaj decreasing valuesNonneg n
  calc
    _ = ∑ j ∈ Finset.range n, u j * value j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [u, Finset.mem_range.mp hj]
    _ ≤ _ := h

theorem grouped_sum {I : Type*} [Fintype I] (grade : I → Nat)
    (m : Nat) (hGrade : ∀ i, grade i ≤ m) (f : I → ℝ) :
    (∑ j ∈ Finset.range (m+1), ∑ i ∈ Finset.univ.filter (fun i => grade i = j), f i) =
      ∑ i, f i := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (grade i)]
  · simp
  · intro j _ h
    simp [h.symm]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le (hGrade i)))).elim

theorem graded_spectral_slots {I : Type*} [Fintype I] (grade : I → Nat)
    (m c : Nat) (hGrade : ∀ i, grade i ≤ m) (w : I → ℝ)
    (hNonneg : ∀ i, 0 ≤ w i) (hUnit : ∀ i, w i ≤ 1) (hBudget : ∑ i, w i ≤ 2^c)
    (hMultiplicity : ∀ j ≤ m, (Finset.univ.filter (fun i : I => grade i = j)).card ≤
        Nat.choose m j * 7^j) :
    (∑ i, (9 : ℝ)^(m-grade i) * w i) ≤
      ∑ j ∈ Finset.range (m+1), (allocateSlots (fun t => Nat.choose m t * 7^t) (2^c) j : ℝ) * 9^(m-j) := by
  classical
  let mass (j : Nat) := ∑ i ∈ Finset.univ.filter (fun i => grade i = j), w i
  have hMass0 (j : Nat) : 0 ≤ mass j := Finset.sum_nonneg fun i _ => hNonneg i
  have hMassCap (j : Nat) : mass j ≤ (Nat.choose m j * 7^j : Nat) := by
    by_cases hj : j ≤ m
    · calc
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => grade i = j), (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => hUnit i)
        _ ≤ _ := by simpa using (show ((Finset.univ.filter (fun i : I => grade i = j)).card : ℝ) ≤
            ((Nat.choose m j * 7^j : Nat) : ℝ) by exact_mod_cast hMultiplicity j hj)
    · have he : (Finset.univ.filter (fun i : I => grade i = j)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hf := (Finset.mem_filter.mp hi).2
        exact hj (hf ▸ hGrade i)
      simp only [mass, he, Finset.sum_empty]
      positivity
  have hMassBudget : (∑ j ∈ Finset.range (m+1), mass j) ≤ ((2^c : Nat) : ℝ) := by
    change (∑ j ∈ Finset.range (m+1), ∑ i ∈ Finset.univ.filter (fun i => grade i = j), w i) ≤ _
    rw [grouped_sum grade m hGrade w]
    exact_mod_cast hBudget
  have hDecrease (j : Nat) : (9 : ℝ) ^ (m-(j+1)) ≤ 9^(m-j) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_left (by omega) m)
  have hb := weighted_slots (fun t => Nat.choose m t * 7^t) (2^c) mass
    (fun j => (9 : ℝ)^(m-j)) hMass0 hMassCap hDecrease (by intro; positivity) (m+1) hMassBudget
  apply le_trans ?_ hb
  rw [← grouped_sum grade m hGrade (fun i => (9 : ℝ)^(m-grade i) * w i)]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  change _ = (∑ i ∈ Finset.univ.filter (fun i => grade i = j), w i) * (9 : ℝ)^(m-j)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2, mul_comm]

def spectrumSupport {m : Nat} (major word : Fin m → Fin 8) : Finset (Fin m) :=
  Finset.univ.filter fun i => word i ≠ major i

private noncomputable def remaining (a : Fin 8) : {x : Fin 8 // x ≠ a} ≃ Fin 7 := by
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_subtype_compl (fun x : Fin 8 => x = a)]
  simp


theorem changed_spectral_count {m : Nat} (major : Fin m → Fin 8) (j : Nat) :
    (Finset.univ.filter (fun word : Fin m → Fin 8 => (spectrumSupport major word).card = j)).card ≤
      Nat.choose m j * 7^j := by
  classical
  let Supports := {s : Finset (Fin m) // s.card = j}
  let Target := Σ s : Supports, (s.val → Fin 7)
  let Domain := {word : Fin m → Fin 8 // (spectrumSupport major word).card = j}
  let encode : Domain → Target := fun word =>
    ⟨⟨spectrumSupport major word.val, word.property⟩,
      fun i => remaining (major i.val) ⟨word.val i.val, (Finset.mem_filter.mp i.property).2⟩⟩
  let decode : Target → (Fin m → Fin 8) := fun packed i =>
    if hi : i ∈ packed.1.val then (remaining (major i)).symm (packed.2 ⟨i, hi⟩)
    else major i
  have hRecover (word : Domain) : decode (encode word) = word.val := by
    funext i
    by_cases h : word.val i = major i
    · have hn : i ∉ spectrumSupport major word.val := by simp [spectrumSupport, h]
      simp [decode, encode, hn, h]
    · have hi : i ∈ spectrumSupport major word.val := by simp [spectrumSupport, h]
      simp [decode, encode, hi]
  have hInjective : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    rw [← hRecover x, ← hRecover y, he]
  have hDom : Fintype.card Domain =
      (Finset.univ.filter (fun word : Fin m → Fin 8 => (spectrumSupport major word).card = j)).card := by
    apply Fintype.card_of_subtype
    simp
  rw [← hDom]
  apply le_trans (Fintype.card_le_of_injective encode hInjective)
  have hTarget : Fintype.card Target = ∑ s : Supports, 7^j := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro s _
    rw [Fintype.card_fun, Fintype.card_coe]
    simp [s.property]
  rw [hTarget]
  have hSupports : Fintype.card Supports = Nat.choose m j := by
    simp [Supports, Fintype.card_finset_len]
  simp [hSupports]

theorem scaled_div_sq {corr mass scale bound : ℝ} (hmass : 0 < mass)
    (h : scale * corr^2 ≤ mass^2 * bound) :
    scale * (corr / mass)^2 ≤ bound := by
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (sq_pos_of_pos hmass)).mpr (by simpa [mul_comm] using h)

private theorem pow8_sq (m : Nat) : ((8 : ℝ)^m)^2 = (64 : ℝ)^m := by
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
  norm_num

private theorem pow10_sq (m : Nat) : ((10 : ℝ)^m)^2 = (100 : ℝ)^m := by
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
  norm_num


theorem uniform_seed_scaling (m : Nat) (N B corr slotsSum : ℝ)
    (hB : 0 < B) (hN : N = 8^m * B)
    (hCorr : corr^2 ≤ N^2 * (B^2 * 4^m * slotsSum)) :
    16^m * (corr / N^2)^2 ≤ slotsSum := by
  have hNpos : 0 < N := by rw [hN]; positivity
  have hCancel : 16^m * (B^2 * 4^m) = N^2 := by
    rw [hN, mul_pow, pow8_sq]
    have hm : (16 : ℝ)^m * 4^m = 64^m := by rw [← mul_pow]; norm_num
    calc
      _ = ((16 : ℝ)^m * 4^m) * B^2 := by ring
      _ = _ := by rw [hm]
  apply scaled_div_sq (by positivity : 0 < N^2)
  calc
    _ ≤ 16^m * (N^2 * (B^2 * 4^m * slotsSum)) :=
      mul_le_mul_of_nonneg_left hCorr (by positivity)
    _ = _ := by
      calc
        _ = N^2 * (16^m * (B^2 * 4^m)) * slotsSum := by ring
        _ = _ := by rw [hCancel]; ring


theorem weighted_seed_scaling (m : Nat) (N B corr traces : ℝ)
    (hB : 0 < B) (hN : N = 8^m * B)
    (hCorr : corr^2 ≤ N^2 * (B^2 * 16^m * traces)) :
    25^m * (corr / (N * B * 10^m))^2 ≤ 4^m * traces := by
  have hNpos : 0 < N := by rw [hN]; positivity
  have he : (25 : ℝ)^m * 16^m = ((10 : ℝ)^m)^2 * 4^m := by
    rw [pow10_sq, ← mul_pow, ← mul_pow]
    norm_num
  apply scaled_div_sq (by positivity : 0 < N * B * 10^m)
  calc
    _ ≤ 25^m * (N^2 * (B^2 * 16^m * traces)) :=
      mul_le_mul_of_nonneg_left hCorr (by positivity)
    _ = N^2 * B^2 * ((25 : ℝ)^m * 16^m) * traces := by ring
    _ = _ := by rw [he]; ring

theorem uniform_seed_projected {R : Type*} [Fintype R] (m : Nat) (N B corr slotsSum : ℝ)
    (eig w value : R → ℝ) (hB : 0 < B) (hN : N = 8^m * B)
    (hEig : ∀ r, (eig r)^2 = B^2 * 4^m * value r)
    (hSlots : (∑ r, value r * w r) ≤ slotsSum)
    (hCorr : corr^2 ≤ N^2 * ∑ r, (eig r)^2 * w r) :
    16^m * (corr / N^2)^2 ≤ slotsSum := by
  apply uniform_seed_scaling m N B corr slotsSum hB hN
  apply le_trans hCorr
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg N)
  calc
    _ = (B^2 * 4^m) * ∑ r, value r * w r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [hEig]
      ring
    _ ≤ _ := by
      rw [mul_assoc]
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hSlots (by positivity : 0 ≤ B^2 * 4^m))

theorem weighted_seed_projected {R : Type*} [Fintype R] (m : Nat) (N B corr traces : ℝ)
    (eig w : R → ℝ) (hB : 0 < B) (hN : N = 8^m * B)
    (hEig : ∀ r, (eig r)^2 ≤ B^2 * 16^m)
    (hNonneg : ∀ r, 0 ≤ w r) (hTraces : (∑ r, w r) ≤ traces)
    (hCorr : corr^2 ≤ N^2 * ∑ r, (eig r)^2 * w r) :
    25^m * (corr / (N * B * 10^m))^2 ≤ 4^m * traces := by
  apply weighted_seed_scaling m N B corr traces hB hN
  apply le_trans hCorr
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg N)
  calc
    _ ≤ ∑ r, (B^2 * 16^m) * w r :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hEig r) (hNonneg r)
    _ = (B^2 * 16^m) * ∑ r, w r := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hTraces (by positivity)

private lemma guardedBoolSign_xor (a b : Bool) :
    guardedBoolSign (xor a b) = guardedBoolSign a * guardedBoolSign b := by
  cases a <;> cases b <;> norm_num [guardedBoolSign]

private lemma parity_succ (b : Bool) (n : ℕ) :
    ((b.toNat + n) % 2 == 1) = xor b (n % 2 == 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> cases b <;> simp [Nat.add_mod, h]

private lemma sign_parity {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    guardedBoolSign ((∑ i ∈ s, (f i).toNat) % 2 == 1) = ∏ i ∈ s, guardedBoolSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [guardedBoolSign]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, parity_succ, guardedBoolSign_xor, ih]

private noncomputable def localKernel (α β δ inj : Bool) (u : Fin 8) : ℝ :=
  guardedBoolSign (xor (tripleBit α β δ u) inj)

private noncomputable def localWeight (α β δ : Bool) (u : Fin 8) : ℝ :=
  if u = heavyPoint α β δ then 3 else 1

private lemma localWeight_nonneg (α β δ : Bool) (u : Fin 8) : 0 ≤ localWeight α β δ u := by
  unfold localWeight
  split <;> norm_num

private lemma localKernel_char (α β δ inj : Bool) (r u : Fin 8) :
    localKernel α β δ inj u * guardedChar r u = guardedBoolSign inj *
      ((if xor (tripleBit α β δ u) (walshBit r u) then (-1 : ℤ) else 1) : ℝ) := by
  rw [guardedChar_eq]
  unfold localKernel
  generalize tripleBit α β δ u = b
  generalize walshBit r u = c
  cases b <;> cases c <;> cases inj <;> norm_num [guardedBoolSign]

private lemma localKernel_coeff_sq (α β δ inj : Bool) (r : Fin 8) :
    (∑ u, localKernel α β δ inj u * guardedChar r u)^2 =
      if r = majorFreq α β δ then 36 else 4 := by
  have hc : (∑ u, localKernel α β δ inj u * guardedChar r u) =
      guardedBoolSign inj * (localCoeff α β δ r : ℝ) := by
    rw [localCoeff, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simpa only [apply_ite (fun z : ℤ => (z : ℝ)), Int.cast_one] using localKernel_char α β δ inj r u
  rw [hc, mul_pow, guardedBoolSign_sq, one_mul]
  have h := local_spectrum α β δ r
  by_cases hr : r = majorFreq α β δ <;> simp only [hr, ite_true, ite_false] at h ⊢ <;> exact_mod_cast h

private lemma localWeightedKernel_coeff_sq (α β δ inj : Bool) (r : Fin 8) :
    (∑ u, (localWeight α β δ u * localKernel α β δ inj u) * guardedChar r u)^2 ≤ 16 := by
  have h (u : Fin 8) : (localWeight α β δ u * localKernel α β δ inj u) * guardedChar r u =
      guardedBoolSign inj * (((if xor (tripleBit α β δ u) (walshBit r u) then (-1 : ℤ) else 1) *
        (if u = heavyPoint α β δ then 3 else 1) : ℤ) : ℝ) := by
    rw [mul_assoc (localWeight α β δ u), localKernel_char]
    by_cases hu : u = heavyPoint α β δ <;> simp [localWeight, hu, mul_comm]
  simp_rw [h]
  rw [← Finset.mul_sum, ← Int.cast_sum]
  change (guardedBoolSign inj * (weightedCoeff α β δ r : ℝ))^2 ≤ _
  rw [mul_pow, guardedBoolSign_sq, one_mul]
  have hbound : |(weightedCoeff α β δ r : ℝ)| ≤ 4 := by
    exact_mod_cast local_weighted_spectrum α β δ r
  simpa only [sq_abs, show (4 : ℝ)^2 = 16 by norm_num] using
    pow_le_pow_left₀ (abs_nonneg _) hbound 2

private lemma tensorKernel_coeff_sq {m : ℕ} (α β δ inj : Fin m → Bool)
    (r : Fin m → Fin 8) :
    (∏ i, ∑ u, localKernel (α i) (β i) (δ i) (inj i) u * guardedChar (r i) u)^2 =
      (4:ℝ)^m * 9^(m-(spectrumSupport (fun i => majorFreq (α i) (β i) (δ i)) r).card) := by
  let a := fun i => majorFreq (α i) (β i) (δ i)
  change _ = (4:ℝ)^m * 9^(m-(spectrumSupport a r).card)
  rw [← Finset.prod_pow]
  simp_rw [localKernel_coeff_sq]
  have h (i : Fin m) : (if r i = a i then (36 : ℝ) else 4) = 4 * (if r i = a i then 9 else 1) := by
    by_cases hi : r i = a i <;> norm_num [hi]
  change (∏ i, if r i = a i then (36 : ℝ) else 4) = _
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin m => r i = a i)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change (Finset.univ.filter (fun i => r i = a i)).card + (spectrumSupport a r).card = m at hc
  rw [show (Finset.univ.filter (fun i => r i = a i)).card = m-(spectrumSupport a r).card by
    omega]

private lemma tensorWeightedKernel_coeff_sq {m : ℕ} (α β δ inj : Fin m → Bool)
    (r : Fin m → Fin 8) :
    (∏ i, ∑ u, (localWeight (α i) (β i) (δ i) u * localKernel (α i) (β i) (δ i) (inj i) u) *
      guardedChar (r i) u)^2 ≤ (16:ℝ)^m := by
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _i : Fin m, (16:ℝ) := Finset.prod_le_prod₀ (f := fun i => (∑ u,
      (localWeight (α i) (β i) (δ i) u * localKernel (α i) (β i) (δ i) (inj i) u) * guardedChar (r i) u)^2)
      (g := fun _ => 16) (fun _ _ => sq_nonneg _)
      (fun i _ => localWeightedKernel_coeff_sq _ _ _ _ _)
    _ = _ := by simp

private def blockAlpha {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (p : ℕ) : Bool :=
  alphaFn (oldFn constant row ref p) (injectedFn k constant 1 ref.val (p+6))

private def blockBeta {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (p : ℕ) : Bool :=
  betaFn (oldFn constant row ref p) (injectedFn k constant 1 ref.val (p+7))

private def blockDelta {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (p : ℕ) : Bool :=
  deltaFn (oldFn constant row ref p) (row.val.testBit ((p+9)%k)) ((constant 1).val.testBit ((p+8)%k))

private def isGuarded {k : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k)) (p : ℕ) : Prop :=
  let first := firstFn constant row ref p
  tauFn (oldFn constant row ref p) = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
    xor (first 4) (first 5) = !(blockAlpha constant row ref p) ∧ first 4 = blockBeta constant row ref p

private def rowTruth {k m : ℕ} (constant : ℕ → Fin (2^k)) (row ref : Fin (2^k))
    (starts : Fin m → ℕ) (x y : Fin (2^k)) : Bool :=
  let key := (x.val ^^^ y.val ^^^ ref.val) % 2^k
  (∑ i : Fin m, (bitFn k constant row.val 2 key (starts i+5)).toNat) % 2 == 1

private lemma guardedRow_factor {k m : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2^k))
    (row ref : Fin (2^k)) (pin : Finset (Fin k)) (starts : Fin m → ℕ)
    (hk0 : 0 < k) (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k))
    (hpin : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k)
    (hgood : ∀ i, isGuarded constant row ref (starts i)) (x y : fiberFn constant row ref pin) :
    let left := fiberCoords hk constant row ref pin starts hk0 hfree hdist
      (fun i => codeTag (oldFn constant row ref (starts i)))
    let right := fiberCoords hk constant row ref pin starts hk0 hfree hdist
      (fun i j => oldFn constant row ref (starts i) (9+j.val))
    guardedBoolSign (rowTruth constant row ref starts x.val y.val) =
      ∏ i : Fin m, localKernel (blockAlpha constant row ref (starts i)) (blockBeta constant row ref (starts i))
        (blockDelta constant row ref (starts i)) (injectedFn k constant 2 ref.val (starts i+5))
        (guardedXor8 ((left x).1 i) ((right y).1 i)) := by
  dsimp only
  let q := keyXor (keyXor x.val y.val) ref
  have hq : q ∈ fiberFn constant row ref pin := xor_mem_fiber hk constant row ref x.val y.val pin x.property y.property
  have hmod : (x.val.val ^^^ y.val.val ^^^ ref.val) % 2^k = q.val := Nat.mod_eq_of_lt q.isLt
  unfold rowTruth
  dsimp only
  rw [hmod, sign_parity]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hg := hgood i
  have hb := local_bit_of_guard k hk constant row ref q (starts i)
    (local_pin hk0 constant row ref pin starts hpin q hq i) hg.1 hg.2.2.1 hg.2.2.2
  rw [hb]
  unfold localKernel blockAlpha blockBeta blockDelta
  rw [fiberCoords_xor hk constant row ref pin starts hk0 hfree hdist x y i]
  rfl

private noncomputable def tensorWeight {m : ℕ} {S : Type*} (α β δ : Fin m → Bool)
    (x y : (Fin m → Fin 8) × S) : ℝ :=
  ∏ i, localWeight (α i) (β i) (δ i) (guardedXor8 (x.1 i) (y.1 i))

private noncomputable def agreementCorr {X Y : Type*} [Fintype X] [Fintype Y]
    (weight : X → Y → ℝ) (truth pred : X → Y → Bool) : ℝ :=
  ∑ x, ∑ y, (weight x y * guardedBoolSign (truth x y)) * guardedBoolSign (pred x y)

private theorem tensorWeight_nonneg {m : ℕ} {S : Type*} (α β δ : Fin m → Bool)
    (x y : (Fin m → Fin 8) × S) : 0 ≤ tensorWeight α β δ x y :=
  Finset.prod_nonneg fun i _ => localWeight_nonneg (α i) (β i) (δ i) _

private theorem tensorWeight_sum {m : ℕ} {S : Type*} [Fintype S] (α β δ : Fin m → Bool) :
    (∑ x : (Fin m → Fin 8) × S, ∑ y, tensorWeight α β δ x y) =
      (Fintype.card ((Fin m → Fin 8) × S) : ℝ) * (Fintype.card S : ℝ) * 10^m := by
  rw [guardedTensor_card]
  have h := guardedTensor_heavy_sum (S := S) (fun i => heavyPoint (α i) (β i) (δ i))
  change (∑ x : (Fin m → Fin 8) × S, ∑ y, tensorWeight α β δ x y) = _ at h
  rw [h, show (80 : ℝ)^m = (8 : ℝ)^m * (10 : ℝ)^m by rw [← mul_pow]; norm_num]
  ring

private theorem guardedSeed_bounds {m : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (c : ℕ) (α β δ inj : Fin m → Bool)
    (truth pred : ((Fin m → Fin 8) × S) → ((Fin m → Fin 8) × S) → Bool)
    (htruth : ∀ x y, guardedBoolSign (truth x y) =
      ∏ i, localKernel (α i) (β i) (δ i) (inj i) (guardedXor8 (x.1 i) (y.1 i)))
    (a b : Fin (2^c) → ((Fin m → Fin 8) × S) → ℝ)
    (hpred : ∀ x y, guardedBoolSign (pred x y) = ∑ q, a q x * b q y) :
    let D := (Fintype.card ((Fin m → Fin 8) × S) : ℝ)
    let B := (Fintype.card S : ℝ)
    (16 : ℝ)^m * (agreementCorr (fun _ _ => 1) truth pred / D^2)^2 ≤
      (∑ j ∈ Finset.range (m+1), (allocateSlots (fun t => Nat.choose m t * 7^t) (2^c) j : ℝ) * 9^(m-j)) ∧
    (25 : ℝ)^m * (agreementCorr (tensorWeight α β δ) truth pred / (D * B * 10^m))^2 ≤ (4 : ℝ)^m * 2^c := by
  intro D B
  let f := fun i => localKernel (α i) (β i) (δ i) (inj i)
  let g := fun i u => localWeight (α i) (β i) (δ i) u * f i u
  let p := fun x y => guardedBoolSign (pred x y)
  let grade := fun r : Fin m → Fin 8 => (spectrumSupport (fun i => majorFreq (α i) (β i) (δ i)) r).card
  let cap := ∑ j ∈ Finset.range (m+1), (allocateSlots (fun t => Nat.choose m t * 7^t) (2^c) j : ℝ) * 9^(m-j)
  have hB : 0 < B := by
    change 0 < (Fintype.card S : ℝ)
    exact_mod_cast Fintype.card_pos (α := S)
  have hD : D = 8^m * B := guardedTensor_card
  have hunit (x y : (Fin m → Fin 8) × S) : (p x y)^2 = 1 := guardedBoolSign_sq _
  constructor
  · obtain ⟨w, hw, hbudget, hc⟩ := guardedTensor_corr f p a b hpred hunit
    have hgrade (r : Fin m → Fin 8) : grade r ≤ m := by
      simpa [grade] using Finset.card_le_univ (spectrumSupport (fun i => majorFreq (α i) (β i) (δ i)) r)
    have hbudget' : (∑ r, w r) ≤ (2 : ℝ)^c := by simpa using hbudget
    have hslots : (∑ r, (9:ℝ)^(m-grade r) * w r) ≤ cap :=
      graded_spectral_slots grade m c hgrade w (fun r => (hw r).1) (fun r => (hw r).2) hbudget'
        (fun j _ => changed_spectral_count _ j)
    have hs (r : Fin m → Fin 8) : guardedTensor_eig S f r ^ 2 = B^2 * 4^m * 9^(m-grade r) := by
      unfold guardedTensor_eig
      rw [mul_pow, tensorKernel_coeff_sq]
      dsimp [grade]
      ring
    have hmass : (∑ r, guardedTensor_eig S f r ^ 2 * w r) ≤ B^2 * 4^m * cap := by
      simp_rw [hs, mul_assoc (B^2 * 4^m), ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hslots (by positivity)
    have hc' : (agreementCorr (fun _ _ => 1) truth pred)^2 ≤ D^2 * (B^2 * 4^m * cap) := by
      simp only [agreementCorr, one_mul, htruth]
      exact hc.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg D))
    exact uniform_seed_scaling m D B _ cap hB hD hc'
  · obtain ⟨w, hw, hbudget, hc⟩ := guardedTensor_corr g p a b hpred hunit
    have hbudget' : (∑ r, w r) ≤ (2 : ℝ)^c := by simpa using hbudget
    have hs (r : Fin m → Fin 8) : guardedTensor_eig S g r ^ 2 ≤ B^2 * 16^m := by
      unfold guardedTensor_eig
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (tensorWeightedKernel_coeff_sq α β δ inj r) (sq_nonneg B)
    have hmass : (∑ r, guardedTensor_eig S g r ^ 2 * w r) ≤ B^2 * 16^m * 2^c := by
      calc
        _ ≤ ∑ r, (B^2 * 16^m) * w r := Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hs r) (hw r).1
        _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hbudget' (by positivity)
    have hc' : (agreementCorr (tensorWeight α β δ) truth pred)^2 ≤ D^2 * (B^2 * 16^m * 2^c) := by
      have hc'' := hc.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg D))
      simpa only [agreementCorr, tensorWeight, htruth, g, Finset.prod_mul_distrib] using hc''
    exact weighted_seed_scaling m D B _ (2^c) hB hD hc'

private theorem normalizedCorrelation {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (mass : Z → ℝ) (weight : X → Y → ℝ) (denom : ℝ) (truth : X → Y → Bool) (pred : Z → X → Y → Bool) :
    (∑ x, ∑ y, (weight x y / denom) * ∑ z, mass z *
      (if pred z x y = truth x y then (1 : ℝ) else -1)) =
      ∑ z, mass z * (agreementCorr weight truth (pred z) / denom) := by
  rw [guardedPublicCoin_corr]
  simp_rw [agreementCorr, Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => congrArg (mass z * ·) ?_
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private theorem guardedTensor_bounds {m s : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (c : ℕ) (α β δ inj : Fin m → Bool) (mass : Fin s → ℝ)
    (mass_nonneg : ∀ z, 0 ≤ mass z) (mass_sum : (∑ z, mass z) = 1)
    (truth : ((Fin m → Fin 8) × S) → ((Fin m → Fin 8) × S) → Bool)
    (pred : Fin s → ((Fin m → Fin 8) × S) → ((Fin m → Fin 8) × S) → Bool)
    (htruth : ∀ x y, guardedBoolSign (truth x y) =
      ∏ i, localKernel (α i) (β i) (δ i) (inj i) (guardedXor8 (x.1 i) (y.1 i)))
    (hpred : ∀ z, ∃ a b : Fin (2^c) → ((Fin m → Fin 8) × S) → ℝ,
      ∀ x y, guardedBoolSign (pred z x y) = ∑ q, a q x * b q y) :
    let X := (Fin m → Fin 8) × S
    let bias := fun x y => ∑ z, mass z * (if pred z x y = truth x y then (1 : ℝ) else -1)
    let uniform := (∑ x : X, ∑ y : X, bias x y) / (Fintype.card X : ℝ)^2
    ((16 : ℝ)^m * uniform^2 ≤
      ∑ j ∈ Finset.range (m+1), (allocateSlots (fun t => Nat.choose m t * 7^t) (2^c) j : ℝ) * 9^(m-j)) ∧
    ∀ adv : ℝ, 0 ≤ adv → (∀ x y : X, adv ≤ bias x y) → (25 : ℝ)^m * adv^2 ≤ (4 : ℝ)^m * 2^c := by
  intro X bias uniform
  let D := (Fintype.card X : ℝ)
  let B := (Fintype.card S : ℝ)
  let cap := ∑ j ∈ Finset.range (m+1), (allocateSlots (fun t => Nat.choose m t * 7^t) (2^c) j : ℝ) * 9^(m-j)
  let r := D * B * (10 : ℝ)^m
  let w : X → X → ℝ := tensorWeight α β δ
  let uCorr (z : Fin s) := agreementCorr (fun _ _ => 1) truth (pred z) / D^2
  let wCorr (z : Fin s) := agreementCorr w truth (pred z) / r
  have hseed (z : Fin s) : (16 : ℝ)^m * (uCorr z)^2 ≤ cap ∧ (25 : ℝ)^m * (wCorr z)^2 ≤ (4 : ℝ)^m * 2^c := by
    obtain ⟨a, b, hp⟩ := hpred z
    exact guardedSeed_bounds c α β δ inj truth (pred z) htruth a b hp
  constructor
  · have hU : uniform = ∑ z, mass z * uCorr z := by
      calc
        uniform = ∑ x : X, ∑ y : X, (1 / D^2) * bias x y := by
          dsimp only [uniform]
          simp_rw [Finset.sum_div, div_eq_mul_inv, one_mul, mul_comm]
          rfl
        _ = _ := normalizedCorrelation mass (fun _ _ => 1) (D^2) truth pred
    rw [hU]
    exact guardedAveraging_bound mass uCorr mass_nonneg mass_sum _ cap (by positivity) (fun z => (hseed z).1)
  · intro adv hadv hp
    let law : X → X → ℝ := fun x y => w x y / r
    have hr : 0 < r := by
      have hD : 0 < D := by
        change 0 < (Fintype.card X : ℝ)
        exact_mod_cast Fintype.card_pos (α := X)
      have hB : 0 < B := by
        change 0 < (Fintype.card S : ℝ)
        exact_mod_cast Fintype.card_pos (α := S)
      dsimp only [r]
      positivity
    have hsum : (∑ x, ∑ y, law x y) = 1 := by
      simp only [law, ← Finset.sum_div]
      rw [tensorWeight_sum α β δ]
      exact div_self hr.ne'
    have hlaw (x y : X) : 0 ≤ law x y := div_nonneg (tensorWeight_nonneg α β δ x y) hr.le
    have hmean : adv ≤ ∑ z, mass z * wCorr z := by
      calc
        _ ≤ ∑ x, ∑ y, law x y * bias x y := guardedProbability_minimum law bias hlaw hsum adv hp
        _ = _ := normalizedCorrelation mass w r truth pred
    have havg := guardedAveraging_bound mass wCorr mass_nonneg mass_sum ((25 : ℝ)^m) ((4 : ℝ)^m * 2^c)
      (by positivity) (fun z => (hseed z).2)
    exact (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hadv (hadv.trans hmean)).2 hmean) (by positivity)).trans havg

private def protocolRun {K : Type*} (c : ℕ) (alice : ℕ → ℕ → Bool) (speak : ℕ → ℕ → K → Bool)
    (x y : K) : ℕ :=
  (List.range c).foldl (fun log t =>
    let v := speak t log (if alice t log then x else y)
    log + (v.toNat <<< t)) 0

set_option maxHeartbeats 600000 in
private theorem guardedRow_bounds (k : ℕ) (hk0 : 0 < k) (constant : ℕ → Fin (2^k))
    (m : ℕ) (starts : Fin m → ℕ) (hm : 0 < m)
    (hdist : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k))
    (row ref : Fin (2^k)) (hgood : ∀ i, isGuarded constant row ref (starts i)) (pin : Finset (Fin k))
    (hpin : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k)
    (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k)
    (c s : ℕ) (mass : Fin s → ℝ) (hn : ∀ z, 0 ≤ mass z) (hmass : (∑ z, mass z) = 1)
    (alice : Fin s → ℕ → ℕ → Bool) (speak : Fin s → ℕ → ℕ → Fin (2^k) → Bool)
    (bob : Fin s → ℕ → Fin (2^k) → Bool) :
    let fiber := fiberFn constant row ref pin
    let pairs := fiber.product fiber
    let bias := fun (x y : Fin (2^k)) => ∑ z, mass z *
      (if bob z (protocolRun c (alice z) (speak z) x y) y = rowTruth constant row ref starts x y then (1 : ℝ) else -1)
    let uniform := (∑ p ∈ pairs, bias p.1 p.2) / (pairs.card : ℝ)
    let mult := fun j : ℕ => Nat.choose m j * 7^j
    let slots := fun j : ℕ => min (mult j) (2^c - (Finset.range j).sum mult)
    ((16 : ℝ)^m * uniform^2 ≤
      ∑ j ∈ Finset.range (m+1), (slots j : ℝ) * 9^(m-j)) ∧
    (∀ adv : ℝ, 0 ≤ adv → (∀ p ∈ pairs, adv ≤ bias p.1 p.2) →
      (25 : ℝ)^m * adv^2 ≤ (4 : ℝ)^m * 2^c) := by
  classical
  intro fiber pairs bias uniform mult slots
  have hk := width_of_layout hm hk0 starts hdist
  let Spare := (((Set.range (freeIndex hk0 starts pin hfree))ᶜ : Set _) → Bool)
  let _ : Fintype Spare := Fintype.ofFinite _
  let _ : Nonempty Spare := ⟨fun _ => false⟩
  let X := (Fin m → Fin 8) × Spare
  let left : (fiber : Type) ≃ X := fiberCoords hk constant row ref pin starts hk0 hfree hdist
    (fun i => codeTag (oldFn constant row ref (starts i)))
  let right : (fiber : Type) ≃ X := fiberCoords hk constant row ref pin starts hk0 hfree hdist
    (fun i j => oldFn constant row ref (starts i) (9+j.val))
  let truth (x y : X) := rowTruth constant row ref starts (left.symm x).val (right.symm y).val
  let pred (z : Fin s) (x y : X) :=
    bob z (protocolRun c (alice z) (speak z) (left.symm x).val (right.symm y).val) (right.symm y).val
  let α (i : Fin m) := blockAlpha constant row ref (starts i)
  let β (i : Fin m) := blockBeta constant row ref (starts i)
  let δ (i : Fin m) := blockDelta constant row ref (starts i)
  let inj (i : Fin m) := injectedFn k constant 2 ref.val (starts i+5)
  have htruth (x y : X) : guardedBoolSign (truth x y) =
      ∏ i, localKernel (α i) (β i) (δ i) (inj i) (guardedXor8 (x.1 i) (y.1 i)) := by
    have ht := guardedRow_factor hk constant row ref pin starts hk0 hfree hdist hpin hgood (left.symm x) (right.symm y)
    change guardedBoolSign (truth x y) = ∏ i, localKernel (α i) (β i) (δ i) (inj i)
      (guardedXor8 ((left (left.symm x)).1 i) ((right (right.symm y)).1 i)) at ht
    simpa only [Equiv.apply_symm_apply] using ht
  have hpred (z : Fin s) : ∃ a b : Fin (2^c) → X → ℝ,
      ∀ x y, guardedBoolSign (pred z x y) = ∑ q, a q x * b q y := by
    obtain ⟨a, b, hab⟩ := guardedLog_sum (alice z) (speak z) (bob z) c guardedBoolSign
    exact ⟨fun q x => a q (left.symm x).val, fun q y => b q (right.symm y).val,
      fun x y => (hab (left.symm x).val (right.symm y).val).1.symm⟩
  have hb := guardedTensor_bounds (S := Spare) c α β δ inj mass hn hmass truth pred htruth hpred
  let biasX (x y : X) := bias (left.symm x).val (right.symm y).val
  have hsum : (∑ p ∈ pairs, bias p.1 p.2) = ∑ x : X, ∑ y : X, biasX x y := by
    calc
      _ = ∑ x ∈ fiber, ∑ y ∈ fiber, bias x y := Finset.sum_product _ _ _
      _ = ∑ x : fiber, ∑ y : fiber, bias x.val y.val := by
        simp_rw [Finset.sum_coe_sort]
        rw [Finset.sum_coe_sort fiber (fun x => ∑ y ∈ fiber, bias x y)]
      _ = _ := by
        refine Fintype.sum_equiv left _ _ (fun x => Fintype.sum_equiv right _ _ (fun y => ?_))
        simp [biasX]
  have hcard : (pairs.card : ℝ) = (Fintype.card X : ℝ)^2 := by
    have hc : fiber.card = Fintype.card X := by simpa using Fintype.card_congr left
    change ((fiber.product fiber).card : ℝ) = _
    rw [show (fiber.product fiber).card = fiber.card * fiber.card from Finset.card_product fiber fiber,
      hc, Nat.cast_mul, pow_two]
  constructor
  · change (16:ℝ)^m * (((∑ p ∈ pairs, bias p.1 p.2) / (pairs.card : ℝ)))^2 ≤ _
    rw [hsum, hcard]
    exact hb.1
  · intro adv ha hpoint
    apply hb.2 adv ha
    intro x y
    exact hpoint ((left.symm x).val, (right.symm y).val)
      (Finset.mem_product.mpr ⟨(left.symm x).property, (right.symm y).property⟩)

end PEqualNP.Outside.L_meta_29769_aux

open PEqualNP.Outside.L_meta_29769_aux

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.L_meta_29769 : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  ∀ (c s : Nat) (mass : Fin s → ℝ), (∀ z, 0 ≤ mass z) → (∑ z : Fin s, mass z) = 1 →
    ∀ (alice : Fin s → Nat → Nat → Bool) (speak : Fin s → Nat → Nat → K → Bool)
        (bob : Fin s → Nat → K → Bool),
      let run := fun (z : Fin s) (x y : K) =>
        (List.range c).foldl (fun log t =>
          let v := speak z t log (if alice z t log then x else y)
          log + (v.toNat <<< t)) 0
      let bias := fun (x y : K) => ∑ z : Fin s,
        mass z * (if bob z (run z x y) y = truth x y then (1 : ℝ) else -1)
      let uniform := (∑ p ∈ pairs, bias p.1 p.2) / (pairs.card : ℝ)
      let mult := fun j : Nat => Nat.choose m j * 7^j
      let slots := fun j : Nat => min (mult j) (2^c - (Finset.range j).sum mult)
      ((16 : ℝ)^m * uniform^2 ≤
        ∑ j ∈ Finset.range (m+1), (slots j : ℝ) * 9^(m-j)) ∧
      (∀ adv : ℝ, 0 ≤ adv → (∀ p ∈ pairs, adv ≤ bias p.1 p.2) →
        (25 : ℝ)^m * adv^2 ≤ (4 : ℝ)^m * 2^c) := by
  intro k hk constant rot step state injected bit m starts hm hdist good row ref hgood pin hpin hfree K fiber
    pairs truth c s mass hn hmass alice speak bob run bias uniform mult slots
  exact guardedRow_bounds k hk constant m starts hm hdist row ref hgood pin hpin hfree
    c s mass hn hmass alice speak bob
