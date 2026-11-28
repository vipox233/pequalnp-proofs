import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_35260

open PEqualNP.CircuitLowerBounds

abbrev Word := Nat
abbrev Row := Fin 256

def fullMask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def bit (r : Row) (w : Word) : Bool := w.testBit r.val
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (Nat.add m 1)) n
@[simp] theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
@[simp] theorem nat_land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
@[simp] theorem nat_lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
@[simp] theorem nat_xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
@[simp] theorem nat_shl_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
@[simp] theorem nat_shr_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nat_beq_eq (a b : Nat) : Nat.beq a b = (a == b) := rfl
theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]
theorem nat_blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]
theorem testBit_one_shl (j k : Nat) : (Nat.shiftLeft 1 j).testBit k = decide (k = j) := by
  rw [nat_shl_eq, Nat.testBit_shiftLeft]
  by_cases hge : k ≥ j
  · by_cases heq : k = j
    · subst heq; simp
    · have hne : k - j ≠ 0 := by omega
      have h0 : (1 : Nat).testBit (k - j) = false := by
        cases h : (1 : Nat).testBit (k - j)
        · rfl
        · rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; omega
      simp [hge, heq, h0]
  · have hne : k ≠ j := by omega
    simp [hge, hne]
theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := by
  cases n with
  | zero => rfl
  | succ m => rfl
inductive BTree (α : Type) where
  | empty : BTree α
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
def forceSpine {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k => forceSpine xs (fun xs1 => k (x :: xs1))
theorem forceSpine_eq {α β : Type} (l : List α) (k : List α → β) : forceSpine l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih => exact ih _
def btreeGet {α : Type} (defv : α) : Nat → BTree α → Nat → α
  | _, .empty, _ => defv
  | _, .leaf v, _ => v
  | 0, .node _ _, _ => defv
  | d + 1, .node l r, i =>
    match Nat.mod i 2 with
    | 0 => btreeGet defv d l (Nat.div i 2)
    | _ => btreeGet defv d r (Nat.div i 2)
def btreeAll {α : Type} (p : α → Bool) : BTree α → Bool
  | .empty => true
  | .leaf v => p v
  | .node l r => match btreeAll p l with | false => false | true => btreeAll p r
theorem btreeGet_prop {α : Type} {p : α → Bool} {defv : α} (hd : p defv = true)
    {t : BTree α} (ht : btreeAll p t = true) (d i : Nat) :
    p (btreeGet defv d t i) = true := by
  induction d generalizing t i with
  | zero =>
    cases t with
    | empty => exact hd
    | leaf v => exact ht
    | node _ _ => exact hd
  | succ d ih =>
    cases t with
    | empty => exact hd
    | leaf v => exact ht
    | node l r =>
      change (match btreeAll p l with | false => false | true => btreeAll p r) = true at ht
      cases hl : btreeAll p l with
      | false => simp [hl] at ht
      | true =>
        rw [hl] at ht
        simp only [btreeGet]
        split
        · exact ih hl _
        · exact ih ht _
def Masked (mask w : Word) : Prop := Nat.land w mask = w
def Proper (mask w : Word) : Prop := Masked mask w ∧ w ≠ 0 ∧ w ≠ mask
def binOp (mask d a b : Word) : Word :=
  match d with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.land a (Nat.xor mask b)
  | _ => Nat.land (Nat.xor mask a) b
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
theorem mask_testBit_ge {mask : Word} (hm : Masked fullMask mask) {k : Nat} (hk : 256 ≤ k) :
    mask.testBit k = false := by
  have h1 : (Nat.land mask fullMask).testBit k = mask.testBit k := congrArg (fun x => x.testBit k) hm
  rw [nat_land_eq, Nat.testBit_and] at h1
  have h2 : fullMask.testBit k = false := by
    have hlt : fullMask < 2 ^ 256 := by decide
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hk))
  rw [h2, Bool.and_false] at h1
  exact h1.symm
theorem masked_testBit_false {mask w : Word} (hm : Masked mask w) {k : Nat}
    (hk : mask.testBit k = false) : w.testBit k = false := by
  have h1 : (Nat.land w mask).testBit k = w.testBit k := congrArg (fun x => x.testBit k) hm
  rw [nat_land_eq, Nat.testBit_and, hk, Bool.and_false] at h1
  exact h1.symm
theorem masked_ext {mask a b : Word} (hm : Masked fullMask mask)
    (ha : Masked mask a) (hb : Masked mask b)
    (heq : ∀ r : Row, bit r a = bit r b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 256
  · exact heq ⟨k, hk⟩
  · have hm0 : mask.testBit k = false := mask_testBit_ge hm (by omega)
    rw [masked_testBit_false ha hm0, masked_testBit_false hb hm0]
theorem masked_land_left {mask a b : Word} (ha : Masked mask a) : Masked mask (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  simp only [nat_land_eq, Nat.testBit_and] at h1 ⊢
  cases hm : mask.testBit k <;> cases hb : b.testBit k <;> simp_all
theorem masked_land_right {mask a b : Word} (hb : Masked mask b) : Masked mask (Nat.land a b) := by
  rw [nat_land_eq, Nat.and_comm]
  exact masked_land_left hb
theorem masked_lor {mask a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (Nat.lor a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  have h2 : (Nat.land b mask).testBit k = b.testBit k := congrArg (fun x => x.testBit k) hb
  simp only [nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or] at h1 h2 ⊢
  cases hm : mask.testBit k <;> simp_all
theorem masked_xor {mask a : Word} (ha : Masked mask a) : Masked mask (Nat.xor mask a) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  simp only [nat_land_eq, Nat.testBit_and, Nat.testBit_xor] at h1 ⊢
  cases hm : mask.testBit k <;> simp_all
theorem masked_self (mask : Word) : Masked mask mask := by
  apply Nat.eq_of_testBit_eq; intro k; simp [nat_land_eq, Nat.testBit_and]
theorem masked_zero (mask : Word) : Masked mask 0 := by
  apply Nat.eq_of_testBit_eq; intro k; simp [nat_land_eq, Nat.testBit_and]
theorem masked_binOp {mask d a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (binOp mask d a b) := by
  unfold binOp
  split
  · exact masked_land_left ha
  · exact masked_lor ha hb
  · exact masked_land_left ha
  · exact masked_land_right hb
theorem binOp2_eq {mask a b : Word} (ha : Masked mask a) :
    binOp mask 2 a b = Nat.xor a (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  simp only [nat_land_eq, Nat.testBit_and] at h1
  simp only [binOp, nat_land_eq, nat_xor_eq, Nat.testBit_and, Nat.testBit_xor]
  cases ha' : a.testBit k <;> cases hb' : b.testBit k <;> cases hm' : mask.testBit k <;> simp_all
theorem binOp3_eq {mask a b : Word} (hb : Masked mask b) :
    binOp mask 3 a b = Nat.xor b (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land b mask).testBit k = b.testBit k := congrArg (fun x => x.testBit k) hb
  simp only [nat_land_eq, Nat.testBit_and] at h1
  simp only [binOp, nat_land_eq, nat_xor_eq, Nat.testBit_and, Nat.testBit_xor]
  cases ha' : a.testBit k <;> cases hb' : b.testBit k <;> cases hm' : mask.testBit k <;> simp_all
theorem binOp_flip {mask a b : Word} {d : Nat} (hd : d < 4) :
    binOp mask d a b = binOp mask (flipOp d) b a := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · simp [binOp, flipOp, Nat.and_comm]
  · simp [binOp, flipOp, Nat.or_comm]
  · simp [binOp, flipOp, Nat.and_comm]
  · simp [binOp, flipOp, Nat.and_comm]
theorem flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> decide
theorem binOp_testBit {mask a b : Word} {d : Nat} (hd : d < 4) (ha : Masked mask a) (hb : Masked mask b) (k : Nat) :
    (binOp mask d a b).testBit k =
      if mask.testBit k then
        match d with
        | 0 => a.testBit k && b.testBit k
        | 1 => a.testBit k || b.testBit k
        | 2 => a.testBit k && !b.testBit k
        | _ => !a.testBit k && b.testBit k
      else false := by
  cases hm : mask.testBit k with
  | false =>
    rw [masked_testBit_false (masked_binOp ha hb) hm]
    simp
  | true =>
    have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [binOp, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, Nat.testBit_xor, hm]
def nrm (mask a : Word) : Word := if a.testBit 0 then Nat.xor mask a else a
theorem masked_nrm {mask a : Word} (ha : Masked mask a) : Masked mask (nrm mask a) := by
  unfold nrm
  split
  · exact masked_xor ha
  · exact ha
theorem nrm_zero_bit {mask a : Word} (hm0 : mask.testBit 0 = true) :
    (nrm mask a).testBit 0 = false := by
  unfold nrm
  cases h : a.testBit 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_self]
theorem nrm_id {mask a : Word} (h : a.testBit 0 = false) : nrm mask a = a := by
  simp [nrm, h]
theorem xor_xor_self {mask a : Word} (ha : Masked mask a) : Nat.xor mask (Nat.xor mask a) = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [nat_xor_eq, Nat.testBit_xor]
theorem nrm_xor {mask a : Word} (hm0 : mask.testBit 0 = true) (ha : Masked mask a) :
    nrm mask (Nat.xor mask a) = nrm mask a := by
  unfold nrm
  cases h : a.testBit 0
  · simp only [nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_false, Bool.false_eq_true, ite_true, ite_false]
    exact xor_xor_self ha
  · simp only [nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_self, Bool.false_eq_true, ite_true, ite_false]
theorem proper_xor {mask a : Word} (ha : Masked mask a) (h : Proper mask (Nat.xor mask a)) :
    Proper mask a := by
  refine ⟨ha, ?_, ?_⟩
  · rintro rfl
    apply h.2.2
    apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_xor]
  · rintro rfl
    apply h.2.1
    apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_xor]
theorem proper_nrm {mask a : Word} (ha : Masked mask a) (h : Proper mask (nrm mask a)) :
    Proper mask a := by
  unfold nrm at h
  split at h
  · exact proper_xor ha h
  · exact h
def primeW (d : Bool) (a b : Word) : Word := if d then Nat.lor a b else Nat.land a b
theorem masked_primeW {mask : Word} (d : Bool) {a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (primeW d a b) := by
  cases d
  · exact masked_land_left ha
  · exact masked_lor ha hb
theorem nrm_primeW {mask : Word} (hm0 : mask.testBit 0 = true) (d : Bool) {a b : Word}
    (ha : Masked mask a) (hb : Masked mask b) :
    ∃ e : Nat, e < 4 ∧ nrm mask (primeW d a b) = binOp mask e (nrm mask a) (nrm mask b) := by
  let e : Nat := if d then (if a.testBit 0 then (if b.testBit 0 then 0 else 2) else (if b.testBit 0 then 3 else 1))
    else (if a.testBit 0 then (if b.testBit 0 then 1 else 3) else (if b.testBit 0 then 2 else 0))
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e]; split_ifs <;> omega
  · apply Nat.eq_of_testBit_eq
    intro k
    cases hm : mask.testBit k with
    | false =>
      have h1 := masked_testBit_false (masked_nrm (masked_primeW d ha hb)) hm
      have h2 := masked_testBit_false (masked_binOp (d := e) (masked_nrm ha) (masked_nrm hb)) hm
      rw [h1, h2]
    | true =>
      dsimp only [e]
      cases d <;> cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0 <;>
        simp only [nrm, primeW, binOp, nat_land_eq, nat_lor_eq, nat_xor_eq,
          Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha0, hb0, hm0, hm,
          Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false,
          Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
          Bool.false_eq_true, ite_true, ite_false] <;>
        cases hx : a.testBit k <;> cases hy : b.testBit k <;> rfl
def Live (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {target} ∧ Proper mask target
  | k + 1, S => ∃ (U : Finset Word) (a b : Word) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ Proper mask a ∧ Proper mask b ∧ a ≠ b ∧
      binOp mask d a b ∉ insert a (insert b U) ∧ Live mask target k (insert (binOp mask d a b) U)
theorem Live.stop {mask target : Word} (hp : Proper mask target) : Live mask target 0 {target} := ⟨rfl, hp⟩
theorem Live.binary {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {d : Nat}
    (hd : d < 4) (ha : Proper mask a) (hb : Proper mask b) (hab : a ≠ b)
    (hfresh : binOp mask d a b ∉ insert a (insert b U))
    (tail : Live mask target k (insert (binOp mask d a b) U)) :
    Live mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩
theorem Live.ind {mask target : Word} {motive : ∀ (k : Nat) (S : Finset Word), Live mask target k S → Prop}
    (stop : ∀ (hp : Proper mask target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Word} {a b : Word} {d : Nat} (hd : d < 4)
      (ha : Proper mask a) (hb : Proper mask b) (hab : a ≠ b)
      (hfresh : binOp mask d a b ∉ insert a (insert b U))
      (tail : Live mask target k (insert (binOp mask d a b) U)),
      motive k (insert (binOp mask d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Word} (h : Live mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
theorem live_proper {mask target k S} (h : Live mask target k S) : ∀ a ∈ S, Proper mask a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
theorem live_size {mask target k S} (h : Live mask target k S) : S.card ≤ k + 1 := by
  induction h using Live.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : binOp mask d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def represented (mask : Word) (w : List Word) (v : Word) : Prop := v ∈ w ∨ ¬Proper mask v
def Repr (mask : Word) (w : List Word) (v : Word) : Prop := represented mask w (nrm mask v)
def witnessBin (mask : Word) (w : List Word) (z : Word) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ Proper mask a ∧ Proper mask b ∧ a ≠ b ∧ z = binOp mask d a b
theorem bin_laws {mask a : Word} (ha : Masked mask a) :
    binOp mask 0 a mask = a ∧ binOp mask 1 a 0 = a ∧
    binOp mask 0 a 0 = 0 ∧ binOp mask 1 a mask = mask ∧
    binOp mask 0 a a = a ∧ binOp mask 1 a a = a ∧
    binOp mask 2 a a = 0 ∧ binOp mask 3 a a = 0 ∧
    binOp mask 2 a 0 = a ∧ binOp mask 3 0 a = a ∧
    binOp mask 2 0 a = 0 ∧ binOp mask 3 a 0 = 0 ∧
    binOp mask 0 0 a = 0 ∧ binOp mask 1 0 a = a ∧
    binOp mask 0 mask a = a ∧ binOp mask 1 mask a = mask := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    (apply Nat.eq_of_testBit_eq; intro k;
     have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha;
     simp only [binOp, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit] at h1 ⊢;
     cases hm : mask.testBit k <;> cases hx : a.testBit k <;> simp_all)
theorem bin_rep {mask w a b} (d : Nat) (hd : d < 4)
    (ma : Masked mask a) (mb : Masked mask b)
    (ha : represented mask w a) (hb : represented mask w b)
    (no : a ≠ mask ∧ b ≠ mask) :
    represented mask w (binOp mask d a b) ∨ witnessBin mask w (binOp mask d a b) := by
  have rz : represented mask w 0 := Or.inr (fun h => h.2.1 rfl)
  have ro : represented mask w mask := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws ma
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws mb
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  by_cases he : a = b
  · subst b; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  by_cases az : a = 0
  · subst a; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  by_cases bz : b = 0
  · subst b; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  have pa : Proper mask a := ⟨ma, az, no.1⟩
  have pb : Proper mask b := ⟨mb, bz, no.2⟩
  exact Or.inr ⟨d, a, b, hd, ha.resolve_right (fun x => x pa), hb.resolve_right (fun x => x pb), pa, pb, he, rfl⟩
theorem norm_ne_mask {mask a : Word} (hm0 : mask.testBit 0 = true) : nrm mask a ≠ mask := by
  intro h
  have := nrm_zero_bit (a := a) hm0
  rw [h, hm0] at this
  exact Bool.noConfusion this
theorem primeW_rep {mask w a b} (hm0 : mask.testBit 0 = true) (d : Bool)
    (ma : Masked mask a) (mb : Masked mask b)
    (ha : Repr mask w a) (hb : Repr mask w b) :
    Repr mask w (primeW d a b) ∨ witnessBin mask w (nrm mask (primeW d a b)) := by
  obtain ⟨e, he, eq⟩ := nrm_primeW hm0 d ma mb
  unfold Repr
  rw [eq]
  exact bin_rep e he (masked_nrm ma) (masked_nrm mb) ha hb ⟨norm_ne_mask hm0, norm_ne_mask hm0⟩
theorem repr_const {mask : Word} {w : List Word} {v : Word} (mv : Masked mask v) (h : v = 0 ∨ v = mask) : Repr mask w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm mv hp
  rcases h with rfl | rfl
  · exact this.2.1 rfl
  · exact this.2.2 rfl
theorem pull_gate {mask target : Word} {w : List Word} {z : Word} {k S c}
    (h : Live mask target k S)
    (hz : represented mask w z ∨ (c = 1 ∧ witnessBin mask w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ Live mask target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases List.mem_append.mp (sub a ha) with hu | hu
      · exact hu
      · rw [List.mem_singleton.mp hu]; exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binOp mask d a b)
        have ht : Live mask target k (insert (binOp mask d a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm'
        have hf : binOp mask d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary hd pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
abbrev WireFn (R : Type) := R → Bool
def obs (w : Word) : WireFn Row := fun r => bit r w
def inv {R} (a : WireFn R) : WireFn R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : WireFn R) : WireFn R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : WireFn R) : WireFn R :=
  if d = 0 then combine false a b
  else if d = 1 then combine true a b
  else if d = 2 then combine false a (inv b)
  else combine false (inv a) b
def Constant {R} (a : WireFn R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : WireFn R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (WireFn R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (WireFn R)) (v : WireFn R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool
def supply {R} (pool xs : List (WireFn R)) : Prop := ∀ a ∈ xs, Available pool a
def Reach {R} (roots : List (WireFn R)) : Nat → List (WireFn R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (WireFn R)) (a b : WireFn R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank
theorem Reach.start {R} {roots : List (WireFn R)} : Reach roots 0 roots := rfl
theorem Reach.two {R} {roots : List (WireFn R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩
theorem Reach.ind {R} {roots : List (WireFn R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih =>
    obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run {R} (goal : WireFn R) : Nat → List (WireFn R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : WireFn R) (rest : List (WireFn R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R} {goal : WireFn R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : WireFn R} {s : Nat} {xs zs : List (WireFn R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h
    exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩
theorem Run.two {R} {goal : WireFn R} {s : Nat} {a b : WireFn R} {rest : List (WireFn R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) : Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩
theorem Run.ind {R} {goal : WireFn R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : op < 4) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem mass_cons {R} (a : WireFn R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_kept {R} (a : WireFn R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]
theorem inv_constant {R} {a : WireFn R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
theorem inv_inv' {R} (a : WireFn R) : inv (inv a) = a := by funext r; simp [inv]
theorem cost_inv {R} (a : WireFn R) : cost (inv a) = cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (this.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (this.mp x))]
theorem avail_inv {R} {bank : List (WireFn R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : WireFn R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩
theorem from_constant {R} (op) {a b : WireFn R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R} {bank v} (w : WireFn R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
theorem extend_two {R} (roots : List (WireFn R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩
theorem comb_prime {R} {bank : List (WireFn R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩
theorem extend_comb {R} (roots : List (WireFn R)) {p bank a b} (d) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]
theorem contraction {R} {goal : WireFn R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (WireFn R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : WireFn R) : WireFn S := fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : WireFn R) (ws) :
    (kept k a ws).map (restrictRows rows) = kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : WireFn R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih
theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (WireFn S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev SubRow (mask : Word) := { r : Row // bit r mask = true }
def obsM (mask : Word) (w : Word) : WireFn (SubRow mask) := fun r => bit r.1 w
theorem obsM_binOp {mask a b : Word} {d : Nat} (hd : d < 4) (ha : Masked mask a) (hb : Masked mask b) :
    obsM mask (binOp mask d a b) = comb d (obsM mask a) (obsM mask b) := by
  funext r
  have h := binOp_testBit hd ha hb r.1.val
  have hm : mask.testBit r.1.val = true := r.2
  simp only [obsM, bit, comb, combine, inv] at h ⊢
  rw [hm] at h
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> simpa using h
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin (k : Bool) (a : Word) (l : List Word) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {mask T : Word} {k S} (h : Live mask T k S) (v : List Word)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (obsM mask T) k (v.map (obsM mask)) := by
  classical
  induction h using Live.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : binOp mask d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (binOp mask d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((binOp mask d a b :: kept ka a (kept kb b rest)).map (obsM mask)) at progress
    rw [List.map_cons, map_kept, map_kept, obsM_binOp hd ha.1 hb.1] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
def tableM (mask : Word) (f : WireFn (SubRow mask)) : Word :=
  (List.finRange 256).foldl (fun acc r =>
    if h : bit r mask = true then if f ⟨r, h⟩ then Nat.lor acc (Nat.shiftLeft 1 r.val) else acc else acc) 0
theorem foldl_testBit_set (l : List Row) (acc : Word) (p : Row → Bool) (r : Row)
    (hn : l.Nodup) :
    (l.foldl (fun a x => if p x then Nat.lor a (Nat.shiftLeft 1 x.val) else a) acc).testBit r.val =
      (acc.testBit r.val || (decide (r ∈ l) && p r)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.nodup_cons] at hn ⊢
    rw [ih _ hn.2]
    by_cases hxr : r = x
    · subst hxr
      have hnot : r ∉ xs := hn.1
      simp only [List.mem_cons, true_or, decide_true, hnot, decide_false, Bool.false_and, Bool.or_false, Bool.true_and]
      cases hp : p r
      · simp
      · simp [nat_lor_eq, Nat.testBit_or, Nat.testBit_shiftLeft]
    · simp only [List.mem_cons, hxr, false_or]
      cases hp : p x
      · rfl
      · have hne : r.val ≠ x.val := fun e => hxr (Fin.ext e)
        have htb : (Nat.shiftLeft 1 x.val).testBit r.val = false := by rw [testBit_one_shl]; simp [hne]
        simp only [ite_true, nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]
theorem tableM_masked {mask : Word} (hm : Masked fullMask mask) (f : WireFn (SubRow mask)) :
    Masked mask (tableM mask f) := by
  have hstep : ∀ (l : List Row) (acc : Word), Masked mask acc →
      Masked mask (l.foldl (fun a x => if h : bit x mask = true then if f ⟨x, h⟩ then Nat.lor a (Nat.shiftLeft 1 x.val) else a else a) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc hacc
      apply ih
      dsimp only
      split_ifs with hx hf
      · apply masked_lor hacc
        apply Nat.eq_of_testBit_eq
        intro k
        rw [nat_land_eq, Nat.testBit_and]
        by_cases hkx : k = x.val
        · subst hkx; have : mask.testBit x.val = true := hx; simp [this]
        · have htb : (Nat.shiftLeft 1 x.val).testBit k = false := by rw [testBit_one_shl]; simp [hkx]
          rw [htb]; simp
      · exact hacc
      · exact hacc
  exact hstep _ 0 (masked_zero mask)
theorem tableM_bit {mask : Word} (f : WireFn (SubRow mask)) (r : SubRow mask) :
    bit r.1 (tableM mask f) = f r := by
  let p : Row → Bool := fun x => if h : bit x mask = true then f ⟨x, h⟩ else false
  have heq : tableM mask f = (List.finRange 256).foldl (fun a x => if p x then Nat.lor a (Nat.shiftLeft 1 x.val) else a) 0 := by
    unfold tableM
    congr 1; funext a x; simp only [p]
    by_cases h : bit x mask = true
    · simp [h]
    · simp [h]
  rw [bit, heq, foldl_testBit_set _ _ _ r.1 (List.nodup_finRange 256)]
  simp [p, r.2]
theorem tableM_obsM {mask : Word} (hm : Masked fullMask mask) {w : Word} (hw : Masked mask w) :
    tableM mask (obsM mask w) = w := by
  apply masked_ext hm (tableM_masked hm _) hw
  intro r
  by_cases hr : bit r mask = true
  · exact tableM_bit (obsM mask w) ⟨r, hr⟩
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit, masked_testBit_false hw hfalse]
theorem tableM_inv {mask : Word} (hm : Masked fullMask mask) (f : WireFn (SubRow mask)) :
    tableM mask (inv f) = Nat.xor mask (tableM mask f) := by
  apply masked_ext hm (tableM_masked hm _) (masked_xor (tableM_masked hm _))
  intro r
  by_cases hr : bit r mask = true
  · rw [tableM_bit (inv f) ⟨r, hr⟩]
    change inv f ⟨r, hr⟩ = (mask ^^^ tableM mask f).testBit r.val
    rw [Nat.testBit_xor]
    have h1 : mask.testBit r.val = true := hr
    have h2 : (tableM mask f).testBit r.val = f ⟨r, hr⟩ := tableM_bit f ⟨r, hr⟩
    rw [h1, h2]; simp [inv]
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit,
      masked_testBit_false (masked_xor (tableM_masked hm _)) hfalse]
theorem tableM_combine {mask : Word} (hm : Masked fullMask mask) (d : Bool) (f g : WireFn (SubRow mask)) :
    tableM mask (combine d f g) = primeW d (tableM mask f) (tableM mask g) := by
  apply masked_ext hm (tableM_masked hm _) (masked_primeW d (tableM_masked hm _) (tableM_masked hm _))
  intro r
  by_cases hr : bit r mask = true
  · rw [tableM_bit (combine d f g) ⟨r, hr⟩]
    have hf := tableM_bit f ⟨r, hr⟩
    have hg := tableM_bit g ⟨r, hr⟩
    cases d <;> simp [combine, primeW, bit, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or] at hf hg ⊢ <;> rw [hf, hg]
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit,
      masked_testBit_false (masked_primeW d (tableM_masked hm _) (tableM_masked hm _)) hfalse]
theorem available_rep {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {bank : List (WireFn (SubRow mask))} {a : WireFn (SubRow mask)} (h : Available bank a) :
    Repr mask ((bank.map (tableM mask)).map (nrm mask)) (tableM mask a) := by
  rcases h with hmem | ⟨b, rfl⟩ | hinv
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hmem))
  · apply repr_const (tableM_masked hm _)
    cases b
    · left
      apply masked_ext hm (tableM_masked hm _) (masked_zero mask)
      intro r
      by_cases hr : bit r mask = true
      · exact (tableM_bit _ ⟨r, hr⟩).trans (by simp [bit])
      · have hf : mask.testBit r.val = false := by simpa [bit] using hr
        rw [bit, masked_testBit_false (tableM_masked hm _) hf]; simp [bit]
    · right
      apply masked_ext hm (tableM_masked hm _) (masked_self mask)
      intro r
      by_cases hr : bit r mask = true
      · exact (tableM_bit _ ⟨r, hr⟩).trans hr.symm
      · have hf : mask.testBit r.val = false := by simpa [bit] using hr
        rw [bit, masked_testBit_false (tableM_masked hm _) hf, bit, hf]
  · have hi := tableM_inv hm a
    refine Or.inl ?_
    rw [← nrm_xor hm0 (tableM_masked hm a), ← hi]
    exact List.mem_map_of_mem (List.mem_map_of_mem hinv)
theorem reach_live_sub {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List (WireFn (SubRow mask))} {p bank}
    (h : Reach roots p bank) {T k S} (run : Live mask T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map (tableM mask)).map (nrm mask)) :
    ∃ l V, l ≤ p + k ∧ Live mask T l V ∧ ∀ a ∈ V, a ∈ (roots.map (tableM mask)).map (nrm mask) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, tableM_combine hm] at sub
    have rep := primeW_rep hm0 d (tableM_masked hm a) (tableM_masked hm b)
      (available_rep hm hm0 ha) (available_rep hm hm0 hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pull_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun w hw => by simpa [or_comm] using sub w hw)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩
def plainWord (mask a : Word) : Bool := Nat.beq (Nat.land a mask) a && !a.testBit 0
theorem nrm_map {mask : Word} {w : List Word} (h : w.all (plainWord mask) = true) :
    w.map (nrm mask) = w := by
  have e : w.map (nrm mask) = w.map id := by
    apply List.map_congr_left
    intro a ha
    have hp := List.all_eq_true.mp h a ha
    simp only [plainWord, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact nrm_id hp.2
  rw [e, List.map_id]
def LowerM (mask : Word) (roots : List Word) (T : Word) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map (obsM mask)) p bank → Available bank (obsM mask T) → L ≤ p
def Impossible (mask T : Word) (cap : Nat) (S : Finset Word) : Prop :=
  ∀ k, k ≤ cap → ¬Live mask T k S
def Essential (mask T : Word) (roots : List Word) (a : Word) : Prop :=
  ∃ r s : Row, bit r mask = true ∧ bit s mask = true ∧ bit r T ≠ bit s T ∧
    ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem live_row_difference {mask T k S} (h : Live mask T k S) {r s : Row}
    (hr : bit r mask = true) (hs : bit s mask = true) (diff : bit r T ≠ bit s T) :
    ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d hd ha hb _ _ _ ih =>
    obtain ⟨v, hv, hdv⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b, by simp, ?_⟩
        intro beq
        apply hdv
        have h1 := binOp_testBit hd ha.1 hb.1 r.val
        have h2 := binOp_testBit hd ha.1 hb.1 s.val
        simp only [bit] at hr hs aeq beq ⊢
        rw [hr] at h1; rw [hs] at h2
        rw [h1, h2, aeq, beq]
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hdv⟩
theorem raw_required {mask T k S} (h : Live mask T k S) (roots : List Word) (a : Word)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (hr : bit r mask = true) (hs : bit s mask = true)
    (diff : bit r T ≠ bit s T) (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := live_row_difference h hr hs diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
theorem reach_live {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List Word} {p bank T} (hp : Proper mask T) (nT : plainWord mask T = true)
    (nR : roots.all (plainWord mask) = true)
    (h : Reach (roots.map (obsM mask)) p bank) (hit : Available bank (obsM mask T)) :
    ∃ k S, k ≤ p ∧ Live mask T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm' := available_rep hm hm0 hit
  rw [tableM_obsM hm hp.1] at hm'
  unfold Repr at hm'
  have nT0 : T.testBit 0 = false := by
    simp only [plainWord, Bool.and_eq_true, Bool.not_eq_true'] at nT; exact nT.2
  rw [nrm_id nT0] at hm'
  have mem := hm'.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reach_live_sub hm hm0 h (Live.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map (obsM mask)).map (tableM mask) = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha
    have hpa := List.all_eq_true.mp nR a ha
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at hpa
    exact tableM_obsM hm hpa.1
  rw [e, nrm_map nR] at hs
  exact hs
theorem lower_impossible {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List Word} {T L} (hp : Proper mask T) (nT : plainWord mask T = true)
    (nR : roots.all (plainWord mask) = true)
    (essential : ∀ a ∈ roots, Essential mask T roots a)
    (noRun : Impossible mask T L roots.toFinset) : LowerM mask roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reach_live hm hm0 hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm' => ?_, hs a⟩
    obtain ⟨r, s, hr, hs', hd, iso⟩ := essential _ hm'
    exact raw_required run roots a hs r s hr hs' hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem observe_proper {mask v : Word} (hm : Masked fullMask mask) (hv : Proper mask v) :
    ¬Constant (obsM mask v) := by
  rintro ⟨b, h⟩
  cases b
  · apply hv.2.1
    apply masked_ext hm hv.1 (masked_zero mask)
    intro r
    by_cases hr : bit r mask = true
    · exact (congrFun h ⟨r, hr⟩).trans (by simp [bit])
    · have hf : mask.testBit r.val = false := by simpa [bit] using hr
      rw [bit, masked_testBit_false hv.1 hf]; simp [bit]
  · apply hv.2.2
    apply masked_ext hm hv.1 (masked_self mask)
    intro r
    by_cases hr : bit r mask = true
    · exact (congrFun h ⟨r, hr⟩).trans hr.symm
    · have hf : mask.testBit r.val = false := by simpa [bit] using hr
      rw [bit, masked_testBit_false hv.1 hf, bit, hf]
def Slice (mask : Word) (raw : List Word) (T dom : Word) (L : Nat) : Prop :=
  ∃ (subMask : Word) (f : SubRow subMask → SubRow mask) (roots : List Word),
    (∀ r, bit (f r).1 dom = true) ∧
    (∀ a ∈ raw, Available (roots.map (obsM subMask)) (restrictRows f (obsM mask a))) ∧
    ¬Constant (restrictRows f (obsM mask T)) ∧
    ∀ p bank, Reach (roots.map (obsM subMask)) p bank →
      Available bank (restrictRows f (obsM mask T)) → L ≤ p
def checkSlice (f : Row → Row) (mask : Word) (raw : List Word) (T dom : Word)
    (subMask : Word) (roots : List Word) (subT : Word) : Bool :=
  forceSpine (((List.finRange 256).filter (fun r => bit r subMask)).map (fun r => (r, f r))) fun ps =>
    ps.all (fun p => bit p.2 mask && bit p.2 dom && (bit p.2 T == bit p.1 subT)) &&
    raw.all (fun a =>
      ps.all (fun p => !bit p.2 a) ||
      ps.all (fun p => bit p.2 a) ||
      roots.any (fun b => ps.all (fun p => bit p.2 a == bit p.1 b)))
theorem checkSlice_sound {f : Row → Row} {mask : Word} {raw : List Word} {T dom subMask : Word}
    {roots : List Word} {subT : Word} {L : Nat}
    (hmSub : Masked fullMask subMask) (hpSub : Proper subMask subT)
    (hL : LowerM subMask roots subT L)
    (hc : checkSlice f mask raw T dom subMask roots subT = true) :
    Slice mask raw T dom L := by
  unfold checkSlice at hc
  rw [forceSpine_eq] at hc
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, List.any_eq_true] at hc
  obtain ⟨hrows, hraw⟩ := hc
  have hmem (r : SubRow subMask) : (r.1, f r.1) ∈ ((List.finRange 256).filter (fun x => bit x subMask)).map (fun x => (x, f x)) :=
    List.mem_map.mpr ⟨r.1, List.mem_filter.mpr ⟨List.mem_finRange r.1, r.2⟩, rfl⟩
  have hfM : ∀ r : SubRow subMask, bit (f r.1) mask = true := fun r => (hrows _ (hmem r)).1.1
  let g : SubRow subMask → SubRow mask := fun r => ⟨f r.1, hfM r⟩
  have hdom : ∀ r : SubRow subMask, bit (g r).1 dom = true := fun r => (hrows _ (hmem r)).1.2
  have hTeq : restrictRows g (obsM mask T) = obsM subMask subT :=
    funext fun r => (hrows _ (hmem r)).2
  refine ⟨subMask, g, roots, hdom, ?_, hTeq ▸ observe_proper hmSub hpSub, hTeq ▸ hL⟩
  intro a ha
  rcases hraw a ha with (hz | ho) | ⟨b, hb, he⟩
  · exact Or.inr (Or.inl ⟨false, funext fun r => hz _ (hmem r)⟩)
  · exact Or.inr (Or.inl ⟨true, funext fun r => ho _ (hmem r)⟩)
  · exact Or.inl (List.mem_map.mpr ⟨b, hb, funext fun r => (he _ (hmem r)).symm⟩)
def checkEssential (mask T : Word) (roots : List Word) (a : Word) (r s : Row) : Bool :=
  bit r mask && bit s mask && (bit r T != bit s T) &&
    roots.all (fun w => Nat.beq w a || (bit r w == bit s w))
theorem checkEssential_sound {mask T : Word} {roots : List Word} {a : Word} {r s : Row}
    (h : checkEssential mask T roots a r s = true) : Essential mask T roots a := by
  simp only [checkEssential, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true,
    Nat.beq_eq, beq_iff_eq] at h
  exact ⟨r, s, h.1.1.1, h.1.1.2, h.1.2, fun w hw hne => (h.2 w hw).resolve_left hne⟩
def checkAllEss (mask T : Word) (roots : List Word) (ps : List Nat) : Bool :=
  (List.zip roots ps).length == roots.length &&
  (List.zip roots ps).all (fun (a, x) =>
    checkEssential mask T roots a
      ⟨Nat.mod (Nat.div x 256) 256, Nat.mod_lt _ (by decide)⟩
      ⟨Nat.mod x 256, Nat.mod_lt _ (by decide)⟩)
theorem checkAllEss_sound {mask T : Word} {roots : List Word} {ps : List Nat}
    (h : checkAllEss mask T roots ps = true) : ∀ a ∈ roots, Essential mask T roots a := by
  simp only [checkAllEss, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (List.zip roots ps).length := by omega
  have hmem : (List.zip roots ps)[i] ∈ List.zip roots ps := List.getElem_mem hi'
  have he := hall _ hmem
  simp only [List.getElem_zip] at he
  exact checkEssential_sound he
def isConst (dom a : Word) : Bool :=
  forceNat (Nat.land a dom) fun m =>
    match Nat.beq m 0 with | true => true | false => Nat.beq m dom
theorem isConst_eq (dom a : Word) :
    isConst dom a = (Nat.beq (Nat.land a dom) 0 || Nat.beq (Nat.land a dom) dom) := by
  unfold isConst
  rw [forceNat_eq]
  cases Nat.beq (Nat.land a dom) 0 <;> rfl
theorem masked_zero_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (hz : Nat.land a dom = 0) :
    restrictRows f (obsM mask a) = fun _ => false := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) hz
  simp only [nat_land_eq, Nat.testBit_and, Nat.zero_testBit] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true] at h1
  exact h1
theorem masked_one_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (ho : Nat.land a dom = dom) :
    restrictRows f (obsM mask a) = fun _ => true := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) ho
  simp only [nat_land_eq, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true] at h1
  exact h1
theorem masked_eq_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a b : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (heq : Nat.land a dom = Nat.land b dom) :
    restrictRows f (obsM mask a) = restrictRows f (obsM mask b) := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) heq
  simp only [nat_land_eq, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true, Bool.and_true] at h1
  exact h1
theorem masked_neg_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a b : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (heq : Nat.xor (Nat.land a dom) dom = Nat.land b dom) :
    inv (restrictRows f (obsM mask a)) = restrictRows f (obsM mask b) := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) heq
  simp only [nat_xor_eq, nat_land_eq, Nat.testBit_xor, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true, Bool.and_true] at h1
  simpa [inv, restrictRows, obsM, bit] using h1
theorem count_constants {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (ws : List Word) :
    ws.countP (isConst dom) ≤ mass ((ws.map (obsM mask)).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases hc : isConst dom a
    · simpa using ih.trans (Nat.le_add_left _ _)
    · rw [isConst_eq, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hc
      have hcon : Constant (restrictRows f (obsM mask a)) := by
        rcases hc with hz | ho
        · exact ⟨false, masked_zero_fn hdom hz⟩
        · exact ⟨true, masked_one_fn hdom ho⟩
      simpa [cost, hcon, Nat.add_comm] using Nat.succ_le_succ ih
theorem slice_lift {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {raw : List Word} {T dom : Word} {L : Nat}
    (hp : Proper mask T) (nT : plainWord mask T = true) (nR : raw.all (plainWord mask) = true)
    (nd : raw.Nodup) (ess : ∀ a ∈ raw, Essential mask T raw a)
    (hsl : Slice mask raw T dom L) :
    LowerM mask raw T (L + raw.countP (isConst dom)) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reach_live hm hm0 hp nT nR hr hit
  have he : raw.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun h => ?_, sub a⟩
    obtain ⟨r, s, hrm, hsm, hd, iso⟩ := ess a h
    exact raw_required run raw a sub r s hrm hsm hd iso
  obtain ⟨subMask, f, roots, hdom, hsup, hnc, hlo⟩ := hsl
  have rrun := list_run run raw nd he
  have psup : supply (roots.map (obsM subMask)) ((raw.map (obsM mask)).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h1
    exact hsup a ha
  have pb := projected_bound f rrun hnc Reach.start psup hlo
  have cc := count_constants hdom raw
  omega
noncomputable def containsNat (z : Word) (ws : List Word) : Bool :=
  List.rec false (fun w _ ih => cond (Nat.beq w z) true ih) ws
theorem containsNat_iff (z : Word) (ws : List Word) : containsNat z ws = true ↔ z ∈ ws := by
  induction ws with
  | nil => simp [containsNat]
  | cons w ws ih =>
    change cond (Nat.beq w z) true (containsNat z ws) = true ↔ _
    cases h : Nat.beq w z
    · have hne : z ≠ w := fun e => by rw [Nat.beq_eq.mpr e.symm] at h; exact Bool.noConfusion h
      simp [ih, hne]
    · simp [Nat.beq_eq.mp h]
noncomputable def availableB (dom : Word) (bank : List Word) (a : Word) : Bool :=
  forceNat (Nat.land a dom) fun m =>
    match Nat.beq m 0 with
    | true => true
    | false =>
      match Nat.beq m dom with
      | true => true
      | false =>
        match containsNat m bank with
        | true => true
        | false =>
          match Nat.beq (Nat.land dom 1) 1 with
          | true => false
          | false => forceNat (Nat.xor m dom) fun mn => containsNat mn bank
def poolSupply {mask subMask : Word} (f : SubRow subMask → SubRow mask)
    (bank : List (WireFn (SubRow subMask))) (ws : List Word) : Prop :=
  ∀ a ∈ ws, Available bank (restrictRows f (obsM mask a))
theorem availableB_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom a : Word} {bank : List (WireFn (SubRow subMask))} {pool : List Word}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hpool : ∀ v ∈ pool, Masked dom v ∧ Available bank (restrictRows f (obsM mask v)))
    (hc : availableB dom pool a = true) :
    Available bank (restrictRows f (obsM mask a)) := by
  unfold availableB at hc
  rw [forceNat_eq] at hc
  cases h0 : Nat.beq (Nat.land a dom) 0 with
  | true =>
    exact Or.inr (Or.inl ⟨false, masked_zero_fn hdom (Nat.beq_eq.mp h0)⟩)
  | false =>
    rw [h0] at hc
    cases h1 : Nat.beq (Nat.land a dom) dom with
    | true =>
      exact Or.inr (Or.inl ⟨true, masked_one_fn hdom (Nat.beq_eq.mp h1)⟩)
    | false =>
      rw [h1] at hc
      cases h2 : containsNat (Nat.land a dom) pool with
      | true =>
        have hm := (containsNat_iff _ _).mp h2
        obtain ⟨md, av⟩ := hpool _ hm
        have heq : Nat.land a dom = Nat.land (Nat.land a dom) dom := (md).symm
        exact masked_eq_fn hdom heq ▸ av
      | false =>
        rw [h2] at hc
        cases hd0 : Nat.beq (Nat.land dom 1) 1 with
        | true => rw [hd0] at hc; cases hc
        | false =>
          rw [hd0, forceNat_eq] at hc
          have hm := (containsNat_iff _ _).mp hc
          obtain ⟨md, av⟩ := hpool _ hm
          have heq : Nat.xor (Nat.land a dom) dom = Nat.land (Nat.xor (Nat.land a dom) dom) dom := md.symm
          have hinv := masked_neg_fn hdom heq
          have hav := avail_inv (hinv ▸ av)
          rwa [inv_inv'] at hav
structure CutSpec where
  dom : Word
  bound : Nat
  stock : List Word
def ValidCut (mask : Word) (raw : List Word) (T : Word) (c : CutSpec) : Prop :=
  Slice mask raw T c.dom c.bound ∧
  ∀ v ∈ c.stock, Masked c.dom v ∧ ∃ a ∈ raw, Nat.land a c.dom = v
def mkPairs (ps : List Nat) : List (Row × Row) :=
  ps.map (fun x => (⟨Nat.mod (Nat.div x 256) 256, Nat.mod_lt _ (by decide)⟩,
                    ⟨Nat.mod x 256, Nat.mod_lt _ (by decide)⟩))
def mkCut (raw : List Word) (dom : Word) (bound : Nat) : CutSpec :=
  ⟨dom, bound, (raw.map (fun a => Nat.land a dom)).filter (fun v => !Nat.beq v 0 && !Nat.beq v dom)⟩
theorem mkCut_valid {f : Row → Row} {mask : Word} {raw : List Word} {T dom subMask : Word}
    {roots : List Word} {subT : Word} {L : Nat}
    (hL : LowerM subMask roots subT L)
    (hc : (Nat.beq (Nat.land subMask fullMask) subMask &&
          Nat.beq (Nat.land subT subMask) subT &&
          !Nat.beq subT 0 && !Nat.beq subT subMask &&
          checkSlice f mask raw T dom subMask roots subT) = true) :
    ValidCut mask raw T (mkCut raw dom L) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have h3' : subT ≠ 0 := fun e => by rw [e] at h3; cases h3
  have h4' : subT ≠ subMask := fun e => by rw [e] at h4; exact absurd (Nat.beq_eq.mpr rfl) (by rw [h4]; decide)
  refine ⟨checkSlice_sound h1 ⟨h2, h3', h4'⟩ hL h5, fun v hv => ?_⟩
  simp only [mkCut, List.mem_filter, List.mem_map] at hv
  obtain ⟨⟨a, ha, rfl⟩, _⟩ := hv
  exact ⟨masked_land_right (masked_self dom), a, ha, rfl⟩
structure MatPool where
  dom : Word
  bound : Nat
  paid : Nat
  bank : List Word
  wsConstMask : Nat
  wsConstCnt : Nat
def ValidPool (mask : Word) (raw : List Word) (T : Word) (ws : List Word) (p : MatPool) : Prop :=
  ∃ (subMask : Word) (f : SubRow subMask → SubRow mask) (roots : List Word)
    (bank : List (WireFn (SubRow subMask))),
    (∀ r, bit (f r).1 p.dom = true) ∧
    ¬Constant (restrictRows f (obsM mask T)) ∧
    (∀ q bs, Reach (roots.map (obsM subMask)) q bs → Available bs (restrictRows f (obsM mask T)) → p.bound ≤ q) ∧
    Reach (roots.map (obsM subMask)) p.paid bank ∧
    (∀ v ∈ p.bank, Masked p.dom v ∧ Available bank (restrictRows f (obsM mask v))) ∧
    poolSupply f bank ws ∧
    (∀ i < ws.length, (Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 i)) 2 == 1) = isConst p.dom (ws.getD i 0)) ∧
    p.wsConstCnt = ws.countP (isConst p.dom)
noncomputable def recipeGateD (dom : Word) (bank : List Word) (w a b : Word) : Bool :=
  match availableB dom bank a with
  | false => false
  | true =>
    match availableB dom bank b with
    | false => false
    | true =>
      forceNat (Nat.land w dom) fun mw =>
        forceNat (Nat.land a dom) fun ma =>
          forceNat (Nat.land b dom) fun mb =>
            match Nat.beq mw (Nat.land ma mb) with
            | true => true
            | false =>
              match Nat.beq mw (Nat.lor ma mb) with
              | true => true
              | false =>
                match Nat.beq mw (Nat.land ma (Nat.xor dom mb)) with
                | true => true
                | false =>
                  match Nat.beq mw (Nat.land (Nat.xor dom ma) mb) with
                  | true => true
                  | false =>
                    match Nat.beq (Nat.xor mw dom) (Nat.land ma mb) with
                    | true => true
                    | false =>
                      match Nat.beq (Nat.xor mw dom) (Nat.lor ma mb) with
                      | true => true
                      | false =>
                        match Nat.beq (Nat.xor mw dom) (Nat.land ma (Nat.xor dom mb)) with
                        | true => true
                        | false =>
                          Nat.beq (Nat.xor mw dom) (Nat.land (Nat.xor dom ma) mb)
theorem recipeGateD_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom w a b : Word} {roots : List (WireFn (SubRow subMask))} {p : Nat}
    {bank : List (WireFn (SubRow subMask))} {pool : List Word}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hr : Reach roots p bank)
    (hpool : ∀ v ∈ pool, Masked dom v ∧ Available bank (restrictRows f (obsM mask v)))
    (hg : recipeGateD dom pool w a b = true) :
    ∃ next, Reach roots (p + 1) next ∧
      ∀ v ∈ (Nat.land w dom) :: pool, Masked dom v ∧ Available next (restrictRows f (obsM mask v)) := by
  unfold recipeGateD at hg
  cases ha : availableB dom pool a with
  | false => simp [ha] at hg
  | true =>
    rw [ha] at hg
    cases hb : availableB dom pool b with
    | false => simp [hb] at hg
    | true =>
      rw [hb, forceNat_eq, forceNat_eq, forceNat_eq] at hg
      have hva := availableB_sound hdom hpool ha
      have hvb := availableB_sound hdom hpool hb
      have mkGate (d : Nat) (hd : d < 4) (flip : Bool)
          (heq : (if flip then Nat.xor (Nat.land w dom) dom else Nat.land w dom) = binOp dom d (Nat.land a dom) (Nat.land b dom)) :
          ∃ next, Reach roots (p + 1) next ∧
            ∀ v ∈ (Nat.land w dom) :: pool, Masked dom v ∧ Available next (restrictRows f (obsM mask v)) := by
        obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime hd hva hvb
        refine ⟨combine op x y :: bank, Reach.two op hr hx hy, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · refine ⟨masked_land_right (masked_self dom), ?_⟩
          have hfn : (if flip then inv (restrictRows f (obsM mask (Nat.land w dom))) else restrictRows f (obsM mask (Nat.land w dom))) =
              comb d (restrictRows f (obsM mask a)) (restrictRows f (obsM mask b)) := by
            funext r
            have hbit := congrArg (fun t => t.testBit (f r).1.val) heq
            have hdr : dom.testBit (f r).1.val = true := hdom r
            have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
            cases flip <;> rcases h4 with rfl | rfl | rfl | rfl <;>
              simp only [ite_true, ite_false, Bool.false_eq_true, binOp, comb, combine, inv, restrictRows, obsM, bit,
                nat_land_eq, nat_lor_eq, nat_xor_eq,
                Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hdr, Bool.and_true,
                show (1 = 0) = False by decide, show (2 = 0) = False by decide, show (3 = 0) = False by decide,
                show (2 = 1) = False by decide, show (3 = 1) = False by decide, show (3 = 2) = False by decide] at hbit ⊢ <;>
              cases hw : w.testBit (f r).1.val <;> cases ha' : a.testBit (f r).1.val <;> cases hb' : b.testBit (f r).1.val <;>
              simp only [hw, ha', hb', Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
                Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, Bool.xor_true, Bool.xor_false,
                Bool.not_true, Bool.not_false] at hbit ⊢ <;> exact hbit
          rw [e] at hfn
          cases flip
          · simp only [Bool.false_eq_true, ite_false] at hfn
            rw [hfn]; exact Or.inl (by simp)
          · simp only [ite_true] at hfn
            have h1 : Available (combine op x y :: bank) (inv (restrictRows f (obsM mask (Nat.land w dom)))) := by
              rw [hfn]; exact Or.inl (by simp)
            have h2 := avail_inv h1
            rwa [inv_inv'] at h2
        · obtain ⟨md, av⟩ := hpool v hmem
          exact ⟨md, available_cons _ av⟩
      cases h0 : Nat.beq (Nat.land w dom) (Nat.land (Nat.land a dom) (Nat.land b dom))
      · rw [h0] at hg
        cases h1 : Nat.beq (Nat.land w dom) (Nat.lor (Nat.land a dom) (Nat.land b dom))
        · rw [h1] at hg
          cases h2 : Nat.beq (Nat.land w dom) (Nat.land (Nat.land a dom) (Nat.xor dom (Nat.land b dom)))
          · rw [h2] at hg
            cases h3 : Nat.beq (Nat.land w dom) (Nat.land (Nat.xor dom (Nat.land a dom)) (Nat.land b dom))
            · rw [h3] at hg
              cases h4 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.land (Nat.land a dom) (Nat.land b dom))
              · rw [h4] at hg
                cases h5 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.lor (Nat.land a dom) (Nat.land b dom))
                · rw [h5] at hg
                  cases h6 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.land (Nat.land a dom) (Nat.xor dom (Nat.land b dom)))
                  · rw [h6] at hg
                    exact mkGate 3 (by omega) true (Nat.beq_eq.mp hg)
                  · exact mkGate 2 (by omega) true (Nat.beq_eq.mp h6)
                · exact mkGate 1 (by omega) true (Nat.beq_eq.mp h5)
              · exact mkGate 0 (by omega) true (Nat.beq_eq.mp h4)
            · exact mkGate 3 (by omega) false (Nat.beq_eq.mp h3)
          · exact mkGate 2 (by omega) false (Nat.beq_eq.mp h2)
        · exact mkGate 1 (by omega) false (Nat.beq_eq.mp h1)
      · exact mkGate 0 (by omega) false (Nat.beq_eq.mp h0)
abbrev HistStep := Word × Word × Word
noncomputable def addNeed (dom : Word) (stock needed : List Word) (w : Word) : List Word :=
  forceNat (Nat.land w dom) fun m =>
    match Nat.beq m 0 with
    | true => needed
    | false =>
      match Nat.beq m dom with
      | true => needed
      | false =>
        match containsNat m stock with
        | true => needed
        | false =>
          match containsNat m needed with
          | true => needed
          | false =>
            match Nat.beq (Nat.land dom 1) 1 with
            | true => m :: needed
            | false =>
              forceNat (Nat.xor m dom) fun mn =>
                match containsNat mn stock with
                | true => needed
                | false =>
                  match containsNat mn needed with
                  | true => needed
                  | false => m :: needed
noncomputable def needStart (dom : Word) (stock : List Word) : List Word → List Word → List Word
  | [], acc => acc
  | w :: ws, acc => needStart dom stock ws (addNeed dom stock acc w)
noncomputable def needClose (dom : Word) (stock : List Word) : List HistStep → List Word → List Word
  | [], acc => acc
  | (w, a, b) :: hs, acc =>
    forceNat (Nat.land w dom) fun m =>
      let acc' := match containsNat m acc with
        | true => addNeed dom stock (addNeed dom stock acc a) b
        | false =>
          match Nat.beq (Nat.land dom 1) 1 with
          | true => acc
          | false =>
            forceNat (Nat.xor m dom) fun mn =>
              match containsNat mn acc with
              | true => addNeed dom stock (addNeed dom stock acc a) b
              | false => acc
      needClose dom stock hs acc'
noncomputable def replayHist (dom : Word) (needed : List Word) : List HistStep → Nat → List Word → Nat × List Word
  | [], paid, bank => (paid, bank)
  | (w, a, b) :: hs, paid, bank =>
    forceNat (Nat.land w dom) fun m =>
      let want := match containsNat m needed with
        | true => true
        | false =>
          match Nat.beq (Nat.land dom 1) 1 with
          | true => false
          | false => forceNat (Nat.xor m dom) fun mn => containsNat mn needed
      match want with
      | false => replayHist dom needed hs paid bank
      | true =>
        match availableB dom bank w with
        | true => replayHist dom needed hs paid bank
        | false =>
          match recipeGateD dom bank w a b with
          | false => replayHist dom needed hs paid bank
          | true => forceNat (Nat.add paid 1) fun p' => replayHist dom needed hs p' (m :: bank)
theorem replayHist_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom : Word} {needed : List Word} {roots : List (WireFn (SubRow subMask))}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hs : List HistStep) :
    ∀ {paid0 : Nat} {bank0 : List (WireFn (SubRow subMask))} {pool0 : List Word},
      Reach roots paid0 bank0 →
      (∀ v ∈ pool0, Masked dom v ∧ Available bank0 (restrictRows f (obsM mask v))) →
      ∃ bank1, Reach roots (replayHist dom needed hs paid0 pool0).1 bank1 ∧
        ∀ v ∈ (replayHist dom needed hs paid0 pool0).2,
          Masked dom v ∧ Available bank1 (restrictRows f (obsM mask v)) := by
  induction hs with
  | nil => intro paid0 bank0 pool0 hr hp; exact ⟨bank0, hr, hp⟩
  | cons st hs ih =>
    obtain ⟨w, a, b⟩ := st
    intro paid0 bank0 pool0 hr hp
    simp only [replayHist, forceNat_eq]
    split
    · exact ih hr hp
    · split
      · exact ih hr hp
      · cases hg : recipeGateD dom pool0 w a b with
        | false => exact ih hr hp
        | true =>
          obtain ⟨next, hr', hp'⟩ := recipeGateD_sound hdom hr hp hg
          exact ih hr' hp'
def buildConstInfo (dom : Word) : List Word → Nat → Nat → Nat → Nat × Nat
  | [], _, cm, cnt => (cm, cnt)
  | w :: ws, idx, cm, cnt =>
    match isConst dom w with
    | false => buildConstInfo dom ws (Nat.add idx 1) cm cnt
    | true =>
      forceNat (Nat.lor cm (Nat.shiftLeft 1 idx)) fun cm' =>
        forceNat (Nat.add cnt 1) fun cnt' =>
          buildConstInfo dom ws (Nat.add idx 1) cm' cnt'
theorem buildConstInfo_low (dom : Word) :
    ∀ (l : List Word) (i0 c0 n0 k : Nat), k < i0 →
      ((buildConstInfo dom l i0 c0 n0).1).testBit k = c0.testBit k := by
  intro l
  induction l with
  | nil => intro i0 c0 n0 k _; rfl
  | cons u us ihu =>
    intro i0 c0 n0 k hk
    simp only [buildConstInfo]
    cases isConst dom u
    · exact ihu (i0 + 1) c0 n0 k (by omega)
    · simp only [forceNat_eq, nat_add_eq]
      rw [ihu (i0 + 1) _ _ k (by omega)]
      have hne : k ≠ i0 := by omega
      have htb : (Nat.shiftLeft 1 i0).testBit k = false := by rw [testBit_one_shl]; simp [hne]
      rw [nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]
theorem mod_div_shl_eq_testBit (x k : Nat) :
    (Nat.mod (Nat.div x (Nat.shiftLeft 1 k)) 2 == 1) = x.testBit k := by
  simp only [nat_mod_eq, nat_div_eq, nat_shl_eq]
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_eq_decide_div_mod_eq]
  cases h : x / 2 ^ k % 2 == 1 <;> simp_all
theorem buildConstInfo_spec (dom : Word) (ws : List Word) :
    ∀ (idx cm cnt : Nat),
      (∀ j ≥ idx, Nat.mod (Nat.div cm (Nat.shiftLeft 1 j)) 2 = 0) →
      (let res := buildConstInfo dom ws idx cm cnt
      (∀ j < ws.length, (Nat.mod (Nat.div res.1 (Nat.shiftLeft 1 (idx + j))) 2 == 1) = isConst dom (ws.getD j 0)) ∧
      res.2 = cnt + ws.countP (isConst dom)) := by
  induction ws with
  | nil =>
    intro idx cm cnt _
    exact ⟨fun j hj => by simp at hj, by simp [buildConstInfo]⟩
  | cons w ws ih =>
    intro idx cm cnt hhi
    simp only [buildConstInfo]
    cases hc : isConst dom w with
    | false =>
      have hhi' : ∀ j ≥ idx + 1, Nat.mod (Nat.div cm (Nat.shiftLeft 1 j)) 2 = 0 := fun j hj => hhi j (by omega)
      obtain ⟨hbits, hcnt⟩ := ih (idx + 1) cm cnt hhi'
      refine ⟨fun j hj => ?_, ?_⟩
      · cases j with
        | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero, hc, nat_add_eq]
          rw [mod_div_shl_eq_testBit, buildConstInfo_low dom ws (idx + 1) cm cnt idx (by omega)]
          have h0 := hhi idx (Nat.le_refl _)
          have hmt := mod_div_shl_eq_testBit cm idx
          rw [h0] at hmt
          exact hmt.symm
        | succ j' =>
          have hstep : idx + (j' + 1) = (idx + 1) + j' := by omega
          rw [hstep]
          exact hbits j' (by simp at hj; omega)
      · simp only [List.countP_cons, hc, Bool.false_eq_true, ite_false, nat_add_eq]
        exact hcnt
    | true =>
      simp only [forceNat_eq]
      let cm' := Nat.lor cm (Nat.shiftLeft 1 idx)
      have hbit_cm' : ∀ k, cm'.testBit k = (cm.testBit k || decide (k = idx)) := by
        intro k
        rw [show cm' = Nat.lor cm (Nat.shiftLeft 1 idx) from rfl, nat_lor_eq, Nat.testBit_or, testBit_one_shl]
      have hhi' : ∀ j ≥ idx + 1, Nat.mod (Nat.div cm' (Nat.shiftLeft 1 j)) 2 = 0 := by
        intro j hj
        have h0 := hhi j (by omega)
        have ht0 : cm.testBit j = false := by
          have := mod_div_shl_eq_testBit cm j; rw [h0] at this; exact this.symm
        have ht1 : cm'.testBit j = false := by
          rw [hbit_cm', ht0]; simp [show j ≠ idx by omega]
        have hmt := mod_div_shl_eq_testBit cm' j
        rw [ht1] at hmt
        simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at hmt ⊢
        have hlt : cm' / (1 <<< j) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hne : cm' / (1 <<< j) % 2 ≠ 1 := by
          intro he; rw [he] at hmt; exact Bool.noConfusion hmt
        omega
      obtain ⟨hbits, hcnt⟩ := ih (idx + 1) cm' (cnt + 1) hhi'
      refine ⟨fun j hj => ?_, ?_⟩
      · cases j with
        | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero, hc, nat_add_eq]
          rw [mod_div_shl_eq_testBit, buildConstInfo_low dom ws (idx + 1) cm' (cnt + 1) idx (by omega), hbit_cm']
          simp
        | succ j' =>
          have hstep : idx + (j' + 1) = (idx + 1) + j' := by omega
          rw [hstep]
          exact hbits j' (by simp at hj; omega)
      · simp only [List.countP_cons, hc, ite_true, nat_add_eq]
        rw [hcnt]; omega
noncomputable def materializeCut (c : CutSpec) (ws : List Word) (hist : List HistStep) : Option MatPool :=
  let needed := needClose c.dom c.stock hist (needStart c.dom c.stock ws [])
  let (paid, bank) := replayHist c.dom needed hist.reverse 0 c.stock
  match ws.all (availableB c.dom bank) with
  | false => none
  | true =>
    let (cm, cnt) := buildConstInfo c.dom ws 0 0 0
    some ⟨c.dom, c.bound, paid, bank, cm, cnt⟩
theorem materializeCut_sound {mask : Word} {raw : List Word} {T : Word} {c : CutSpec}
    (hc : ValidCut mask raw T c) {ws : List Word} {hist : List HistStep} {mp : MatPool}
    (hm : materializeCut c ws hist = some mp) :
    ValidPool mask raw T ws mp := by
  obtain ⟨⟨subMask, f, roots, hdom, hsup, hnc, hlo⟩, hstock⟩ := hc
  have hstockPool : ∀ v ∈ c.stock, Masked c.dom v ∧ Available (roots.map (obsM subMask)) (restrictRows f (obsM mask v)) := by
    intro v hv
    obtain ⟨md, a, ha, rfl⟩ := hstock v hv
    refine ⟨md, ?_⟩
    have heq : Nat.land (Nat.land a c.dom) c.dom = Nat.land a c.dom := md
    exact masked_eq_fn hdom heq ▸ hsup a ha
  unfold materializeCut at hm
  dsimp only at hm
  cases hall : ws.all (availableB c.dom (replayHist c.dom (needClose c.dom c.stock hist (needStart c.dom c.stock ws [])) hist.reverse 0 c.stock).2) with
  | false => simp [hall] at hm
  | true =>
    rw [hall] at hm
    injection hm with hmp
    subst hmp
    obtain ⟨bank1, hreach, hbank⟩ := replayHist_sound hdom hist.reverse Reach.start hstockPool
    obtain ⟨hbits, hcnt⟩ := buildConstInfo_spec c.dom ws 0 0 0 (fun j _ => by simp [nat_mod_eq, nat_div_eq])
    refine ⟨subMask, f, roots, bank1, hdom, hnc, hlo, hreach, hbank, ?_, ?_, ?_⟩
    · intro w hw
      exact availableB_sound hdom hbank (List.all_eq_true.mp hall w hw)
    · intro i hi
      simpa using hbits i hi
    · simpa using hcnt
noncomputable def scalarPoolCut (p : MatPool) (childFuel : Nat) (idxA idxB : Nat) (ka kb : Bool) (z : Word) : Bool :=
  forceNat (Nat.land z p.dom) fun mz =>
    let flatZ := match Nat.beq mz 0 with | true => true | false => Nat.beq mz p.dom
    let extra := match flatZ with
      | true => 0
      | false =>
        match containsNat mz p.bank with
        | true => 0
        | false =>
          match Nat.beq (Nat.land p.dom 1) 1 with
          | true => 1
          | false =>
            match containsNat (Nat.xor mz p.dom) p.bank with
            | true => 0
            | false => 1
    let dropA := match ka with
      | true => 0
      | false => Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxA)) 2
    let dropB := match kb with
      | true => 0
      | false => Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxB)) 2
    let addZ := match flatZ with | true => 1 | false => 0
    Nat.blt (Nat.add (Nat.add childFuel p.paid) extra)
      (Nat.add p.bound (Nat.add (Nat.sub (Nat.sub p.wsConstCnt dropA) dropB) addZ))
theorem countP_erase_two {α : Type} [DecidableEq α] (p : α → Bool) (ws : List α) (hnd : ws.Nodup)
    (a b : α) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (ka kb : Bool) :
    (kept ka a (kept kb b ((ws.erase a).erase b))).countP p =
      ws.countP p - (if ka then 0 else if p a then 1 else 0) - (if kb then 0 else if p b then 1 else 0) := by
  have hb' : b ∈ ws.erase a := (List.mem_erase_of_ne hab.symm).mpr hb
  have h1 : ws.countP p = (if p a then 1 else 0) + (ws.erase a).countP p := by
    have hp := List.perm_cons_erase ha
    rw [hp.countP_eq, List.countP_cons]
    cases p a <;> omega
  have h2 : (ws.erase a).countP p = (if p b then 1 else 0) + ((ws.erase a).erase b).countP p := by
    have hp := List.perm_cons_erase hb'
    rw [hp.countP_eq, List.countP_cons]
    cases p b <;> omega
  cases ka <;> cases kb <;> cases hpa : p a <;> cases hpb : p b <;>
    simp only [kept, List.countP_cons, hpa, hpb, ite_true, ite_false, Bool.false_eq_true] at h1 h2 ⊢ <;> omega
theorem selfPoolCut_sound {mask : Word} {raw : List Word} {T : Word} {ws : List Word}
    {p : MatPool} (vp : ValidPool mask raw T ws p)
    {fuel : Nat} (hnd : ws.Nodup)
    (hcut : Nat.blt (Nat.add fuel p.paid) (Nat.add p.bound p.wsConstCnt) = true) :
    Impossible mask T fuel ws.toFinset := by
  intro k hk run
  obtain ⟨subMask, f, roots, bank, hdom, hnc, hlo, hreach, _, hsup, _, hcnt⟩ := vp
  have rrun := list_run run ws hnd rfl
  have psup : supply bank ((ws.map (obsM mask)).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
    exact hsup w hw
  have pb := projected_bound f rrun hnc hreach psup hlo
  have cc := count_constants hdom ws
  have hlt : fuel + p.paid < p.bound + p.wsConstCnt := by
    simpa [nat_add_eq] using Nat.blt_eq.mp hcut
  omega
theorem scalarPoolCut_sound {mask : Word} {raw : List Word} {T : Word} {ws : List Word}
    {p : MatPool} (vp : ValidPool mask raw T ws p)
    {childFuel idxA idxB d : Nat} {ka kb : Bool}
    (hnd : ws.Nodup) (ha : idxA < ws.length) (hb : idxB < ws.length) (hab : idxA < idxB) (hd : d < 4)
    (hmask : ∀ w ∈ ws, Masked mask w)
    (hfresh : binOp mask d (ws.getD idxA 0) (ws.getD idxB 0) ∉ ws)
    (hcut : scalarPoolCut p childFuel idxA idxB ka kb (binOp mask d (ws.getD idxA 0) (ws.getD idxB 0)) = true) :
    let a := ws.getD idxA 0
    let b := ws.getD idxB 0
    let z := binOp mask d a b
    let child := z :: kept ka a (kept kb b ((ws.erase a).erase b))
    Impossible mask T childFuel child.toFinset := by
  intro a b z child k hk run
  obtain ⟨subMask, f, roots, bank, hdom, hnc, hlo, hreach, hbank, hsup, hcm, hcnt⟩ := vp
  have ham : a ∈ ws := by
    have : ws.getD idxA 0 = ws[idxA] := by simp [List.getD_eq_getElem?_getD, ha]
    rw [show a = ws[idxA] from this]; exact List.getElem_mem ha
  have hbm : b ∈ ws := by
    have : ws.getD idxB 0 = ws[idxB] := by simp [List.getD_eq_getElem?_getD, hb]
    rw [show b = ws[idxB] from this]; exact List.getElem_mem hb
  have hne : a ≠ b := by
    have ea : a = ws[idxA] := by simp [a, List.getD_eq_getElem?_getD, ha]
    have eb : b = ws[idxB] := by simp [b, List.getD_eq_getElem?_getD, hb]
    rw [ea, eb]
    intro eq
    exact Nat.ne_of_lt hab ((List.Nodup.getElem_inj_iff hnd).mp eq)
  have hndc : child.Nodup := by
    let rest := (ws.erase a).erase b
    have hrnd : rest.Nodup := (hnd.erase a).erase b
    have har : a ∉ rest := fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
    have hbr : b ∉ rest := (hnd.erase a).not_mem_erase
    have hamid : a ∉ kept kb b rest := by cases kb <;> simp [kept, har, hne]
    have hfresh' : z ∉ ws := hfresh
    refine List.nodup_cons.mpr ⟨?_, kept_nd ka a _ (kept_nd kb b _ hrnd hbr) hamid⟩
    intro hm
    rcases mem_kept hm with hza | hm
    · exact hfresh' (by rw [hza]; exact ham)
    rcases mem_kept hm with hzb | hm
    · exact hfresh' (by rw [hzb]; exact hbm)
    · exact hfresh' (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
  have hcount : child.countP (isConst p.dom) =
      ws.countP (isConst p.dom) -
        (if ka then 0 else if isConst p.dom a then 1 else 0) -
        (if kb then 0 else if isConst p.dom b then 1 else 0) +
        (if isConst p.dom z then 1 else 0) := by
    simp only [child, List.countP_cons, countP_erase_two (isConst p.dom) ws hnd a b ham hbm hne ka kb]
  have hbitA : Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxA)) 2 = if isConst p.dom a then 1 else 0 := by
    have h := hcm idxA ha
    simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at h ⊢
    have hlt : p.wsConstMask / (1 <<< idxA) % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hca : isConst p.dom a
    · rw [hca] at h; simp only [beq_eq_false_iff_ne] at h; simp; omega
    · rw [hca] at h; simp [beq_iff_eq.mp h]
  have hbitB : Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxB)) 2 = if isConst p.dom b then 1 else 0 := by
    have h := hcm idxB hb
    simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at h ⊢
    have hlt : p.wsConstMask / (1 <<< idxB) % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hcb : isConst p.dom b
    · rw [hcb] at h; simp only [beq_eq_false_iff_ne] at h; simp; omega
    · rw [hcb] at h; simp [beq_iff_eq.mp h]
  have hflatZ_eq : (match Nat.beq (Nat.land z p.dom) 0 with | true => true | false => Nat.beq (Nat.land z p.dom) p.dom) = isConst p.dom z := by
    rw [isConst_eq]; cases Nat.beq (Nat.land z p.dom) 0 <;> rfl
  have hextra_eq : (match (match Nat.beq (Nat.land z p.dom) 0 with | true => true | false => Nat.beq (Nat.land z p.dom) p.dom) with
      | true => 0
      | false => match containsNat (Nat.land z p.dom) p.bank with
        | true => 0
        | false => match Nat.beq (Nat.land p.dom 1) 1 with
          | true => 1
          | false => match containsNat (Nat.xor (Nat.land z p.dom) p.dom) p.bank with | true => 0 | false => 1) =
      if availableB p.dom p.bank z then 0 else 1 := by
    unfold availableB; simp only [forceNat_eq]
    cases Nat.beq (Nat.land z p.dom) 0 <;> cases Nat.beq (Nat.land z p.dom) p.dom <;>
      cases containsNat (Nat.land z p.dom) p.bank <;> cases Nat.beq (Nat.land p.dom 1) 1 <;>
      cases containsNat (Nat.xor (Nat.land z p.dom) p.dom) p.bank <;> rfl
  unfold scalarPoolCut at hcut
  dsimp only at hcut
  rw [forceNat_eq] at hcut
  change Nat.blt (Nat.add (Nat.add childFuel p.paid) _) _ = true at hcut
  rw [hextra_eq, hflatZ_eq, hbitA, hbitB, hcnt] at hcut
  have hlt_cut : childFuel + p.paid + (if availableB p.dom p.bank z then 0 else 1) < p.bound + child.countP (isConst p.dom) := by
    have h1 := Nat.blt_eq.mp hcut
    rw [hcount]
    cases ka <;> cases kb <;> cases hz : isConst p.dom z <;> simp only [hz, ite_true, ite_false, Bool.false_eq_true, nat_add_eq, nat_sub_eq] at h1 ⊢ <;> omega
  have hsub_rest : ∀ w ∈ kept ka a (kept kb b ((ws.erase a).erase b)), w ∈ ws := by
    intro w hw
    rcases mem_kept hw with rfl | hw
    · exact ham
    rcases mem_kept hw with rfl | hw
    · exact hbm
    · exact List.mem_of_mem_erase (List.mem_of_mem_erase hw)
  have rrun := list_run run child hndc rfl
  have hcc := count_constants hdom child
  cases havz : availableB p.dom p.bank z with
  | true =>
    simp only [havz, ite_true] at hlt_cut
    have hsupc : supply bank ((child.map (obsM mask)).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact availableB_sound hdom hbank havz
      · exact hsup w (hsub_rest w hw')
    have pb := projected_bound f rrun hnc hreach hsupc hlo
    omega
  | false =>
    simp only [havz, Bool.false_eq_true, ite_false] at hlt_cut
    obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime hd (hsup a ham) (hsup b hbm)
    let bank' := combine op x y :: bank
    have hreach' : Reach (roots.map (obsM subMask)) (p.paid + 1) bank' := Reach.two op hreach hx hy
    have hsupc : supply bank' ((child.map (obsM mask)).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
      rcases List.mem_cons.mp hw with rfl | hw'
      · change Available bank' (restrictRows f (obsM mask (binOp mask d a b)))
        rw [obsM_binOp hd (hmask a ham) (hmask b hbm), restrict_comb, e]
        exact Or.inl (by simp [bank'])
      · exact available_cons _ (hsup w (hsub_rest w hw'))
    have pb := projected_bound f rrun hnc hreach' hsupc hlo
    omega
structure Wire where
  val : Word
  pos : Nat
  neg : Nat
  sep : Nat
def packBitsFrom (idx : Nat) : List Row → Word → Nat → Nat
  | [], _, acc => acc
  | r :: rs, w, acc =>
    packBitsFrom (idx + 1) rs w (if bit r w then Nat.lor acc (Nat.shiftLeft 1 idx) else acc)
def packBits (rows : List Row) (w : Word) : Nat := packBitsFrom 0 rows w 0
def pairValid (mask T : Word) (p : Row × Row) : Bool :=
  bit p.1 mask && bit p.2 mask && bit p.1 T && !bit p.2 T
def wireMatchesPairs (pairs : List (Row × Row)) (w : Wire) : Bool :=
  Nat.beq w.pos (packBits (pairs.map Prod.fst) w.val) &&
  Nat.beq w.neg (packBits (pairs.map Prod.snd) w.val) &&
  Nat.beq w.sep (Nat.xor w.pos w.neg)
def Faithful (pairs : List (Row × Row)) (w : Wire) : Prop :=
  (∀ i < pairs.length, w.pos.testBit i = bit (pairs.getD i (0, 0)).1 w.val) ∧
  (∀ i < pairs.length, w.neg.testBit i = bit (pairs.getD i (0, 0)).2 w.val) ∧
  (∀ i ≥ pairs.length, w.pos.testBit i = false ∧ w.neg.testBit i = false) ∧
  w.sep = Nat.xor w.pos w.neg
theorem packBits_testBit (rows : List Row) (w : Word) (i : Nat) :
    (packBits rows w).testBit i = if h : i < rows.length then bit rows[i] w else false := by
  have hgen : ∀ (l : List Row) (base acc : Nat),
      (∀ k ≥ base, acc.testBit k = false) →
      (packBitsFrom base l w acc).testBit i =
        if i < base then acc.testBit i
        else if h : i - base < l.length then bit l[i - base] w else false := by
    intro l
    induction l with
    | nil =>
      intro base acc hacc
      simp only [packBitsFrom, List.length_nil]
      by_cases hi : i < base
      · simp [hi]
      · simp [hi, hacc i (by omega)]
    | cons r rs ih =>
      intro base acc hacc
      simp only [packBitsFrom]
      have hacc' : ∀ k ≥ base + 1, (if bit r w then Nat.lor acc (Nat.shiftLeft 1 base) else acc).testBit k = false := by
        intro k hk
        cases bit r w
        · exact hacc k (by omega)
        · have hne : k ≠ base := by omega
          have htb : (Nat.shiftLeft 1 base).testBit k = false := by rw [testBit_one_shl]; simp [hne]
          simp only [ite_true, nat_lor_eq, Nat.testBit_or, hacc k (by omega), htb, Bool.or_false]
      rw [ih (base + 1) _ hacc']
      by_cases hlt : i < base
      · have hlt1 : i < base + 1 := by omega
        simp only [hlt, hlt1, ite_true]
        cases bit r w
        · rfl
        · have hne : i ≠ base := by omega
          have htb : (Nat.shiftLeft 1 base).testBit i = false := by rw [testBit_one_shl]; simp [hne]
          simp only [ite_true, nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]
      · by_cases heq : i = base
        · subst heq
          have hlt1 : i < i + 1 := by omega
          simp only [hlt, hlt1, ite_true, ite_false, Nat.sub_self, List.length_cons, Nat.zero_lt_succ,
            List.getElem_cons_zero]
          cases hb : bit r w
          · simp [hacc i (Nat.le_refl _)]
          · simp [nat_lor_eq, Nat.testBit_or, testBit_one_shl]
        · have hng1 : ¬ (i < base + 1) := by omega
          simp only [hlt, hng1, ite_false]
          have hsub : i - base = (i - (base + 1)) + 1 := by omega
          rw [hsub]
          by_cases hs : i - (base + 1) < rs.length
          · simp [hs]
          · simp [hs]
  have h0 := hgen rows 0 0 (fun _ _ => by simp)
  simpa [packBits] using h0
theorem wireMatchesPairs_sound {pairs : List (Row × Row)} {w : Wire}
    (h : wireMatchesPairs pairs w = true) : Faithful pairs w := by
  simp only [wireMatchesPairs, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hpos, hneg⟩, hsep⟩ := h
  refine ⟨?_, ?_, ?_, hsep⟩
  · intro i hi
    rw [hpos, packBits_testBit]
    have hi' : i < (pairs.map Prod.fst).length := by simpa using hi
    simp [hi', List.getD_eq_getElem?_getD, hi]
  · intro i hi
    rw [hneg, packBits_testBit]
    have hi' : i < (pairs.map Prod.snd).length := by simpa using hi
    simp [hi', List.getD_eq_getElem?_getD, hi]
  · intro i hi
    rw [hpos, hneg, packBits_testBit, packBits_testBit]
    have h1 : ¬ (i < (pairs.map Prod.fst).length) := by rw [List.length_map]; omega
    have h2 : ¬ (i < (pairs.map Prod.snd).length) := by rw [List.length_map]; omega
    simp only [dif_neg h1, dif_neg h2, and_self]
theorem faithful_bin {mask : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {a b : Wire} (ha : Faithful pairs a) (hb : Faithful pairs b)
    (hma : Masked mask a.val) (hmb : Masked mask b.val)
    (d : Nat) (hd : d < 4) :
    let p0 := Nat.land a.pos b.pos
    let n0 := Nat.land a.neg b.neg
    let sep0 := Nat.xor p0 n0
    let posZ := match d with | 0 => p0 | 1 => Nat.lor a.pos b.pos | 2 => Nat.xor a.pos p0 | _ => Nat.xor b.pos p0
    let negZ := match d with | 0 => n0 | 1 => Nat.lor a.neg b.neg | 2 => Nat.xor a.neg n0 | _ => Nat.xor b.neg n0
    let sepZ := match d with | 0 => sep0 | 1 => Nat.xor a.sep (Nat.xor b.sep sep0) | 2 => Nat.xor a.sep sep0 | _ => Nat.xor b.sep sep0
    Faithful pairs ⟨binOp mask d a.val b.val, posZ, negZ, sepZ⟩ := by
  intro p0 n0 sep0 posZ negZ sepZ
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have hpm : ∀ i < pairs.length, bit (pairs.getD i (0, 0)).1 mask = true ∧ bit (pairs.getD i (0, 0)).2 mask = true := by
    intro i hi
    have hmem : pairs.getD i (0, 0) ∈ pairs := by
      simp [List.getD_eq_getElem?_getD, hi]
    have hv := hpairs _ hmem
    simp only [pairValid, Bool.and_eq_true] at hv
    exact ⟨hv.1.1.1, hv.1.1.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := (hpm i hi).1
    have ha1 := ha.1 i hi
    have hb1 := hb.1 i hi
    have hbt := binOp_testBit hd hma hmb (pairs.getD i (0, 0)).1.val
    simp only [bit] at h1 ha1 hb1 ⊢
    rw [h1] at hbt
    rw [hbt]
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [posZ, p0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha1, hb1] <;>
      cases a.val.testBit (pairs.getD i (0, 0)).1.val <;>
      cases b.val.testBit (pairs.getD i (0, 0)).1.val <;> rfl
  · intro i hi
    have h2 := (hpm i hi).2
    have ha2 := ha.2.1 i hi
    have hb2 := hb.2.1 i hi
    have hbt := binOp_testBit hd hma hmb (pairs.getD i (0, 0)).2.val
    simp only [bit] at h2 ha2 hb2 ⊢
    rw [h2] at hbt
    rw [hbt]
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [negZ, n0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha2, hb2] <;>
      cases a.val.testBit (pairs.getD i (0, 0)).2.val <;>
      cases b.val.testBit (pairs.getD i (0, 0)).2.val <;> rfl
  · intro i hi
    obtain ⟨ha1, ha2⟩ := ha.2.2.1 i hi
    obtain ⟨hb1, hb2⟩ := hb.2.2.1 i hi
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [posZ, negZ, p0, n0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha1, ha2, hb1, hb2]
  · apply Nat.eq_of_testBit_eq
    intro i
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [sepZ, sep0, posZ, negZ, p0, n0, ha.2.2.2, hb.2.2.2,
        nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor] <;>
      cases a.pos.testBit i <;> cases b.pos.testBit i <;> cases a.neg.testBit i <;> cases b.neg.testBit i <;> rfl
theorem sep_required {mask T : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {ws : List Wire} (hfaith : ∀ w ∈ ws, Faithful pairs w)
    {k : Nat} (run : Live mask T k (ws.map Wire.val).toFinset) :
    ws.foldr (fun w acc => Nat.lor w.sep acc) 0 = Nat.sub (Nat.shiftLeft 1 pairs.length) 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hfold : ∀ (l : List Wire), (l.foldr (fun w acc => Nat.lor w.sep acc) 0).testBit i =
      l.any (fun w => w.sep.testBit i) := by
    intro l; induction l with
    | nil => simp
    | cons w ws ih =>
      change (Nat.lor w.sep (ws.foldr (fun w acc => Nat.lor w.sep acc) 0)).testBit i = _
      rw [nat_lor_eq, Nat.testBit_or, ih, List.any_cons]
  rw [hfold]
  have hmask : (Nat.sub (Nat.shiftLeft 1 pairs.length) 1).testBit i = decide (i < pairs.length) := by
    rw [nat_sub_eq, nat_shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.testBit_two_pow_sub_one (n := pairs.length) (i := i)
  rw [hmask]
  by_cases hi : i < pairs.length
  · simp only [hi, decide_true, List.any_eq_true]
    have hmem : pairs.getD i (0, 0) ∈ pairs := by simp [List.getD_eq_getElem?_getD, hi]
    have hv := hpairs _ hmem
    simp only [pairValid, Bool.and_eq_true, Bool.not_eq_true'] at hv
    have hdiff : bit (pairs.getD i (0, 0)).1 T ≠ bit (pairs.getD i (0, 0)).2 T := by
      rw [hv.1.2, hv.2]; decide
    obtain ⟨v, hvS, hdv⟩ := live_row_difference run hv.1.1.1 hv.1.1.2 hdiff
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hvS)
    refine ⟨w, hw, ?_⟩
    have hf := hfaith w hw
    rw [hf.2.2.2, nat_xor_eq, Nat.testBit_xor, hf.1 i hi, hf.2.1 i hi]
    cases h1 : bit (pairs.getD i (0, 0)).1 w.val <;> cases h2 : bit (pairs.getD i (0, 0)).2 w.val <;>
      simp_all
  · simp only [hi, decide_false, Bool.eq_false_iff]
    intro hany
    obtain ⟨w, hw, hbit⟩ := List.any_eq_true.mp hany
    have hf := hfaith w hw
    obtain ⟨h1, h2⟩ := hf.2.2.1 i (by omega)
    rw [hf.2.2.2, nat_xor_eq, Nat.testBit_xor, h1, h2] at hbit
    simp at hbit
def SymOK (mask T : Word) (sym : Word → Word) : Prop :=
  ∃ (f : Row → Row), Function.Bijective f ∧
    (∀ r : Row, bit (f r) mask = bit r mask) ∧
    (∀ w, Masked mask w → Masked mask (sym w) ∧ ∀ r : Row, bit r (sym w) = bit (f r) w) ∧
    sym T = T
theorem sym_id_ok (mask T : Word) : SymOK mask T id :=
  ⟨id, Function.bijective_id, fun _ => rfl, fun _ hw => ⟨hw, fun _ => rfl⟩, rfl⟩
def swapWord (mEq m01 m10 sh : Word) (w : Word) : Word :=
  Nat.lor (Nat.land w mEq)
    (Nat.lor (Nat.shiftRight (Nat.land w m01) sh) (Nat.shiftLeft (Nat.land w m10) sh))
def swapSpecOK (mEq m01 m10 sh : Word) (f : Row → Row) : Bool :=
  Nat.beq (Nat.land mEq fullMask) mEq &&
  Nat.beq (Nat.land m01 fullMask) m01 &&
  Nat.beq (Nat.land m10 fullMask) m10 &&
  Nat.beq (Nat.land (Nat.shiftLeft m10 sh) fullMask) (Nat.shiftLeft m10 sh) &&
  (List.finRange 256).all fun r =>
    decide (f (f r) = r) &&
    ((bit r mEq && !m01.testBit (sh + r.val) && !(decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide (f r = r)) ||
    (!bit r mEq && m01.testBit (sh + r.val) && !(decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide ((f r).val = sh + r.val)) ||
    (!bit r mEq && !m01.testBit (sh + r.val) && (decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide ((f r).val = r.val - sh)))
theorem swapWord_spec {mEq m01 m10 sh : Word} {f : Row → Row}
    (hok : swapSpecOK mEq m01 m10 sh f = true) :
    Function.Bijective f ∧
    (∀ w, Masked fullMask (swapWord mEq m01 m10 sh w) ∧
      ∀ r : Row, bit r (swapWord mEq m01 m10 sh w) = bit (f r) w) := by
  simp only [swapSpecOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmEq, hm01⟩, hm10⟩, hmSh⟩, hall⟩ := hok
  have hbij : Function.Bijective f :=
    Function.Involutive.bijective (fun r => (hall r (List.mem_finRange r)).1)
  refine ⟨hbij, fun w => ⟨?_, ?_⟩⟩
  · apply masked_lor (masked_land_right hmEq)
    apply masked_lor
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [nat_land_eq, Nat.testBit_and]
      by_cases hk : k < 256
      · have hfm : fullMask.testBit k = true := by
          have : fullMask = 2 ^ 256 - 1 := by decide
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        simp [hfm]
      · have hfm : fullMask.testBit k = false := mask_testBit_ge (masked_self fullMask) (by omega)
        have h0 : (Nat.land w m01).testBit (sh + k) = false := by
          rw [nat_land_eq, Nat.testBit_and, mask_testBit_ge hm01 (by omega), Bool.and_false]
        rw [hfm, Bool.and_false, nat_shr_eq, Nat.testBit_shiftRight, h0]
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [nat_land_eq, Nat.testBit_and]
      by_cases hk : k < 256
      · have hfm : fullMask.testBit k = true := by
          have : fullMask = 2 ^ 256 - 1 := by decide
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        simp [hfm]
      · have hfm : fullMask.testBit k = false := mask_testBit_ge (masked_self fullMask) (by omega)
        have hsh0 : (Nat.shiftLeft m10 sh).testBit k = false := mask_testBit_ge hmSh (by omega)
        have h1 : (Nat.shiftLeft (Nat.land w m10) sh).testBit k = false := by
          rw [nat_shl_eq, Nat.testBit_shiftLeft] at hsh0 ⊢
          by_cases hge : k ≥ sh
          · simp only [hge, decide_true, Bool.true_and] at hsh0 ⊢
            rw [nat_land_eq, Nat.testBit_and, hsh0, Bool.and_false]
          · simp [hge]
        rw [hfm, Bool.and_false, h1]
  · intro r
    have hr := (hall r (List.mem_finRange r)).2
    simp only [bit, swapWord, nat_lor_eq, Nat.testBit_or, nat_land_eq, Nat.testBit_and,
      nat_shr_eq, Nat.testBit_shiftRight, nat_shl_eq, Nat.testBit_shiftLeft]
    rcases hr with (⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · simp only [bit] at h1
      have h3' : (decide (r.val ≥ sh) && (w.testBit (r.val - sh) && m10.testBit (r.val - sh))) = false := by
        by_cases hge : sh ≤ r.val
        · simp only [hge, decide_true, Bool.true_and] at h3
          simp [hge, h3]
        · have : ¬ (r.val ≥ sh) := by omega
          simp [this]
      rw [h1, h2, h4]; simp [h3']
    · simp only [bit] at h1
      have h3' : (decide (r.val ≥ sh) && (w.testBit (r.val - sh) && m10.testBit (r.val - sh))) = false := by
        by_cases hge : sh ≤ r.val
        · simp only [hge, decide_true, Bool.true_and] at h3
          simp [hge, h3]
        · have : ¬ (r.val ≥ sh) := by omega
          simp [this]
      rw [h1, h2, h4]; simp [h3']
    · simp only [bit] at h1
      have h3a : sh ≤ r.val := h3.1
      have h3b : m10.testBit (r.val - sh) = true := h3.2
      have hge : r.val ≥ sh := h3a
      rw [h1, h2, h4]; simp [hge, h3b]
theorem sym_of_row {mask T : Word} {f : Row → Row} {sym : Word → Word}
    (hm : Masked fullMask mask) (hbij : Function.Bijective f)
    (hsw : ∀ w, Masked fullMask (sym w) ∧ ∀ r : Row, bit r (sym w) = bit (f r) w)
    (hmask : (List.finRange 256).all (fun r => bit (f r) mask == bit r mask) = true)
    (hT : Nat.beq (sym T) T = true) :
    SymOK mask T sym := by
  have hfM : ∀ r : Row, bit (f r) mask = bit r mask := fun r =>
    beq_iff_eq.mp (List.all_eq_true.mp hmask r (List.mem_finRange r))
  refine ⟨f, hbij, hfM, fun w hw => ⟨?_, (hsw w).2⟩, Nat.beq_eq.mp hT⟩
  apply Nat.eq_of_testBit_eq
  intro k
  rw [nat_land_eq, Nat.testBit_and]
  by_cases hk : k < 256
  · let r : Row := ⟨k, hk⟩
    have h1 : (sym w).testBit r.val = w.testBit (f r).val := (hsw w).2 r
    cases hmr : mask.testBit r.val with
    | true => simp
    | false =>
      have hmf : mask.testBit (f r).val = false := by
        have := hfM r; simp only [bit] at this; rw [this, hmr]
      rw [h1, masked_testBit_false hw hmf]; simp
  · have h0 := mask_testBit_ge (hsw w).1 (show 256 ≤ k by omega)
    rw [h0]; simp
theorem sym_comp_spec {f1 f2 : Row → Row} {s1 s2 : Word → Word}
    (h1 : Function.Bijective f1 ∧ ∀ w, Masked fullMask (s1 w) ∧ ∀ r, bit r (s1 w) = bit (f1 r) w)
    (h2 : Function.Bijective f2 ∧ ∀ w, Masked fullMask (s2 w) ∧ ∀ r, bit r (s2 w) = bit (f2 r) w) :
    Function.Bijective (fun r => f1 (f2 r)) ∧
    ∀ w, Masked fullMask (s2 (s1 w)) ∧ ∀ r, bit r (s2 (s1 w)) = bit (f1 (f2 r)) w := by
  refine ⟨h1.1.comp h2.1, fun w => ⟨(h2.2 (s1 w)).1, fun r => ?_⟩⟩
  rw [(h2.2 (s1 w)).2 r, (h1.2 w).2 (f2 r)]
theorem live_sym {mask T : Word} {sym : Word → Word} (hm : Masked fullMask mask)
    (hsym : SymOK mask T sym) {k : Nat} {S : Finset Word} (h : Live mask T k S) :
    Live mask T k (S.image sym) := by
  obtain ⟨f, hbij, hfM, hsw, hT⟩ := hsym
  have hinj : ∀ a b, Masked mask a → Masked mask b → sym a = sym b → a = b := by
    intro a b ha hb heq
    apply masked_ext hm ha hb
    intro r
    obtain ⟨q, hq⟩ := hbij.2 r
    have h1 := (hsw a ha).2 q
    have h2 := (hsw b hb).2 q
    rw [heq] at h1
    rw [← hq, ← h1, h2]
  have hzero : sym 0 = 0 := by
    apply masked_ext hm (hsw 0 (masked_zero mask)).1 (masked_zero mask)
    intro r; rw [(hsw 0 (masked_zero mask)).2 r]; simp [bit]
  have hmask : sym mask = mask := by
    apply masked_ext hm (hsw mask (masked_self mask)).1 (masked_self mask)
    intro r; rw [(hsw mask (masked_self mask)).2 r, hfM r]
  have hprop : ∀ a, Proper mask a → Proper mask (sym a) := by
    intro a ha
    refine ⟨(hsw a ha.1).1, ?_, ?_⟩
    · intro hz; exact ha.2.1 (hinj a 0 ha.1 (masked_zero mask) (hz.trans hzero.symm))
    · intro hma; exact ha.2.2 (hinj a mask ha.1 (masked_self mask) (hma.trans hmask.symm))
  have hbin : ∀ d a b, d < 4 → Masked mask a → Masked mask b →
      sym (binOp mask d a b) = binOp mask d (sym a) (sym b) := by
    intro d a b hd ha hb
    apply masked_ext hm (hsw _ (masked_binOp ha hb)).1 (masked_binOp (hsw a ha).1 (hsw b hb).1)
    intro r
    rw [(hsw _ (masked_binOp ha hb)).2 r]
    simp only [bit]
    rw [binOp_testBit hd ha hb (f r).val, binOp_testBit hd (hsw a ha).1 (hsw b hb).1 r.val]
    have hfm : mask.testBit (f r).val = mask.testBit r.val := hfM r
    have hsa : (sym a).testBit r.val = a.testBit (f r).val := (hsw a ha).2 r
    have hsb : (sym b).testBit r.val = b.testBit (f r).val := (hsw b hb).2 r
    rw [hfm, hsa, hsb]
  induction h using Live.ind with
  | stop hp =>
    rw [Finset.image_singleton, hT]
    exact Live.stop hp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hUm : ∀ u ∈ U, Masked mask u := fun u hu =>
      (live_proper tail u (Finset.mem_insert_of_mem hu)).1
    have hfresh : binOp mask d (sym a) (sym b) ∉ (insert a (insert b U)).image sym := by
      intro hmem
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
      have hvm : Masked mask v := by
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact ha.1
        rcases Finset.mem_insert.mp hv' with rfl | hv''
        · exact hb.1
        · exact hUm v hv''
      have hv_eq : v = binOp mask d a b := hinj v (binOp mask d a b) hvm (masked_binOp ha.1 hb.1)
        (heq.trans (hbin d a b hd ha.1 hb.1).symm)
      exact hf (hv_eq ▸ hv)
    simp only [Finset.image_insert, hbin d a b hd ha.1 hb.1] at hfresh ih ⊢
    exact Live.binary hd (hprop a ha) (hprop b hb)
      (fun e => hab (hinj a b ha.1 hb.1 e)) hfresh ih
noncomputable def eraseWord (x : Word) (ws : List Word) : List Word :=
  List.rec [] (fun w rest ih => cond (Nat.beq w x) rest (w :: ih)) ws
theorem eraseWord_eq (x : Word) (ws : List Word) : eraseWord x ws = ws.erase x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change cond (Nat.beq w x) ws (w :: eraseWord x ws) = _
    simp only [List.erase_cons]
    cases h : Nat.beq w x
    · have hne : w ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
      have h' : (w == x) = false := beq_eq_false_iff_ne.mpr hne
      simp [h', ih]
    · have h' : (w == x) = true := beq_iff_eq.mpr (Nat.beq_eq.mp h)
      simp [h']
noncomputable def eraseWire (x : Word) (ws : List Wire) : List Wire :=
  List.rec [] (fun w rest ih => cond (Nat.beq w.val x) rest (w :: ih)) ws
theorem eraseWire_map (x : Word) (ws : List Wire) :
    (eraseWire x ws).map Wire.val = (ws.map Wire.val).erase x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (cond (Nat.beq w.val x) ws (w :: eraseWire x ws)).map Wire.val = _
    simp only [List.map_cons, List.erase_cons]
    cases h : Nat.beq w.val x
    · have hne : w.val ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
      have h' : (w.val == x) = false := beq_eq_false_iff_ne.mpr hne
      simp [h', ih]
    · have h' : (w.val == x) = true := beq_iff_eq.mpr (Nat.beq_eq.mp h)
      simp [h']
noncomputable def childWires (ws : List Wire) (a b z : Wire) (ka kb : Bool) : List Wire :=
  z :: kept ka a (kept kb b (eraseWire b.val (eraseWire a.val ws)))
theorem childWires_map (ws : List Wire) (a b z : Wire) (ka kb : Bool) :
    (childWires ws a b z ka kb).map Wire.val =
      z.val :: kept ka a.val (kept kb b.val (((ws.map Wire.val).erase a.val).erase b.val)) := by
  simp [childWires, map_kept, eraseWire_map]
def makeWireBin (mask : Word) (d : Nat) (a b : Wire) : Wire :=
  forceNat (binOp mask d a.val b.val) fun valZ =>
    forceNat (Nat.land a.pos b.pos) fun p0 =>
      forceNat (Nat.land a.neg b.neg) fun n0 =>
        forceNat (Nat.xor p0 n0) fun sep0 =>
          let posE := match d with | 0 => p0 | 1 => Nat.lor a.pos b.pos | 2 => Nat.xor a.pos p0 | _ => Nat.xor b.pos p0
          let negE := match d with | 0 => n0 | 1 => Nat.lor a.neg b.neg | 2 => Nat.xor a.neg n0 | _ => Nat.xor b.neg n0
          let sepE := match d with | 0 => sep0 | 1 => Nat.xor a.sep (Nat.xor b.sep sep0) | 2 => Nat.xor a.sep sep0 | _ => Nat.xor b.sep sep0
          forceNat posE fun posZ =>
            forceNat negE fun negZ =>
              forceNat sepE fun sepZ =>
                ⟨valZ, posZ, negZ, sepZ⟩
theorem makeWireBin_val (mask : Word) (d : Nat) (a b : Wire) : (makeWireBin mask d a b).val = binOp mask d a.val b.val := by
  simp [makeWireBin, forceNat_eq]
theorem makeWireBin_sep (mask : Word) (d : Nat) (a b : Wire) :
    (makeWireBin mask d a b).sep =
      match d with
      | 0 => Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)
      | 1 => Nat.xor a.sep (Nat.xor b.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)))
      | 2 => Nat.xor a.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg))
      | _ => Nat.xor b.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)) := by
  unfold makeWireBin
  simp only [forceNat_eq]
theorem makeWireBin_faithful {mask T : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {a b : Wire} (ha : Faithful pairs a) (hb : Faithful pairs b)
    (hma : Masked mask a.val) (hmb : Masked mask b.val) (d : Nat) (hd : d < 4) :
    Faithful pairs (makeWireBin mask d a b) := by
  have h := faithful_bin hpairs ha hb hma hmb d hd
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> simpa [makeWireBin, forceNat_eq] using h
def getWire (ws : List Wire) (i : Nat) : Wire := ws.getD i ⟨0, 0, 0, 0⟩
noncomputable def applyTok (mask : Word) (tok : Nat) (st : Nat × List Wire × List HistStep) :
    Option (Nat × List Wire × List HistStep) :=
  let (fuel, ws, hist) := st
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let keep := Nat.mod tok 4
    let d := Nat.mod (Nat.div tok 4) 4
    let b := Nat.mod (Nat.div tok 16) 16
    let a := Nat.div tok 256
    match Nat.blt a b && Nat.blt b ws.length with
    | false => none
    | true =>
      let wa := getWire ws a
      let wb := getWire ws b
      let wz := makeWireBin mask d wa wb
      match Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws.map Wire.val) with
      | true => none
      | false =>
        let ka := Nat.beq (Nat.div keep 2) 1
        let kb := Nat.beq (Nat.mod keep 2) 1
        some (fuel', childWires ws wa wb wz ka kb, (wz.val, wa.val, wb.val) :: hist)
noncomputable def applyTokVals (mask : Word) (tok : Nat) (st : Nat × List Word) : Option (Nat × List Word) :=
  let (fuel, vs) := st
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let keep := Nat.mod tok 4
    let d := Nat.mod (Nat.div tok 4) 4
    let b := Nat.mod (Nat.div tok 16) 16
    let a := Nat.div tok 256
    match Nat.blt a b && Nat.blt b vs.length with
    | false => none
    | true =>
      let va := vs.getD a 0
      let vb := vs.getD b 0
      forceNat (binOp mask d va vb) fun vz =>
        match Nat.beq vz 0 || Nat.beq vz mask || containsNat vz vs with
        | true => none
        | false =>
          let ka := Nat.beq (Nat.div keep 2) 1
          let kb := Nat.beq (Nat.mod keep 2) 1
          some (fuel', vz :: kept ka va (kept kb vb (eraseWord vb (eraseWord va vs))))
theorem applyTokVals_eq (mask : Word) (tok : Nat) (fuel : Nat) (ws : List Wire) (hist : List HistStep)
    {st' : Nat × List Wire × List HistStep}
    (h : applyTok mask tok (fuel, ws, hist) = some st') :
    applyTokVals mask tok (fuel, ws.map Wire.val) = some (st'.1, st'.2.1.map Wire.val) := by
  unfold applyTok at h
  unfold applyTokVals
  cases fuel with
  | zero => simp at h
  | succ fuel' =>
    dsimp only at h ⊢
    rw [List.length_map]
    cases hc : (Nat.blt (Nat.div tok 256) (Nat.mod (Nat.div tok 16) 16) && Nat.blt (Nat.mod (Nat.div tok 16) 16) ws.length) with
    | false => rw [hc] at h; simp at h
    | true =>
      rw [hc] at h
      have ha_lt : Nat.div tok 256 < ws.length := by
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc; omega
      have hb_lt : Nat.mod (Nat.div tok 16) 16 < ws.length := by
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.2
      have hva : (ws.map Wire.val).getD (Nat.div tok 256) 0 = (getWire ws (Nat.div tok 256)).val := by
        simp only [getWire, List.getD_eq_getElem?_getD, List.getElem?_map, ha_lt, getElem?_pos, Option.map_some, Option.getD_some]
      have hvb : (ws.map Wire.val).getD (Nat.mod (Nat.div tok 16) 16) 0 = (getWire ws (Nat.mod (Nat.div tok 16) 16)).val := by
        simp only [getWire, List.getD_eq_getElem?_getD, List.getElem?_map, hb_lt, getElem?_pos, Option.map_some, Option.getD_some]
      rw [hva, hvb, forceNat_eq, ← makeWireBin_val]
      cases hz : (Nat.beq (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val 0 ||
          Nat.beq (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val mask ||
          containsNat (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val (ws.map Wire.val)) with
      | true => rw [hz] at h; simp at h
      | false =>
        rw [hz] at h
        injection h with hst
        subst hst
        simp only [childWires_map, eraseWord_eq]
abbrev NodeRec := Nat × List Nat × List Nat
noncomputable def traceState (mask : Word) (rootFuel : Nat) (rootWs : List Wire)
    (dag : BTree NodeRec) (fdepth : Nat) : Nat → Nat → Option (Nat × List Wire × List HistStep)
  | _, 0 => some (rootFuel, rootWs, [])
  | 0, _ + 1 => none
  | gas + 1, i + 1 =>
    let pt := (btreeGet (0, [], []) fdepth dag (Nat.add i 1)).1
    let par := Nat.div pt 4096
    let tok := Nat.mod pt 4096
    match Nat.blt par (Nat.add i 1) with
    | false => none
    | true =>
      match traceState mask rootFuel rootWs dag fdepth gas par with
      | none => none
      | some st => applyTok mask tok st
noncomputable def traceVals (mask : Word) (rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) : Nat → Nat → Option (Nat × List Word)
  | _, 0 => some (rootFuel, rootVals)
  | 0, _ + 1 => none
  | gas + 1, i + 1 =>
    let pt := (btreeGet (0, [], []) fdepth dag (Nat.add i 1)).1
    let par := Nat.div pt 4096
    let tok := Nat.mod pt 4096
    match Nat.blt par (Nat.add i 1) with
    | false => none
    | true =>
      match traceVals mask rootFuel rootVals dag fdepth gas par with
      | none => none
      | some st => applyTokVals mask tok st
theorem traceState_gas_mono (mask : Word) (rootFuel : Nat) (rootWs : List Wire)
    (dag : BTree NodeRec) (fdepth : Nat) :
    ∀ gas i st, traceState mask rootFuel rootWs dag fdepth gas i = some st →
      st.1 ≤ rootFuel ∧ ∀ gas', rootFuel - st.1 ≤ gas' →
        traceState mask rootFuel rootWs dag fdepth gas' i = some st := by
  intro gas
  induction gas with
  | zero =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨Nat.le_refl _, fun g _ => by cases g <;> rfl⟩
    | succ _ => simp [traceState] at h
  | succ gas ih =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨Nat.le_refl _, fun g _ => by cases g <;> rfl⟩
    | succ i' =>
      unfold traceState at h
      dsimp only at h
      cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) (Nat.add i' 1) with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hpar : traceState mask rootFuel rootWs dag fdepth gas (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) with
        | none => rw [hpar] at h; cases h
        | some st0 =>
          rw [hpar] at h
          obtain ⟨hle0, hmono0⟩ := ih _ _ hpar
          have hdec : st.1 + 1 = st0.1 := by
            obtain ⟨f0, w0, hi0⟩ := st0
            unfold applyTok at h
            cases f0 with
            | zero => simp at h
            | succ f' =>
              dsimp only at h
              split at h
              · cases h
              · split at h
                · cases h
                · cases h; rfl
          refine ⟨by omega, fun gas' hg' => ?_⟩
          cases gas' with
          | zero => omega
          | succ g' =>
            unfold traceState
            dsimp only
            rw [hlt, hmono0 g' (by omega)]
            exact h
theorem traceVals_eq (mask : Word) (rootFuel : Nat) (rootWs : List Wire)
    (dag : BTree NodeRec) (fdepth : Nat) :
    ∀ gas i st, traceState mask rootFuel rootWs dag fdepth gas i = some st →
      traceVals mask rootFuel (rootWs.map Wire.val) dag fdepth gas i = some (st.1, st.2.1.map Wire.val) := by
  intro gas
  induction gas with
  | zero =>
    intro i st h
    cases i with
    | zero => cases h; rfl
    | succ _ => simp [traceState] at h
  | succ gas ih =>
    intro i st h
    cases i with
    | zero => cases h; rfl
    | succ i' =>
      unfold traceState at h
      unfold traceVals
      dsimp only at h ⊢
      cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) (Nat.add i' 1) with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hpar : traceState mask rootFuel rootWs dag fdepth gas (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) with
        | none => rw [hpar] at h; cases h
        | some st0 =>
          rw [hpar] at h
          rw [ih _ _ hpar]
          exact applyTokVals_eq mask _ st0.1 st0.2.1 st0.2.2 h
theorem traceState_inv {mask T : Word} {pairs : List (Row × Row)} {rootFuel : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {fdepth : Nat}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    (hrootM : ∀ w ∈ rootWs, Masked mask w.val)
    (hrootF : ∀ w ∈ rootWs, Faithful pairs w)
    (hrootNd : (rootWs.map Wire.val).Nodup) :
    ∀ gas i st, traceState mask rootFuel rootWs dag fdepth gas i = some st →
      (∀ w ∈ st.2.1, Masked mask w.val) ∧
      (∀ w ∈ st.2.1, Faithful pairs w) ∧
      (st.2.1.map Wire.val).Nodup := by
  intro gas
  induction gas with
  | zero =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨hrootM, hrootF, hrootNd⟩
    | succ _ => simp [traceState] at h
  | succ gas ih =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨hrootM, hrootF, hrootNd⟩
    | succ i' =>
      unfold traceState at h
      dsimp only at h
      cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) (Nat.add i' 1) with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hpar : traceState mask rootFuel rootWs dag fdepth gas (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) with
        | none => rw [hpar] at h; cases h
        | some st0 =>
          rw [hpar] at h
          obtain ⟨hM, hF, hNd⟩ := ih _ _ hpar
          obtain ⟨fuel0, ws0, hist0⟩ := st0
          unfold applyTok at h
          cases fuel0 with
          | zero => simp at h
          | succ fuel' =>
            dsimp only at h
            let tok := Nat.mod (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096
            cases hc : (Nat.blt (Nat.div tok 256) (Nat.mod (Nat.div tok 16) 16) && Nat.blt (Nat.mod (Nat.div tok 16) 16) ws0.length) with
            | false => simp only [tok] at hc; rw [hc] at h; simp at h
            | true =>
              simp only [tok] at hc
              rw [hc] at h
              have hab : Nat.div tok 256 < Nat.mod (Nat.div tok 16) 16 := by
                simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.1
              have hb_lt : Nat.mod (Nat.div tok 16) 16 < ws0.length := by
                simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.2
              have ha_lt : Nat.div tok 256 < ws0.length := Nat.lt_trans hab hb_lt
              let wa := getWire ws0 (Nat.div tok 256)
              let wb := getWire ws0 (Nat.mod (Nat.div tok 16) 16)
              let d := Nat.mod (Nat.div tok 4) 4
              have hd : d < 4 := Nat.mod_lt _ (by omega)
              have ham : wa ∈ ws0 := by
                simp only [wa, getWire, List.getD_eq_getElem?_getD, ha_lt, getElem?_pos, Option.getD_some]
                exact List.getElem_mem ha_lt
              have hbm : wb ∈ ws0 := by
                simp only [wb, getWire, List.getD_eq_getElem?_getD, hb_lt, getElem?_pos, Option.getD_some]
                exact List.getElem_mem hb_lt
              let wz := makeWireBin mask d wa wb
              cases hz : (Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws0.map Wire.val)) with
              | true => simp only [wa, wb, d, wz] at hz; rw [hz] at h; simp at h
              | false =>
                simp only [wa, wb, d, wz] at hz
                rw [hz] at h
                injection h with hst
                subst hst
                have hfresh : wz.val ∉ ws0.map Wire.val := by
                  simp only [Bool.or_eq_false_iff] at hz
                  intro hm
                  have hc' := (containsNat_iff _ _).mpr hm
                  simp only [wa, wb, d, wz] at hc'
                  rw [hz.2] at hc'
                  exact Bool.noConfusion hc'
                have hne : wa.val ≠ wb.val := by
                  have ha_m : Nat.div tok 256 < (ws0.map Wire.val).length := by rw [List.length_map]; exact ha_lt
                  have hb_m : Nat.mod (Nat.div tok 16) 16 < (ws0.map Wire.val).length := by rw [List.length_map]; exact hb_lt
                  have ea : wa.val = (ws0.map Wire.val)[Nat.div tok 256]'ha_m := by
                    simp only [wa, getWire, List.getD_eq_getElem?_getD, ha_lt, getElem?_pos, Option.getD_some, List.getElem_map]
                  have eb : wb.val = (ws0.map Wire.val)[Nat.mod (Nat.div tok 16) 16]'hb_m := by
                    simp only [wb, getWire, List.getD_eq_getElem?_getD, hb_lt, getElem?_pos, Option.getD_some, List.getElem_map]
                  rw [ea, eb]
                  intro e
                  exact Nat.ne_of_lt hab ((List.Nodup.getElem_inj_iff hNd).mp e)
                have hsubW : ∀ w ∈ childWires ws0 wa wb wz (Nat.beq (Nat.div (Nat.mod tok 4) 2) 1) (Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1),
                    w = wz ∨ w ∈ ws0 := by
                  intro w hw
                  rcases List.mem_cons.mp hw with rfl | hw'
                  · exact Or.inl rfl
                  · right
                    rcases mem_kept hw' with rfl | hw''
                    · exact ham
                    rcases mem_kept hw'' with rfl | hw'''
                    · exact hbm
                    · have hsub1 : ∀ x (l : List Wire), ∀ u ∈ eraseWire x l, u ∈ l := by
                        intro x l; induction l with
                        | nil => intro u hu; cases hu
                        | cons y ys ihy =>
                          intro u hu; simp only [eraseWire] at hu
                          cases hbeq : Nat.beq y.val x
                          · rw [hbeq] at hu
                            rcases List.mem_cons.mp hu with rfl | hu'
                            · exact List.mem_cons_self
                            · exact List.mem_cons_of_mem _ (ihy u hu')
                          · rw [hbeq] at hu
                            exact List.mem_cons_of_mem _ hu
                      exact hsub1 _ _ _ (hsub1 _ _ _ hw''')
                refine ⟨?_, ?_, ?_⟩
                · intro w hw
                  rcases hsubW w hw with rfl | hmem
                  · rw [makeWireBin_val]; exact masked_binOp (hM wa ham) (hM wb hbm)
                  · exact hM w hmem
                · intro w hw
                  rcases hsubW w hw with rfl | hmem
                  · exact makeWireBin_faithful hpairs (hF wa ham) (hF wb hbm) (hM wa ham) (hM wb hbm) d hd
                  · exact hF w hmem
                · rw [childWires_map]
                  let vs0 := ws0.map Wire.val
                  let rest := (vs0.erase wa.val).erase wb.val
                  have hrnd : rest.Nodup := (hNd.erase _).erase _
                  have har : wa.val ∉ rest := fun hm => hNd.not_mem_erase (List.mem_of_mem_erase hm)
                  have hbr : wb.val ∉ rest := (hNd.erase _).not_mem_erase
                  have hamid : wa.val ∉ kept (Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1) wb.val rest := by
                    cases Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1 <;> simp [kept, har, hne]
                  refine List.nodup_cons.mpr ⟨?_, kept_nd _ wa.val _ (kept_nd _ wb.val _ hrnd hbr) hamid⟩
                  intro hm
                  rcases mem_kept hm with hza | hm'
                  · exact hfresh (by rw [hza]; exact List.mem_map_of_mem ham)
                  rcases mem_kept hm' with hzb | hm''
                  · exact hfresh (by rw [hzb]; exact List.mem_map_of_mem hbm)
                  · exact hfresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm''))
def withSuffix : List Wire → List (Wire × Nat) × Nat
  | [] => ([], 0)
  | w :: ws =>
    let (tail, s) := withSuffix ws
    forceNat (Nat.lor w.sep s) fun s' => ((w, s) :: tail, s')
theorem withSuffix_len (ws : List Wire) : (withSuffix ws).1.length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [withSuffix, forceNat_eq, ih]
theorem withSuffix_fold (ws : List Wire) :
    (withSuffix ws).2 = ws.foldr (fun w acc => Nat.lor w.sep acc) 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [withSuffix, forceNat_eq, ih]
theorem withSuffix_spec (ws : List Wire) :
    ∀ i < ws.length,
      ((withSuffix ws).1.getD i (⟨0,0,0,0⟩, 0)).1 = ws.getD i ⟨0,0,0,0⟩ ∧
      ((withSuffix ws).1.getD i (⟨0,0,0,0⟩, 0)).2 = (ws.drop (i + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
  induction ws with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
    intro i hi
    simp only [withSuffix, forceNat_eq]
    cases i with
    | zero => simp [withSuffix_fold]
    | succ i' =>
      have hi' : i' < ws.length := by simp at hi; omega
      simpa using ih i' hi'
noncomputable def findLink (tok : Nat) (es : List Nat) : Option (Nat × Bool) :=
  List.rec none (fun e _ ih => cond (Nat.beq (Nat.land e 4095) tok) (some (Nat.shiftRight e 13, Nat.beq (Nat.land (Nat.shiftRight e 12) 1) 1)) ih) es
noncomputable def sameSetFast (a b : List Word) : Bool :=
  Nat.beq a.length b.length && a.all (fun x => containsNat x b)
theorem sameSetFast_sound {a b : List Word} (hna : a.Nodup) (hnb : b.Nodup)
    (h : sameSetFast a b = true) : a.toFinset = b.toFinset := by
  simp only [sameSetFast, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hsub : a.toFinset ⊆ b.toFinset := fun x hx =>
    List.mem_toFinset.mpr ((containsNat_iff x b).mp (hall x (List.mem_toFinset.mp hx)))
  have hcard : b.toFinset.card ≤ a.toFinset.card := by
    rw [List.toFinset_card_of_nodup hna, List.toFinset_card_of_nodup hnb, hlen]
  exact Finset.eq_of_subset_of_card_le hsub hcard
noncomputable def sameSetSym (sym : Word → Word) (a b : List Word) : Bool :=
  Nat.beq a.length b.length && a.all (fun x => forceNat (sym x) fun sx => containsNat sx b)
theorem sameSetSym_sound {sym : Word → Word} {a b : List Word}
    (hna : (a.map sym).Nodup) (hnb : b.Nodup)
    (h : sameSetSym sym a b = true) : (a.map sym).toFinset = b.toFinset := by
  apply sameSetFast_sound hna hnb
  simp only [sameSetFast, sameSetSym, List.length_map, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have h1 := h.2 x hx
  rwa [forceNat_eq] at h1
noncomputable def materializeList (cutTree : BTree CutSpec) (cdepth : Nat) (ws : List Word) (hist : List HistStep) :
    List Nat → List MatPool
  | [] => []
  | ci :: cis =>
    match materializeCut (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci) ws hist with
    | none => materializeList cutTree cdepth ws hist cis
    | some mp => mp :: materializeList cutTree cdepth ws hist cis
theorem materializeList_sound {mask : Word} {raw : List Word} {T : Word}
    {cutTree : BTree CutSpec} {cdepth : Nat}
    (ws : List Word) (hist : List HistStep) (cis : List Nat)
    (hvalid : ∀ ci ∈ cis, ValidCut mask raw T (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci)) :
    ∀ p ∈ materializeList cutTree cdepth ws hist cis, ValidPool mask raw T ws p := by
  induction cis with
  | nil => intro p hp; cases hp
  | cons ci cis ih =>
    intro p hp
    unfold materializeList at hp
    cases hm : materializeCut (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci) ws hist with
    | none =>
      rw [hm] at hp
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) p hp
    | some mp =>
      rw [hm] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact materializeCut_sound (hvalid ci (List.mem_cons_self)) hm
      · exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) p hp'
noncomputable def checkLink (mask : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat)
    (nodeId childFuel : Nat) (ws : List Word) (idxB baseTok : Nat) (ka kb : Bool) (va vb vz : Word) : Bool :=
  match nlinks with
  | [] => false
  | _ =>
    let keep := match ka with | true => (match kb with | true => 3 | false => 2) | false => (match kb with | true => 1 | false => 0)
    let tok := Nat.add baseTok keep
    match findLink tok nlinks with
    | none => false
    | some (tid, isSym) =>
      match Nat.blt tid count with
      | false => false
      | true =>
        match Nat.blt idxB 16 && Nat.blt nodeId tid &&
              Nat.beq (btreeGet (0, [], []) fdepth dag tid).1 (Nat.add (Nat.mul nodeId 4096) tok) with
        | true => true
        | false =>
          match traceVals mask rootFuel rootVals dag fdepth (Nat.add rootFuel 1) tid with
          | none => false
          | some (tf, tvs) =>
            match Nat.beq tf childFuel with
            | false => false
            | true =>
              let cvals := vz :: kept ka va (kept kb vb (eraseWord vb (eraseWord va ws)))
              match isSym with
              | false => sameSetFast cvals tvs
              | true => sameSetSym sym cvals tvs
noncomputable def checkPoolsRem (idxA idxB : Nat) (vz : Word) (ps : List (MatPool × Bool)) :
    Bool → Bool → Bool → Bool → Bool × Bool × Bool × Bool :=
  List.rec (fun u00 u01 u10 u11 => (u00, u01, u10, u11))
    (fun q _ ih u00 u01 u10 u11 =>
      cond (or (or (or u00 u01) u10) u11)
        (let p := q.1
         let aConst := Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1
         let bConst := Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1
         cond q.2
           (cond (or (or (or u11 u10) u01) (cond (and aConst bConst) false u00))
             (forceNat (Nat.land vz p.dom) fun mz =>
               cond (or (Nat.beq mz 0) (Nat.beq mz p.dom))
                 (ih (cond u00 (and aConst bConst) false) false false false)
                 (let c10 := cond bConst false u10
                  let c01 := cond aConst false u01
                  let c00 := cond (or aConst bConst) false u00
                  cond (or (or (or u11 c10) c01) c00)
                    (cond (cond (containsNat mz p.bank) true
                            (cond (Nat.beq (Nat.land p.dom 1) 1) false
                              (forceNat (Nat.xor mz p.dom) fun mzn => containsNat mzn p.bank)))
                      (ih (cond c00 false u00) (cond c01 false u01) (cond c10 false u10) false)
                      (ih u00 u01 u10 u11))
                    (ih u00 u01 u10 u11)))
             (ih u00 u01 u10 u11))
           (let c10 := cond bConst false u10
            let c01 := cond aConst false u01
            let c00 := cond (or aConst bConst) false u00
            cond (or (or (or u11 c10) c01) c00)
              (forceNat (Nat.land vz p.dom) fun mz =>
                cond (or (Nat.beq mz 0) (Nat.beq mz p.dom))
                  (ih (cond c00 false u00) (cond c01 false u01) (cond c10 false u10) false)
                  (ih u00 u01 u10 u11))
              (ih u00 u01 u10 u11)))
        (false, false, false, false))
    ps
def prepPools (childFuel : Nat) : List MatPool → List (MatPool × Bool)
  | [] => []
  | p :: ps =>
    let lhs := Nat.add childFuel p.paid
    let b11 := Nat.add p.bound p.wsConstCnt
    match Nat.blt b11 lhs with
    | true => prepPools childFuel ps
    | false => (p, Nat.blt lhs b11) :: prepPools childFuel ps
theorem land_shr_eq_mod_div_shl (x i : Nat) :
    Nat.land (Nat.shiftRight x i) 1 = Nat.mod (Nat.div x (Nat.shiftLeft 1 i)) 2 := by
  have h1 : Nat.shiftRight x i = x / 2 ^ i := Nat.shiftRight_eq_div_pow x i
  have h2 : Nat.div x (Nat.shiftLeft 1 i) = x / 2 ^ i := by
    simp only [nat_div_eq, nat_shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1, h2]
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
    simp only [nat_land_eq, Nat.testBit_and, Nat.testBit_zero, nat_mod_eq]
    have hlt : (x / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
    rcases (show (x / 2 ^ i) % 2 = 0 ∨ (x / 2 ^ i) % 2 = 1 by omega) with h | h <;> simp [h]
  | succ k' =>
    simp only [nat_land_eq, Nat.testBit_and, nat_mod_eq]
    have h1b : (1 : Nat).testBit (k' + 1) = false := Nat.testBit_lt_two_pow (by
      have : 2 ≤ 2 ^ (k' + 1) := Nat.le_self_pow (by omega) 2; omega)
    have h2b : ((x / 2 ^ i) % 2).testBit (k' + 1) = false := Nat.testBit_lt_two_pow (by
      have hlt : (x / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
      have : 2 ≤ 2 ^ (k' + 1) := Nat.le_self_pow (by omega) 2; omega)
    rw [h1b, h2b, Bool.and_false]
def mkVzVal (d : Nat) (a b : Word) : Word :=
  match d with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | _ => Nat.xor b (Nat.land a b)
theorem mkVzVal_eq {mask a b : Word} (ha : Masked mask a) (hb : Masked mask b) {d : Nat} (hd : d < 4) :
    mkVzVal d a b = binOp mask d a b := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact (binOp2_eq ha).symm
  · exact (binOp3_eq hb).symm
theorem prepPools_inv {childFuel : Nat} (ps : List MatPool) :
    ∀ q ∈ prepPools childFuel ps,
      q.1 ∈ ps ∧ Nat.add childFuel q.1.paid ≤ Nat.add q.1.bound q.1.wsConstCnt ∧
      (q.2 = true → Nat.add childFuel q.1.paid < Nat.add q.1.bound q.1.wsConstCnt) := by
  induction ps with
  | nil => intro q hq; cases hq
  | cons p ps ih =>
    intro q hq
    unfold prepPools at hq
    dsimp only at hq
    cases hlt : Nat.blt (Nat.add p.bound p.wsConstCnt) (Nat.add childFuel p.paid) with
    | true =>
      rw [hlt] at hq
      obtain ⟨h1, h2, h3⟩ := ih q hq
      exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
    | false =>
      rw [hlt] at hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · refine ⟨List.mem_cons_self, ?_, fun h => Nat.blt_eq.mp h⟩
        have hn : ¬ (Nat.add p.bound p.wsConstCnt < Nat.add childFuel p.paid) := fun h => by
          rw [Nat.blt_eq.mpr h] at hlt; cases hlt
        simp only [nat_add_eq] at hn ⊢; omega
      · obtain ⟨h1, h2, h3⟩ := ih q hq'
        exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
theorem bool_pool_scalar {p : MatPool} {childFuel idxA idxB : Nat} {vz : Word}
    (hle : Nat.add childFuel p.paid ≤ Nat.add p.bound p.wsConstCnt)
    (ka kb : Bool)
    (hclosed :
      let aC := Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1
      let bC := Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1
      let drop := (if ka then 0 else if aC then 1 else 0) + (if kb then 0 else if bC then 1 else 0)
      let flat := Nat.beq (Nat.land vz p.dom) 0 || Nat.beq (Nat.land vz p.dom) p.dom
      let inB := containsNat (Nat.land vz p.dom) p.bank ||
        (match Nat.beq (Nat.land p.dom 1) 1 with | true => false | false => containsNat (Nat.xor (Nat.land vz p.dom) p.dom) p.bank)
      (flat = true ∧ drop = 0) ∨
      (Nat.add childFuel p.paid < Nat.add p.bound p.wsConstCnt ∧
        ((flat = true ∧ drop ≤ 1) ∨ (inB = true ∧ drop = 0)))) :
    scalarPoolCut p childFuel idxA idxB ka kb vz = true := by
  unfold scalarPoolCut
  rw [forceNat_eq]
  have bitEq (idx : Nat) : Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idx)) 2 =
      if Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idx) 1) 1 then 1 else 0 := by
    rw [← land_shr_eq_mod_div_shl]
    have hlt : Nat.land (Nat.shiftRight p.wsConstMask idx) 1 < 2 := by
      rw [land_shr_eq_mod_div_shl]; simp only [nat_mod_eq]; exact Nat.mod_lt _ (by omega)
    cases h : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idx) 1) 1
    · have hne : Nat.land (Nat.shiftRight p.wsConstMask idx) 1 ≠ 1 := fun e => by rw [Nat.beq_eq.mpr e] at h; cases h
      simp only [Bool.false_eq_true, ite_false]; omega
    · simp only [ite_true]; exact Nat.beq_eq.mp h
  have h1 := bitEq idxA
  have h2 := bitEq idxB
  dsimp only at hclosed ⊢
  simp only [Nat.blt_eq, nat_add_eq, nat_sub_eq] at hle hclosed ⊢
  rcases hclosed with ⟨hflat, hdrop⟩ | ⟨hlt, (⟨hflat, hdrop⟩ | ⟨hinB, hdrop⟩)⟩
  · have hf' : (match Nat.beq (Nat.land vz p.dom) 0 with | true => true | false => Nat.beq (Nat.land vz p.dom) p.dom) = true := by
      cases h0 : Nat.beq (Nat.land vz p.dom) 0
      · simp only [h0, Bool.false_or] at hflat; exact hflat
      · rfl
    rw [hf']; dsimp only
    cases ka <;> cases kb <;>
      cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
      cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
      simp only [h1, h2, ha, hb, Bool.false_eq_true, ite_true, ite_false] at hdrop ⊢ <;> omega
  · have hf' : (match Nat.beq (Nat.land vz p.dom) 0 with | true => true | false => Nat.beq (Nat.land vz p.dom) p.dom) = true := by
      cases h0 : Nat.beq (Nat.land vz p.dom) 0
      · simp only [h0, Bool.false_or] at hflat; exact hflat
      · rfl
    rw [hf']; dsimp only
    cases ka <;> cases kb <;>
      cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
      cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
      simp only [h1, h2, ha, hb, Bool.false_eq_true, ite_true, ite_false] at hdrop ⊢ <;> omega
  · have hex0 : (match (match Nat.beq (Nat.land vz p.dom) 0 with | true => true | false => Nat.beq (Nat.land vz p.dom) p.dom) with
        | true => 0
        | false => match containsNat (Nat.land vz p.dom) p.bank with
          | true => 0
          | false => match Nat.beq (Nat.land p.dom 1) 1 with
            | true => 1
            | false => match containsNat (Nat.xor (Nat.land vz p.dom) p.dom) p.bank with | true => 0 | false => 1) = 0 := by
      cases h0 : Nat.beq (Nat.land vz p.dom) 0 <;> cases h1' : Nat.beq (Nat.land vz p.dom) p.dom <;>
        cases hcb : containsNat (Nat.land vz p.dom) p.bank <;>
        cases hd1 : Nat.beq (Nat.land p.dom 1) 1 <;>
        cases hcx : containsNat (Nat.xor (Nat.land vz p.dom) p.dom) p.bank <;>
        first
        | rfl
        | (exfalso; simp only [nat_land_eq, nat_xor_eq, Nat.and_one_is_mod] at hcb hd1 hcx; simp_all)
    rw [hex0]
    cases ka <;> cases kb <;>
      cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
      cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
      simp only [h1, h2, ha, hb, Bool.false_eq_true, ite_true, ite_false] at hdrop ⊢ <;> omega
theorem checkPoolsRem_sound {childFuel idxA idxB : Nat} {vz : Word} :
    ∀ (ps : List (MatPool × Bool))
      (hinv : ∀ q ∈ ps, Nat.add childFuel q.1.paid ≤ Nat.add q.1.bound q.1.wsConstCnt ∧
        (q.2 = true → Nat.add childFuel q.1.paid < Nat.add q.1.bound q.1.wsConstCnt))
      (u00 u01 u10 u11 : Bool),
      let r := checkPoolsRem idxA idxB vz ps u00 u01 u10 u11
      (u00 = true → r.1 = false → ∃ q ∈ ps, scalarPoolCut q.1 childFuel idxA idxB false false vz = true) ∧
      (u01 = true → r.2.1 = false → ∃ q ∈ ps, scalarPoolCut q.1 childFuel idxA idxB false true vz = true) ∧
      (u10 = true → r.2.2.1 = false → ∃ q ∈ ps, scalarPoolCut q.1 childFuel idxA idxB true false vz = true) ∧
      (u11 = true → r.2.2.2 = false → ∃ q ∈ ps, scalarPoolCut q.1 childFuel idxA idxB true true vz = true) := by
  intro ps
  induction ps with
  | nil =>
    intro _ u00 u01 u10 u11
    cases u00 <;> cases u01 <;> cases u10 <;> cases u11 <;> simp [checkPoolsRem]
  | cons q ps ih =>
    obtain ⟨p, isS1⟩ := q
    intro hinv u00 u01 u10 u11
    have hpInv := hinv (p, isS1) List.mem_cons_self
    have hpsInv : ∀ q' ∈ ps, Nat.add childFuel q'.1.paid ≤ Nat.add q'.1.bound q'.1.wsConstCnt ∧
        (q'.2 = true → Nat.add childFuel q'.1.paid < Nat.add q'.1.bound q'.1.wsConstCnt) :=
      fun q' hq' => hinv q' (List.mem_cons_of_mem _ hq')
    have hstep (u00' u01' u10' u11' : Bool)
        (h00 : u00 = true → u00' = false → scalarPoolCut p childFuel idxA idxB false false vz = true)
        (h01 : u01 = true → u01' = false → scalarPoolCut p childFuel idxA idxB false true vz = true)
        (h10 : u10 = true → u10' = false → scalarPoolCut p childFuel idxA idxB true false vz = true)
        (h11 : u11 = true → u11' = false → scalarPoolCut p childFuel idxA idxB true true vz = true) :
        let r := checkPoolsRem idxA idxB vz ps u00' u01' u10' u11'
        (u00 = true → r.1 = false → ∃ q' ∈ (p, isS1) :: ps, scalarPoolCut q'.1 childFuel idxA idxB false false vz = true) ∧
        (u01 = true → r.2.1 = false → ∃ q' ∈ (p, isS1) :: ps, scalarPoolCut q'.1 childFuel idxA idxB false true vz = true) ∧
        (u10 = true → r.2.2.1 = false → ∃ q' ∈ (p, isS1) :: ps, scalarPoolCut q'.1 childFuel idxA idxB true false vz = true) ∧
        (u11 = true → r.2.2.2 = false → ∃ q' ∈ (p, isS1) :: ps, scalarPoolCut q'.1 childFuel idxA idxB true true vz = true) := by
      have hrec := ih hpsInv u00' u01' u10' u11'
      refine ⟨fun hu hr => ?_, fun hu hr => ?_, fun hu hr => ?_, fun hu hr => ?_⟩
      · cases hu' : u00'
        · exact ⟨(p, isS1), List.mem_cons_self, h00 hu hu'⟩
        · obtain ⟨q', hq', hs⟩ := hrec.1 hu' hr; exact ⟨q', List.mem_cons_of_mem _ hq', hs⟩
      · cases hu' : u01'
        · exact ⟨(p, isS1), List.mem_cons_self, h01 hu hu'⟩
        · obtain ⟨q', hq', hs⟩ := hrec.2.1 hu' hr; exact ⟨q', List.mem_cons_of_mem _ hq', hs⟩
      · cases hu' : u10'
        · exact ⟨(p, isS1), List.mem_cons_self, h10 hu hu'⟩
        · obtain ⟨q', hq', hs⟩ := hrec.2.2.1 hu' hr; exact ⟨q', List.mem_cons_of_mem _ hq', hs⟩
      · cases hu' : u11'
        · exact ⟨(p, isS1), List.mem_cons_self, h11 hu hu'⟩
        · obtain ⟨q', hq', hs⟩ := hrec.2.2.2 hu' hr; exact ⟨q', List.mem_cons_of_mem _ hq', hs⟩
    have hnoop := hstep u00 u01 u10 u11 (fun a b => by simp [a] at b) (fun a b => by simp [a] at b) (fun a b => by simp [a] at b) (fun a b => by simp [a] at b)
    dsimp only
    unfold checkPoolsRem
    dsimp only
    cases hany : or (or (or u00 u01) u10) u11 with
    | false =>
      have ⟨h0, h1, h2, h3⟩ : u00 = false ∧ u01 = false ∧ u10 = false ∧ u11 = false := by
        cases u00 <;> cases u01 <;> cases u10 <;> cases u11 <;> simp at hany ⊢
      subst h0 h1 h2 h3; simp
    | true =>
      cases isS1 with
      | false =>
        cases hcan : or (or (or u11 (cond (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1) false u10))
            (cond (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1) false u01))
            (cond (or (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1) (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1)) false u00) with
        | false => exact hnoop
        | true =>
          dsimp only [cond]; rw [forceNat_eq]
          cases hflat : or (Nat.beq (Nat.land vz p.dom) 0) (Nat.beq (Nat.land vz p.dom) p.dom) with
          | false => dsimp only [cond]; exact hnoop
          | true =>
            dsimp only [cond]
            have hflat' : (Nat.beq (Nat.land vz p.dom) 0 || Nat.beq (Nat.land vz p.dom) p.dom) = true := hflat
            apply hstep
            · intro hu hc; apply bool_pool_scalar hpInv.1 false false; left; refine ⟨hflat', ?_⟩
              cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
                cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
                simp only [ha, hb, hu, cond, Bool.true_or, Bool.or_true, Bool.false_or, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                first | rfl | cases hc
            · intro hu hc; apply bool_pool_scalar hpInv.1 false true; left; refine ⟨hflat', ?_⟩
              cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
                simp only [ha, hu, cond, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                first | rfl | cases hc
            · intro hu hc; apply bool_pool_scalar hpInv.1 true false; left; refine ⟨hflat', ?_⟩
              cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
                simp only [hb, hu, cond, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                first | rfl | cases hc
            · intro _ _; exact bool_pool_scalar hpInv.1 true true (Or.inl ⟨hflat', rfl⟩)
      | true =>
        have hltS1 : Nat.add childFuel p.paid < Nat.add p.bound p.wsConstCnt := hpInv.2 rfl
        cases hcan : or (or (or u11 u10) u01)
            (cond (and (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1) (Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1)) false u00) with
        | false => exact hnoop
        | true =>
          dsimp only [cond]; rw [forceNat_eq]
          cases hflat : or (Nat.beq (Nat.land vz p.dom) 0) (Nat.beq (Nat.land vz p.dom) p.dom) with
          | true =>
            dsimp only [cond]
            have hflat' : (Nat.beq (Nat.land vz p.dom) 0 || Nat.beq (Nat.land vz p.dom) p.dom) = true := hflat
            apply hstep
            · intro hu hc; apply bool_pool_scalar hpInv.1 false false; right; refine ⟨hltS1, Or.inl ⟨hflat', ?_⟩⟩
              cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
                cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
                simp only [ha, hb, hu, cond, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                first | omega | cases hc
            · intro _ _; apply bool_pool_scalar hpInv.1 false true; right; refine ⟨hltS1, Or.inl ⟨hflat', ?_⟩⟩
              cases Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;> simp
            · intro _ _; apply bool_pool_scalar hpInv.1 true false; right; refine ⟨hltS1, Or.inl ⟨hflat', ?_⟩⟩
              cases Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;> simp
            · intro _ _; exact bool_pool_scalar hpInv.1 true true (Or.inr ⟨hltS1, Or.inl ⟨hflat', by simp⟩⟩)
          | false =>
            dsimp only [cond]
            split
            · split
              · next hin =>
                have hinB : (containsNat (Nat.land vz p.dom) p.bank ||
                    (match Nat.beq (Nat.land p.dom 1) 1 with | true => false | false => containsNat (Nat.xor (Nat.land vz p.dom) p.dom) p.bank)) = true := by
                  cases h1 : containsNat (Nat.land vz p.dom) p.bank
                  · rw [h1] at hin
                    cases h2 : Nat.beq (Nat.land p.dom 1) 1
                    · rw [h2, forceNat_eq] at hin; simp only [Bool.false_or, h2]; exact hin
                    · rw [h2] at hin; cases hin
                  · rfl
                apply hstep
                · intro hu hc; apply bool_pool_scalar hpInv.1 false false; right; refine ⟨hltS1, Or.inr ⟨hinB, ?_⟩⟩
                  cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
                    cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
                    simp only [ha, hb, hu, cond, Bool.true_or, Bool.or_true, Bool.false_or, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                    first | rfl | cases hc
                · intro hu hc; apply bool_pool_scalar hpInv.1 false true; right; refine ⟨hltS1, Or.inr ⟨hinB, ?_⟩⟩
                  cases ha : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxA) 1) 1 <;>
                    simp only [ha, hu, cond, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                    first | rfl | cases hc
                · intro hu hc; apply bool_pool_scalar hpInv.1 true false; right; refine ⟨hltS1, Or.inr ⟨hinB, ?_⟩⟩
                  cases hb : Nat.beq (Nat.land (Nat.shiftRight p.wsConstMask idxB) 1) 1 <;>
                    simp only [hb, hu, cond, ite_true, ite_false, Bool.false_eq_true] at hc ⊢ <;>
                    first | rfl | cases hc
                · intro _ _; exact bool_pool_scalar hpInv.1 true true (Or.inr ⟨hltS1, Or.inr ⟨hinB, rfl⟩⟩)
              · exact hnoop
            · exact hnoop
noncomputable def checkVzCore (mask goal : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List (MatPool × Bool))
    (nodeId childFuel : Nat) (ws : List Word) (idxA idxB : Nat) (va vb vz : Word) (d : Nat)
    (ok00 ok01 ok10 ok11 : Bool) : Bool :=
  match Nat.beq vz 0 || Nat.beq vz mask || containsNat vz ws with
  | true => true
  | false =>
    match childFuel with
    | 0 => !Nat.beq vz goal
    | _ =>
      match checkPoolsRem idxA idxB vz pools ok00 ok01 ok10 ok11 with
      | (false, false, false, false) => true
      | (r00, r01, r10, r11) =>
        match nlinks with
        | [] => false
        | _ =>
          let baseTok := Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4
          (match r00 with | false => true | true => checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB baseTok false false va vb vz) &&
          (match r01 with | false => true | true => checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB baseTok false true va vb vz) &&
          (match r10 with | false => true | true => checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB baseTok true false va vb vz) &&
          (match r11 with | false => true | true => checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB baseTok true true va vb vz)
noncomputable def checkOpFast (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List (MatPool × Bool))
    (nodeId childFuel : Nat) (can1 can2 : Bool) (ws : List Word) (idxA idxB : Nat)
    (va vb : Word) (otherSep sepA0 sepB0 sepAB0 sepZ : Nat) (d : Nat) (mkVz : Word) : Bool :=
  let ok00 := Nat.beq (Nat.lor otherSep sepZ) allSep
  let ok01 := match can1 with | false => false | true => Nat.beq (Nat.lor sepB0 sepZ) allSep
  let ok10 := match can1 with | false => false | true => Nat.beq (Nat.lor sepA0 sepZ) allSep
  let ok11 := match can2 with | false => false | true => Nat.beq (Nat.lor sepAB0 sepZ) allSep
  match ok00 || ok01 || ok10 || ok11 with
  | false => true
  | true =>
    forceNat mkVz fun vz =>
      checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB va vb vz d ok00 ok01 ok10 ok11
noncomputable def checkLoopB (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List (MatPool × Bool))
    (nodeId childFuel : Nat) (can1 can2 : Bool) (ws : List Word) (idxA : Nat) (wa : Wire)
    (bs : List (Wire × Nat)) : Nat → Nat → Bool :=
  List.rec (fun _ _ => true)
    (fun p _ ih preMid idxB =>
      let wb := p.1
      forceNat (Nat.lor preMid p.2) fun otherSep =>
        cond
          (cond (Nat.beq otherSep allSep)
            (forceNat (Nat.land wa.val wb.val) fun ab =>
              cond (checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB wa.val wb.val ab 0 true can1 can1 can2)
                (cond (forceNat (Nat.lor wa.val wb.val) fun z1 => checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB wa.val wb.val z1 1 true can1 can1 can2)
                  (cond (forceNat (Nat.xor wa.val ab) fun z2 => checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB wa.val wb.val z2 2 true can1 can1 can2)
                    (forceNat (Nat.xor wb.val ab) fun z3 => checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB wa.val wb.val z3 3 true can1 can1 can2)
                    false) false) false)
            (forceNat (cond can1 (Nat.lor otherSep wa.sep) 0) fun sepA0 =>
              forceNat (cond can1 (Nat.lor otherSep wb.sep) 0) fun sepB0 =>
                forceNat (cond can2 (Nat.lor sepA0 wb.sep) 0) fun sepAB0 =>
                  forceNat (Nat.xor (Nat.land wa.pos wb.pos) (Nat.land wa.neg wb.neg)) fun sep0 =>
                    forceNat (Nat.xor wb.sep sep0) fun sep3 =>
                      forceNat (Nat.land wa.val wb.val) fun ab =>
                        cond (checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep0 0 ab)
                          (cond (checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 (Nat.xor wa.sep sep3) 1 (Nat.lor wa.val wb.val))
                            (cond (checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 (Nat.xor wa.sep sep0) 2 (Nat.xor wa.val ab))
                              (checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep3 3 (Nat.xor wb.val ab))
                              false) false) false))
          (forceNat (Nat.lor preMid wb.sep) fun preMid1 => ih preMid1 (Nat.add idxB 1))
          false)
    bs
noncomputable def checkLoopA (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List (MatPool × Bool))
    (nodeId childFuel : Nat) (can1 can2 : Bool) (ws : List Word)
    (xs : List (Wire × Nat)) : Nat → Nat → Bool :=
  List.rec (fun _ _ => true)
    (fun p tail ih pre idxA =>
      cond (checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA p.1 tail pre (Nat.add idxA 1))
        (forceNat (Nat.lor pre p.1.sep) fun pre1 => ih pre1 (Nat.add idxA 1))
        false)
    xs
noncomputable def checkNodeWith (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat)
    (rootVals : List Word) (dag : BTree NodeRec) (fdepth : Nat)
    (cutTree : BTree CutSpec) (cdepth : Nat) (i : Nat) (st : Nat × List Wire × List HistStep) : Bool :=
  let (fuel, ws, hist) := st
  forceSpine (ws.map Wire.val) fun vals =>
    match containsNat goal vals with
    | true => false
    | false =>
      match fuel with
      | 0 => true
      | childFuel + 1 =>
        let wsLen := ws.length
        match Nat.ble wsLen (Nat.add childFuel 2) with
        | false => true
        | true =>
          let nd := btreeGet (0, [], []) fdepth dag i
          let pools := materializeList cutTree cdepth vals hist nd.2.1
          match pools.any (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) with
          | true => true
          | false =>
            let can1 := Nat.ble wsLen (Nat.add childFuel 1)
            let can2 := Nat.ble (Nat.add wsLen 1) (Nat.add childFuel 1)
            let (wsSuf, _) := withSuffix ws
            forceSpine (prepPools childFuel pools) fun pools1 =>
              checkLoopA mask goal allSep sym count rootFuel rootVals dag fdepth nd.2.2 pools1 i childFuel can1 can2 vals wsSuf 0 0
noncomputable def checkNode (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat)
    (rootWs : List Wire) (dag : BTree NodeRec) (fdepth : Nat)
    (cutTree : BTree CutSpec) (cdepth : Nat) (i : Nat) : Bool :=
  match traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) i with
  | none => false
  | some st => checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth i st
abbrev StateEntry := Nat × (Nat × List Wire × List HistStep)
def popToParent (par : Nat) : List StateEntry → List StateEntry
  | [] => []
  | (k, st) :: rest => match Nat.beq k par with | true => (k, st) :: rest | false => popToParent par rest
theorem popToParent_mem {par : Nat} : ∀ (c : List StateEntry) (e : StateEntry), e ∈ popToParent par c → e ∈ c := by
  intro c; induction c with
  | nil => intro e h; cases h
  | cons x xs ih =>
    intro e h; unfold popToParent at h
    cases hb : Nat.beq x.1 par
    · rw [hb] at h; exact List.mem_cons_of_mem _ (ih e h)
    · rw [hb] at h; exact h
theorem popToParent_head {par : Nat} : ∀ (c : List StateEntry) (e : StateEntry) (rs : List StateEntry),
    popToParent par c = e :: rs → e.1 = par := by
  intro c; induction c with
  | nil => intro e rs h; cases h
  | cons x xs ih =>
    intro e rs h; unfold popToParent at h
    cases hb : Nat.beq x.1 par
    · rw [hb] at h; exact ih e rs h
    · rw [hb] at h; injection h with he; subst he; exact Nat.beq_eq.mp hb
noncomputable def checkRangeLoop (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat)
    (rootWs : List Wire) (rootVals : List Word) (dag : BTree NodeRec) (fdepth : Nat)
    (cutTree : BTree CutSpec) (cdepth : Nat) :
    Nat → Nat → List StateEntry → Bool
  | _, 0, _ => true
  | start, cnt + 1, cache =>
    let res : Option ((Nat × List Wire × List HistStep) × List StateEntry) := match start with
      | 0 => some ((rootFuel, rootWs, []), [])
      | _ =>
        let pt := (btreeGet (0, [], []) fdepth dag start).1
        let par := Nat.div pt 4096
        let tok := Nat.mod pt 4096
        match Nat.blt par start with
        | false => none
        | true =>
          let c1 := popToParent par cache
          match c1 with
          | (_, pst) :: _ =>
            match applyTok mask tok pst with
            | none => none
            | some st => some (st, c1)
          | [] =>
            match traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) start with
            | none => none
            | some st => some (st, [])
    match res with
    | none => false
    | some (st, cache1) =>
      match checkNodeWith mask goal allSep sym count rootFuel rootVals dag fdepth cutTree cdepth start st with
      | false => false
      | true => checkRangeLoop mask goal allSep sym count rootFuel rootWs rootVals dag fdepth cutTree cdepth (Nat.add start 1) cnt ((start, st) :: cache1)
noncomputable def checkRange (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat)
    (rootWs : List Wire) (dag : BTree NodeRec) (fdepth : Nat)
    (cutTree : BTree CutSpec) (cdepth : Nat) (start cnt : Nat) : Bool :=
  forceSpine (rootWs.map Wire.val) fun rootVals =>
    checkRangeLoop mask goal allSep sym count rootFuel rootWs rootVals dag fdepth cutTree cdepth start cnt []
theorem checkRangeLoop_sound {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootWs : List Wire} {dag : BTree NodeRec} {fdepth : Nat}
    {cutTree : BTree CutSpec} {cdepth : Nat} :
    ∀ (cnt start : Nat) (cache : List StateEntry),
      (∀ e ∈ cache, traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) e.1 = some e.2) →
      checkRangeLoop mask goal allSep sym count rootFuel rootWs (rootWs.map Wire.val) dag fdepth cutTree cdepth start cnt cache = true →
      ∀ i, start ≤ i → i < start + cnt →
        checkNode mask goal allSep sym count rootFuel rootWs dag fdepth cutTree cdepth i = true := by
  intro cnt
  induction cnt with
  | zero => intro _ _ _ _ i h1 h2; omega
  | succ cnt ih =>
    intro start cache hcache hloop i h1 h2
    unfold checkRangeLoop at hloop
    dsimp only at hloop
    have hstep : ∃ st cache1,
        traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) start = some st ∧
        (∀ e ∈ cache1, traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) e.1 = some e.2) ∧
        checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth start st = true ∧
        checkRangeLoop mask goal allSep sym count rootFuel rootWs (rootWs.map Wire.val) dag fdepth cutTree cdepth (Nat.add start 1) cnt ((start, st) :: cache1) = true := by
      cases start with
      | zero =>
        change (match checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth 0 (rootFuel, rootWs, []) with
          | false => false
          | true => checkRangeLoop mask goal allSep sym count rootFuel rootWs (rootWs.map Wire.val) dag fdepth cutTree cdepth (Nat.add 0 1) cnt ((0, (rootFuel, rootWs, [])) :: [])) = true at hloop
        cases hcn : checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth 0 (rootFuel, rootWs, []) with
        | false => rw [hcn] at hloop; cases hloop
        | true => rw [hcn] at hloop; exact ⟨(rootFuel, rootWs, []), [], rfl, (fun _ h => by cases h), hcn, hloop⟩
      | succ s' =>
        change (match (match Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) (s' + 1) with
          | false => none
          | true => match popToParent (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) cache with
            | (_, pst) :: rs => match applyTok mask (Nat.mod (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) pst with
              | none => none | some st => some (st, popToParent (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) cache)
            | [] => match traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) (s' + 1) with
              | none => none | some st => some (st, [])) with
          | none => false
          | some (st, cache1) => match checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth (s' + 1) st with
            | false => false | true => checkRangeLoop mask goal allSep sym count rootFuel rootWs (rootWs.map Wire.val) dag fdepth cutTree cdepth (Nat.add (s' + 1) 1) cnt ((s' + 1, st) :: cache1)) = true at hloop
        cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) (s' + 1) with
        | false => rw [hlt] at hloop; cases hloop
        | true =>
          rw [hlt] at hloop
          cases hpop : popToParent (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) cache with
          | nil =>
            rw [hpop] at hloop
            cases htr : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) (s' + 1) with
            | none => rw [htr] at hloop; cases hloop
            | some st =>
              rw [htr] at hloop; dsimp only at hloop
              cases hcn : checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth (s' + 1) st with
              | false => rw [hcn] at hloop; cases hloop
              | true => rw [hcn] at hloop; exact ⟨st, [], rfl, (fun _ h => by cases h), hcn, hloop⟩
          | cons e rs =>
            obtain ⟨ek, pst⟩ := e
            rw [hpop] at hloop
            dsimp only at hloop
            cases hap : applyTok mask (Nat.mod (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) pst with
            | none => rw [hap] at hloop; cases hloop
            | some st =>
              rw [hap] at hloop; dsimp only at hloop
              cases hcn : checkNodeWith mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth cutTree cdepth (s' + 1) st with
              | false => rw [hcn] at hloop; cases hloop
              | true =>
                rw [hcn] at hloop
                have hek : ek = Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096 :=
                  popToParent_head cache (ek, pst) rs hpop
                have htr_par : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) (Nat.div (btreeGet (0, [], []) fdepth dag (s' + 1)).1 4096) = some pst := by
                  rw [← hek]; exact hcache (ek, pst) (popToParent_mem cache _ (hpop ▸ List.mem_cons_self))
                have hpst_pos : 0 < pst.1 := by
                  obtain ⟨f0, w0, hi0⟩ := pst
                  cases f0 with
                  | zero => unfold applyTok at hap; cases hap
                  | succ _ => exact Nat.succ_pos _
                obtain ⟨hle_rf, hmono⟩ := traceState_gas_mono mask rootFuel rootWs dag fdepth _ _ _ htr_par
                have htr_par_rf := hmono rootFuel (by omega)
                have htr_cur : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) (s' + 1) = some st := by
                  unfold traceState; dsimp only
                  rw [show Nat.add s' 1 = s' + 1 from rfl, hlt, htr_par_rf]
                  exact hap
                refine ⟨st, (ek, pst) :: rs, htr_cur, fun x hx => hcache x (popToParent_mem cache x (hpop ▸ hx)), hcn, hloop⟩
    obtain ⟨st, cache1, htr_s, hc1, hcn_s, hrest⟩ := hstep
    by_cases hi : i = start
    · subst hi; unfold checkNode; rw [htr_s]; exact hcn_s
    · have hcache' : ∀ e ∈ (start, st) :: cache1, traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) e.1 = some e.2 := by
        intro e he; rcases List.mem_cons.mp he with rfl | he'; exact htr_s; exact hc1 e he'
      exact ih (Nat.add start 1) ((start, st) :: cache1) hcache' hrest i (by simp only [nat_add_eq]; omega) (by simp only [nat_add_eq]; omega)
def AllChecked (f : Nat → Bool) (s n : Nat) : Prop := ∀ i, s ≤ i → i < s + n → f i = true
theorem cr_sound {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootWs : List Wire} {dag : BTree NodeRec} {fdepth : Nat}
    {cutTree : BTree CutSpec} {cdepth start cnt : Nat}
    (h : checkRange mask goal allSep sym count rootFuel rootWs dag fdepth cutTree cdepth start cnt = true) :
    AllChecked (checkNode mask goal allSep sym count rootFuel rootWs dag fdepth cutTree cdepth) start cnt := by
  unfold checkRange at h; rw [forceSpine_eq] at h
  exact checkRangeLoop_sound cnt start [] (fun _ hm => by cases hm) h
theorem ac_merge {f : Nat → Bool} (s l r : Nat) (a : AllChecked f s l) (b : AllChecked f (s + l) r) :
    AllChecked f s (l + r) := by
  intro i h1 h2
  by_cases h : i < s + l
  · exact a i h1 h
  · exact b i (by omega) (by omega)
theorem foldr_or_erase_two (ws : List Wire) (idxA idxB : Nat) (ha : idxA < ws.length)
    (hb : idxB < ws.length) (hab : idxA < idxB) :
    let wa := ws.getD idxA ⟨0,0,0,0⟩
    let wb := ws.getD idxB ⟨0,0,0,0⟩
    let pre := (ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0
    let mid := ((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0
    let suf := (ws.drop (idxB + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0
    ∀ (ka kb : Bool), (ws.map Wire.val).Nodup →
      (childWires ws wa wb z ka kb).foldr (fun w acc => Nat.lor w.sep acc) 0 =
        Nat.lor (Nat.lor (Nat.lor (Nat.lor pre mid) suf)
          (Nat.lor (if ka then wa.sep else 0) (if kb then wb.sep else 0))) z.sep := by
  intro wa wb pre mid suf ka kb hnd
  have hfold_bit : ∀ (l : List Wire) (k : Nat),
      (l.foldr (fun w acc => Nat.lor w.sep acc) 0).testBit k = l.any (fun w => w.sep.testBit k) := by
    intro l k; induction l with
    | nil => simp
    | cons w ws ih =>
      change (Nat.lor w.sep (ws.foldr (fun w acc => Nat.lor w.sep acc) 0)).testBit k = _
      rw [nat_lor_eq, Nat.testBit_or, ih, List.any_cons]
  have hmem_erase : ∀ (l : List Wire) (x : Word), (l.map Wire.val).Nodup → ∀ w, w ∈ eraseWire x l ↔ w ∈ l ∧ w.val ≠ x := by
    intro l x
    induction l with
    | nil => intro _ w; simp [eraseWire]
    | cons u us ih =>
      intro hnd' w
      simp only [List.map_cons, List.nodup_cons] at hnd'
      simp only [eraseWire]
      cases h : Nat.beq u.val x with
      | true =>
        have hux : u.val = x := Nat.beq_eq.mp h
        constructor
        · intro hw
          refine ⟨List.mem_cons_of_mem _ hw, ?_⟩
          intro hwx
          exact hnd'.1 (hux ▸ hwx ▸ List.mem_map_of_mem hw)
        · rintro ⟨hw, hne⟩
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact absurd hux hne
          · exact hw'
      | false =>
        have hux : u.val ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
        change w ∈ u :: eraseWire x us ↔ _
        rw [List.mem_cons, List.mem_cons, ih hnd'.2]
        constructor
        · rintro (rfl | ⟨hw, hne⟩)
          · exact ⟨Or.inl rfl, hux⟩
          · exact ⟨Or.inr hw, hne⟩
        · rintro ⟨rfl | hw, hne⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hw, hne⟩
  have hwa_eq : wa = ws[idxA] := by
    simp only [wa, List.getD_eq_getElem?_getD, ha, getElem?_pos, Option.getD_some]
  have hwb_eq : wb = ws[idxB] := by
    simp only [wb, List.getD_eq_getElem?_getD, hb, getElem?_pos, Option.getD_some]
  have hsplit : ws = ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1) := by
    have h1 : ws = ws.take idxA ++ ws[idxA] :: ws.drop (idxA + 1) := by
      have := (List.take_append_drop idxA ws).symm
      rwa [List.drop_eq_getElem_cons ha] at this
    have hb' : idxB - idxA - 1 < (ws.drop (idxA + 1)).length := by simp; omega
    have h2 : ws.drop (idxA + 1) = (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++
        (ws.drop (idxA + 1))[idxB - idxA - 1] :: (ws.drop (idxA + 1)).drop (idxB - idxA - 1 + 1) := by
      have := (List.take_append_drop (idxB - idxA - 1) (ws.drop (idxA + 1))).symm
      rwa [List.drop_eq_getElem_cons hb'] at this
    have hidx : (ws.drop (idxA + 1))[idxB - idxA - 1] = wb := by
      simp only [List.getElem_drop, hwb_eq]; congr 1; omega
    have hdrop2 : (ws.drop (idxA + 1)).drop (idxB - idxA - 1 + 1) = ws.drop (idxB + 1) := by
      rw [List.drop_drop]; congr 1; omega
    rw [hidx, hdrop2] at h2
    rw [← hwa_eq] at h1
    calc ws = ws.take idxA ++ wa :: ws.drop (idxA + 1) := h1
      _ = ws.take idxA ++ wa :: ((ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ wb :: ws.drop (idxB + 1)) :=
        congrArg (fun t => ws.take idxA ++ wa :: t) h2
      _ = ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1) := by
        simp [List.append_assoc]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [hfold_bit]
  dsimp only [pre, mid, suf]
  rw [nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or,
      nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or, hfold_bit, hfold_bit, hfold_bit]
  have hrest_mem : ∀ w, w ∈ eraseWire wb.val (eraseWire wa.val ws) ↔
      w ∈ ws.take idxA ∨ w ∈ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ∨ w ∈ ws.drop (idxB + 1) := by
    intro w
    have hnd1 : ((eraseWire wa.val ws).map Wire.val).Nodup := by
      rw [eraseWire_map]; exact hnd.erase _
    rw [hmem_erase _ _ hnd1, hmem_erase _ _ hnd]
    constructor
    · rintro ⟨⟨hw, hna⟩, hnb⟩
      rw [hsplit] at hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with (((h1 | rfl) | h2) | rfl) | h3
      · exact Or.inl h1
      · exact absurd rfl hna
      · exact Or.inr (Or.inl h2)
      · exact absurd rfl hnb
      · exact Or.inr (Or.inr h3)
    · intro hor
      have hw : w ∈ ws := by
        rw [hsplit]; simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
        · exact Or.inl (Or.inl (Or.inr h2))
        · exact Or.inr h3
      have hnd_split := hnd
      rw [hsplit, List.map_append, List.map_append, List.map_append, List.map_append] at hnd_split
      have hne_from : ∀ (l1 l2 : List Wire) (u : Wire),
          (l1.map Wire.val ++ u.val :: l2.map Wire.val).Nodup → ∀ v ∈ l1 ++ l2, v.val ≠ u.val := by
        intro l1 l2 u hnu v hv heq
        rw [List.nodup_append] at hnu
        rcases List.mem_append.mp hv with hv1 | hv2
        · exact hnu.2.2 _ (List.mem_map_of_mem hv1) _ (List.mem_cons_self) heq
        · exact (List.nodup_cons.mp hnu.2.1).1 (heq ▸ List.mem_map_of_mem hv2)
      refine ⟨⟨hw, ?_⟩, ?_⟩
      · have hndA : ((ws.take idxA).map Wire.val ++ wa.val :: ((ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1)).map Wire.val).Nodup := by
          simpa [List.map_append, List.append_assoc] using hnd_split
        apply hne_from _ _ wa hndA w
        simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl (Or.inl h2))
        · exact Or.inr (Or.inr h3)
      · have hndB : ((ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1)).map Wire.val ++ wb.val :: (ws.drop (idxB + 1)).map Wire.val).Nodup := by
          simpa [List.map_append, List.append_assoc] using hnd_split
        apply hne_from _ _ wb hndB w
        simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl (Or.inl (Or.inl h1))
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3
  apply Bool.eq_iff_iff.mpr
  simp only [childWires, List.any_cons, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (hz | ⟨w, hw, hwk⟩)
    · exact Or.inr hz
    · left
      cases ka with
      | true =>
        simp only [kept, ite_true, List.mem_cons] at hw
        rcases hw with rfl | hw'
        · exact Or.inr (Or.inl (by simp [hwk]))
        · cases kb with
          | true =>
            simp only [kept, ite_true, List.mem_cons] at hw'
            rcases hw' with rfl | hw''
            · exact Or.inr (Or.inr (by simp [hwk]))
            · rcases (hrest_mem w).mp hw'' with h1 | h2 | h3
              · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
              · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
              · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
          | false =>
            simp only [kept, Bool.false_eq_true, ite_false] at hw'
            rcases (hrest_mem w).mp hw' with h1 | h2 | h3
            · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
            · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
      | false =>
        simp only [kept, Bool.false_eq_true, ite_false] at hw
        cases kb with
        | true =>
          simp only [kept, ite_true, List.mem_cons] at hw
          rcases hw with rfl | hw''
          · exact Or.inr (Or.inr (by simp [hwk]))
          · rcases (hrest_mem w).mp hw'' with h1 | h2 | h3
            · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
            · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
        | false =>
          simp only [kept, Bool.false_eq_true, ite_false] at hw
          rcases (hrest_mem w).mp hw with h1 | h2 | h3
          · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
          · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
  · rintro ((((⟨w, h1, hwk⟩ | ⟨w, h2, hwk⟩) | ⟨w, h3, hwk⟩) | (hka | hkb)) | hz)
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inl h1)
      cases ka <;> cases kb <;> simp [kept, hm]
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inr (Or.inl h2))
      cases ka <;> cases kb <;> simp [kept, hm]
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inr (Or.inr h3))
      cases ka <;> cases kb <;> simp [kept, hm]
    · cases ka with
      | false => simp at hka
      | true => right; exact ⟨wa, by simp [kept], by simpa using hka⟩
    · cases kb with
      | false => simp at hkb
      | true => right; exact ⟨wb, by cases ka <;> simp [kept], by simpa using hkb⟩
    · exact Or.inl hz
theorem cond_and_true {a b : Bool} (h : cond a b false = true) : a = true ∧ b = true := by
  cases a <;> simp at h ⊢; exact h
theorem checkLoopB_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List (MatPool × Bool)} {nodeId childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} {idxA : Nat} {wa : Wire} :
    ∀ (bs : List (Wire × Nat)) (preMid idxB : Nat),
      checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA wa bs preMid idxB = true →
      ∀ j < bs.length, ∀ d < 4,
        let wb := (bs.getD j (⟨0,0,0,0⟩, 0)).1
        let sufB := (bs.getD j (⟨0,0,0,0⟩, 0)).2
        let mid := (bs.take j).foldr (fun x acc => Nat.lor x.1.sep acc) 0
        let otherSep := Nat.lor (Nat.lor preMid mid) sufB
        let sepA0 := if can1 then Nat.lor otherSep wa.sep else 0
        let sepB0 := if can1 then Nat.lor otherSep wb.sep else 0
        let sepAB0 := if can2 then Nat.lor sepA0 wb.sep else 0
        let p0 := Nat.land wa.pos wb.pos
        let n0 := Nat.land wa.neg wb.neg
        let sep0 := Nat.xor p0 n0
        let sepZ := match d with | 0 => sep0 | 1 => Nat.xor wa.sep (Nat.xor wb.sep sep0) | 2 => Nat.xor wa.sep sep0 | _ => Nat.xor wb.sep sep0
        let mkVz := mkVzVal d wa.val wb.val
        (Nat.beq otherSep allSep = true ∧
          checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA (idxB + j) wa.val wb.val mkVz d true can1 can1 can2 = true) ∨
        checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA (idxB + j) wa.val wb.val otherSep sepA0 sepB0 sepAB0 sepZ d mkVz = true := by
  intro bs
  induction bs with
  | nil => intro _ _ _ j hj; simp at hj
  | cons p bs ih =>
    obtain ⟨wb0, suf0⟩ := p
    intro preMid idxB h j hj d hd
    unfold checkLoopB at h
    dsimp only at h
    rw [forceNat_eq] at h
    obtain ⟨hcur, hrest⟩ := cond_and_true h
    rw [forceNat_eq] at hrest
    change checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA wa bs (Nat.lor preMid wb0.sep) (Nat.add idxB 1) = true at hrest
    cases j with
    | zero =>
      have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      have h0' : Nat.lor preMid 0 = preMid := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
      have h0l : Nat.lor 0 wb0.sep = wb0.sep := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
      cases heq : Nat.beq (Nat.lor preMid suf0) allSep with
      | true =>
        rw [heq] at hcur; dsimp only [cond] at hcur; rw [forceNat_eq] at hcur
        obtain ⟨h0, h123⟩ := cond_and_true hcur
        rw [forceNat_eq] at h123
        obtain ⟨h1, h23⟩ := cond_and_true h123
        rw [forceNat_eq] at h23
        obtain ⟨h2, h3⟩ := cond_and_true h23
        rw [forceNat_eq] at h3
        left
        refine ⟨?_, ?_⟩
        · simpa [List.getD_cons_zero, List.take_zero, List.foldr_nil, h0'] using heq
        · rcases h4 with rfl | rfl | rfl | rfl <;>
            simpa [List.getD_cons_zero, Nat.add_zero, mkVzVal] using (by first | exact h0 | exact h1 | exact h2 | exact h3)
      | false =>
        rw [heq] at hcur; dsimp only [cond] at hcur
        simp only [forceNat_eq] at hcur
        obtain ⟨h0, h123⟩ := cond_and_true hcur
        obtain ⟨h1, h23⟩ := cond_and_true h123
        obtain ⟨h2, h3⟩ := cond_and_true h23
        right
        cases can1 <;> cases can2 <;> rcases h4 with rfl | rfl | rfl | rfl <;>
          (dsimp only [cond] at h0 h1 h2 h3 ⊢;
           simp only [List.getD_cons_zero, List.take_zero, List.foldr_nil, h0', h0l,
             Nat.add_zero, ite_true, ite_false, Bool.false_eq_true, mkVzVal] at h0 h1 h2 h3 ⊢;
           first | exact h0 | exact h1 | exact h2 | exact h3)
    | succ j' =>
      have hj' : j' < bs.length := by simp at hj; omega
      have hrec := ih (Nat.lor preMid wb0.sep) (Nat.add idxB 1) hrest j' hj' d hd
      have hidx : idxB + (j' + 1) = Nat.add idxB 1 + j' := by simp only [nat_add_eq]; omega
      have hlor : Nat.lor (Nat.lor preMid wb0.sep) ((bs.take j').foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
          Nat.lor preMid (Nat.lor wb0.sep ((bs.take j').foldr (fun x acc => Nat.lor x.1.sep acc) 0)) := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
      dsimp only at hrec ⊢
      simp only [List.getD_cons_succ, List.take_succ_cons, List.foldr_cons]
      rw [hidx, ← hlor]
      exact hrec
theorem checkLoopA_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List (MatPool × Bool)} {nodeId childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} :
    ∀ (xs : List (Wire × Nat)) (pre idxA : Nat),
      checkLoopA mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws xs pre idxA = true →
      ∀ i j, i < j → j < xs.length → ∀ d < 4,
        let wa := (xs.getD i (⟨0,0,0,0⟩, 0)).1
        let wb := (xs.getD j (⟨0,0,0,0⟩, 0)).1
        let sufB := (xs.getD j (⟨0,0,0,0⟩, 0)).2
        let preI := Nat.lor pre ((xs.take i).foldr (fun x acc => Nat.lor x.1.sep acc) 0)
        let mid := ((xs.drop (i + 1)).take (j - i - 1)).foldr (fun x acc => Nat.lor x.1.sep acc) 0
        let otherSep := Nat.lor (Nat.lor preI mid) sufB
        let sepA0 := if can1 then Nat.lor otherSep wa.sep else 0
        let sepB0 := if can1 then Nat.lor otherSep wb.sep else 0
        let sepAB0 := if can2 then Nat.lor sepA0 wb.sep else 0
        let p0 := Nat.land wa.pos wb.pos
        let n0 := Nat.land wa.neg wb.neg
        let sep0 := Nat.xor p0 n0
        let sepZ := match d with | 0 => sep0 | 1 => Nat.xor wa.sep (Nat.xor wb.sep sep0) | 2 => Nat.xor wa.sep sep0 | _ => Nat.xor wb.sep sep0
        let mkVz := mkVzVal d wa.val wb.val
        (Nat.beq otherSep allSep = true ∧
          checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws (idxA + i) (idxA + j) wa.val wb.val mkVz d true can1 can1 can2 = true) ∨
        checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws (idxA + i) (idxA + j) wa.val wb.val otherSep sepA0 sepB0 sepAB0 sepZ d mkVz = true := by
  intro xs
  induction xs with
  | nil => intro _ _ _ i j _ hj; simp at hj
  | cons p xs ih =>
    obtain ⟨wa0, _⟩ := p
    intro pre idxA h i j hij hj d hd
    change cond (checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA wa0 xs pre (Nat.add idxA 1)) (forceNat (Nat.lor pre wa0.sep) fun pre1 => checkLoopA mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws xs pre1 (Nat.add idxA 1)) false = true at h
    obtain ⟨hB, hA⟩ := cond_and_true h
    rw [forceNat_eq] at hA
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < xs.length := by simp at hj; omega
        have h0' : Nat.lor pre 0 = pre := by
          apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
        have hstep : idxA + (j' + 1) = Nat.add idxA 1 + j' := by simp only [nat_add_eq]; omega
        simpa [h0', hstep] using checkLoopB_at xs pre (Nat.add idxA 1) hB j' hj' d hd
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hij' : i' < j' := by omega
        have hj' : j' < xs.length := by simp at hj; omega
        have hlor : Nat.lor (Nat.lor pre wa0.sep) ((xs.take i').foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
            Nat.lor pre (Nat.lor wa0.sep ((xs.take i').foldr (fun x acc => Nat.lor x.1.sep acc) 0)) := by
          apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
        have hstep1 : idxA + (i' + 1) = Nat.add idxA 1 + i' := by simp only [nat_add_eq]; omega
        have hstep2 : idxA + (j' + 1) = Nat.add idxA 1 + j' := by simp only [nat_add_eq]; omega
        have hrec := ih (Nat.lor pre wa0.sep) (Nat.add idxA 1) hA i' j' hij' hj' d hd
        dsimp only at hrec ⊢
        simp only [List.getD_cons_succ, List.take_succ_cons, List.foldr_cons, List.drop_succ_cons]
        have hsub : j' + 1 - (i' + 1 + 1) = j' - (i' + 1) := by omega
        rw [hstep1, hstep2, ← hlor]
        simpa [hsub] using hrec
theorem restoreSet (U : Finset Word) (a b : Word) (hab : a ≠ b) :
    (if decide (a ∈ U) = true then insert a (if decide (b ∈ U) = true then insert b (((insert a (insert b U)).erase a).erase b) else ((insert a (insert b U)).erase a).erase b)
    else (if decide (b ∈ U) = true then insert b (((insert a (insert b U)).erase a).erase b) else ((insert a (insert b U)).erase a).erase b)) = U := by
  ext u
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
  · simp only [ha, hb, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true,
      Finset.mem_insert, Finset.mem_erase]
    by_cases hua : u = a
    · subst hua; simp [hab, ha]
    · by_cases hub : u = b
      · subst hub; simp [Ne.symm hab, hb]
      · simp [hua, hub]
theorem checkVzCore_at {mask goal : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List (MatPool × Bool)} {nodeId childFuel : Nat}
    {ws : List Word} {idxA idxB d : Nat} {va vb vz : Word}
    {ok00 ok01 ok10 ok11 : Bool}
    (hinv : ∀ q ∈ pools, Nat.add childFuel q.1.paid ≤ Nat.add q.1.bound q.1.wsConstCnt ∧
      (q.2 = true → Nat.add childFuel q.1.paid < Nat.add q.1.bound q.1.wsConstCnt))
    (hcore : checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB va vb vz d ok00 ok01 ok10 ok11 = true)
    (h1 : vz ≠ 0) (h2 : vz ≠ mask) (h3 : vz ∉ ws)
    (ka kb : Bool)
    (hok : (if ka then (if kb then ok11 else ok10) else (if kb then ok01 else ok00)) = true) :
    (childFuel = 0 ∧ vz ≠ goal) ∨
    (0 < childFuel ∧
      ((∃ q ∈ pools, scalarPoolCut q.1 childFuel idxA idxB ka kb vz = true) ∨
      checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB
        (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4) ka kb va vb vz = true)) := by
  have hnot_stale : (Nat.beq vz 0 || Nat.beq vz mask || containsNat vz ws) = false := by
    have hb1 : Nat.beq vz 0 = false := by
      cases h : Nat.beq vz 0
      · rfl
      · exact absurd (Nat.beq_eq.mp h) h1
    have hb2 : Nat.beq vz mask = false := by
      cases h : Nat.beq vz mask
      · rfl
      · exact absurd (Nat.beq_eq.mp h) h2
    have hb3 : containsNat vz ws = false := by
      cases h : containsNat vz ws
      · rfl
      · exact absurd ((containsNat_iff _ _).mp h) h3
    simp [hb1, hb2, hb3]
  unfold checkVzCore at hcore
  rw [hnot_stale] at hcore
  cases childFuel with
  | zero =>
    left
    refine ⟨rfl, fun eq => ?_⟩
    simp only [eq, Bool.not_eq_true'] at hcore
    exact absurd (Nat.beq_eq.mpr rfl) (by rw [hcore]; decide)
  | succ cf' =>
    right
    refine ⟨Nat.succ_pos cf', ?_⟩
    have hrem := checkPoolsRem_sound (childFuel := cf' + 1) (idxA := idxA) (idxB := idxB) (vz := vz) pools hinv ok00 ok01 ok10 ok11
    dsimp only at hcore hrem
    generalize hr_eq : checkPoolsRem idxA idxB vz pools ok00 ok01 ok10 ok11 = r at hcore hrem
    obtain ⟨r00, r01, r10, r11⟩ := r
    cases ka <;> cases kb
    · simp only [Bool.false_eq_true, ite_false] at hok
      cases hr00 : r00
      · exact Or.inl (hrem.1 hok hr00)
      · right
        rw [hr00] at hcore
        cases hnl : nlinks with
        | nil => rw [hnl] at hcore; cases r01 <;> cases r10 <;> cases r11 <;> simp at hcore
        | cons e es =>
          rw [hnl] at hcore
          cases r01 <;> cases r10 <;> cases r11 <;> simp only [Bool.and_eq_true] at hcore <;> exact hcore.1.1.1
    · simp only [Bool.false_eq_true, ite_false, ite_true] at hok
      cases hr01 : r01
      · exact Or.inl (hrem.2.1 hok hr01)
      · right
        rw [hr01] at hcore
        cases hnl : nlinks with
        | nil => rw [hnl] at hcore; cases r00 <;> cases r10 <;> cases r11 <;> simp at hcore
        | cons e es =>
          rw [hnl] at hcore
          cases r00 <;> cases r10 <;> cases r11 <;> simp only [Bool.and_eq_true] at hcore <;> exact hcore.1.1.2
    · simp only [Bool.false_eq_true, ite_false, ite_true] at hok
      cases hr10 : r10
      · exact Or.inl (hrem.2.2.1 hok hr10)
      · right
        rw [hr10] at hcore
        cases hnl : nlinks with
        | nil => rw [hnl] at hcore; cases r00 <;> cases r01 <;> cases r11 <;> simp at hcore
        | cons e es =>
          rw [hnl] at hcore
          cases r00 <;> cases r01 <;> cases r11 <;> simp only [Bool.and_eq_true] at hcore <;> exact hcore.1.2
    · simp only [ite_true] at hok
      cases hr11 : r11
      · exact Or.inl (hrem.2.2.2 hok hr11)
      · right
        rw [hr11] at hcore
        cases hnl : nlinks with
        | nil => rw [hnl] at hcore; cases r00 <;> cases r01 <;> cases r10 <;> simp at hcore
        | cons e es =>
          rw [hnl] at hcore
          cases r00 <;> cases r01 <;> cases r10 <;> simp only [Bool.and_eq_true] at hcore <;> exact hcore.2
theorem checkOpFast_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List (MatPool × Bool)} {nodeId childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} {idxA idxB d : Nat} {va vb vz : Word}
    {otherSep sepA0 sepB0 sepAB0 sepZ : Nat}
    (hinv : ∀ q ∈ pools, Nat.add childFuel q.1.paid ≤ Nat.add q.1.bound q.1.wsConstCnt ∧
      (q.2 = true → Nat.add childFuel q.1.paid < Nat.add q.1.bound q.1.wsConstCnt))
    (hop : (Nat.beq otherSep allSep = true ∧
            checkVzCore mask goal sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel ws idxA idxB va vb vz d true can1 can1 can2 = true) ∨
          checkOpFast mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools nodeId childFuel can1 can2 ws idxA idxB va vb otherSep sepA0 sepB0 sepAB0 sepZ d vz = true)
    (h1 : vz ≠ 0) (h2 : vz ≠ mask) (h3 : vz ∉ ws)
    (ka kb : Bool)
    (hcan1 : (ka = true ∨ kb = true) → can1 = true)
    (hcan2 : (ka = true ∧ kb = true) → can2 = true)
    (hsep : (if ka then (if kb then Nat.lor sepAB0 sepZ else Nat.lor sepA0 sepZ)
            else (if kb then Nat.lor sepB0 sepZ else Nat.lor otherSep sepZ)) = allSep) :
    (childFuel = 0 ∧ vz ≠ goal) ∨
    (0 < childFuel ∧
      ((∃ q ∈ pools, scalarPoolCut q.1 childFuel idxA idxB ka kb vz = true) ∨
      checkLink mask sym count rootFuel rootVals dag fdepth nlinks nodeId childFuel ws idxB
        (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4) ka kb va vb vz = true)) := by
  rcases hop with ⟨_, hcore⟩ | hop
  · apply checkVzCore_at hinv hcore h1 h2 h3 ka kb
    cases ka <;> cases kb
    · rfl
    · exact hcan1 (Or.inr rfl)
    · exact hcan1 (Or.inl rfl)
    · exact hcan2 ⟨rfl, rfl⟩
  · unfold checkOpFast at hop
    dsimp only at hop
    cases ka <;> cases kb
    · have hb0 : Nat.beq (Nat.lor otherSep sepZ) allSep = true := Nat.beq_eq.mpr hsep
      rw [hb0] at hop
      exact checkVzCore_at hinv (by simpa [forceNat_eq] using hop) h1 h2 h3 false false rfl
    · have hc1 := hcan1 (Or.inr rfl); subst hc1
      have hb1 : Nat.beq (Nat.lor sepB0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
      rw [hb1] at hop
      exact checkVzCore_at hinv (by simpa [forceNat_eq] using hop) h1 h2 h3 false true rfl
    · have hc1 := hcan1 (Or.inl rfl); subst hc1
      have hb2 : Nat.beq (Nat.lor sepA0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
      rw [hb2] at hop
      exact checkVzCore_at hinv (by simpa [forceNat_eq] using hop) h1 h2 h3 true false rfl
    · have hc2 := hcan2 ⟨rfl, rfl⟩; subst hc2
      have hb3 : Nat.beq (Nat.lor sepAB0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
      rw [hb3] at hop
      exact checkVzCore_at hinv (by simpa [forceNat_eq] using hop) h1 h2 h3 true true rfl
theorem sym_inj {mask T : Word} {sym : Word → Word} (hm : Masked fullMask mask) (hsym : SymOK mask T sym) :
    ∀ a b, Masked mask a → Masked mask b → sym a = sym b → a = b := by
  obtain ⟨f, hbij, hfM, hsymW, _⟩ := hsym
  intro a b ha hb eq
  refine masked_ext hm ha hb (fun r => ?_)
  obtain ⟨r', hr'⟩ := hbij.2 r
  have h1 := (hsymW a ha).2 r'
  have h2 := (hsymW b hb).2 r'
  rw [eq] at h1
  rw [← hr', ← h1, h2]
set_option maxHeartbeats 800000 in
theorem dagAllNodes {mask goal : Word} {pairs : List (Row × Row)} {sym : Word → Word}
    {count rootFuel fdepth cdepth : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {cutTree : BTree CutSpec}
    (hm : Masked fullMask mask)
    (hpairs : ∀ p ∈ pairs, pairValid mask goal p = true)
    (hsym : SymOK mask goal sym)
    (hrootM : ∀ w ∈ rootWs, Masked mask w.val)
    (hrootF : ∀ w ∈ rootWs, Faithful pairs w)
    (hrootNd : (rootWs.map Wire.val).Nodup)
    (hcuts : ∀ i < count, ∀ ci ∈ (btreeGet (0, [], []) fdepth dag i).2.1,
      ValidCut mask (rootWs.map Wire.val) goal (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci))
    (hcheck : AllChecked (checkNode mask goal (Nat.sub (Nat.shiftLeft 1 pairs.length) 1) sym
      count rootFuel rootWs dag fdepth cutTree cdepth) 0 count) :
    ∀ cap i st, i < count →
      traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) i = some st →
      st.1 = cap → Impossible mask goal cap (st.2.1.map Wire.val).toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk run
    obtain ⟨fuel, ws, hist⟩ := st
    dsimp only at hcap
    subst hcap
    obtain ⟨hM, hF, hNd⟩ := traceState_inv hpairs hrootM hrootF hrootNd _ _ _ htr
    dsimp only at hM hF hNd
    have hck := hcheck i (Nat.zero_le i) (by omega)
    unfold checkNode at hck
    rw [htr] at hck
    unfold checkNodeWith at hck
    simp only [forceSpine_eq] at hck
    cases hgoal : containsNat goal (ws.map Wire.val) with
    | true => simp [hgoal] at hck
    | false =>
      rw [hgoal] at hck
      have hnoGoal : goal ∉ ws.map Wire.val := fun hmem =>
        absurd ((containsNat_iff _ _).mpr hmem) (by simp [hgoal])
      cases fuel with
      | zero =>
        have hk0 : k = 0 := by omega
        subst hk0
        obtain ⟨heq, _⟩ := run
        have hmem : goal ∈ (ws.map Wire.val).toFinset := by rw [heq]; simp
        exact hnoGoal (List.mem_toFinset.mp hmem)
      | succ childFuel =>
        dsimp only at hck
        have hsz : (ws.map Wire.val).length ≤ childFuel + 2 := by
          have hs := live_size run
          rw [List.toFinset_card_of_nodup hNd] at hs
          have hkle : k ≤ childFuel + 1 := hk
          omega
        have hble : Nat.ble ws.length (Nat.add childFuel 2) = true := by
          rw [Nat.ble_eq]; rw [List.length_map] at hsz; simp only [nat_add_eq]; omega
        rw [hble] at hck
        dsimp only at hck
        have hsf : (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1).any
            (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) = false := by
          cases hself : (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1).any
              (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) with
          | false => rfl
          | true =>
            rw [List.any_eq_true] at hself
            obtain ⟨mp, hmp_mem, hmp_cut⟩ := hself
            have hvp := materializeList_sound (ws.map Wire.val) hist _ (hcuts i hi) mp hmp_mem
            exact absurd run (selfPoolCut_sound hvp hNd hmp_cut k (by simpa [nat_add_eq] using hk))
        rw [hsf] at hck
        dsimp only at hck
        cases k with
        | zero =>
          obtain ⟨heq, _⟩ := run
          have hmem : goal ∈ (ws.map Wire.val).toFinset := by rw [heq]; simp
          exact hnoGoal (List.mem_toFinset.mp hmem)
        | succ k' =>
          obtain ⟨U, x, y, d0, hd0, hSeq, hpx, hpy, hxy, hfresh0, tail0⟩ := run
          have hx_mem : x ∈ ws.map Wire.val := List.mem_toFinset.mp (hSeq ▸ Finset.mem_insert_self _ _)
          have hy_mem : y ∈ ws.map Wire.val := List.mem_toFinset.mp (hSeq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have hidx_ne : (ws.map Wire.val).idxOf x ≠ (ws.map Wire.val).idxOf y := by
            intro heq
            have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'(List.idxOf_lt_length_of_mem hx_mem) = x :=
              List.getElem_idxOf (List.idxOf_lt_length_of_mem hx_mem)
            have h2 : (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'(List.idxOf_lt_length_of_mem hy_mem) = y :=
              List.getElem_idxOf (List.idxOf_lt_length_of_mem hy_mem)
            have h12 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'(List.idxOf_lt_length_of_mem hx_mem) =
                (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'(List.idxOf_lt_length_of_mem hy_mem) := by
              congr 1
            exact hxy (h1.symm.trans (h12.trans h2))
          have hstep : ∃ (idxA idxB d : Nat), idxA < idxB ∧ idxB < ws.length ∧ d < 4 ∧
              let wa := ws.getD idxA ⟨0,0,0,0⟩
              let wb := ws.getD idxB ⟨0,0,0,0⟩
              wa.val ≠ wb.val ∧
              (ws.map Wire.val).toFinset = insert wa.val (insert wb.val U) ∧
              binOp mask d wa.val wb.val ∉ ws.map Wire.val ∧
              Proper mask (binOp mask d wa.val wb.val) ∧
              Live mask goal k' (insert (binOp mask d wa.val wb.val) U) := by
            have hix := List.idxOf_lt_length_of_mem hx_mem
            have hiy := List.idxOf_lt_length_of_mem hy_mem
            have hgx : (ws.getD ((ws.map Wire.val).idxOf x) ⟨0,0,0,0⟩).val = x := by
              have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'hix = x := List.getElem_idxOf hix
              have hix' : (ws.map Wire.val).idxOf x < ws.length := by simpa using hix
              simp only [List.getD_eq_getElem?_getD, hix', getElem?_pos, Option.getD_some]
              rw [← List.getElem_map (f := Wire.val)]; exact h1
            have hgy : (ws.getD ((ws.map Wire.val).idxOf y) ⟨0,0,0,0⟩).val = y := by
              have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'hiy = y := List.getElem_idxOf hiy
              have hiy' : (ws.map Wire.val).idxOf y < ws.length := by simpa using hiy
              simp only [List.getD_eq_getElem?_getD, hiy', getElem?_pos, Option.getD_some]
              rw [← List.getElem_map (f := Wire.val)]; exact h1
            have hfresh' : binOp mask d0 x y ∉ ws.map Wire.val := fun hm =>
              hfresh0 (hSeq ▸ List.mem_toFinset.mpr hm)
            have hpropZ := live_proper tail0 _ (Finset.mem_insert_self _ _)
            rcases lt_or_gt_of_ne hidx_ne with hlt | hgt
            · refine ⟨(ws.map Wire.val).idxOf x, (ws.map Wire.val).idxOf y, d0, hlt, by simpa using hiy, hd0, ?_⟩
              simp only [hgx, hgy]
              exact ⟨hxy, hSeq, hfresh', hpropZ, tail0⟩
            · refine ⟨(ws.map Wire.val).idxOf y, (ws.map Wire.val).idxOf x, flipOp d0, hgt, by simpa using hix, flipOp_lt hd0, ?_⟩
              simp only [hgx, hgy, ← binOp_flip hd0]
              exact ⟨hxy.symm, by rw [hSeq, Finset.insert_comm], hfresh', hpropZ, tail0⟩
          obtain ⟨idxA, idxB, d, hab, hb, hd, hne, hSeq', hfresh, hpropZ, tail⟩ := hstep
          have ha : idxA < ws.length := by omega
          let wa := ws.getD idxA ⟨0,0,0,0⟩
          let wb := ws.getD idxB ⟨0,0,0,0⟩
          let wz := makeWireBin mask d wa wb
          let ka := decide (wa.val ∈ U)
          let kb := decide (wb.val ∈ U)
          let child := childWires ws wa wb wz ka kb
          have hchildSet : (child.map Wire.val).toFinset = insert (binOp mask d wa.val wb.val) U := by
            rw [childWires_map, makeWireBin_val]
            simp only [List.toFinset_cons, kept_fin]
            have he1 : ((ws.map Wire.val).erase wa.val).toFinset = (ws.map Wire.val).toFinset.erase wa.val := by
              ext u; simp [hNd.mem_erase_iff]
            have he2 : (((ws.map Wire.val).erase wa.val).erase wb.val).toFinset =
                ((ws.map Wire.val).toFinset.erase wa.val).erase wb.val := by
              ext u
              rw [List.mem_toFinset, (hNd.erase _).mem_erase_iff, Finset.mem_erase, ← List.mem_toFinset, he1]
            rw [he2, hSeq']
            exact congrArg (insert (binOp mask d wa.val wb.val)) (restoreSet U wa.val wb.val hne)
          have hwa_m : wa ∈ ws := by
            simp only [wa, List.getD_eq_getElem?_getD, ha, getElem?_pos, Option.getD_some]
            exact List.getElem_mem ha
          have hwb_m : wb ∈ ws := by
            simp only [wb, List.getD_eq_getElem?_getD, hb, getElem?_pos, Option.getD_some]
            exact List.getElem_mem hb
          have hndC : (child.map Wire.val).Nodup := by
              rw [childWires_map, makeWireBin_val]
              let rest := ((ws.map Wire.val).erase wa.val).erase wb.val
              have hrnd : rest.Nodup := (hNd.erase _).erase _
              have har : wa.val ∉ rest := fun hm => hNd.not_mem_erase (List.mem_of_mem_erase hm)
              have hbr : wb.val ∉ rest := (hNd.erase _).not_mem_erase
              have hamid : wa.val ∉ kept kb wb.val rest := by
                cases kb
                · simp only [kept, Bool.false_eq_true, ite_false]; exact har
                · simp only [kept, ite_true, List.mem_cons, not_or]; exact ⟨hne, har⟩
              refine List.nodup_cons.mpr ⟨?_, kept_nd ka wa.val _ (kept_nd kb wb.val _ hrnd hbr) hamid⟩
              intro hm
              rcases mem_kept hm with hza | hm'
              · exact hfresh (by rw [hza]; exact List.mem_map_of_mem hwa_m)
              rcases mem_kept hm' with hzb | hm''
              · exact hfresh (by rw [hzb]; exact List.mem_map_of_mem hwb_m)
              · exact hfresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm''))
          have hchildLen : child.length ≤ childFuel + 1 := by
            have hsz' := live_size tail
            rw [← hchildSet] at hsz'
            rw [List.toFinset_card_of_nodup hndC, List.length_map] at hsz'
            omega
          have hclen_eq : child.length = ws.length - 1 + (if ka then 1 else 0) + (if kb then 1 else 0) := by
            have hwa_mv : wa.val ∈ ws.map Wire.val := List.mem_map_of_mem hwa_m
            have hwb_mv : wb.val ∈ (ws.map Wire.val).erase wa.val :=
              (List.mem_erase_of_ne hne.symm).mpr (List.mem_map_of_mem hwb_m)
            have hl : (child.map Wire.val).length = child.length := List.length_map _
            rw [← hl, childWires_map]
            have h1 := List.length_erase_of_mem hwa_mv
            have h2 := List.length_erase_of_mem hwb_mv
            have hws2 : 2 ≤ ws.length := by omega
            cases ka <;> cases kb <;> simp only [kept, List.length_cons, List.length_map, ite_true, ite_false, Bool.false_eq_true, h1, h2] at h1 h2 ⊢ <;> omega
          have hchildFaith : ∀ w ∈ child, Faithful pairs w := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact makeWireBin_faithful hpairs (hF wa hwa_m) (hF wb hwb_m) (hM wa hwa_m) (hM wb hwb_m) d hd
            rcases mem_kept hw' with rfl | hw''
            · exact hF wa hwa_m
            rcases mem_kept hw'' with rfl | hw'''
            · exact hF wb hwb_m
            · have hsub1 : ∀ x (l : List Wire), ∀ u ∈ eraseWire x l, u ∈ l := by
                intro x l; induction l with
                | nil => intro u hu; cases hu
                | cons y ys ihy =>
                  intro u hu; simp only [eraseWire] at hu
                  cases hbeq : Nat.beq y.val x
                  · rw [hbeq] at hu
                    rcases List.mem_cons.mp hu with rfl | hu'
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ (ihy u hu')
                  · rw [hbeq] at hu
                    exact List.mem_cons_of_mem _ hu
              exact hF w (hsub1 _ _ _ (hsub1 _ _ _ hw'''))
          have hsep := sep_required hpairs hchildFaith (hchildSet.symm ▸ tail)
          have hfoldEq := foldr_or_erase_two (z := wz) ws idxA idxB ha hb hab ka kb hNd
          have hop := checkLoopA_at (withSuffix ws).1 0 0 hck idxA idxB hab (by rw [withSuffix_len]; exact hb) d hd
          have hwsA := withSuffix_spec ws idxA ha
          have hwsB := withSuffix_spec ws idxB hb
          have htake_eq : ((withSuffix ws).1.take idxA).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
              (ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
            have : ∀ (l : List Wire) (m : Nat), ((withSuffix l).1.take m).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
                (l.take m).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
              intro l; induction l with
              | nil => intro m; simp [withSuffix]
              | cons u us ihu =>
                intro m; cases m with
                | zero => simp [withSuffix, forceNat_eq]
                | succ m' => simp only [withSuffix, forceNat_eq, List.take_succ_cons, List.foldr_cons, ihu m']
            exact this ws idxA
          have hmid_eq : (((withSuffix ws).1.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
              ((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
            have hmap : ∀ l : List Wire, (withSuffix l).1.map Prod.fst = l := by
              intro l
              induction l with
              | nil => rfl
              | cons u us ihu =>
                simp only [withSuffix, forceNat_eq, List.map_cons]
                exact congrArg (u :: ·) ihu
            have h1 : ∀ (l : List (Wire × Nat)), l.foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
                (l.map Prod.fst).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
              intro l; induction l with
              | nil => rfl
              | cons x xs ihx =>
                change Nat.lor x.1.sep (xs.foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
                  Nat.lor x.1.sep ((xs.map Prod.fst).foldr (fun w acc => Nat.lor w.sep acc) 0)
                rw [ihx]
            rw [h1, List.map_take, List.map_drop, hmap ws]
          have h0lor : ∀ x, Nat.lor 0 x = x := fun x => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or]
          simp only [Nat.zero_add, hwsA.1, hwsB.1, hwsB.2, htake_eq, hmid_eq, h0lor] at hop
          have hcan1 : (ka = true ∨ kb = true) → Nat.ble ws.length (Nat.add childFuel 1) = true := by
            intro hor; rw [Nat.ble_eq]; simp only [nat_add_eq]
            rcases hor with hka | hkb
            · simp only [hka, ite_true] at hclen_eq
              cases hkb' : kb <;> simp only [hkb', ite_true, ite_false, Bool.false_eq_true] at hclen_eq <;> omega
            · simp only [hkb, ite_true] at hclen_eq
              cases hka' : ka <;> simp only [hka', ite_true, ite_false, Bool.false_eq_true] at hclen_eq <;> omega
          have hcan2 : (ka = true ∧ kb = true) → Nat.ble (Nat.add ws.length 1) (Nat.add childFuel 1) = true := by
            rintro ⟨hka, hkb⟩; rw [Nat.ble_eq]; simp only [nat_add_eq]
            simp only [hka, hkb, ite_true] at hclen_eq; omega
          have hsep_ok : Nat.lor (Nat.lor (Nat.lor (Nat.lor ((ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0)
                (((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0))
              ((ws.drop (idxB + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0))
              (Nat.lor (if ka then wa.sep else 0) (if kb then wb.sep else 0))) wz.sep =
              Nat.sub (Nat.shiftLeft 1 pairs.length) 1 := by
            rw [← hfoldEq]; exact hsep
          have hlor_comm : ∀ x y, Nat.lor x y = Nat.lor y x := fun x y => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or, Bool.or_comm]
          have hlor_assoc : ∀ x y z, Nat.lor (Nat.lor x y) z = Nat.lor x (Nat.lor y z) := fun x y z => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
          have hlor_zero : ∀ x, Nat.lor x 0 = x := fun x => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or]
          have hchildM : ∀ v ∈ child.map Wire.val, Masked mask v := by
            intro v hv
            rw [childWires_map, makeWireBin_val] at hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact masked_binOp (hM wa hwa_m) (hM wb hwb_m)
            · rcases mem_kept hv' with rfl | hv''
              · exact hM wa hwa_m
              · rcases mem_kept hv'' with rfl | hv'''
                · exact hM wb hwb_m
                · have hmem := List.mem_of_mem_erase (List.mem_of_mem_erase hv''')
                  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmem
                  exact hM w hw
          have hmkVz := mkVzVal_eq (hM wa hwa_m) (hM wb hwb_m) hd
          have hprepInv := prepPools_inv (childFuel := childFuel) (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1)
          have hres : (childFuel = 0 ∧ binOp mask d wa.val wb.val ≠ goal) ∨
              (0 < childFuel ∧
                ((∃ q ∈ prepPools childFuel (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1),
                    scalarPoolCut q.1 childFuel idxA idxB ka kb (binOp mask d wa.val wb.val) = true) ∨
                checkLink mask sym count rootFuel (rootWs.map Wire.val) dag fdepth
                  (btreeGet (0, [], []) fdepth dag i).2.2 i childFuel (ws.map Wire.val) idxB
                  (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4) ka kb wa.val wb.val (binOp mask d wa.val wb.val) = true)) := by
            have hsepZ := (makeWireBin_sep mask d wa wb).symm
            rw [hsepZ, hmkVz] at hop
            apply checkOpFast_at (fun q hq => ⟨(hprepInv q hq).2.1, (hprepInv q hq).2.2⟩) hop hpropZ.2.1 hpropZ.2.2 hfresh ka kb hcan1 hcan2
            by_cases hka : ka = true <;> by_cases hkb : kb = true
            · have hc1 := hcan1 (Or.inl hka)
              have hc2 := hcan2 ⟨hka, hkb⟩
              simp only [hka, hkb, hc1, hc2, ite_true] at hsep_ok ⊢
              rw [← hlor_assoc] at hsep_ok
              exact hsep_ok
            · have hkb' : kb = false := Bool.eq_false_iff.mpr hkb
              have hc1 := hcan1 (Or.inl hka)
              simp only [hka, hkb', hc1, ite_true, ite_false, Bool.false_eq_true, hlor_zero] at hsep_ok ⊢
              exact hsep_ok
            · have hka' : ka = false := Bool.eq_false_iff.mpr hka
              have hc1 := hcan1 (Or.inr hkb)
              simp only [hka', hkb, hc1, ite_true, ite_false, Bool.false_eq_true, h0lor] at hsep_ok ⊢
              exact hsep_ok
            · have hka' : ka = false := Bool.eq_false_iff.mpr hka
              have hkb' : kb = false := Bool.eq_false_iff.mpr hkb
              simp only [hka', hkb', ite_false, Bool.false_eq_true, hlor_zero] at hsep_ok ⊢
              exact hsep_ok
          rcases hres with ⟨hcf0, hzg⟩ | ⟨_, (⟨q, hq_mem, hmp_cut⟩ | hlink)⟩
          · subst hcf0
            have hk0 : k' = 0 := by omega
            subst hk0
            obtain ⟨heq, _⟩ := tail
            have hmem : goal ∈ insert (binOp mask d wa.val wb.val) U := by rw [heq]; simp
            rcases Finset.mem_insert.mp hmem with h1 | hgu
            · exact hzg h1.symm
            · have hgu' : goal ∈ (ws.map Wire.val).toFinset := by
                rw [hSeq']; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hgu)
              exact hnoGoal (List.mem_toFinset.mp hgu')
          · have hvp := materializeList_sound (ws.map Wire.val) hist _ (hcuts i hi) q.1 (hprepInv q hq_mem).1
            have hwa_get : (ws.map Wire.val).getD idxA 0 = wa.val := by
              simp [wa, List.getD_eq_getElem?_getD, ha]
            have hwb_get : (ws.map Wire.val).getD idxB 0 = wb.val := by
              simp [wb, List.getD_eq_getElem?_getD, hb]
            have hMvals : ∀ v ∈ ws.map Wire.val, Masked mask v := by
              intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact hM w hw
            rw [← hwa_get, ← hwb_get] at hfresh hmp_cut
            have himp := scalarPoolCut_sound hvp hNd (by simpa using ha) (by simpa using hb) hab hd hMvals hfresh hmp_cut
            dsimp only at himp
            have heq_child : (binOp mask d ((ws.map Wire.val).getD idxA 0) ((ws.map Wire.val).getD idxB 0) ::
                kept ka ((ws.map Wire.val).getD idxA 0) (kept kb ((ws.map Wire.val).getD idxB 0)
                  (((ws.map Wire.val).erase ((ws.map Wire.val).getD idxA 0)).erase ((ws.map Wire.val).getD idxB 0)))).toFinset =
                insert (binOp mask d wa.val wb.val) U := by
              rw [hwa_get, hwb_get]
              rw [← makeWireBin_val (mask := mask) (d := d) (a := wa) (b := wb)]
              rw [← childWires_map ws wa wb wz ka kb]
              rw [makeWireBin_val]
              exact hchildSet
            rw [heq_child] at himp
            exact himp k' (by omega) tail
          · unfold checkLink at hlink
            cases hnl : (btreeGet (0, [], []) fdepth dag i).2.2 with
            | nil => rw [hnl] at hlink; cases hlink
            | cons e es =>
              rw [hnl] at hlink
              dsimp only at hlink
              let keepN := match ka with | true => (match kb with | true => 3 | false => 2) | false => (match kb with | true => 1 | false => 0)
              let tokN := Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4) keepN
              cases hfl : findLink tokN (e :: es) with
              | none => simp only [keepN, tokN] at hfl; rw [hfl] at hlink; cases hlink
              | some p =>
                obtain ⟨tid, isSym⟩ := p
                simp only [keepN, tokN] at hfl
                rw [hfl] at hlink
                dsimp only at hlink
                cases htid : Nat.blt tid count with
                | false => rw [htid] at hlink; cases hlink
                | true =>
                  rw [htid] at hlink
                  have htid_lt : tid < count := Nat.blt_eq.mp htid
                  cases htree : (Nat.blt idxB 16 && Nat.blt i tid &&
                      Nat.beq (btreeGet (0, [], []) fdepth dag tid).1 (Nat.add (Nat.mul i 4096) tokN)) with
                  | true =>
                    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at htree
                    obtain ⟨⟨hb16, hilt⟩, hpt⟩ := htree
                    have hkeep_lt : keepN < 4 := by unfold keepN; cases ka <;> cases kb <;> decide
                    have htok_lt : tokN < 4096 := by
                      simp only [tokN, nat_add_eq, nat_mul_eq]; omega
                    cases tid with
                    | zero => omega
                    | succ tid' =>
                      have hpar_eq : Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add tid' 1)).1 4096 = i := by
                        rw [show Nat.add tid' 1 = tid' + 1 from rfl, hpt]
                        simp only [nat_div_eq, nat_add_eq, nat_mul_eq]; omega
                      have htok_eq : Nat.mod (btreeGet (0, [], []) fdepth dag (Nat.add tid' 1)).1 4096 = tokN := by
                        rw [show Nat.add tid' 1 = tid' + 1 from rfl, hpt]
                        simp only [nat_mod_eq, nat_add_eq, nat_mul_eq]; omega
                      obtain ⟨hle_rf, hmono⟩ := traceState_gas_mono mask rootFuel rootWs dag fdepth _ _ _ htr
                      dsimp only at hle_rf hmono
                      have htr_i_rf : traceState mask rootFuel rootWs dag fdepth rootFuel i = some (childFuel + 1, ws, hist) :=
                        hmono rootFuel (by omega)
                      have hka_eq : Nat.beq (Nat.div (Nat.mod tokN 4) 2) 1 = ka := by
                        have : Nat.mod tokN 4 = keepN := by simp only [tokN, nat_mod_eq, nat_add_eq, nat_mul_eq]; omega
                        rw [this]; unfold keepN; cases ka <;> cases kb <;> rfl
                      have hkb_eq : Nat.beq (Nat.mod (Nat.mod tokN 4) 2) 1 = kb := by
                        have : Nat.mod tokN 4 = keepN := by simp only [tokN, nat_mod_eq, nat_add_eq, nat_mul_eq]; omega
                        rw [this]; unfold keepN; cases ka <;> cases kb <;> rfl
                      have hd_eq : Nat.mod (Nat.div tokN 4) 4 = d := by
                        simp only [tokN, nat_mod_eq, nat_div_eq, nat_add_eq, nat_mul_eq]; omega
                      have hb_eq : Nat.mod (Nat.div tokN 16) 16 = idxB := by
                        simp only [tokN, nat_mod_eq, nat_div_eq, nat_add_eq, nat_mul_eq]; omega
                      have ha_eq : Nat.div tokN 256 = idxA := by
                        simp only [tokN, nat_div_eq, nat_add_eq, nat_mul_eq]; omega
                      have htr_tid : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) (tid' + 1) =
                          some (childFuel, child, (wz.val, wa.val, wb.val) :: hist) := by
                        unfold traceState
                        dsimp only
                        rw [hpar_eq, htok_eq, show Nat.blt i (Nat.add tid' 1) = true from Nat.blt_eq.mpr hilt, htr_i_rf]
                        unfold applyTok
                        dsimp only
                        rw [ha_eq, hb_eq, hd_eq, hka_eq, hkb_eq]
                        have hchk_idx : (Nat.blt idxA idxB && Nat.blt idxB ws.length) = true := by
                          simp [Nat.blt_eq, hab, hb]
                        rw [hchk_idx]
                        have hnot_stale : (Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws.map Wire.val)) = false := by
                          have hvz : wz.val = binOp mask d wa.val wb.val := makeWireBin_val _ _ _ _
                          rw [hvz]
                          have b1 : Nat.beq (binOp mask d wa.val wb.val) 0 = false := by
                            cases h : Nat.beq (binOp mask d wa.val wb.val) 0
                            · rfl
                            · exact absurd (Nat.beq_eq.mp h) hpropZ.2.1
                          have b2 : Nat.beq (binOp mask d wa.val wb.val) mask = false := by
                            cases h : Nat.beq (binOp mask d wa.val wb.val) mask
                            · rfl
                            · exact absurd (Nat.beq_eq.mp h) hpropZ.2.2
                          have b3 : containsNat (binOp mask d wa.val wb.val) (ws.map Wire.val) = false := by
                            cases h : containsNat (binOp mask d wa.val wb.val) (ws.map Wire.val)
                            · rfl
                            · exact absurd ((containsNat_iff _ _).mp h) hfresh
                          simp [b1, b2, b3]
                        change (match Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws.map Wire.val) with
                          | true => none | false => some (childFuel, child, (wz.val, wa.val, wb.val) :: hist)) = _
                        rw [hnot_stale]
                      have himp := ih childFuel (by omega) (tid' + 1) _ htid_lt htr_tid rfl
                      rw [hchildSet] at himp
                      exact himp k' (by omega) tail
                  | false =>
                    rw [htree] at hlink
                    dsimp only at hlink
                    have hck_tid := hcheck tid (Nat.zero_le tid) (by omega)
                    unfold checkNode at hck_tid
                    cases htr_t : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) tid with
                    | none => simp [htr_t] at hck_tid
                    | some stT =>
                      have htv := traceVals_eq mask rootFuel rootWs dag fdepth _ _ _ htr_t
                      rw [htv] at hlink
                      dsimp only at hlink
                      cases htf : Nat.beq stT.1 childFuel with
                      | false => rw [htf] at hlink; cases hlink
                      | true =>
                        rw [htf] at hlink
                        dsimp only at hlink
                        have htf_eq : stT.1 = childFuel := Nat.beq_eq.mp htf
                        have himp := ih childFuel (by omega) tid stT htid_lt htr_t htf_eq
                        obtain ⟨_, _, hNdT⟩ := traceState_inv hpairs hrootM hrootF hrootNd _ _ _ htr_t
                        have hcv : (binOp mask d wa.val wb.val :: kept ka wa.val (kept kb wb.val (eraseWord wb.val (eraseWord wa.val (ws.map Wire.val))))) = child.map Wire.val := by
                          rw [childWires_map, makeWireBin_val, eraseWord_eq, eraseWord_eq]
                        cases isSym
                        · dsimp only at hlink
                          rw [hcv] at hlink
                          have hsame := sameSetFast_sound hndC hNdT hlink
                          rw [hchildSet] at hsame
                          exact himp k' (by omega) (hsame ▸ tail)
                        · dsimp only at hlink
                          rw [hcv] at hlink
                          have hndSym : ((child.map Wire.val).map sym).Nodup :=
                            hndC.map_on (fun u hu v hv eq => sym_inj hm hsym u v (hchildM u hu) (hchildM v hv) eq)
                          have hsame := sameSetSym_sound hndSym hNdT hlink
                          have hmapF : ∀ (l : List Word), (l.map sym).toFinset = l.toFinset.image sym := by
                            intro l; ext x; simp
                          rw [hmapF, hchildSet] at hsame
                          exact himp k' (by omega) (hsame ▸ live_sym hm hsym tail)
theorem lowerPoolDAG {mask goal : Word} {pairs : List (Row × Row)} {sym : Word → Word}
    {count rootFuel fdepth cdepth : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {cutTree : BTree CutSpec}
    (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    (hp : Proper mask goal) (nT : plainWord mask goal = true)
    (nR : (rootWs.map Wire.val).all (plainWord mask) = true)
    (hpairs : pairs.all (pairValid mask goal) = true)
    (hsym : SymOK mask goal sym)
    (hrootF : rootWs.all (wireMatchesPairs pairs) = true)
    (hrootNd : (rootWs.map Wire.val).Nodup)
    (hcount : 0 < count)
    (hess : ∀ a ∈ rootWs.map Wire.val, Essential mask goal (rootWs.map Wire.val) a)
    (hcuts : ∀ i < count, ∀ ci ∈ (btreeGet (0, [], []) fdepth dag i).2.1,
      ValidCut mask (rootWs.map Wire.val) goal (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci))
    (hcheck : AllChecked (checkNode mask goal (Nat.sub (Nat.shiftLeft 1 pairs.length) 1) sym
      count rootFuel rootWs dag fdepth cutTree cdepth) 0 count) :
    LowerM mask (rootWs.map Wire.val) goal (rootFuel + 1) := by
  have hrootM : ∀ w ∈ rootWs, Masked mask w.val := by
    intro w hw
    have hp' := List.all_eq_true.mp nR w.val (List.mem_map_of_mem hw)
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at hp'
    exact hp'.1
  have hnoRun := dagAllNodes hm (fun p hp' => List.all_eq_true.mp hpairs p hp') hsym hrootM
    (fun w hw => wireMatchesPairs_sound (List.all_eq_true.mp hrootF w hw)) hrootNd hcuts hcheck
    rootFuel 0 (rootFuel, rootWs, []) hcount rfl rfl
  exact lower_impossible hm hm0 hp nT nR hess hnoRun
def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false
def gv (w : List Word) (g : Gate) : Word :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (primeW false) fullMask
  | .or => xs.foldr (primeW true) 0
  | .not => Nat.xor fullMask (xs.headD 0)
  | _ => 0
def execute (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun l g => l ++ [gv l g]) w
theorem gv_masked {w : List Word} (hw : ∀ a ∈ w, Masked fullMask a) (g : Gate) :
    Masked fullMask (gv w g) := by
  have hget : ∀ i, Masked fullMask (w.getD i 0) := by
    intro i; simp only [List.getD_eq_getElem?_getD]
    cases h : w[i]? with
    | none => exact masked_zero fullMask
    | some a => exact hw a (List.mem_of_getElem? h)
  unfold gv
  cases g.op <;> dsimp only
  · induction g.inputs with
    | nil => exact masked_self fullMask
    | cons i is ih => exact masked_primeW false (hget i) ih
  · induction g.inputs with
    | nil => exact masked_zero fullMask
    | cons i is ih => exact masked_primeW true (hget i) ih
  · cases g.inputs with
    | nil => exact masked_xor (masked_zero fullMask)
    | cons i _ => exact masked_xor (hget i)
  · exact masked_zero fullMask
  · exact masked_zero fullMask
theorem execute_masked (gs : List Gate) {w : List Word} (hw : ∀ a ∈ w, Masked fullMask a) :
    ∀ a ∈ execute gs w, Masked fullMask a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hw a h1
    · rw [List.mem_singleton.mp h2]; exact gv_masked hw g
theorem run_bit (r : Row) (g : Gate) (w : List Word)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    bit r (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit r)).getD j false) := by
  have hbread : ∀ j, (w.map (bit r)).getD j false = bit r (w.getD j 0) := by
    intro j; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[j]? <;> simp [bit]
  have hfm : fullMask.testBit r.val = true := by
    have : fullMask = 2 ^ 256 - 1 := by decide
    rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true r.isLt
  obtain ⟨o, l⟩ := g
  simp only [hbread]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => simp [gv, bit, hfm, GateOp.eval]
    | cons a l ih =>
      simp only [gv, List.map_cons, List.foldr_cons, primeW, Bool.false_eq_true, ite_false, bit, nat_land_eq, Nat.testBit_and,
        GateOp.eval, List.all_cons, id_eq] at ih ⊢
      rw [ih]
  · induction l with
    | nil => simp [gv, bit, GateOp.eval]
    | cons a l ih =>
      simp only [gv, List.map_cons, List.foldr_cons, primeW, ite_true, bit, nat_lor_eq, Nat.testBit_or,
        GateOp.eval, List.any_cons, id_eq] at ih ⊢
      rw [ih]
  · cases l with
    | nil => simp [gv, bit, nat_xor_eq, Nat.testBit_xor, hfm, GateOp.eval]
    | cons a l => simp [gv, bit, nat_xor_eq, Nat.testBit_xor, hfm, GateOp.eval]
theorem execute_bits (gs : List Gate) (r : Row) (w : List Word)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (execute gs w).map (bit r) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit r g w (hg g (List.mem_cons_self))]
theorem gate_rep (w : List Word) (hw : ∀ a ∈ w, Masked fullMask a) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    Repr fullMask (w.map (nrm fullMask)) (gv w g) ∨
      (isNot g = false ∧ witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g))) := by
  have hm0 : fullMask.testBit 0 = true := by decide
  have hget : ∀ i, Masked fullMask (w.getD i 0) ∧ Repr fullMask (w.map (nrm fullMask)) (w.getD i 0) := by
    intro i; simp only [List.getD_eq_getElem?_getD]
    cases h : w[i]? with
    | none => exact ⟨masked_zero fullMask, repr_const (masked_zero fullMask) (Or.inl rfl)⟩
    | some a => exact ⟨hw a (List.mem_of_getElem? h), Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))⟩
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := hg
  have prim (d : Bool) : Repr fullMask (w.map (nrm fullMask)) ((l.map (fun i => w.getD i 0)).foldr (primeW d) (if d then 0 else fullMask)) ∨
      witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask ((l.map (fun i => w.getD i 0)).foldr (primeW d) (if d then 0 else fullMask))) := by
    have unit (v : Word) (mv : Masked fullMask v) : primeW d v (if d then 0 else fullMask) = v := by
      cases d
      · exact mv
      · apply Nat.eq_of_testBit_eq; intro k; simp [primeW, nat_lor_eq, Nat.testBit_or]
    cases l with
    | nil =>
      left; cases d
      · exact repr_const (masked_self fullMask) (Or.inr rfl)
      · exact repr_const (masked_zero fullMask) (Or.inl rfl)
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit _ (hget i).1]
        exact Or.inl (hget i).2
      | cons j l =>
        cases l with
        | cons _ _ => simp at hl
        | nil =>
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit _ (hget j).1]
          exact primeW_rep hm0 d (hget i).1 (hget j).1 (hget i).2 (hget j).2
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl, h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl, h⟩)
  · left
    cases l with
    | nil =>
      have : gv w ⟨.not, []⟩ = fullMask := by
        apply Nat.eq_of_testBit_eq; intro k; simp [gv, Nat.testBit_xor]
      rw [this]; exact repr_const (masked_self fullMask) (Or.inr rfl)
    | cons i _ =>
      change Repr fullMask (w.map (nrm fullMask)) (Nat.xor fullMask (w.getD i 0))
      unfold Repr
      rw [nrm_xor hm0 (hget i).1]
      exact (hget i).2
theorem extract_live (gs : List Gate) (w : List Word) (hw : ∀ a ∈ w, Masked fullMask a)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    {target : Word} (hp : Proper fullMask target) (hout : target ∈ (execute gs w).map (nrm fullMask)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live fullMask target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm fullMask) := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Masked fullMask a := by
      intro a ha
      rcases List.mem_append.mp ha with h1 | h2
      · exact hw a h1
      · rw [List.mem_singleton.mp h2]; exact gv_masked hw g
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw'
      (fun a ha => legal a (List.mem_cons_of_mem _ ha)) hout
    have rep := gate_rep w hw g (legal g (List.mem_cons_self))
    rw [List.map_append] at hs
    have rep' : represented fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g)) ∨
        ((if isNot g then 0 else 1) = 1 ∧ witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1], h.2⟩)
    obtain ⟨l, T, hl, hu, hT⟩ := pull_gate ht rep' hs
    refine ⟨l, T, ?_, hu, hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega
theorem physical_lower {vars8 : List Word} {goal8 : Word} {L : Nat}
    {targetFn : (Fin 8 → Bool) → Bool}
    (hp : Proper fullMask goal8) (nT : goal8.testBit 0 = false)
    (nR : vars8.all (plainWord fullMask) = true)
    (hlow : LowerM fullMask vars8 goal8 L)
    (hsample : ∀ r : Row, vars8.map (bit r) = List.ofFn (fun i : Fin 8 => r.val.testBit i.val))
    (hgoal : ∀ r : Row, bit r goal8 = targetFn (fun i : Fin 8 => r.val.testBit i.val))
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFn x) :
    L ≤ gates.countP (fun g => !isNot g) := by
  have hw : ∀ a ∈ vars8, Masked fullMask a := by
    intro a ha
    have h := List.all_eq_true.mp nR a ha
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at h; exact h.1
  have heq : (execute gates vars8).getD o 0 = goal8 := by
    refine masked_ext (masked_self fullMask) ?_ hp.1 ?_
    · simp only [List.getD_eq_getElem?_getD]
      cases h : (execute gates vars8)[o]? with
      | none => exact masked_zero fullMask
      | some a => exact execute_masked gates hw a (List.mem_of_getElem? h)
    · intro r
      have hbread : bit r ((execute gates vars8).getD o 0) = ((execute gates vars8).map (bit r)).getD o false := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execute gates vars8)[o]? <;> simp [bit]
      rw [hbread, execute_bits gates r vars8 (fun g hg => (legal g hg).1), hsample r]
      exact (computes (fun i : Fin 8 => r.val.testBit i.val)).trans (hgoal r).symm
  have hmem : goal8 ∈ (execute gates vars8).map (nrm fullMask) := by
    rw [← nrm_id nT, ← heq]
    simp only [List.getD_eq_getElem?_getD]
    cases h : (execute gates vars8)[o]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, h] at heq
      exact absurd heq.symm hp.2.1
    | some a =>
      exact List.mem_map_of_mem (List.mem_of_getElem? h)
  obtain ⟨k, S, hk, run, sub⟩ := extract_live gates vars8 hw legal hp hmem
  rw [nrm_map nR] at sub
  have hnd := Finset.nodup_toList S
  have hrun := list_run run S.toList hnd (by simp)
  have hsup : supply (vars8.map (obsM fullMask)) (S.toList.map (obsM fullMask)) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, hreach, hav, hq⟩ := contraction (observe_proper (masked_self fullMask) hp) hrun
    (vars8.map (obsM fullMask)) Reach.start hsup
  have hL := hlow q bank hreach hav
  omega
def pack8 (x : Fin 8 → Bool) : Fin 256 :=
  ⟨(if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) +
   (if x 4 then 16 else 0) + (if x 5 then 32 else 0) + (if x 6 then 64 else 0) + (if x 7 then 128 else 0),
   by cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> cases x 7 <;> decide⟩
theorem pack8_bit (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (i : Fin 8) :
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) +
     (if b4 then 16 else 0) + (if b5 then 32 else 0) + (if b6 then 64 else 0) + (if b7 then 128 else 0)).testBit i.val =
    match i.val with
    | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 i; decide +kernel
theorem forall_fin8_of_fin256 {P : (Fin 8 → Bool) → Prop}
    (h : ∀ r : Fin 256, P (fun i : Fin 8 => r.val.testBit i.val)) : ∀ x : Fin 8 → Bool, P x := by
  intro x
  have heq : (fun i : Fin 8 => (pack8 x).val.testBit i.val) = x := by
    funext i
    have hb := pack8_bit (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
    exact hb.trans (by fin_cases i <;> rfl)
  rw [← heq]; exact h (pack8 x)

abbrev N {α : Type} := @BTree.node α
abbrev L {α : Type} := @BTree.leaf α
abbrev E {α : Type} := @BTree.empty α
abbrev u (x : Nat) : BTree NodeRec := L (x,[],[])
abbrev z (x : Nat) : BTree NodeRec := L (x,[0],[])
abbrev v (x c : Nat) : BTree NodeRec := L (x,[c],[])
abbrev w (x : Nat) (cs : List Nat) : BTree NodeRec := L (x,cs,[])
abbrev y (x : Nat) (ls : List Nat) : BTree NodeRec := L (x,[],ls)
abbrev f (x : Nat) (ls : List Nat) : BTree NodeRec := L (x,[0],ls)
abbrev j (x c : Nat) (ls : List Nat) : BTree NodeRec := L (x,[c],ls)
abbrev k (x : Nat) (cs ls : List Nat) : BTree NodeRec := L (x,cs,ls)
abbrev mc (r : List Word) (d b : Nat) : BTree CutSpec := L (mkCut r d b)
abbrev ac := AllChecked
theorem tm {c : Nat → Bool} (s l r : Nat) (a : ac c s l) (b : ac c (s + l) r) : ac c s (l + r) := ac_merge s l r a b
def mkWs (raw : List Word) (pn : List (Nat × Nat)) : List Wire := List.zipWith (fun a p => ⟨a, p.1, p.2, Nat.xor p.1 p.2⟩) raw pn
def mkR (m : Word) (vs : List Word) : List Word := vs.map (fun v => Nat.land v m)
def v0 : Word := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def v1 : Word := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def v2 : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def v3 : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def v4 : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def v5 : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def v6 : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def v7 : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def gAll : Word := 0xfffffffffffffffefffffffffffefffefffffefefffffafafefefefceeeeaa00

def mr (p0 p1 p2 p3 p4 p5 p6 p7 ones : Nat) (r : Row) : Row :=
  ⟨Nat.mod (Nat.lor ones
    (Nat.lor (if r.val.testBit 0 then Nat.shiftLeft 1 p0 else 0)
    (Nat.lor (if r.val.testBit 1 then Nat.shiftLeft 1 p1 else 0)
    (Nat.lor (if r.val.testBit 2 then Nat.shiftLeft 1 p2 else 0)
    (Nat.lor (if r.val.testBit 3 then Nat.shiftLeft 1 p3 else 0)
    (Nat.lor (if r.val.testBit 4 then Nat.shiftLeft 1 p4 else 0)
    (Nat.lor (if r.val.testBit 5 then Nat.shiftLeft 1 p5 else 0)
    (Nat.lor (if r.val.testBit 6 then Nat.shiftLeft 1 p6 else 0)
             (if r.val.testBit 7 then Nat.shiftLeft 1 p7 else 0))))))))) 256, Nat.mod_lt _ (by decide)⟩

def mrP (code : Nat) : Row → Row :=
  mr (Nat.mod code 8) (Nat.mod (Nat.div code 8) 8) (Nat.mod (Nat.div code 64) 8) (Nat.mod (Nat.div code 512) 8)
     (Nat.mod (Nat.div code 4096) 8) (Nat.mod (Nat.div code 32768) 8) (Nat.mod (Nat.div code 262144) 8)
     (Nat.mod (Nat.div code 2097152) 8) (Nat.div code 16777216)

theorem cv (code : Nat) {mask : Word} {raw : List Word} {T dom subMask : Word} {roots : List Word} {subT : Word} {L : Nat}
    (hL : LowerM subMask roots subT L)
    (hc : (Nat.beq (Nat.land subMask fullMask) subMask && Nat.beq (Nat.land subT subMask) subT &&
           !Nat.beq subT 0 && !Nat.beq subT subMask && checkSlice (mrP code) mask raw T dom subMask roots subT) = true) :
    ValidCut mask raw T (mkCut raw dom L) := mkCut_valid hL hc

theorem liftLow (code : Nat) {mask : Word} {raw : List Word} {T dom subMask : Word} {roots : List Word} {subT : Word} {L need : Nat}
    (hL : LowerM subMask roots subT L) (ess : ∀ a ∈ raw, Essential mask T raw a)
    (hnd : raw.Nodup)
    (hc : (Nat.beq (Nat.land subMask fullMask) subMask && Nat.beq (Nat.land subT subMask) subT &&
           !Nat.beq subT 0 && !Nat.beq subT subMask && checkSlice (mrP code) mask raw T dom subMask roots subT &&
           Nat.beq (Nat.land mask fullMask) mask && mask.testBit 0 &&
           Nat.beq (Nat.land T mask) T && !Nat.beq T 0 && !Nat.beq T mask &&
           plainWord mask T && raw.all (plainWord mask) &&
           Nat.beq (L + raw.countP (isConst dom)) need) = true) :
    LowerM mask raw T need := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hc
  have h3' : subT ≠ 0 := fun e => by rw [e] at h3; cases h3
  have h4' : subT ≠ subMask := fun e => by rw [e] at h4; exact absurd (Nat.beq_eq.mpr rfl) (by rw [h4]; decide)
  have h9' : T ≠ 0 := fun e => by rw [e] at h9; cases h9
  have h10' : T ≠ mask := fun e => by rw [e] at h10; exact absurd (Nat.beq_eq.mpr rfl) (by rw [h10]; decide)
  rw [← h13]
  exact slice_lift h6 h7 ⟨h8, h9', h10'⟩ h11 h12 hnd ess (checkSlice_sound h1 ⟨h2, h3', h4'⟩ hL h5)

theorem dagLow {mask goal : Word} {raw : List Word} {pairs : List (Row × Row)} {sym : Word → Word}
    {count rootFuel fdepth cdepth ncuts : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {cutTree : BTree CutSpec}
    (hraw : rootWs.map Wire.val = raw) (hnd : (rootWs.map Wire.val).Nodup)
    (hsym : SymOK mask goal sym) (hess : ∀ a ∈ raw, Essential mask goal raw a)
    (hcv : ∀ ci < ncuts, ValidCut mask raw goal (btreeGet ⟨0,0,[]⟩ cdepth cutTree ci))
    (hck : AllChecked (checkNode mask goal (Nat.sub (Nat.shiftLeft 1 pairs.length) 1) sym count rootFuel rootWs dag fdepth cutTree cdepth) 0 count)
    (hb : (Nat.beq (Nat.land mask fullMask) mask && mask.testBit 0 &&
           Nat.beq (Nat.land goal mask) goal && !Nat.beq goal 0 && !Nat.beq goal mask &&
           plainWord mask goal && (rootWs.map Wire.val).all (plainWord mask) &&
           pairs.all (pairValid mask goal) && rootWs.all (wireMatchesPairs pairs) &&
           Nat.blt 0 count && btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci ncuts)) dag) = true) :
    LowerM mask raw goal (rootFuel + 1) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.blt_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hb
  have h4' : goal ≠ 0 := fun e => by rw [e] at h4; cases h4
  have h5' : goal ≠ mask := fun e => by rw [e] at h5; exact absurd (Nat.beq_eq.mpr rfl) (by rw [h5]; decide)
  rw [← hraw]
  refine lowerPoolDAG h1 h2 ⟨h3, h4', h5'⟩ h6 h7 h8 hsym h9 hnd h10 (by rw [hraw]; exact hess) (fun i _ ci hci => ?_) hck
  have hp := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x ncuts)) (defv := (0,[],[])) rfl h11 fdepth i
  rw [hraw]; exact hcv ci (Nat.blt_eq.mp (List.all_eq_true.mp hp ci hci))

def sw12 (w : Word) : Word := swapWord 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3 0x3030303030303030303030303030303030303030303030303030303030303030 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c 2 w
def sw12Row : Row → Row := mr 0 2 1 3 4 5 6 7 0
theorem sw12_spec : Function.Bijective sw12Row ∧ ∀ w, Masked fullMask (sw12 w) ∧ ∀ r : Row, bit r (sw12 w) = bit (sw12Row r) w :=
  swapWord_spec (by decide +kernel)

def sw46 (w : Word) : Word := swapWord 0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 0xffff0000ffff00000000000000000000ffff0000ffff0000 48 w
def sw46Row : Row → Row := mr 0 1 2 3 6 5 4 7 0
theorem sw46_spec : Function.Bijective sw46Row ∧ ∀ w, Masked fullMask (sw46 w) ∧ ∀ r : Row, bit r (sw46 w) = bit (sw46Row r) w :=
  swapWord_spec (by decide +kernel)

def symMain (w : Word) : Word := sw46 (sw12 w)
def symMainRow (r : Row) : Row := sw12Row (sw46Row r)
theorem symMain_spec : Function.Bijective symMainRow ∧ ∀ w, Masked fullMask (symMain w) ∧ ∀ r : Row, bit r (symMain w) = bit (symMainRow r) w :=
  sym_comp_spec (f1 := sw12Row) (f2 := sw46Row) (s1 := sw12) (s2 := sw46) sw12_spec sw46_spec

def sw07 (w : Word) : Word := swapWord 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555 0x5555555555555555555555555555555500000000000000000000000000000000 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 127 w
def sw07Row : Row → Row := mr 7 1 2 3 4 5 6 0 0
theorem sw07_spec : Function.Bijective sw07Row ∧ ∀ w, Masked fullMask (sw07 w) ∧ ∀ r : Row, bit r (sw07 w) = bit (sw07Row r) w :=
  swapWord_spec (by decide +kernel)

def sw14 (w : Word) : Word := swapWord 0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333 0x3333000033330000333300003333000033330000333300003333000033330000 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc 14 w
def sw14Row : Row → Row := mr 0 4 2 3 1 5 6 7 0
theorem sw14_spec : Function.Bijective sw14Row ∧ ∀ w, Masked fullMask (sw14 w) ∧ ∀ r : Row, bit r (sw14 w) = bit (sw14Row r) w :=
  swapWord_spec (by decide +kernel)

def sw56 (w : Word) : Word := swapWord 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff 0xffffffff000000000000000000000000ffffffff0000000000000000 0xffffffff000000000000000000000000ffffffff00000000 32 w
def sw56Row : Row → Row := mr 0 1 2 3 4 6 5 7 0
theorem sw56_spec : Function.Bijective sw56Row ∧ ∀ w, Masked fullMask (sw56 w) ∧ ∀ r : Row, bit r (sw56 w) = bit (sw56Row r) w :=
  swapWord_spec (by decide +kernel)

def sym251 (w : Word) : Word := sw56 (sw14 (sw07 w))
def sym251Row (r : Row) : Row := sw07Row (sw14Row (sw56Row r))
theorem sym251_spec : Function.Bijective sym251Row ∧ ∀ w, Masked fullMask (sym251 w) ∧ ∀ r : Row, bit r (sym251 w) = bit (sym251Row r) w :=
  sym_comp_spec (f1 := fun r => sw07Row (sw14Row r)) (f2 := sw56Row) (s1 := fun w => sw14 (sw07 w)) (s2 := sw56) (sym_comp_spec (f1 := sw07Row) (f2 := sw14Row) (s1 := sw07) (s2 := sw14) sw07_spec sw14_spec) sw56_spec

theorem symMainOK {m g : Word} (h1 : Nat.beq (Nat.land m fullMask) m = true) (h2 : (List.finRange 256).all (fun r => bit (symMainRow r) m == bit r m) = true) (h3 : Nat.beq (symMain g) g = true) : SymOK m g symMain := sym_of_row (Nat.beq_eq.mp h1) symMain_spec.1 symMain_spec.2 h2 h3
theorem sym251OK {m g : Word} (h1 : Nat.beq (Nat.land m fullMask) m = true) (h2 : (List.finRange 256).all (fun r => bit (sym251Row r) m == bit r m) = true) (h3 : Nat.beq (sym251 g) g = true) : SymOK m g sym251 := sym_of_row (Nat.beq_eq.mp h1) sym251_spec.1 sym251_spec.2 h2 h3

def m81Mask : Word := 0x300030000000000030003
def m81Goal : Word := Nat.land gAll m81Mask
def m81Raw : List Word := mkR m81Mask [v0,v4,v6]
theorem m81Ess : ∀ a ∈ m81Raw, Essential m81Mask m81Goal m81Raw a :=
  checkAllEss_sound (ps := [4113,273,321]) (by decide +kernel)
def m81Pairs : List (Row × Row) := mkPairs [4353,4368,16641,16704,20496,20544,4352,16640,20480,20737,20752,20800,4416,16656,20481,20736]
def m81Ws : List Wire := mkWs m81Raw [(0xbecf,0x4205),(0xdf73,0x2412),(0xefbc,0x1828)]
def m81Cuts : BTree CutSpec := E
theorem m81CutValid : ∀ ci < 0, ValidCut m81Mask m81Raw m81Goal (btreeGet ⟨0,0,[]⟩ 0 m81Cuts ci) := by
  intro ci hci
  omega
noncomputable def m81D : BTree NodeRec := (u 0)
noncomputable def x81 : Nat → Bool := checkNode m81Mask m81Goal (Nat.sub (Nat.shiftLeft 1 m81Pairs.length) 1) symMain 1 3 m81Ws m81D 0 m81Cuts 0
noncomputable def y81 : Nat → Nat → Bool := checkRange m81Mask m81Goal (Nat.sub (Nat.shiftLeft 1 m81Pairs.length) 1) symMain 1 3 m81Ws m81D 0 m81Cuts 0
theorem s81 (s n : Nat) (h : y81 s n = true) : ac x81 s n := cr_sound h
theorem q0 : ac x81 0 1 := s81 0 1 (by decide +kernel)
theorem m81All : ac x81 0 1 := q0
theorem m81Low : LowerM m81Mask m81Raw m81Goal 4 :=
  dagLow (pairs := m81Pairs) (sym := symMain) (ncuts := 0) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m81Ess m81CutValid m81All (by decide +kernel)

def m86Mask : Word := 0x5500550000000000550055
def m86Goal : Word := Nat.land gAll m86Mask
def m86Raw : List Word := mkR m86Mask [v1,v2,v4,v6]
theorem m86Ess : ∀ a ∈ m86Raw, Essential m86Mask m86Goal m86Raw a :=
  checkAllEss_sound (ps := [4114,16452,530,1092]) (by decide +kernel)
def m86Pairs : List (Row × Row) := mkPairs [4610,4624,17412,17472,20496,20544,5638,5652,17926,17986,21058,21524,4614,4628,4674,17414,17428,17474,20500,20546,4608,17408,20480,5634,5636,5648,17922,17924,17984,20994,21008,21056,21508,21520,21568,22022,22036,22082,4612,4672,17410,17424,20482,20484,5698,17940,20998,21012,21510,21570,5632,17920,20992,21504,22018,22020,22032,22080,20486,5696,17936,20996,21506,22016]
def m86Ws : List Wire := mkWs m86Raw [(0xbbdcf0f8ff9077c3,0x44435528248ad741),(0xdbef333f1fa38bcc,0x2481e8590905b9c4),(0xeff7dcffe3dc7cf3,0x1100a21242052892),(0xf7fbef3ffc6f8f3c,0xa0210a4900a4628)]
def m86Cuts : BTree CutSpec := E
theorem m86CutValid : ∀ ci < 0, ValidCut m86Mask m86Raw m86Goal (btreeGet ⟨0,0,[]⟩ 0 m86Cuts ci) := by
  intro ci hci
  omega
noncomputable def m86D : BTree NodeRec := (u 0)
noncomputable def x86 : Nat → Bool := checkNode m86Mask m86Goal (Nat.sub (Nat.shiftLeft 1 m86Pairs.length) 1) symMain 1 3 m86Ws m86D 0 m86Cuts 0
noncomputable def y86 : Nat → Nat → Bool := checkRange m86Mask m86Goal (Nat.sub (Nat.shiftLeft 1 m86Pairs.length) 1) symMain 1 3 m86Ws m86D 0 m86Cuts 0
theorem s86 (s n : Nat) (h : y86 s n = true) : ac x86 s n := cr_sound h
theorem q1 : ac x86 0 1 := s86 0 1 (by decide +kernel)
theorem m86All : ac x86 0 1 := q1
theorem m86Low : LowerM m86Mask m86Raw m86Goal 4 :=
  dagLow (pairs := m86Pairs) (sym := symMain) (ncuts := 0) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m86Ess m86CutValid m86All (by decide +kernel)

def m89Mask : Word := 0x30303030000000003030303
def m89Goal : Word := Nat.land gAll m89Mask
def m89Raw : List Word := mkR m89Mask [v0,v3,v4,v6]
theorem m89Ess : ∀ a ∈ m89Raw, Essential m89Mask m89Goal m89Raw a :=
  checkAllEss_sound (ps := [2057,265,273,321]) (by decide +kernel)
theorem m89Low : LowerM m89Mask m89Raw m89Goal 5 :=
  liftLow (dom := 0x300030000000000030003) 1589248 m81Low m89Ess (by decide +kernel) (by decide +kernel)

def m166Mask : Word := 0x550000005500000000000000000000005500000055
def m166Goal : Word := Nat.land gAll m166Mask
def m166Raw : List Word := mkR m166Mask [v1,v2,v5,v7]
theorem m166Ess : ∀ a ∈ m166Raw, Essential m166Mask m166Goal m166Raw a :=
  checkAllEss_sound (ps := [8226,8228,546,642]) (by decide +kernel)
theorem m166Low : LowerM m166Mask m166Raw m166Goal 5 :=
  liftLow (dom := 0x110000001100000000000000000000001100000011) 1855490 m81Low m166Ess (by decide +kernel) (by decide +kernel)

def m55Mask : Word := 0xff00ff00ff00ff
def m55Goal : Word := Nat.land gAll m55Mask
def m55Raw : List Word := mkR m55Mask [v0,v1,v2,v4,v5]
theorem m55Ess : ∀ a ∈ m55Raw, Essential m55Mask m55Goal m55Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546]) (by decide +kernel)
theorem m55Low : LowerM m55Mask m55Raw m55Goal 5 :=
  liftLow (dom := 0x55005500550055) 282896 m86Low m55Ess (by decide +kernel) (by decide +kernel)

def m87Mask : Word := 0xff00ff0000000000ff00ff
def m87Goal : Word := Nat.land gAll m87Mask
def m87Raw : List Word := mkR m87Mask [v0,v1,v2,v4,v6]
theorem m87Ess : ∀ a ∈ m87Raw, Essential m87Mask m87Goal m87Raw a :=
  checkAllEss_sound (ps := [4113,4114,16452,273,321]) (by decide +kernel)
theorem m87Low : LowerM m87Mask m87Raw m87Goal 6 :=
  liftLow (dom := 0x3300330000000000330033) 1049606 m89Low m87Ess (by decide +kernel) (by decide +kernel)

def m118Mask : Word := 0x550055005500550055005500550055
def m118Goal : Word := Nat.land gAll m118Mask
def m118Raw : List Word := mkR m118Mask [v1,v2,v4,v5,v6]
theorem m118Ess : ∀ a ∈ m118Raw, Essential m118Mask m118Goal m118Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,1092]) (by decide +kernel)
def m118Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,17412,17472,20496,20544,5638,5652,9734,12848,13332,13360,17926,17986,21058,21524,25154,25184,25696,28720,28768,4614,4628,4656,4674,8710,8752,8770,8800,9222,9236,9264,9312,17414,17428,17474,17504,20500,20528,20546,20576,4608,8704,9216,17408,20480,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,17922,17924,17984,20994,21008,21056,21508,21520,21568,25090,25120,25152,25604,25632,25664,28688,28704,28736,13830,13844,13872,22022,22036,22082,26118,26178,26208,29232,29250,29280,29716,29744,29792,4612,4640,4672,8708,8720,8768,9218,9232,9280,17410,17424,17440,20482,20484,20512,5680,5698,9748,9776,9794,9824,12806,12820,12866,12896,13318,13408,17940,18016,20998,21012,21040,21088]
def m118Ws : List Wire := mkWs m118Raw [(0xfcffc01f8fff038fc7fc6001fe373c0f,0x1154892004e90082412408a2b2171405),(0xf0fc7e071ff1c71f8fd81fe004bdcf0,0x35311004905b04108848026626095c50),(0xf3f0f803fe3fe07e3f1e3e001f8cef03,0x64234248321620241210064c4c88e902),(0x3ff00fc7fc7ff803fe0c01fe1f0f03c,0xca8a64016b0449002480151949e0a028),(0xfc003f007ff8ffffc0031fe001ff03c0,0x8acc80924da092490000199191760280)]
def m118Cuts : BTree CutSpec := (N (N (N (mc m118Raw 0x55005500550055 4) (mc m118Raw 0x110011001100110011001100110011 4)) (N (mc m118Raw 0x55000000550000005500000055 4) E)) (N (N (mc m118Raw 0x5500550000000000550055 4) E) (N (mc m118Raw 0x50005000500050005000500050005 4) E)))
theorem m118CutValid : ∀ ci < 5, ValidCut m118Mask m118Raw m118Goal (btreeGet ⟨0,0,[]⟩ 3 m118Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 1589384 m86Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 549216 m86Low (by decide +kernel)
noncomputable def m118D : BTree NodeRec := (N (N (N (N (k 0 [0,1,2,3,4] [8215,32807,41015,49223,53543,45367,37191,74295,98887,78663]) (u 24648)) (N (u 39) (u 583))) (N (N (v 4160 1) (v 36912 4)) (N (y 71 [57408,65608]) E))) (N (N (N (y 23 [16448,24648]) (y 567 [81968,90168])) (N (u 55) E)) (N (N (u 4168) (u 36920)) (N (v 24640 2) E))))
noncomputable def x118 : Nat → Bool := checkNode m118Mask m118Goal (Nat.sub (Nat.shiftLeft 1 m118Pairs.length) 1) symMain 13 6 m118Ws m118D 4 m118Cuts 3
noncomputable def y118 : Nat → Nat → Bool := checkRange m118Mask m118Goal (Nat.sub (Nat.shiftLeft 1 m118Pairs.length) 1) symMain 13 6 m118Ws m118D 4 m118Cuts 3
theorem s118 (s n : Nat) (h : y118 s n = true) : ac x118 s n := cr_sound h
theorem q2 : ac x118 0 13 := s118 0 13 (by decide +kernel)
theorem m118All : ac x118 0 13 := q2
theorem m118Low : LowerM m118Mask m118Raw m118Goal 7 :=
  dagLow (pairs := m118Pairs) (sym := symMain) (ncuts := 5) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m118Ess m118CutValid m118All (by decide +kernel)

def m143Mask : Word := 0xffff0000000000000000000000000000ffff
def m143Goal : Word := Nat.land gAll m143Mask
def m143Raw : List Word := mkR m143Mask [v0,v1,v2,v3,v7]
theorem m143Ess : ∀ a ∈ m143Raw, Essential m143Mask m143Goal m143Raw a :=
  checkAllEss_sound (ps := [2057,32898,32900,265,385]) (by decide +kernel)
theorem m143Low : LowerM m143Mask m143Raw m143Goal 6 :=
  liftLow (dom := 0x333300000000000000000000000000003333) 787463 m89Low m143Ess (by decide +kernel) (by decide +kernel)

def m151Mask : Word := 0xff00ff00000000000000000000000000ff00ff
def m151Goal : Word := Nat.land gAll m151Mask
def m151Raw : List Word := mkR m151Mask [v0,v1,v2,v4,v7]
theorem m151Ess : ∀ a ∈ m151Raw, Essential m151Mask m151Goal m151Raw a :=
  checkAllEss_sound (ps := [4113,4114,32900,273,385]) (by decide +kernel)
theorem m151Low : LowerM m151Mask m151Raw m151Goal 5 :=
  liftLow (dom := 0x55005500000000000000000000000000550055) 291088 m86Low m151Ess (by decide +kernel) (by decide +kernel)

def m155Mask : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
def m155Goal : Word := Nat.land gAll m155Mask
def m155Raw : List Word := mkR m155Mask [v0,v1,v3,v4,v7]
theorem m155Ess : ∀ a ∈ m155Raw, Essential m155Mask m155Goal m155Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,385]) (by decide +kernel)
theorem m155Low : LowerM m155Mask m155Raw m155Goal 6 :=
  liftLow (dom := 0x303030300000000000000000000000003030303) 1849344 m89Low m155Ess (by decide +kernel) (by decide +kernel)

def m158Mask : Word := 0x5555555500000000000000000000000055555555
def m158Goal : Word := Nat.land gAll m158Mask
def m158Raw : List Word := mkR m158Mask [v1,v2,v3,v4,v7]
theorem m158Ess : ∀ a ∈ m158Raw, Essential m158Mask m158Goal m158Raw a :=
  checkAllEss_sound (ps := [4114,32900,32904,530,642]) (by decide +kernel)
theorem m158Low : LowerM m158Mask m158Raw m158Goal 5 :=
  liftLow (dom := 0x505050500000000000000000000000005050505) 291096 m86Low m158Ess (by decide +kernel) (by decide +kernel)

def m167Mask : Word := 0xff000000ff0000000000000000000000ff000000ff
def m167Goal : Word := Nat.land gAll m167Mask
def m167Raw : List Word := mkR m167Mask [v0,v1,v2,v5,v7]
theorem m167Ess : ∀ a ∈ m167Raw, Essential m167Mask m167Goal m167Raw a :=
  checkAllEss_sound (ps := [32897,8226,8228,546,385]) (by decide +kernel)
theorem m167Low : LowerM m167Mask m167Raw m167Goal 6 :=
  liftLow (dom := 0x550000005500000000000000000000005500000055) 14844040 m166Low m167Ess (by decide +kernel) (by decide +kernel)

def m182Mask : Word := 0x5500550055005500000000000000000055005500550055
def m182Goal : Word := Nat.land gAll m182Mask
def m182Raw : List Word := mkR m182Mask [v1,v2,v4,v5,v7]
theorem m182Ess : ∀ a ∈ m182Raw, Essential m182Mask m182Goal m182Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,642]) (by decide +kernel)
def m182Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,33282,33408,33796,33920,40992,41088,5638,5652,9734,12848,13332,13360,34310,37520,37908,38032,45104,45200,4614,4628,4656,4752,8710,8752,9222,9236,9264,33286,33424,33798,33812,33936,41008,41104,4608,8704,9216,33280,33792,40960,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,34306,34308,34432,37378,37392,37504,37892,37904,38016,41474,41504,41600,41988,42016,42112,45072,45088,45184,13830,13844,13872,38406,38420,38544,42502,45616,45712,46100,46128,46224,4612,4640,4736,8708,8720,8832,9218,9232,9344,33284,33296,33312,33794,33808,33824,40962,40964,40976,5680,5776,9748,9776,12806,12820,12944,13318,13456,34324,34448,37382,37396,37424,37894,37936,41478,41520,41616,41990,42004,42032]
def m182Ws : List Wire := mkWs m182Raw [(0x1cf9fc0e3f1ff038fc7fcb063f0cf0cf,0x25224090400490082412400a51045045),(0xe31e3c71c0e7f1c71f8fd439c0377330,0x656ad1020925b0410884801ad3157110),(0x3e7cc0007fbfe07e3f1c1000ffbb003,0xdaddbe2490fb6202412100f5aefba002),(0xfc07f381f8fc7ff803fe26c1f0c3cc3c,0x8a802448024844900248004124428428),(0xfff803fe00ff8ffffc0038fe00fc0fc0,0x1015080124920924900000a408a80a80)]
def m182Cuts : BTree CutSpec := (N (N (mc m182Raw 0x1100000011000000000000000000000011000000110000 4) (mc m182Raw 0x55005500550055 4)) (N (mc m182Raw 0x50000000500000000000000000000000500000005 4) (mc m182Raw 0x55005500000000000000000000000000550055 4)))
theorem m182CutValid : ∀ ci < 4, ValidCut m182Mask m182Raw m182Goal (btreeGet ⟨0,0,[]⟩ 2 m182Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 1855489 m81Low (by decide +kernel)
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
noncomputable def m182D : BTree NodeRec := (N (N (k 0 [0,1,2,3] [9031]) (u 4168)) (N (k 839 [1,2,0] [16456]) E))
noncomputable def x182 : Nat → Bool := checkNode m182Mask m182Goal (Nat.sub (Nat.shiftLeft 1 m182Pairs.length) 1) id 3 6 m182Ws m182D 2 m182Cuts 2
noncomputable def y182 : Nat → Nat → Bool := checkRange m182Mask m182Goal (Nat.sub (Nat.shiftLeft 1 m182Pairs.length) 1) id 3 6 m182Ws m182D 2 m182Cuts 2
theorem s182 (s n : Nat) (h : y182 s n = true) : ac x182 s n := cr_sound h
theorem q3 : ac x182 0 3 := s182 0 3 (by decide +kernel)
theorem m182All : ac x182 0 3 := q3
theorem m182Low : LowerM m182Mask m182Raw m182Goal 7 :=
  dagLow (pairs := m182Pairs) (sym := id) (ncuts := 4) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m182Ess m182CutValid m182All (by decide +kernel)

def m217Mask : Word := 0x3030303000000000303030300000000030303030000000003030303
def m217Goal : Word := Nat.land gAll m217Mask
def m217Raw : List Word := mkR m217Mask [v0,v3,v4,v6,v7]
theorem m217Ess : ∀ a ∈ m217Raw, Essential m217Mask m217Goal m217Raw a :=
  checkAllEss_sound (ps := [2057,265,273,321,385]) (by decide +kernel)
def m217Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,16641,16704,20496,20544,33025,33152,34824,34944,6424,18760,22552,22600,37264,38936,39056,49600,51272,51392,53392,53440,2328,2376,4376,4496,16712,16832,20504,20552,20624,20672,33168,33216,34840,34888,34960,35008,2304,4352,16640,20480,33024,34816,6401,6408,6416,18689,18696,18752,20737,20752,20800,22536,22544,22592,35073,35080,35200,37121,37136,37248,38920,38928,39040,49409,49472,49536,51208,51264,51328,53264,53312,53376,22808,22856,39192,39312,51528,51648,53648,53696,55320,55368,55440,55488,2320,2368,2432,4360,4416,4480,16648,16656,16768,20481,20488,20608,33032,33040,33088,34817,34832,34880,6472,6544,18712,18880,20760,20808,20880,20928,22672,22720,35096,35144,35216,35264,37144,37312,38984,39104,49480,49552,51224,51344]
def m217Ws : List Wire := mkWs m217Raw [(0x33f3fc71ff0ff038fc7fd70c3f09333f,0x82000000082412400000000115),(0xccfc3f8007f3f1c71f8fe1f00336fc03,0x5530d4144831704108848030d712f402),(0xf0fcc0e38fcfe07e3f1ca03ccc7d0cc,0xe15559208154d202412100554d475048),(0xf00ff00fc0ff3ff803fe0c03f0f8e0f0,0x1eaaa64012ab2490024800aab2b8a0a0),(0xfff003f000ffcffffc0030fc00ff0f00,0xaacf280924ce8924900000cf28ed0a00)]
def m217Cuts : BTree CutSpec := (N (N (N (mc m217Raw 0x300030000000000030003 4) (mc m217Raw 0x303030300000000000000000000000003030303 5)) (N (mc m217Raw 0x30303030000000003030303 5) E)) (N (N (mc m217Raw 0x30300000000000000000000000000000303 4) (mc m217Raw 0x30003000000000003000300000000000300030000000000030003 5)) (N (mc m217Raw 0x303000000000000030300000000000003030000000000000303 5) E)))
theorem m217CutValid : ∀ ci < 6, ValidCut m217Mask m217Raw m217Goal (btreeGet ⟨0,0,[]⟩ 3 m217Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 1847296 m81Low (by decide +kernel)
  · exact cv 1590784 m89Low (by decide +kernel)
  · exact cv 1850368 m89Low (by decide +kernel)
  · exact cv 1849344 m89Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
noncomputable def m217D : BTree NodeRec := (N (N (N (N (N (N (k 0 [0,1] [8215,81947,114727,204843,118839,208955,254023,303179,327975,332087,369223,373575]) (z 127018)) (N (u 57401) (u 188500))) (N (N (v 4186 2) (k 295 [0,1] [335921,24629,360505,106557,74037,188981])) (N (w 57941 [2,1]) E))) (N (N (N (u 12360) (w 127557 [3,0])) (N (u 77896) E)) (N (N (u 45128) (u 163897)) (N (f 102485 [237640]) E)))) (N (N (N (N (z 4138) (v 127034 5)) (N (v 57418 4) E)) (N (N (k 27 [0,1] [16422,90165,106553,94277,110665,16678]) (u 168004)) (N (f 102453 [221272]) E))) (N (N (N (u 4153) (j 151621 1 [319576])) (N (u 57433) E)) (N (N (k 39 [1,0] [122922,24629,131129,139336,147530,155733,180313,123178,188981,197205]) (k 184369 [0,1] [385092,393300])) (N (u 102489) E))))) (N (N (N (N (N (k 23 [0,1] [16426,24629,49209,28741,53321,57432,65626,16682,74293,78405]) (u 127032)) (N (u 57416) (u 184377))) (N (N (w 4661 [3,0]) (k 163889 [0,1] [344132,352340])) (N (k 43 [1,0] [122918,213045,106553,229461,245849,123174]) E))) (N (N (N (u 12376) (k 75 [0,1] [262182,311365,245833,315477,249945,262438])) (N (u 77912) E)) (N (N (u 41017) (k 583 [0,1] [376881,155701,401465,245821,196917,295477])) (N (u 114760) E)))) (N (N (N (N (k 4149 [0,1] [32840,41048]) (u 127049)) (N (k 57429 [0,1] [163912,172120]) E)) (N (N (j 41013 1 [98376]) (u 168020)) (N (u 106584) E))) (N (N (N (u 4184) (u 155736)) (N (w 57909 [5,1]) E)) (N (N (v 57386 1) (u 188484)) (N (k 71 [0,1] [262186,270392,278586,155717,286793,159829,290905,262442,295493,299605]) E))))))
noncomputable def x217 : Nat → Bool := checkNode m217Mask m217Goal (Nat.sub (Nat.shiftLeft 1 m217Pairs.length) 1) symMain 50 7 m217Ws m217D 6 m217Cuts 3
noncomputable def y217 : Nat → Nat → Bool := checkRange m217Mask m217Goal (Nat.sub (Nat.shiftLeft 1 m217Pairs.length) 1) symMain 50 7 m217Ws m217D 6 m217Cuts 3
theorem s217 (s n : Nat) (h : y217 s n = true) : ac x217 s n := cr_sound h
theorem q4 : ac x217 0 50 := s217 0 50 (by decide +kernel)
theorem m217All : ac x217 0 50 := q4
theorem m217Low : LowerM m217Mask m217Raw m217Goal 8 :=
  dagLow (pairs := m217Pairs) (sym := symMain) (ncuts := 6) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m217Ess m217CutValid m217All (by decide +kernel)

def m241Mask : Word := 0x3000300030003000300030003000300030003000300030003000300030003
def m241Goal : Word := Nat.land gAll m241Mask
def m241Raw : List Word := mkR m241Mask [v0,v4,v5,v6,v7]
theorem m241Ess : ∀ a ∈ m241Raw, Essential m241Mask m241Goal m241Raw a :=
  checkAllEss_sound (ps := [4113,273,32928,321,385]) (by decide +kernel)
def m241Pairs : List (Row × Row) := mkPairs [4353,4368,16641,16704,20496,20544,33025,33152,40992,41088,12577,12592,24865,24928,28720,28768,37264,41249,45104,45200,49600,53392,53440,57440,57536,4385,4400,4496,16673,16736,16832,20528,20576,20624,20672,33057,33168,33216,40993,41008,41056,41104,41152,4352,16640,20480,33024,40960,12545,12560,12576,20737,20752,20800,24833,24864,24896,28688,28704,28736,37121,37136,37248,41217,41248,41344,45072,45088,45184,49409,49472,49536,53264,53312,53376,57376,57408,57472,28961,28976,29024,45345,45360,45456,53648,53696,57633,57696,57792,61488,61536,61584,61632,4384,4416,4480,16656,16672,16768,20481,20512,20608,33040,33056,33088,40961,40976,41024,12640,12688,20769,20784,20832,20880,20928,24880,25024,28705,28816,28864,37153,37168,37312,41264,41312,41360,41408,45089]
def m241Ws : List Wire := mkWs m241Raw [(0x7f1ff1c7e1ffc0e3f1ff58387e133ccf,0x81204208004240209049004812021445),(0x87e7f038fe3fc71c7e3f28078e6dcc33,0x2a4aa4410a1c8104221202928c2d4812),(0xf8f83e001fcff81f8fc787c0018eff00,0x9b29d09226c7c809048401c9b686fd00),(0xffc03f1ff1ffe00ff83007f1f0f03c,0x5495190055a112400920052561d0a028),(0xff000fc01ffe3ffff000c7f801ff03c0,0x64d62024993824924000063649790280)]
def m241Cuts : BTree CutSpec := (N (N (mc m241Raw 0x30003000000000003000300000000 4) (mc m241Raw 0x300000003000000030000000300000003000000030000000300000003 4)) (N (mc m241Raw 0x300030003000300000000000000000003000300030003 4) (mc m241Raw 0x30003000000000003000300000000000300030000000000030003 5)))
theorem m241CutValid : ∀ ci < 4, ValidCut m241Mask m241Raw m241Goal (btreeGet ⟨0,0,[]⟩ 2 m241Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 1835360 m86Low (by decide +kernel)
  · exact cv 29096 m86Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
noncomputable def m241D : BTree NodeRec := (N (N (N (k 0 [0,1,2,3] [8215,32795,12343,36923,41271]) (w 27 [3,0])) (N (v 4160 1) E)) (N (N (y 23 [16448,24648]) (v 311 1)) (N (u 4168) E)))
noncomputable def x241 : Nat → Bool := checkNode m241Mask m241Goal (Nat.sub (Nat.shiftLeft 1 m241Pairs.length) 1) symMain 6 6 m241Ws m241D 3 m241Cuts 2
noncomputable def y241 : Nat → Nat → Bool := checkRange m241Mask m241Goal (Nat.sub (Nat.shiftLeft 1 m241Pairs.length) 1) symMain 6 6 m241Ws m241D 3 m241Cuts 2
theorem s241 (s n : Nat) (h : y241 s n = true) : ac x241 s n := cr_sound h
theorem q5 : ac x241 0 6 := s241 0 6 (by decide +kernel)
theorem m241All : ac x241 0 6 := q5
theorem m241Low : LowerM m241Mask m241Raw m241Goal 7 :=
  dagLow (pairs := m241Pairs) (sym := symMain) (ncuts := 4) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m241Ess m241CutValid m241All (by decide +kernel)

def m63Mask : Word := 0xffffffffffffffff
def m63Goal : Word := Nat.land gAll m63Mask
def m63Raw : List Word := mkR m63Mask [v0,v1,v2,v3,v4,v5]
theorem m63Ess : ∀ a ∈ m63Raw, Essential m63Mask m63Goal m63Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546]) (by decide +kernel)
def m63Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,2307,2309,2314,2316,2328,2337,2344,4355,4357,4372,4376,4385,4400,4611,4614,4618,4628,4632,4656,8707,8710,8714,8737,8744,8752,9221,9222,9228,9236,9249,9256,9264,2304,4352,4608,8704,9216,2823,2830,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6456,6670,6684,6712,8967,9479,9735,9742,10552,10766,10808,11278,11292,11320,12600,12856,13340,13368,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380]
def m63Ws : List Wire := mkWs m63Raw [(0xffe2098c7f8c00007ffc53c61bc9fc0f,0x49200380b2808920a68c11420bc0d405),(0x38e436f391b007ff8000bdc864f64cf0,0x10405791b78010e3821435c024524c50),(0xc719c703ee43f80000033ff18707b300,0x8208d7b7ff8078450c293fd08507b100),(0x7e1f87c0f84000001ffeec1f8383c03,0x49ffc7f4d01228a1173ee81f0382802),(0xf81e007ff018001ffe03cf3e003fc03c,0x201fa86e4802441c5843ca3c002d0028),(0x1fff800063ffe00003f03fffc003c0,0x172848000387106182c02f5a800280)]
def m63Cuts : BTree CutSpec := (N (N (mc m63Raw 0xf000f000f000f 4) (mc m63Raw 0x5500550055005500 4)) (N (mc m63Raw 0xf0f0f0f0 4) E))
theorem m63CutValid : ∀ ci < 3, ValidCut m63Mask m63Raw m63Goal (btreeGet ⟨0,0,[]⟩ 2 m63Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
noncomputable def m63D : BTree NodeRec := (w 0 [0,1,2])
noncomputable def x63 : Nat → Bool := checkNode m63Mask m63Goal (Nat.sub (Nat.shiftLeft 1 m63Pairs.length) 1) id 1 6 m63Ws m63D 0 m63Cuts 2
noncomputable def y63 : Nat → Nat → Bool := checkRange m63Mask m63Goal (Nat.sub (Nat.shiftLeft 1 m63Pairs.length) 1) id 1 6 m63Ws m63D 0 m63Cuts 2
theorem s63 (s n : Nat) (h : y63 s n = true) : ac x63 s n := cr_sound h
theorem q6 : ac x63 0 1 := s63 0 1 (by decide +kernel)
theorem m63All : ac x63 0 1 := q6
theorem m63Low : LowerM m63Mask m63Raw m63Goal 7 :=
  dagLow (pairs := m63Pairs) (sym := id) (ncuts := 3) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m63Ess m63CutValid m63All (by decide +kernel)

def m95Mask : Word := 0xffffffff00000000ffffffff
def m95Goal : Word := Nat.land gAll m95Mask
def m95Raw : List Word := mkR m95Mask [v0,v1,v2,v3,v4,v6]
theorem m95Ess : ∀ a ∈ m95Raw, Essential m95Mask m95Goal m95Raw a :=
  checkAllEss_sound (ps := [2057,4114,16452,265,273,321]) (by decide +kernel)
def m95Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,3847,3854,5895,7452,7694,7708,18183,19274,19982,20042,23114,23580,2307,2309,2314,2316,2328,2376,4355,4357,4372,4376,4611,4614,4618,4628,4632,4674,16643,16645,16706,16712,17413,17414,17420,17428,17474,17480,20500,20504,20546,20552,2304,4352,4608,16640,17408,20480,2823,2830,2890,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6670,6684,6730,17159,17226,17671,17927,17934,17994,18762,19470,19484,19530,21066,21532,22556,22602,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380,5392,5634,5636]
def m95Ws : List Wire := mkWs m95Raw [(0x3ffc04711ff2c00f03ff0cf02727f0cf,0x92400d02c90001304c3045005035045),(0xc71c43bee4710000fc007f711bd93030,0x420a6ffa6df011259c457d711b493010),(0xf8e0bbc0fb8403f00000b7f2dc1ec300,0x904199d7ffb004f2298a97f24c1ec100),(0xff3c0f03f04000003ffbbce0e0f003,0x93ff2fd3602a48523cfbace0e0a002),(0xff03c00ffc09bc00ffc0c3cf00ff0c3c,0x2401900592000c806310828600b40428),(0x3fff0000e3fff0000fc0fff000fc0,0x266280040330c80206809b2000a80)]
def m95Cuts : BTree CutSpec := (N (N (N (mc m95Raw 0x300030000000000030003 4) (mc m95Raw 0xf000f00000000000f000f 5)) (N (mc m95Raw 0xcccc000000000000cccc 4) E)) (N (N (mc m95Raw 0xf0f0f0f0 4) (mc m95Raw 0x30303030000000003030303 5)) (N (mc m95Raw 0x550055000000000055005500 4) E)))
theorem m95CutValid : ∀ ci < 6, ValidCut m95Mask m95Raw m95Goal (btreeGet ⟨0,0,[]⟩ 3 m95Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 1590784 m89Low (by decide +kernel)
noncomputable def m95D : BTree NodeRec := (N (N (N (N (N (k 0 [0,1,2,3] [8214,12326,32826,73799,77911,90445,139605,143941,94813,156485,160597,173143]) (u 46165)) (N (u 16981) E)) (N (N (k 58 [3,5] [41029,45141,49741,66133,70469,54109]) (u 77913)) (N (u 45093) E))) (N (N (N (u 4185) (u 69673)) (N (v 36932 1) E)) (N (N (y 16973 [57380]) (v 86116 3)) (N (y 45917 [122916]) E)))) (N (N (N (N (k 22 [2,3,4] [16473,25181]) (k 341 [2,1,4] [147497,66122])) (N (k 71 [0,2,3] [81988]) E)) (N (N (u 16453) (k 1111 [0,1,2] [180324])) (N (u 45141) E))) (N (N (N (u 4701) (k 837 [3,2,5] [163929,136285])) (N (k 333 [2,4] [98341,106581,29238,49738,115549,132181]) E)) (N (N (u 24612) E) (N (u 57380) E)))))
noncomputable def x95 : Nat → Bool := checkNode m95Mask m95Goal (Nat.sub (Nat.shiftLeft 1 m95Pairs.length) 1) symMain 23 7 m95Ws m95D 5 m95Cuts 3
noncomputable def y95 : Nat → Nat → Bool := checkRange m95Mask m95Goal (Nat.sub (Nat.shiftLeft 1 m95Pairs.length) 1) symMain 23 7 m95Ws m95D 5 m95Cuts 3
theorem s95 (s n : Nat) (h : y95 s n = true) : ac x95 s n := cr_sound h
theorem q7 : ac x95 0 23 := s95 0 23 (by decide +kernel)
theorem m95All : ac x95 0 23 := q7
theorem m95Low : LowerM m95Mask m95Raw m95Goal 8 :=
  dagLow (pairs := m95Pairs) (sym := symMain) (ncuts := 6) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m95Ess m95CutValid m95All (by decide +kernel)

def m119Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff
def m119Goal : Word := Nat.land gAll m119Mask
def m119Raw : List Word := mkR m119Mask [v0,v1,v2,v4,v5,v6]
theorem m119Ess : ∀ a ∈ m119Raw, Essential m119Mask m119Goal m119Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,321]) (by decide +kernel)
def m119Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,21058,21524,24865,24928,25154,25184,25696,28720,28768,5895,9991,18183,4355,4357,4372,4385,4400,4611,4614,4628,4656,4674,8707,8710,8737,8752,8770,8800,9221,9222,9236,9249,9264,9312,16643,16645,16673,16706,16736,17413,17414,17428,17474,17504,20500,20528,20546,20576,4352,4608,8704,9216,16640,17408,20480,4871,5383,5639,8967,9479,9735,17159,17671,17927,4865,4866,4880,5377,5380,5392,5634,5636,5648,8961,8962,8992,9473,9476,9504,9730,9732,9760,12545,12560,12576,12802,12816,12832,13316,13328,13344,17153,17154,17216]
def m119Ws : List Wire := mkWs m119Raw [(0xe071f8fdb64401f00007f830e379c303,0x20104827fe000272450af810a178c101),(0xe38e3f1eda1800003ff838c7649e403c,0x4082110bfe01149093987847608a4014),(0x1c0fc7e36ca03e0fc000390b98e78cc0,0x4048243fe004e21c231b80988a78440),(0x1ff007fc0f0fc00000ffce0c1f07f00f,0x92004900000c805086502081e05100a),(0x1ffff8007030000fff0017f01ff800f0,0x124920000002a14e2c4607b0175000a0),(0xe000000381c3fff0000027ffe0003f00,0x8000000000033188308005e640002a00)]
def m119Cuts : BTree CutSpec := (N (N (N (N (mc m119Raw 0x30003000000000003000300000000 4) (mc m119Raw 0xff000000ff000000ff000000ff 5)) (N (mc m119Raw 0xff00ff0000000000ff00ff 6) E)) (N (N (mc m119Raw 0xf000f000f000f000f000f000f000f 7) E) (N (mc m119Raw 0x33000000330000003300000033 4) E))) (N (N (N (mc m119Raw 0x550055005500550055005500550055 7) (mc m119Raw 0x55000000550000005500000055 4)) (N (mc m119Raw 0xf000f000f000f 4) E)) (N (N (mc m119Raw 0x330033003300330033003300330033 7) E) (N (mc m119Raw 0xff00ff00ff00ff 5) E))))
theorem m119CutValid : ∀ ci < 10, ValidCut m119Mask m119Raw m119Goal (btreeGet ⟨0,0,[]⟩ 4 m119Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 1753224 m118Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 549184 m86Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
noncomputable def m119D : BTree NodeRec := (N (N (N (N (k 0 [0,1,2,3,4] [9043,50007,74587,78687]) (v 24634 1)) (N (z 4196) E)) (N (N (w 4148 [7,8]) (j 36901 1 [90168])) (N (k 855 [1,2,3,7,8,4,0] [57400,65594]) E))) (N (N (N (k 851 [5,6,1,2,3,4,0] [16436,24644,28756,32868,41068]) (k 859 [9,2,3,4,7,0] [81957])) (N (v 4204 4) E)) (N (N (v 4164 8) (u 41016)) (N (u 24632) E))))
noncomputable def x119 : Nat → Bool := checkNode m119Mask m119Goal (Nat.sub (Nat.shiftLeft 1 m119Pairs.length) 1) symMain 12 8 m119Ws m119D 4 m119Cuts 4
noncomputable def y119 : Nat → Nat → Bool := checkRange m119Mask m119Goal (Nat.sub (Nat.shiftLeft 1 m119Pairs.length) 1) symMain 12 8 m119Ws m119D 4 m119Cuts 4
theorem s119 (s n : Nat) (h : y119 s n = true) : ac x119 s n := cr_sound h
theorem q8 : ac x119 0 12 := s119 0 12 (by decide +kernel)
theorem m119All : ac x119 0 12 := q8
theorem m119Low : LowerM m119Mask m119Raw m119Goal 9 :=
  dagLow (pairs := m119Pairs) (sym := symMain) (ncuts := 10) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m119Ess m119CutValid m119All (by decide +kernel)

def m123Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def m123Goal : Word := Nat.land gAll m123Mask
def m123Raw : List Word := mkR m123Mask [v0,v1,v3,v4,v5,v6]
theorem m123Ess : ∀ a ∈ m123Raw, Essential m123Mask m123Goal m123Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,321]) (by decide +kernel)
theorem m123Low : LowerM m123Mask m123Raw m123Goal 8 :=
  liftLow (dom := 0xf000f000f000f000f000f000f000f) 3833860 m241Low m123Ess (by decide +kernel) (by decide +kernel)

def m159Mask : Word := 0xffffffff000000000000000000000000ffffffff
def m159Goal : Word := Nat.land gAll m159Mask
def m159Raw : List Word := mkR m159Mask [v0,v1,v2,v3,v4,v7]
theorem m159Ess : ∀ a ∈ m159Raw, Essential m159Mask m159Goal m159Raw a :=
  checkAllEss_sound (ps := [2057,4114,32900,265,273,385]) (by decide +kernel)
def m159Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,33025,33152,33282,33408,33796,33920,34824,34944,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,3847,3854,5895,7452,7694,7708,34567,36366,39964,2307,2309,2314,2316,2328,4355,4357,4372,4376,4496,4611,4614,4618,4628,4632,4752,33027,33029,33168,33283,33286,33290,33424,33797,33798,33804,33812,33936,34826,34828,34840,34960,2304,4352,4608,33024,33280,33792,34816,2823,2830,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6670,6684,33543,34055,34311,34318,35342,35854,35868,37916,38940,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380,5392,5634,5636,5648,6401,6408,6416,6658,6664]
def m159Ws : List Wire := mkWs m159Raw [(0x38fff0191fe2c001c0ffc9e08c9fc0cf,0x82490382ca00022c118c8a00c0d4045),(0xc71c70eee465001e3f001ee13764c330,0x410821fa6de0044e47095ae03524c110),(0x7e38770fb8803e000003fe6587b0c00,0x2410fffffe009e48a32bfe2587b0400),(0xf803fb8703f07c000007f7786383f003,0x90024fc7d3401c881447374863829002),(0xfffc0c07fc0180003ff8279f83fc003c,0x24900e059200331138e4251f82d00028),(0xff8001e3fffc000381ffc003fc0,0x22112080001580002a80)]
def m159Cuts : BTree CutSpec := (N (N (N (mc m159Raw 0x30300000000000000000000000000000303 4) (mc m159Raw 0xf0f0f0f0000000000000000000000000f0f0f0f 6)) (N (mc m159Raw 0xf0f0f0f0 4) (mc m159Raw 0x3333333300000000000000000000000033333333 6))) (N (N (mc m159Raw 0x55005500000000000000000000000000550055 4) (mc m159Raw 0x333300000000000000000000000000003333 5)) (N (mc m159Raw 0x505050500000000000000000000000005050505 4) E)))
theorem m159CutValid : ∀ ci < 7, ValidCut m159Mask m159Raw m159Goal (btreeGet ⟨0,0,[]⟩ 3 m159Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1847296 m81Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 291096 m86Low (by decide +kernel)
  · exact cv 14697992 m155Low (by decide +kernel)
  · exact cv 787463 m89Low (by decide +kernel)
  · exact cv 28947 m87Low (by decide +kernel)
noncomputable def m159D : BTree NodeRec := (N (N (N (N (N (k 0 [0,1,2] [8214,81958,90199,115253,123485,156503,164949]) (y 61477 [139336,57652])) (N (y 5205 [73760,41268]) E)) (N (N (j 4437 1 [41300]) (k 1109 [0,2] [172090,106789,66102])) (N (u 45144) E))) (N (N (N (z 4134) (u 61509)) (N (w 38 [2,3]) E)) (N (N (y 4701 [57396]) E) (N (w 565 [2,1,5]) E)))) (N (N (N (N (k 22 [0,1] [16422,24650,33109,49757,66645]) (u 65608)) (N (u 32800) E)) (N (N (u 16724) (u 81978)) (N (j 45668 2 [41524]) E))) (N (N (N (u 4170) (w 855 [2,4])) (N (k 87 [2,4,1] [98392,33076,107108]) E)) (N (N (u 24628) E) (N (k 605 [2,6] [131109,147525,49718]) E)))))
noncomputable def x159 : Nat → Bool := checkNode m159Mask m159Goal (Nat.sub (Nat.shiftLeft 1 m159Pairs.length) 1) id 22 7 m159Ws m159D 5 m159Cuts 3
noncomputable def y159 : Nat → Nat → Bool := checkRange m159Mask m159Goal (Nat.sub (Nat.shiftLeft 1 m159Pairs.length) 1) id 22 7 m159Ws m159D 5 m159Cuts 3
theorem s159 (s n : Nat) (h : y159 s n = true) : ac x159 s n := cr_sound h
theorem q9 : ac x159 0 22 := s159 0 22 (by decide +kernel)
theorem m159All : ac x159 0 22 := q9
theorem m159Low : LowerM m159Mask m159Raw m159Goal 8 :=
  dagLow (pairs := m159Pairs) (sym := id) (ncuts := 7) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m159Ess m159CutValid m159All (by decide +kernel)

def m175Mask : Word := 0xffff0000ffff00000000000000000000ffff0000ffff
def m175Goal : Word := Nat.land gAll m175Mask
def m175Raw : List Word := mkR m175Mask [v0,v1,v2,v3,v5,v7]
theorem m175Ess : ∀ a ∈ m175Raw, Essential m175Mask m175Goal m175Raw a :=
  checkAllEss_sound (ps := [2057,8226,8228,265,546,385]) (by decide +kernel)
theorem m175Low : LowerM m175Mask m175Raw m175Goal 9 :=
  liftLow (dom := 0x33330000333300000000000000000000333300003333) 7610375 m217Low m175Ess (by decide +kernel) (by decide +kernel)

def m183Mask : Word := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def m183Goal : Word := Nat.land gAll m183Mask
def m183Raw : List Word := mkR m183Mask [v0,v1,v2,v4,v5,v7]
theorem m183Ess : ∀ a ∈ m183Raw, Essential m183Mask m183Goal m183Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,385]) (by decide +kernel)
def m183Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,33025,33152,33282,33408,33796,33920,40992,41088,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,33539,34053,34310,37264,37520,37908,38032,41249,45104,45200,5895,9991,34567,4355,4357,4372,4385,4400,4496,4611,4614,4628,4656,4752,8707,8710,8737,8752,9221,9222,9236,9249,9264,33027,33029,33057,33168,33283,33286,33424,33797,33798,33812,33936,40993,41008,41104,4352,4608,8704,9216,33024,33280,33792,40960,4871,5383,5639,8967,9479,9735,33543,34055,34311,4865,4866,4880,5377,5380,5392,5634,5636,5648,8961,8962,8992,9473,9476,9504,9730,9732,9760,12545,12560,12576,12802,12816,12832,13316,13328,13344,33537,33538,33664,34049,34052,34176]
def m183Ws : List Wire := mkWs m183Raw [(0xfc0e3f1fb6c4400f0003fe458de70303,0x24020904ffc008974a84be4185e30101),(0x1c71c7e3db49807007fc0e0a92790c3c,0x81042217fc00131118c1e0282290414),(0xe381f8fc6d920780f8000e33639e30c0,0x408090487fc003a239186e13229e1040),(0x3fe00ff81c0c000007ff3bc7c1f000f,0x124009200003648a47341bc7814000a),(0x3ffff000e233800ff8005c07fe0c0f0,0x249240000001804c62180c05d4040a0),(0xfc000000703c3fff000009ff8000ff00,0x90000000000024480042012c0000aa00)]
def m183Cuts : BTree CutSpec := (N (N (N (N (mc m183Raw 0x50000000500000000000000000000000500000005 4) (mc m183Raw 0x110000001100000000000000000000001100000011 4)) (N (mc m183Raw 0xff00ff00000000000000000000000000ff00ff 5) E)) (N (N (mc m183Raw 0x5500550055005500000000000000000055005500550055 7) (mc m183Raw 0xff00ff00ff00ff 5)) (N (mc m183Raw 0x33003300000000000000000000000000330033 4) E))) (N (N (N (mc m183Raw 0x3300330033003300000000000000000033003300330033 7) (mc m183Raw 0xf0000000f00000000000000000000000f0000000f 5)) (N (mc m183Raw 0xf000f000f000f 4) E)) (N (N (mc m183Raw 0x1100000011000000000000000000000011000000110000 4) (mc m183Raw 0xf000f000f000f0000000000000000000f000f000f000f 6)) (N (mc m183Raw 0xff000000ff0000000000000000000000ff000000ff 6) E))))
theorem m183CutValid : ∀ ci < 12, ValidCut m183Mask m183Raw m183Goal (btreeGet ⟨0,0,[]⟩ 4 m183Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1855489 m81Low (by decide +kernel)
  · exact cv 1449991 m241Low (by decide +kernel)
  · exact cv 14860424 m182Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 14696584 m151Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 28944 m86Low (by decide +kernel)
  · exact cv 14844040 m167Low (by decide +kernel)
  · exact cv 1855490 m81Low (by decide +kernel)
  · exact cv 1314823 m89Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
noncomputable def m183D : BTree NodeRec := (N (N (N (N (N (N (k 0 [0,1,2,3] [8775,90703,156247,180831,222037,254809,287827,345175,402523,427103]) (j 127319 9 [270440])) (N (u 57652) (v 172122 11))) (N (N (j 4709 11 [57652]) (v 143460 3)) (N (y 90213 [24616,123176]) E))) (N (N (N (y 4201 [41316]) (w 143412 [5,1])) (N (v 77933 4) (k 1119 [5,1,2,7,4,3] [409621,434276,442476]))) (N (N (y 45157 [24616,106792]) (y 172114 [24604,368724])) (N (j 110935 5 [237672]) E)))) (N (N (N (N (y 4197 [24616]) (u 127327)) (N (u 46437) (j 200741 5 [24664]))) (N (N (j 5477 5 [41260]) (k 1111 [1,2,5,4,7,3] [352336,360530,16469,376920,385113,393306,65877,139609,172629,213593,229990,262766])) (N (j 90725 11 [131384]) E))) (N (N (N (j 4453 5 [57652]) (w 143444 [6,10])) (N (k 607 [5,0,1] [188500,196709,204909,115053,213605]) (v 213100 7))) (N (N (y 45421 [24612,122932,106788,131380]) (j 172120 1 [238166,270942])) (N (v 110943 10) E))))) (N (N (N (N (N (k 583 [0,1,4,5] [16485,32873,49509,66149,74345,83301]) (u 131176)) (N (j 45669 11 [131384]) (k 1115 [6,2,9,10,3] [409637,417877,74069,246374,279150]))) (N (N (u 4713) (v 143468 7)) (N (v 90221 4) E))) (N (N (N (u 16740) (w 143428 [6,10])) (N (j 78437 11 [57652]) (v 213092 3))) (N (N (u 49448) (u 180308)) (N (u 114792) E)))) (N (N (N (N (u 8232) (k 1107 [6,5,2,1,7,3] [294964,303172,311380,319580,327780,335980])) (N (k 599 [5,0,1] [16485,163949,49509,172645]) (u 200789))) (N (N (k 591 [6,0,5] [98405,115053,139877,148837]) (v 172112 11)) (N (k 853 [3,5,7] [229719,246111,83031,148575]) E))) (N (N (N (u 24884) (v 143452 11)) (N (v 90196 3) E)) (N (N (u 57396) (u 172121)) (N (k 857 [8,9,10,3] [262487,278879]) E))))))
noncomputable def x183 : Nat → Bool := checkNode m183Mask m183Goal (Nat.sub (Nat.shiftLeft 1 m183Pairs.length) 1) id 55 8 m183Ws m183D 6 m183Cuts 4
noncomputable def y183 : Nat → Nat → Bool := checkRange m183Mask m183Goal (Nat.sub (Nat.shiftLeft 1 m183Pairs.length) 1) id 55 8 m183Ws m183D 6 m183Cuts 4
theorem s183 (s n : Nat) (h : y183 s n = true) : ac x183 s n := cr_sound h
theorem q10 : ac x183 0 40 := s183 0 40 (by decide +kernel)
theorem q11 : ac x183 40 15 := s183 40 15 (by decide +kernel)
theorem m183All : ac x183 0 55 := (tm 0 40 15 q10 q11)
theorem m183Low : LowerM m183Mask m183Raw m183Goal 9 :=
  dagLow (pairs := m183Pairs) (sym := id) (ncuts := 12) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m183Ess m183CutValid m183All (by decide +kernel)

def m187Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def m187Goal : Word := Nat.land gAll m187Mask
def m187Raw : List Word := mkR m187Mask [v0,v1,v3,v4,v5,v7]
theorem m187Ess : ∀ a ∈ m187Raw, Essential m187Mask m187Goal m187Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,385]) (by decide +kernel)
theorem m187Low : LowerM m187Mask m187Raw m187Goal 9 :=
  liftLow (dom := 0xf0f00000f0f000000000000000000000f0f00000f0f) 7606279 m217Low m187Ess (by decide +kernel) (by decide +kernel)

def m190Mask : Word := 0x555555555555555500000000000000005555555555555555
def m190Goal : Word := Nat.land gAll m190Mask
def m190Raw : List Word := mkR m190Mask [v1,v2,v3,v4,v5,v7]
theorem m190Ess : ∀ a ∈ m190Raw, Essential m190Mask m190Goal m190Raw a :=
  checkAllEss_sound (ps := [4114,8228,32904,530,546,642]) (by decide +kernel)
theorem m190Low : LowerM m190Mask m190Raw m190Goal 8 :=
  liftLow (dom := 0x5500550055005500000000000000000055005500550055) 14860424 m182Low m190Ess (by decide +kernel) (by decide +kernel)

def m215Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def m215Goal : Word := Nat.land gAll m215Mask
def m215Raw : List Word := mkR m215Mask [v0,v1,v2,v4,v6,v7]
theorem m215Ess : ∀ a ∈ m215Raw, Essential m215Mask m215Goal m215Raw a :=
  checkAllEss_sound (ps := [4113,4114,16452,273,321,385]) (by decide +kernel)
def m215Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,4867,5381,5396,5638,5652,17155,17218,17669,17926,17986,21058,21524,33539,34053,34310,37264,37520,37908,38032,49600,49730,49856,50368,53392,53440,5895,18183,34567,4355,4357,4372,4496,4611,4614,4628,4674,4752,16643,16645,16706,16832,17413,17414,17428,17474,17600,20500,20546,20624,20672,33027,33029,33168,33216,33283,33286,33346,33424,33472,33797,33798,33812,33936,33984,4352,4608,16640,17408,20480,33024,33280,33792,4871,5383,5639,17159,17671,17927,33543,34055,34311,4865,4866,4880,5377,5380,5392,5634,5636,5648,17153,17154,17216,17665,17668,17728,17922,17924,17984,20737,20752,20800,20994,21008,21056,21508,21520,21568,33537,33538,33664,34049]
def m215Ws : List Wire := mkWs m215Raw [(0xf038fc7edb25003c01e0fe08b0e70c33,0x90082413ff00084c02613e0030a30411),(0x71c71f8f6d4207c0001f0e315779300c,0x20410885ff0011c494ab1e1057691004),(0x8e07e3f1b688f8003e000e466b9ec0c0,0x2024121ff0038884e466e02699e4040),(0xff803fe07130003c01ff3878c1f030f,0x4900248000062114814c0878814010a),(0xffffc00381c0003ffe005f80fe003f0,0x924900000008522b1880178064002a0),(0xf0000001c0e0fffc000009fff000fc00,0x400000000000c633211081ed8000a800)]
def m215Cuts : BTree CutSpec := (N (N (N (N (mc m215Raw 0x300030000000000030003 4) (mc m215Raw 0xff00ff00000000000000000000000000ff00ff 5)) (N (mc m215Raw 0x55000000000000005500000000000000550000000000000055 4) E)) (N (N (mc m215Raw 0xff00000000000000ff00000000000000ff00000000000000ff 5) (mc m215Raw 0xff00ff0000000000ff00ff 6)) (N (mc m215Raw 0xf000000000000000f000000000000000f000000000000000f 4) E))) (N (N (N (mc m215Raw 0x550055000000000055005500000000005500550000000000550055 7) (mc m215Raw 0x330033000000000033003300000000003300330000000000330033 6)) (N (mc m215Raw 0x55005500000000000000000000000000550055 4) E)) (N (N (mc m215Raw 0x33003300000000000000000000000000330033 4) E) (N (mc m215Raw 0x3300330000000000330033 5) E))))
theorem m215CutValid : ∀ ci < 11, ValidCut m215Mask m215Raw m215Goal (btreeGet ⟨0,0,[]⟩ 4 m215Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 14704720 m151Low (by decide +kernel)
  · exact cv 28944 m86Low (by decide +kernel)
  · exact cv 553352 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 29064 m86Low (by decide +kernel)
  · exact cv 1049606 m89Low (by decide +kernel)
  · exact cv 14696584 m151Low (by decide +kernel)
  · exact cv 12613648 m155Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
noncomputable def m215D : BTree NodeRec := (N (N (N (N (N (N (k 0 [0,1] [8503,41279,57671,82255,62007,86591,12871,45647,123715,238407,287563,291663,344919,410459,349271,414811]) (u 127048)) (N (k 61492 [5,2] [139605,143957]) (f 172645 [401440,229680]))) (N (N (v 28765 2) (v 143973 10)) (N (v 61540 1) E))) (N (N (N (v 4437 3) (u 143397)) (N (y 78165 [172340]) (v 204901 10))) (N (N (v 41053 2) (v 172106 9)) (N (y 110900 [148020,172612,176724]) E)))) (N (N (N (N (u 4181) (u 118889)) (N (u 69940) (k 859 [4,0] [417876,426085,434285,340333]))) (N (N (k 335 [5,0] [90197,98397,106596,115285]) (k 855 [0,1,2] [352328,360522,368737,254053,376937,385133,221537,332141,393829])) (N (v 61548 10) E))) (N (N (N (u 20565) (j 143461 7 [319576])) (N (y 78421 [172340]) E)) (N (N (u 41557) (v 172137 10)) (N (u 118857) E))))) (N (N (N (N (N (k 311 [0,1,2,3] [16469,24665,33109]) (u 127064)) (N (y 65877 [147764]) (v 196640 8))) (N (N (v 29269 9) (u 143977)) (N (u 61541) E))) (N (N (N (k 319 [0,4,3] [49237]) (u 143429)) (N (u 82228) (v 204909 8))) (N (N (v 41060 1) (v 172129 8)) (N (k 839 [1,0,8,2] [16453,245833,20565,249945,254053,278633,78165,119129,74309,115273]) E)))) (N (N (N (N (u 4185) (k 843 [4,0,6,8] [294949,303173,311397,328293,336489])) (N (k 61508 [4,8] [164181,180821]) (v 204884 1))) (N (N (u 41045) (v 172104 1)) (N (j 61797 10 [229684,139844,164436,184932]) E))) (N (N (N (k 327 [0,3,1] [16469,65629,33109,74325]) (u 155736)) (N (v 61516 9) E)) (N (N (k 835 [5,6,7,1,3] [131124,155716,188492,159828,192604,196708,204901,213100,221541,225893]) (v 172141 8)) (N (k 118885 [0,1] [262216,270424,274536]) E))))))
noncomputable def x215 : Nat → Bool := checkNode m215Mask m215Goal (Nat.sub (Nat.shiftLeft 1 m215Pairs.length) 1) symMain 54 8 m215Ws m215D 6 m215Cuts 4
noncomputable def y215 : Nat → Nat → Bool := checkRange m215Mask m215Goal (Nat.sub (Nat.shiftLeft 1 m215Pairs.length) 1) symMain 54 8 m215Ws m215D 6 m215Cuts 4
theorem s215 (s n : Nat) (h : y215 s n = true) : ac x215 s n := cr_sound h
theorem q12 : ac x215 0 40 := s215 0 40 (by decide +kernel)
theorem q13 : ac x215 40 14 := s215 40 14 (by decide +kernel)
theorem m215All : ac x215 0 54 := (tm 0 40 14 q12 q13)
theorem m215Low : LowerM m215Mask m215Raw m215Goal 9 :=
  dagLow (pairs := m215Pairs) (sym := symMain) (ncuts := 11) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m215Ess m215CutValid m215All (by decide +kernel)

def m222Mask : Word := 0x55555555000000005555555500000000555555550000000055555555
def m222Goal : Word := Nat.land gAll m222Mask
def m222Raw : List Word := mkR m222Mask [v1,v2,v3,v4,v6,v7]
theorem m222Ess : ∀ a ∈ m222Raw, Essential m222Mask m222Goal m222Raw a :=
  checkAllEss_sound (ps := [4114,16452,32904,530,1092,642]) (by decide +kernel)
theorem m222Low : LowerM m222Mask m222Raw m222Goal 8 :=
  liftLow (dom := 0x550055000000000055005500000000005500550000000000550055) 1818760 m118Low m222Ess (by decide +kernel) (by decide +kernel)

def m243Mask : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def m243Goal : Word := Nat.land gAll m243Mask
def m243Raw : List Word := mkR m243Mask [v0,v1,v4,v5,v6,v7]
theorem m243Ess : ∀ a ∈ m243Raw, Essential m243Mask m243Goal m243Raw a :=
  checkAllEss_sound (ps := [4113,4114,273,546,321,385]) (by decide +kernel)
def m243Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,16641,16704,20496,20544,33025,33152,33282,33408,40992,41088,4867,8963,8993,12577,12592,12848,17155,17218,21058,24865,24928,25154,25184,28720,28768,33539,37264,37520,41249,45104,45200,49600,49730,49856,53392,53440,57440,57536,4355,4385,4400,4496,4611,4656,4674,4752,8707,8737,8752,8770,8800,16643,16673,16706,16736,16832,20528,20546,20576,20624,20672,33027,33057,33168,33216,33283,33346,33424,33472,40993,41008,41056,41104,41152,4352,4608,8704,16640,20480,33024,33280,40960,4865,4866,4880,8961,8962,8992,12545,12560,12576,12802,12816,12832,17153,17154,17216,20737,20752,20800,20994,21008,21056,24833,24864,24896,25090,25120,25152,28688,28704,28736,33537,33538,33664,37121,37136,37248,37378,37392,37504,41217]
def m243Ws : List Wire := mkWs m243Raw [(0x8fc0e3f1ff2900783e00f02586df0cc3,0x824020904900089806313004824f0441),(0x71c71c7e3f46078001ff00c299e7303c,0x10810422120001888a95104089c31014),(0x7e381f8fc7130007c00ff31b6139030f,0x2408090484005222404ac11b2030010a),(0x803fe00ff884f80001f00c1c7e3ec030,0x124009200038115562640c763c4020),(0x3ffff000180007fe000fe07fc003c0,0x2492400000a545b9840ee05d800280),(0xffc0000000e0fff800000fff8000fc00,0x490000000000c66620088bb30000a800)]
def m243Cuts : BTree CutSpec := (N (N (N (mc m243Raw 0x30003000000000003000300000000 4) (mc m243Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6)) (N (mc m243Raw 0xf000f000f000f000f000f000f000f 7) E)) (N (N (mc m243Raw 0x500000005000000000000000000000005000000050000000000000000 4) E) (N (mc m243Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) E)))
theorem m243CutValid : ∀ ci < 5, ValidCut m243Mask m243Raw m243Goal (btreeGet ⟨0,0,[]⟩ 3 m243Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
noncomputable def m243D : BTree NodeRec := (w 0 [0,1,2,3,4])
noncomputable def x243 : Nat → Bool := checkNode m243Mask m243Goal (Nat.sub (Nat.shiftLeft 1 m243Pairs.length) 1) id 1 8 m243Ws m243D 0 m243Cuts 3
noncomputable def y243 : Nat → Nat → Bool := checkRange m243Mask m243Goal (Nat.sub (Nat.shiftLeft 1 m243Pairs.length) 1) id 1 8 m243Ws m243D 0 m243Cuts 3
theorem s243 (s n : Nat) (h : y243 s n = true) : ac x243 s n := cr_sound h
theorem q14 : ac x243 0 1 := s243 0 1 (by decide +kernel)
theorem m243All : ac x243 0 1 := q14
theorem m243Low : LowerM m243Mask m243Raw m243Goal 9 :=
  dagLow (pairs := m243Pairs) (sym := id) (ncuts := 5) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m243Ess m243CutValid m243All (by decide +kernel)

def m246Mask : Word := 0x55005500550055005500550055005500550055005500550055005500550055
def m246Goal : Word := Nat.land gAll m246Mask
def m246Raw : List Word := mkR m246Mask [v1,v2,v4,v5,v6,v7]
theorem m246Ess : ∀ a ∈ m246Raw, Essential m246Mask m246Goal m246Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,1092,642]) (by decide +kernel)
def m246Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,17412,17472,20496,20544,33282,33408,33796,33920,40992,41088,5638,5652,9734,12848,13332,13360,17926,17986,21058,21524,25154,25184,25696,28720,28768,34310,37520,37908,38032,45104,45200,49730,49856,50368,53392,53440,57440,57536,4614,4628,4656,4674,4752,8710,8752,8770,8800,9222,9236,9264,9312,17414,17428,17474,17504,17600,20500,20528,20546,20576,20624,20672,33286,33346,33424,33472,33798,33812,33936,33984,41008,41056,41104,41152,4608,8704,9216,17408,20480,33280,33792,40960,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,17922,17924,17984,20994,21008,21056,21508,21520,21568,25090,25120,25152,25604,25632,25664,28688,28704,28736,34306,34308,34432,37378,37392,37504,37892,37904,38016,41474]
def m246Ws : List Wire := mkWs m246Raw [(0x8fc0e3f1ff2300f0001ff0618dcf0c0f,0x82402090490001310a2a902085c50405),(0x71c71c7e3f4c0f003fe0008692f730f0,0x10810422120003104662300282571050),(0x7e381f8fc711000fc001f31f633b0303,0x2408090484005644c4c5611f223a0102),(0x803fe00ff886f00001fe0c187c3cc03c,0x124009200030029194440878284028),(0x3ffff00018000ffe000fe07fc003c0,0x2492400000a8ab39188ee05d800280),(0xffc0000000e0fff000000fff8000fc00,0x490000000000cccc20010bd50000a800)]
def m246Cuts : BTree CutSpec := (N (N (N (N (N (mc m246Raw 0x550055005500550055005500550055 7) (mc m246Raw 0x55005500550055 4)) (N (mc m246Raw 0x1100000011000000110000001100000011000000110000001100000011 5) E)) (N (N (mc m246Raw 0x5000500050005000500050005000500050005000500050005000500050005 7) E) (N (mc m246Raw 0x5500550000000000550055 4) E))) (N (N (N (mc m246Raw 0x550055000000000055005500000000005500550000000000550055 7) (mc m246Raw 0x550000005500000000000000000000005500000055 5)) (N (mc m246Raw 0x110011001100110011001100110011 4) E)) (N (N (mc m246Raw 0x500000005000000000000000000000005000000050000000000000000 4) E) (N (mc m246Raw 0x50005000500050005000500050005 4) E)))) (N (N (N (N (mc m246Raw 0x5500550055005500000000000000000055005500550055 7) (mc m246Raw 0x55000000000000005500000000000000550000000000000055 4)) (N (mc m246Raw 0x110011000000000011001100000000001100110000000000110011 4) E)) (N (N (mc m246Raw 0x11001100110011001100110011001100110011001100110011001100110011 7) E) (N (mc m246Raw 0x50005000000000005000500000000000500050000000000050005 4) E))) (N (N (N (mc m246Raw 0x5500000055000000550000005500000055000000550000005500000055 7) (mc m246Raw 0x55000000550000005500000055 4)) (N (mc m246Raw 0x110000001100000000000000000000001100000011 4) E)) (N (N (mc m246Raw 0x1100000011000000000000000000000011000000110000 4) E) (N (mc m246Raw 0x55005500000000000000000000000000550055 4) E)))))
theorem m246CutValid : ∀ ci < 20, ValidCut m246Mask m246Raw m246Goal (btreeGet ⟨0,0,[]⟩ 5 m246Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1753224 m118Low (by decide +kernel)
  · exact cv 14860424 m182Low (by decide +kernel)
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 14868560 m182Low (by decide +kernel)
  · exact cv 10440705 m241Low (by decide +kernel)
  · exact cv 14569474 m241Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 1858562 m89Low (by decide +kernel)
  · exact cv 549344 m86Low (by decide +kernel)
  · exact cv 549216 m86Low (by decide +kernel)
  · exact cv 1855490 m81Low (by decide +kernel)
  · exact cv 1589384 m86Low (by decide +kernel)
  · exact cv 279024 m86Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 553352 m86Low (by decide +kernel)
  · exact cv 14844040 m166Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
noncomputable def m246D : BTree NodeRec := (N (N (N (N (N (N (N (N (k 0 [0,1,2,3,4,5] [8215,458791,491575,786503,852055,790823,495927,463175,856407,1016375,1057351,1073751,1020743,1114967,1078359]) (u 520277)) (N (u 249976) E)) (N (N (v 102490 2) E) (N (k 71 [6,7,0,2] [794688,802888,820583]) E))) (N (N (N (k 4167 [2,13,9] [139376,147576,24872]) (z 581720)) (N (v 319589 6) E)) (N (N (u 192836) E) (N (w 426071 [2,12,10,9]) E)))) (N (N (N (N (y 8293 [57368,73768]) (k 855 [0,2,1,3,4,5,12] [598069,1122359,1130553,602181,1126471,1134665,1155157,1163351,1187929,1159269,1167463,1192041,704821,708933,983605,987717,435015,484183,820071,824407,488551,1066343])) (N (v 245849 6) E)) (N (N (v 159829 2) E) (N (k 87 [7,0,2,4,3,5,10] [204853,860215,892985,598101,917591,925785,958565,966759,974953,409909,672085,983637,734039,480103,992615]) E))) (N (N (N (u 94772) E) (N (v 356400 14) E)) (N (N (k 39 [7,8,0,2,4] [467783,476007,484455]) E) (N (k 426581 [2,5,0,7,12,10] [696628,717125,270917,909897,426821]) E))))) (N (N (N (N (N (u 12640) (k 536649 [19,7,2] [1089621])) (N (u 274756) E)) (N (N (k 4199 [0,14,10] [303200,311400,213288]) E) (N (k 394599 [7,6,0] [827464,844656,811896]) E))) (N (N (N (z 77925) E) (N (u 340548) E)) (N (N (y 205141 [114996,397636]) E) (N (v 463205 1) E)))) (N (N (N (N (z 8298) (v 565349 6)) (N (v 299113 6) E)) (N (N (k 4421 [2,4,7,6,9] [368741,376937,196909,385381,287333,336489,402277]) E) (N (u 430184) E))) (N (N (N (v 102480 2) E) (N (v 364604 9) E)) (N (N (k 55 [7,2,0,4,3,5,9] [16437,499767,532537,573525,581719,589913,598117,630887,639081,360757,672101,705125,471895,729959,763239]) E) (N (k 567 [7,2,0,3,4] [1024073,1040489,996455]) E)))))) (N (N (N (N (N (N (k 4165 [6,7,0,2,4,5,13,9] [24602,41056,49250,65637,82024,90217,98410,106853,123493,127845]) (w 529767 [18,6,0])) (N (u 266341) E)) (N (N (v 135476 2) E) (N (k 393288 [6,5,0,2] [812119]) E))) (N (N (N (u 65656) E) (N (k 246117 [0,2,7,10,9] [286789,680009,696628,123461,549449]) E)) (N (N (k 4453 [0,4,7,6,10] [368725,417881,352557,426325,123477,180825,406357]) E) (N (v 462917 4) E)))) (N (N (N (N (u 8296) (k 557113 [12,3,5,7,4] [1138757,1146981,827749])) (N (u 299081) E)) (N (N (k 4203 [0,4,5] [213284,352820,356932]) E) (N (z 430152) E))) (N (N (N (f 102426 [221520]) E) (N (v 364592 14) E)) (N (N (w 230247 [8,7]) E) (N (v 495664 10) E))))) (N (N (N (N (N (y 8290 [57372,33064]) (k 536665 [19,7,4] [1106005])) (N (v 245845 6) E)) (N (N (u 147560) E) (N (v 414560 3) E))) (N (N (N (z 78437) E) (N (k 246373 [0,5,2,7,12,9] [696628,713029,107077,565833,385861]) E)) (N (N (v 217136 12) E) (N (w 426087 [7,16,10,11]) E)))) (N (N (N (N (z 53556) (k 557143 [3,0,12,19,17] [1171536,1179736])) (N (k 245865 [9,0,4,7,3] [647237,655461,663909,377413]) E)) (N (N (v 180329 4) E) (N (u 446549) E))) (N (N (N (u 102488) E) (N (v 380976 16) E)) (N (N (v 249928 2) E) (N (u 512101) E))))))) (N (N (N (N (N (N (N (k 23 [6,7,0,2,4,5] [16453,131143,155721,188491,204901,295015,319593,344171,360773,409957,365125,414309,435303]) (k 583 [6,11,0,2] [1066343])) (N (k 245817 [9,6,7,0,4] [540773,549477,566117]) E)) (N (N (j 102741 2 [278836,282948]) E) (N (v 393280 3) E))) (N (N (N (z 65648) (v 557145 7)) (N (v 319845 1) E)) (N (N (y 181093 [393524]) E) (N (k 426073 [10,2,4,7,3] [933957,942181,950629,418373]) E)))) (N (N (N (N (u 32808) (w 557111 [5,0,12,10,9])) (N (k 245861 [7,3,4,5,10,9,12] [65605,606281,614501,622697,369221]) E)) (N (N (v 160341 2) E) (N (k 426039 [4,14,10] [868424,876640,884840]) E))) (N (N (N (k 4197 [6,7,0,2,4,5,14,10] [213018,229456,237650,65621,245848,254041,262234,270677,287317,291669]) E) (N (k 246631 [4,5] [737328,65588,745528,753724,286788,127284,401732,713300]) E)) (N (N (w 230215 [8,7]) E) (N (k 427367 [6,1,2] [999472,1007672,950588]) E))))) (N (N (N (N (N (z 8288) (u 540757)) (N (f 267109 [557380]) E)) (N (N (v 147552 2) E) (N (j 409672 1 [836448]) E))) (N (N (N (z 77929) E) (N (k 336180 [0,2,7] [278837,688441,115253,557625]) E)) (N (N (k 5223 [0,2,4,5] [442416,65588,450616,172092,368708,372820,106804,385348,389460,270900,426564,430676]) E) (N (v 426085 6) E)))) (N (N (N (N (f 8549 [114996,119108]) (v 557141 7)) (N (w 245863 [0,12,10,9]) E)) (N (N (v 180325 4) E) (N (k 426041 [10,6,7,2,4] [901205,680533,910165]) E))) (N (N (N (y 102482 [73756,221480]) E) (N (k 247143 [6,0,1] [770096,778296,664124]) E)) (N (N (k 245815 [4,13,9] [507976,516208,524408]) E) (N (k 507977 [17,7,0] [1032293]) E)))))) (N (N (N (N (N (N (j 8218 2 [33120]) (k 599 [7,0,2,3,4] [1081417,1097817,767063])) (N (y 266853 [557380]) E)) (N (N (j 102997 2 [278836]) E) (N (z 402519) E))) (N (N (N (k 4169 [2,6,7,0,4,5] [24598,163941,172137,180837,185189]) E) (N (y 335945 [688708]) E)) (N (N (v 204889 4) E) (N (v 462949 6) E)))) (N (N (N (N (u 8297) (u 565317)) (N (v 299109 6) E)) (N (N (u 172596) E) (N (v 430176 2) E))) (N (N (N (u 106832) E) (N (v 364600 14) E)) (N (N (w 230503 [8,7,0]) E) (N (v 495672 15) E))))) (N (N (N (N (N (u 24604) (u 548949)) (N (w 245847 [7,15,6,11]) E)) (N (N (k 4201 [0,6,7,2,4,5] [213014,327765,172121,336469,340821]) E) (N (v 410480 3) E))) (N (N (N (k 4171 [2,4,5] [24868,197172,201284]) E) (N (y 352581 [720944,278596,119092,393540]) E)) (N (N (v 217144 12) E) (N (v 426089 6) E)))) (N (N (N (N (f 8805 [114996]) (v 581712 5)) (N (v 319557 4) E)) (N (N (y 180581 [278836,393540]) E) (N (j 447317 2 [688452]) E))) (N (N (N (u 102489) E) (N (v 380984 16) E)) (N (N (z 249968) E) (N (k 508009 [7,17,4] [1048661]) E))))))))
noncomputable def x246 : Nat → Bool := checkNode m246Mask m246Goal (Nat.sub (Nat.shiftLeft 1 m246Pairs.length) 1) symMain 146 9 m246Ws m246D 8 m246Cuts 5
noncomputable def y246 : Nat → Nat → Bool := checkRange m246Mask m246Goal (Nat.sub (Nat.shiftLeft 1 m246Pairs.length) 1) symMain 146 9 m246Ws m246D 8 m246Cuts 5
theorem s246 (s n : Nat) (h : y246 s n = true) : ac x246 s n := cr_sound h
theorem q15 : ac x246 0 40 := s246 0 40 (by decide +kernel)
theorem q16 : ac x246 40 40 := s246 40 40 (by decide +kernel)
theorem q17 : ac x246 80 40 := s246 80 40 (by decide +kernel)
theorem q18 : ac x246 120 26 := s246 120 26 (by decide +kernel)
theorem m246All : ac x246 0 146 := (tm 0 80 66 (tm 0 40 40 q15 q16) (tm 80 40 26 q17 q18))
theorem m246Low : LowerM m246Mask m246Raw m246Goal 10 :=
  dagLow (pairs := m246Pairs) (sym := symMain) (ncuts := 20) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m246Ess m246CutValid m246All (by decide +kernel)

def m249Mask : Word := 0x303030303030303030303030303030303030303030303030303030303030303
def m249Goal : Word := Nat.land gAll m249Mask
def m249Raw : List Word := mkR m249Mask [v0,v3,v4,v5,v6,v7]
theorem m249Ess : ∀ a ∈ m249Raw, Essential m249Mask m249Goal m249Raw a :=
  checkAllEss_sound (ps := [2057,265,273,32928,321,385]) (by decide +kernel)
theorem m249Low : LowerM m249Mask m249Raw m249Goal 9 :=
  liftLow (dom := 0x3030303000000000303030300000000030303030000000003030303) 16270848 m217Low m249Ess (by decide +kernel) (by decide +kernel)

def m127Mask : Word := 0xffffffffffffffffffffffffffffffff
def m127Goal : Word := Nat.land gAll m127Mask
def m127Raw : List Word := mkR m127Mask [v0,v1,v2,v3,v4,v5,v6]
theorem m127Ess : ∀ a ∈ m127Raw, Essential m127Mask m127Goal m127Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,321]) (by decide +kernel)
def m127Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,24865,24928,25154,25184,25696,28720,28768,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,18183,19274,19982,20042,23114,23580,26984,27210,27240,27752,30776,30824,2307,2309,2314,2316,2328,2337,2344,2376,4355,4357,4372,4376,4385,4400,4611,4614,4618,4628,4632,4656,4674,8707,8710,8714,8737,8744,8752,8770,8800,9221,9222,9228,9236,9249,9256,9264,9312,16643,16645,16673,16706]
def m127Ws : List Wire := mkWs m127Raw [(0xf000001fff8218a783027186f27f0c0f,0x711090299180082281005082f0350405),(0xfffe0000cf97b8c11b2193d9300f0,0x902478e08284f86b8411b00914930050),(0xff0000000116e7f902dcc61c1ec3300,0x20f0214305012a7f8024c42141ec1100),(0x7ffff7dd80ce007e0e0f0003,0x24142846e7ff7dd00ce007c0e0a0002),(0xfff8061879e60f00f800ff0c03c,0x48207160821079420600f000b404028),(0xffff000007e07e07f000ffff00003c0,0x4f0b8418307a05807b000bd6a0000280),(0xf0000000007ff8007ffff0000000fc00,0x880c0800405ed0005e9b20000000a800)]
def m127Cuts : BTree CutSpec := (N (N (N (N (N (N (mc m127Raw 0xff00ff00ff00ff00ff00ff00ff00ff 9) (mc m127Raw 0xff00ff0000000000ff00ff 6)) (N (mc m127Raw 0xf000f000f000f000f000f000f000f 7) E)) (N (N (mc m127Raw 0x11001100110011001100110011001100 4) E) (N (mc m127Raw 0xf000f00000000000f000f 5) E))) (N (N (N (mc m127Raw 0x55005500550055005500550055005500 7) E) (N (mc m127Raw 0x55000000550000005500000055 4) E)) (N (N (mc m127Raw 0xf0f0f0f0 4) E) (N (mc m127Raw 0xf000f000f000f 4) E)))) (N (N (N (N (mc m127Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 8) E) (N (mc m127Raw 0x5500550055005500 4) E)) (N (N (mc m127Raw 0xffff0000ffff0000ffff0000ffff 7) E) (N (mc m127Raw 0x33330000000000003333 4) E))) (N (N (N (mc m127Raw 0xcccc000000000000cccc 4) E) (N (mc m127Raw 0x33000000330000003300000033 4) E)) (N (N (mc m127Raw 0x333333330000000033333333 6) E) (N (mc m127Raw 0xff000000ff000000ff000000ff 5) E))))) (N (N (N (N (N (mc m127Raw 0xffffffff00000000ffffffff 8) E) (N (mc m127Raw 0x30303030000000003030303 5) E)) (N (N (mc m127Raw 0x5500000055000000550000005500 4) E) (N (mc m127Raw 0x550055005500550055005500550055 7) E))) (N (N (N (mc m127Raw 0x330033003300330033003300330033 7) E) (N (mc m127Raw 0x550055000000000055005500 4) E)) (N (N (mc m127Raw 0x3333000033330000333300003333 5) E) (N (mc m127Raw 0xf0f0f0f0f0f0f0f 5) E)))) (N (N (N (N (mc m127Raw 0x33333333333333333333333333333333 8) E) (N (mc m127Raw 0x5000500050005000500050005000500 4) E)) (N (N (mc m127Raw 0x30003000000000003000300000000 4) E) (N (mc m127Raw 0x55005500550055 4) E))) (N (N (N (mc m127Raw 0x3030303000000000303030300000000 5) E) (N (mc m127Raw 0x3300330000000000330033 5) E)) (N (N (mc m127Raw 0xffffffffffffffff 7) E) (N (mc m127Raw 0xff00ff00ff00ff 5) E))))))
theorem m127CutValid : ∀ ci < 33, ValidCut m127Mask m127Raw m127Goal (btreeGet ⟨0,0,[]⟩ 6 m127Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1753224 m119Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 1754632 m123Low (by decide +kernel)
  · exact cv 1238544 m123Low (by decide +kernel)
  · exact cv 135970952 m118Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 134766944 m86Low (by decide +kernel)
  · exact cv 134762888 m86Low (by decide +kernel)
  · exact cv 190032 m63Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 65907 m55Low (by decide +kernel)
  · exact cv 24788 m87Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 1590784 m89Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 135270824 m86Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 549184 m86Low (by decide +kernel)
  · exact cv 1049606 m89Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 1753224 m118Low (by decide +kernel)
  · exact cv 24784 m86Low (by decide +kernel)
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 33123 m55Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
noncomputable def m127D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (k 0 [0,1,2,3,4] [8215,12327,491578,1589319,2474063,2687063,1593447,2478191,2810151,3080519,3424591,3596631,3670375,4047215,3674695,4051535,3600983,3084903,3428975,4195141,4199269,4457559,4613211,4703331,4818023,5129323,5133423,4461927,4617583]) (k 837 [4,16,1,3,10] [4202601,3277111,3854663,4284759,4325735,4358511,3023687,3605335,4023143,4170607,3626071,3396711,3576943,4384103,4416879])) (N (k 795257 [9,0,15,4,6] [2105365,1970486,2114133]) E)) (N (N (j 487797 2 [1057392]) (v 2564196 4)) (N (v 1540209 15) E))) (N (N (N (u 258160) (w 2355290 [18,10])) (N (v 1302612 4) E)) (N (N (v 766069 7) E) (N (k 359 [11,6,5,4,15,1] [122933,3678265,3727419,2822213,3735625,3768395,3776609,3154021,3784809,3842157,303413,2990405,3228005,1995319,3273287,3850838,3908197,3973735,3998313,332615,1180506,2171751,4007015,4023653]) E)))) (N (N (N (N (v 127036 8) (k 1111 [11,10,4,1] [4464697,4489280,4497480,4538481,4546681,1999159,4284774,4563319,4587903,1319786,2364279,2634623,4388469])) (N (k 796279 [11,4,1] [2367536,2375736,2383984,2392184,2400816,1843772]) E)) (N (N (y 623205 [696644,1262148]) E) (N (v 1696357 12) E))) (N (N (N (u 389172) (v 2408548 4)) (N (v 1437812 4) E)) (N (N (v 901237 7) E) (N (v 1962544 10) E))))) (N (N (N (N (N (v 61513 12) (k 2097511 [4,6,10,16,3,15] [3182693,4333673,4341877,4350073,3879269,4211260,4219454])) (N (v 1097812 4) E)) (N (N (k 246375 [4,7,3,1,15] [987221,1187929,1196129,1089637,1204329,1212525,1048917,1114469,651830,1221221,1237609,770917]) E) (N (w 1540694 [22,6,4,3]) E))) (N (N (N (y 250199 [663632,671832]) (v 2416713 6)) (N (w 1364068 [0,4]) E)) (N (N (v 847952 3) E) (N (j 1892661 6 [3809380]) E)))) (N (N (N (N (v 180284 12) (k 2228607 [6,11] [4595844,4309380,4604768,4522856])) (N (w 1237061 [12,16,4,3,6]) E)) (N (N (u 704597) E) (N (k 1713279 [11,15,10] [3547188,3563636,2941252,3568500]) E))) (N (N (N (j 251247 1 [925748,933948,942148,950348,958564,966764,614972]) (k 2408571 [0,1,7] [5120132,5063044])) (N (v 1495664 1) E)) (N (N (k 950585 [4,15] [1974292]) E) (N (y 2028389 [2064692]) E)))))) (N (N (N (N (N (N (v 24689 15) (u 2121848)) (N (w 795495 [23,4,7]) E)) (N (N (y 532853 [1122336]) E) (N (u 1593702) E))) (N (N (N (u 290837) (v 2351204 4)) (N (k 87 [11,4,1,0] [2695265,2703465,2699377,2707577,2729587,2762359,2786939,2791039]) E)) (N (N (k 794695 [16,4,9,19] [1646648,1654912,1663112]) E) (N (k 1835081 [11,12,4,6] [3743813,3752037,311877,1188954,3761509]) E)))) (N (N (N (N (k 4951 [6,5,4] [335920,344124,352816,90684]) (k 2249071 [0,10] [4530292])) (N (v 1204284 9) E)) (N (N (j 680036 9 [963429]) E) (N (k 1712245 [5,10,7,1,4] [2322501,3481673,3362901,3489881,3498084,3506278,2347333,2625865,3522918,2916949,1156202]) E))) (N (N (N (j 250991 2 [860212,868412,876612,884812]) (v 2519136 3)) (N (y 1470500 [2958176]) E)) (N (N (k 794997 [4,18,9,0] [1908768,1916997,1925193,1933620,1958197,1962294,1966393,1970494,1921621,1929817]) E) (N (k 1835625 [6,15,5] [3719753,1238122]) E))))) (N (N (N (N (N (v 94320 1) (u 2191433)) (N (v 1134652 12) E)) (N (N (k 246383 [18,7,3,1,4] [1253428,1269845,1278053,1286253,1294452,1302652,1311333,779109]) E) (N (v 1658936 29) E))) (N (N (N (u 356373) (k 2408521 [6,5,2,4] [4923461,4931669,4939876,4338534,1500266])) (N (k 1405013 [12,11,6,4,17] [2826313,984154]) E)) (N (N (v 868469 7) E) (N (u 1929508) E)))) (N (N (N (N (v 221244 8) (v 2306148 4)) (N (k 1237621 [4,10,0,18,6] [2564693]) E)) (N (N (u 749636) E) (N (k 1799525 [6,23,4] [3612793]) E))) (N (N (N (w 487509 [7,17]) (v 2568309 7)) (N (k 327 [11,6,5,4,13,1,10] [49205,3088441,2818117,3129417,3145841,3154037,3186809,3219581,278837,3228021,1983031,3269191,3277398,3285623,3302015,365383,1065818,2274167,2585471,3318903,3351679,3392885]) E)) (N (N (w 1011770 [10,4]) E) (N (w 2061669 [18,0]) E))))))) (N (N (N (N (N (N (N (v 12373 2) (k 2101545 [22,18] [4235621])) (N (k 795463 [11,6,4] [2138224,2146424,2155060]) E)) (N (N (v 532593 15) E) (N (u 1577318) E))) (N (N (N (u 270424) (v 2351164 4)) (N (w 1314936 [4,0]) E)) (N (N (k 794681 [9,6,5,2] [1613893,1622133,1630333]) E) (N (w 1839205 [0,4]) E)))) (N (N (N (N (u 139385) (v 2228288 3)) (N (w 1179768 [4,0]) E)) (N (N (v 659569 15) E) (N (v 1716349 15) E))) (N (N (N (u 389236) (v 2502736 3)) (N (j 1446005 2 [2925424]) E)) (N (N (v 794749 15) E) (N (v 1978416 12) E))))) (N (N (N (N (N (v 77893 12) (k 2097519 [18,10,6,3,0,2,4] [4366437,4374645,4309365,4227644])) (N (w 795751 [24,4,7]) E)) (N (N (v 589933 10) E) (N (v 1650804 4) E))) (N (N (N (u 340293) (k 2408519 [5,13,6] [3801144,4890996])) (N (k 1345147 [11,4,20,1] [2793532,2801964]) E)) (N (N (k 794741 [4,0,1,2,3,18,9] [1744938,1753157,1761353,1757269,1765465,1769589,1777785]) E) (N (v 1893222 4) E)))) (N (N (N (N (v 204860 8) (k 2306101 [9,11,4] [2420853,4628605,2437493])) (N (v 1253465 12) E)) (N (N (v 704636 1) E) (N (k 1713525 [9,5,7,1,15,4] [3579944,3522854,3588709,2974565]) E))) (N (N (N (v 458828 10) (w 2568249 [0,4])) (N (v 1512032 1) E)) (N (N (k 795239 [4,6,11] [2007120,2015320]) E) (N (k 2023525 [6,5,12,2,15,4] [2203717,4104292,2228549,1279082]) E)))))) (N (N (N (N (N (N (v 41341 6) (v 2142288 3)) (N (k 795519 [4,5,15] [2203700,2211900,2220100,2228308,2236508,2244740,2252940,2056788]) E)) (N (N (u 565333) E) (N (u 1613897) E))) (N (N (N (j 249967 9 [589844,630836]) (k 1127 [0,15,10,1,2,3,4] [1736757,4825143,4833337,4874299,3153989,4882503,4915273,4948043,3158101,4886615,4919385,4952155,4980836,4989030,5070965,5079159,5103737,5111931,2023733,2089271,2556217,3285319,3912021,3977559,4149593,4325734,4563319,2028085,2093623,2560569,3908165,3973703,4145737,3289687,4330086,4567671,443207,447319,1483626,2761591,3056727,3638391,3642743])) (N (v 1351805 15) E)) (N (N (k 794697 [9,12,3] [1679429]) E) (N (w 1835083 [12,2]) E)))) (N (N (N (N (k 4983 [5,4] [368688,376884,385080,393276,401492]) (w 2273349 [0,4])) (N (w 1204324 [4,0]) E)) (N (N (k 246883 [18,10,4,1,2,3] [1417268,1425476,1433684,1441877,1450076,1437796,1445989,1454188,1458292,1466485,1474684]) E) (N (j 1736806 30 [3514448]) E))) (N (N (N (v 426060 10) (k 2408567 [1,11,12,6] [5087328,5095528,5091440,5099640,5038468])) (N (v 1487984 1) E)) (N (N (k 950580 [4,0,18,9] [1941813,1950009,1946181,1954377]) E) (N (j 2011209 22 [3826236]) E))))) (N (N (N (N (N (w 110965 [6,4]) (w 2207804 [18,0])) (N (v 1155132 9) E)) (N (N (j 622693 4 [786500,803140]) E) (N (v 1675332 6) E))) (N (N (N (u 368744) (k 2408523 [5,6] [4956276,4964724])) (N (k 1405032 [11,4,12,6] [1008458,2147159,2151271,2860117,2864229,2876775]) E)) (N (N (k 794745 [9,2,0,1,3,4] [1810453,1818693,1826901,1835125,1843573,1859961]) E) (N (v 1925741 10) E)))) (N (N (N (N (k 58 [4,1,2,3] [499781,503909,975415,1065543,1131087,1172055,1180263,1245807,1184583,1250127,1176407,1069927,1135471,1320023,1360987,1410147,1483879,1533035,1537135,1324391,1365359]) (v 2330742 30)) (N (v 1290296 29) E)) (N (N (j 765989 4 [589876,725300,721460]) E) (N (k 1799799 [23,7] [3645572]) E))) (N (N (N (j 487773 7 [1024068,1040992]) (v 2596981 7)) (N (v 1544317 15) E)) (N (N (u 1028164) E) (N (u 2076752) E)))))))) (N (N (N (N (N (N (N (N (w 4149 [12,11,4,6,17]) (k 2101541 [20,15] [3871061])) (N (v 1049173 12) E)) (N (N (k 246343 [4,7,10,1,3] [983125,1073241,1081457,1089653,1097849,1106045,1114485,639542,848757]) (k 2564396 [12,22,18,10,15,6,0,2] [1581658,2802279])) (N (w 1577033 [0,4]) E))) (N (N (N (k 249943 [1,21] [548944,557144]) (k 2351157 [18,10,12,0,2,3,6,4] [4743285,1425768,2744693])) (N (v 1314872 12) E)) (N (N (k 71 [4,9,1,2,3,0,10] [49205,1597495,1605689,127045,1638471,1671241,1687653,1695847,1720425,1728625,1736821,1785975,1802361,1867901,1876095,221493,1900917,1983031,1991239,1999463,2024053,2089591,2097785,2122367,2130759,2163559,2171767,2196351,2262119,2270327,2311295,2360951,2410111]) E) (N (v 1839173 12) E)))) (N (N (N (N (k 4693 [6,4,0] [286793,295033,205433]) (w 2232437 [0,4])) (N (v 1179704 12) E)) (N (N (v 659536 3) E) (N (k 335 [5,10,7,1,4] [3432501,3448901,3465300,3473525,3530877,2892101,414535,1131354,2315127,2610047,3355767,3540095,3573109]) E))) (N (N (N (u 389188) (k 2494528 [4,15,10,1,2,3] [4899141,4972873,4903253,4976985,5005669,5030249,3928661,4166233,3924805,4162377])) (N (y 1445957 [2909024]) E)) (N (N (v 921696 2) E) (N (v 1954080 10) E))))) (N (N (N (N (N (w 61544 [4,0]) (v 2162805 7)) (N (w 1097860 [4,0]) E)) (N (N (v 589921 10) E) (N (v 1642612 4) E))) (N (N (N (u 327768) (v 2416761 7)) (N (v 1380400 21) E)) (N (N (v 794729 7) E) (N (j 1892708 4 [3825721]) E)))) (N (N (N (N (k 4991 [11,18,4] [417844,426044,434260,254292]) (v 2294624 3)) (N (k 1237109 [4,6,0,2,3,10] [2515029,2523225,2531445,2539641]) E)) (N (N (w 704628 [18,10]) E) (N (v 1773668 4) E))) (N (N (N (v 458812 9) (k 1131 [10,0,6,2,3,15,4,1] [5136421,5193781,5218373,5226581,5242980,5251189,5259564,2097461,4002133,2126391,3306071,4362854,4592247,471895,1532778,2786167,3659127])) (N (y 1511545 [3040112,2868088]) E)) (N (N (w 795191 [4,22,6]) E) (N (u 2037093) E)))))) (N (N (N (N (N (N (k 4185 [8,6,0,4] [90437,98685]) (u 2134120)) (N (v 1085488 9) E)) (N (N (k 246351 [9,3,7,1,4] [1138740,1146965,1155189,1163389,1016149,856949]) E) (N (k 1540469 [6,5,15] [3235872,3244105,3252582,3121737,3261017,1115242]) E))) (N (N (N (v 299104 2) (v 2351221 7)) (N (k 1343593 [21,11,4] [2711669,2719869]) E)) (N (N (w 819328 [4,0]) E) (N (v 1867877 2) E)))) (N (N (N (N (v 163900 12) (v 2228337 15)) (N (v 1204308 4) E)) (N (N (j 680053 4 [929860,946500]) E) (N (v 1736793 12) E))) (N (N (N (v 426044 9) (j 2494841 32 [5030480])) (N (v 1471600 1) E)) (N (N (v 950341 6) E) (N (j 2002992 12 [3965508]) E))))) (N (N (N (N (N (v 4221 15) (k 2191480 [4,0] [4260414])) (N (k 795775 [4,16,15] [2318388,2326588,2334788,2342996,2351196]) E)) (N (N (u 627285) E) (N (v 1675316 6) E))) (N (N (N (y 250695 [745568,753768]) (v 2457685 12)) (N (v 1405021 10) E)) (N (N (k 794743 [4,20,18,0] [1794104]) E) (N (v 1937712 10) E)))) (N (N (N (N (v 233532 8) (w 2330697 [0,4])) (N (w 1238119 [4,24,7]) E)) (N (N (v 741497 7) E) (N (k 1799541 [11,4,14] [3629177]) E))) (N (N (N (v 487520 1) (k 2564149 [9,25,6,2,3,4] [1810485,5202005,5210229,1888565])) (N (v 1544261 12) E)) (N (N (v 1019952 9) E) (N (k 2024037 [6,0,12,13] [4153446,2056517,4063813,1311850]) E))))))) (N (N (N (N (N (N (N (k 4181 [6,4,5,2] [57417,65649,73849]) (y 2101607 [4251760,4259960])) (N (w 1065080 [4,0]) E)) (N (N (u 532601) E) (N (w 1593413 [0,4]) E))) (N (N (N (w 249959 [9,18]) (k 2351173 [22,6,15] [1442922])) (N (w 1331252 [0,4]) E)) (N (N (u 802933) E) (N (u 1839977) E)))) (N (N (N (N (u 151625) (f 2249063 [4513908])) (N (k 796287 [18,25,1,4] [2416692,2424892,2433092,2441300,2449500,2457700,2465900,1860156]) E)) (N (N (k 246875 [9,7,1,4] [1368116,1376356,1384556,1392757,1400957,922485]) E) (N (w 1724489 [0,4]) E))) (N (N (N (u 250967) (u 2498921)) (N (v 1446496 1) E)) (N (N (v 938036 4) E) (N (v 1986676 4) E))))) (N (N (N (N (N (v 78437 4) (v 2179189 7)) (N (v 1134640 29) E)) (N (N (v 610592 10) E) (N (v 1658928 29) E))) (N (N (N (w 250215 [9,4]) (y 2445392 [4907320])) (N (w 1392940 [0,4]) E)) (N (N (v 868421 6) E) (N (k 1835606 [5,4,7,12,15] [3858537,3875173,3891809,3179109,3834473,3900013,3253093]) E)))) (N (N (N (N (k 5495 [6,5,4] [450608,458812,229700]) (k 2306132 [11,10,4,12] [1377114,2462567,4445541])) (N (v 1253497 7) E)) (N (N (w 741430 [18,9]) E) (N (v 1786469 12) E))) (N (N (N (v 458860 3) (k 2568294 [0,31] [5169216])) (N (v 1527924 4) E)) (N (N (w 999512 [4,0]) E) (N (v 2023533 10) E)))))) (N (N (N (N (N (N (v 4209 15) (k 2142589 [6,0] [4235596,4317792])) (N (v 1097788 9) E)) (N (N (v 565373 15) E) (N (v 1614425 12) E))) (N (N (N (u 250167) (k 2408505 [4,0,1,2,3,15,10] [1744918,4841541,4849737,4845653,4853849,4857973,4866169,1794341,1798453])) (N (v 1364028 21) E)) (N (N (v 794725 7) E) (N (k 1835113 [6,5,4,2] [2187337,3792985,3801397,3817828,3834726,1205354]) E)))) (N (N (N (N (v 180276 12) (v 2281604 4)) (N (k 79 [4,10,6,2,3,0,1] [2482229,2490437,2498661,2506869,2547837,2556533,2573415,2581623,2606207,2631287,2664063]) E)) (N (N (w 704580 [18,10]) E) (N (z 1737062) E))) (N (N (N (v 446576 2) (f 2539624 [5054836])) (N (y 1495113 [3007344]) E)) (N (N (v 966969 6) E) (N (k 367 [15,11,5,12,4,1,6] [4055093,4071493,4087892,4096101,4112493,4120692,4137084,4145765,1246042,2196327,4171109]) E))))) (N (N (N (N (N (v 118880 1) (w 2207844 [18,0])) (N (v 1155156 4) E)) (N (N (j 622708 18 [820069]) E) (N (k 1541493 [4,11,10,1,15,3] [3399753,3178790,3211566,3252534,3408485,3416681]) E))) (N (N (N (y 250727 [688708]) (j 2474356 5 [4972624])) (N (u 1429609) E)) (N (N (v 901189 6) E) (N (j 1953894 3 [3866664,3924048,3940912]) E)))) (N (N (N (N (w 249911 [3,8]) (k 1123 [15,6,0,10,2,3,4,12,1] [4710452,4735029,4751420,4759620,4767813,4776012,4763732,4771925,4780124,4784228,4792436,4800629,4808828,1409898,2728823])) (N (k 1238143 [18,16,10,4] [2613300,2621524]) E)) (N (N (u 766037) E) (N (k 1799807 [23,6] [3661956]) E))) (N (N (N (v 512592 1) (k 2564181 [12,16,3,10,4,6] [5234761,1565802])) (N (k 1540169 [22,12,4] [3137605,287301,1074266]) E)) (N (N (v 1012313 12) E) (N (w 2084904 [20,15]) E))))))))) (N (N (N (N (N (N (N (N (N (k 23 [5,6,4,7,1,8] [16437,24633,41041,49237,82009,106589,114801,122997,155769,213117,221525,238133,279125,303733,328535,361335,410495,443767,468351]) (k 2097257 [22,4,18,16,1,0] [4210981,4219175,4227369,4030791,3404119,4243815,3863127,4268647,3032151,3613799,3634535])) (N (j 1048597 4 [1974580]) E)) (N (N (v 524912 1) (v 2564213 7)) (N (k 1540213 [6,5,2,4,13] [3162185,3170393,3178854,1090666]) E))) (N (N (N (u 258168) (w 2355303 [0,18])) (N (k 1238647 [11,4,1,10] [2637880,2646128,2654328]) E)) (N (N (w 766252 [18,10]) E) (N (k 1835065 [5,4,6,7,1] [3686469,3694665,3702885,2187369,1650997,2998853,3244645,3711845,3720041]) E)))) (N (N (N (N (v 127600 1) (k 2228281 [6,11,4] [4472949,4481149])) (N (v 1179696 12) E)) (N (N (k 246871 [11,4,1] [1327184,1335384,1343601,1351801,655670,897909]) E) (N (v 1696361 12) E))) (N (N (N (v 389180 9) (k 2408550 [4,15,10,16,1,3] [4214824,4223017,4210744,4218937,4997184,4890965,4964697,4895077,4968809,5038453,5063033,3920485,4158057,3916629,4154201])) (N (k 1405277 [6,11] [2900037,2916469,2933344,258885,2941821,1016922,2975093]) E)) (N (N (j 901493 1 [1851488]) E) (N (v 1958448 10) E))))) (N (N (N (N (N (v 61536 10) (v 2162793 16)) (N (v 1097820 10) E)) (N (N (u 589913) E) (N (k 1540727 [5,6,13] [3293300]) E))) (N (N (N (v 327760 3) (v 2416757 7)) (N (k 1345143 [11,4,0,1] [2768944,2777148]) E)) (N (N (w 847960 [4,0]) E) (N (v 1900644 4) E)))) (N (N (N (N (v 180308 6) (v 2293892 4)) (N (v 1237093 7) E)) (N (N (v 704604 3) E) (N (f 1769524 [3555428,2949428]) E))) (N (N (N (u 458804) (v 2556036 4)) (N (k 1406037 [6,11,4] [3031161,3048032,2859624,2978941]) E)) (N (N (v 983060 4) E) (N (k 2023493 [28,12] [1270874,4080997]) E)))))) (N (N (N (N (N (N (w 24697 [0,4]) (k 2101863 [22,0] [4276328,4235596])) (N (k 795511 [6,5,4] [2179120,2187320,2040404]) E)) (N (N (v 557088 15) E) (N (v 1540221 15) E))) (N (N (N (y 291173 [606304]) (k 2351220 [11,15,10] [1459050])) (N (v 1343585 10) E)) (N (N (w 819256 [4,9]) E) (N (w 1867845 [0,4]) E)))) (N (N (N (N (v 163888 8) (v 2261108 4)) (N (v 1204292 18) E)) (N (N (v 680044 2) E) (N (w 1736777 [0,4]) E))) (N (N (N (u 426036) (y 2519144 [5022288])) (N (v 1475424 1) E)) (N (N (v 950304 15) E) (N (k 1836135 [12,6] [4014128,3957332]) E))))) (N (N (N (N (N (u 78693) (v 2191472 2)) (N (v 1134900 12) E)) (N (N (j 622644 18 [786517,1262165]) E) (N (k 1541247 [11,15] [3358772,3366972,3375172,3383412]) E))) (N (N (N (j 250223 9 [720916,589876]) (w 2457669 [0,4])) (N (w 1409097 [0,4]) E)) (N (N (v 868473 7) E) (N (j 1925477 3 [3866924,3883312]) E)))) (N (N (N (N (k 5503 [6,5,4,15] [475196,483632,98620]) (k 2306165 [11,10,4] [2420805,4669513,4677748,4685942,2445637,2683209,4436342,1393786])) (N (v 1278549 12) E)) (N (N (v 741493 7) E) (N (u 1802361) E))) (N (N (N (v 487517 10) (v 2568313 7)) (N (k 1540153 [22,4,7,0,1] [3096645,3104885,3113085,3121781]) E)) (N (N (j 1012037 6 [2048048]) E) (N (v 2023548 1) E))))))) (N (N (N (N (N (N (N (v 4177 10) (v 2113893 22)) (N (v 1065072 1) E)) (N (N (u 532597) E) (N (k 1540217 [22,7,6,4] [3194949,3203157,3211622,295493,1098858]) E))) (N (N (N (w 249957 [18,9]) (k 2351172 [12,22,18,10,6,0,2,15] [1434458,2753383])) (N (k 1238655 [18,6,0,4,26] [2670644,2678868]) E)) (N (N (v 802885 12) E) (N (v 1839973 6) E)))) (N (N (N (N (k 4725 [6,4,5,15] [311369,320073]) (k 2228296 [11,10,4] [2015543,4301142,4505959,4522351,1336154,2397031,2659183,4412773])) (N (v 1180208 15) E)) (N (N (u 659577) E) (N (k 1712197 [12,16,10,4] [3457097,1147994]) E))) (N (N (N (v 389244 1) (u 2502744)) (N (v 1459056 1) E)) (N (N (k 794751 [4,20,0] [1810452,1884212,1892420]) E) (N (k 1835623 [5,6,15] [3981428,3875188,3990064,3801660]) E))))) (N (N (N (N (N (w 77925 [0,4]) (u 2179173)) (N (k 795767 [16,4] [2277424,1757236,2285624,2293820,2302260]) E)) (N (N (j 590437 3 [1229088,688452]) E) (N (y 1541239 [3326000,3334196,3342392,3346492]) E))) (N (N (N (u 340297) (y 2441588 [4898896,3809592])) (N (v 1392700 21) E)) (N (N (w 868394 [0,18,9]) E) (N (v 1835117 10) E)))) (N (N (N (N (v 204884 6) (v 2310269 15)) (N (v 1253493 7) E)) (N (N (k 246887 [4,15,10,1,2,3] [565300,1490998,1089621,1499225,1093733,1503337,1515637,1523833,680244,704822,1225061,1315177,684596,709174,1221205,1311321]) E) (N (w 1785896 [27,10]) E))) (N (N (N (u 458852) (v 2568292 4)) (N (k 1406327 [11,12,6] [3063924,3072896,2876296]) E)) (N (N (v 999504 3) E) (N (v 2048100 4) E)))))) (N (N (N (N (N (N (v 4189 10) (k 2142296 [4,0] [4277097])) (N (w 1097780 [0,4]) E)) (N (N (j 565365 4 [864324,880964]) E) (N (v 1614182 15) E))) (N (N (N (u 311348) (k 2408503 [4,0,18,9] [1745192])) (N (k 1345139 [11,4,27,1] [2736188,2744388,2752612,2756724]) E)) (N (N (v 835653 6) E) (N (v 1835105 10) E)))) (N (N (N (N (v 180272 29) (k 2228599 [6,11,1] [4571268,4580192,4506472])) (N (v 1204332 3) E)) (N (N (w 704564 [18,10]) E) (N (u 1753168) E))) (N (N (N (y 251239 [901232,909432,598588]) (v 2539616 3)) (N (k 1405301 [6,11,12] [2998345,3015280,1049690]) E)) (N (N (v 966965 6) E) (N (v 2011424 10) E))))) (N (N (N (N (N (k 4661 [6,11,4] [245856,254333,189049]) (z 2207813)) (N (v 1155140 18) E)) (N (N (v 622701 10) E) (N (v 1675380 4) E))) (N (N (N (u 250711) (v 2474100 4)) (N (k 1426517 [4,0] [2867305]) E)) (N (N (w 901141 [0,4]) E) (N (k 1835621 [6,5,15] [3915878,3948832,2040133,3957077,3711561,1221738]) E)))) (N (N (N (N (k 245829 [9,4,1,2,3] [507959,516167,540759,565349,573543,581737,622703,639287,647495,655703,680293,704871,713065,729455,738119,762711,770919,779119,836695,844903,853103,894311,918895]) (v 2306173 15)) (N (v 1290548 12) E)) (N (N (j 766004 9 [589861]) E) (N (v 1818756 4) E))) (N (N (N (y 507972 [1032784]) (k 2564165 [22,6] [4371302,1557610])) (N (u 1544821) E)) (N (N (v 1012309 12) E) (N (k 2024805 [18,6,2,3,4] [4177960,4080229,4129396,4186748]) E)))))))) (N (N (N (N (N (N (N (N (k 4153 [8,12,0,6] [32853]) (w 2101543 [15,0])) (N (k 795263 [4,20,0] [2105364,1810484,1884228,1966660]) E)) (N (N (u 532569) E) (N (v 1577049 12) E))) (N (N (N (v 270416 3) (v 2367605 7)) (N (v 1314928 2) E)) (N (N (w 794679 [5,4,13,6,8]) E) (N (v 1839177 12) E)))) (N (N (N (N (u 139337) (v 2232445 15)) (N (v 1179760 2) E)) (N (N (j 659544 4 [672054,914277]) E) (N (k 1712181 [9,5,1,7,4] [421957,2322549,3440765,2339189,2900549]) E))) (N (N (N (v 389196 10) (y 2498917 [5013584,5021784,5017696,5025896])) (N (v 1450848 1) E)) (N (N (u 901497) E) (N (j 1954133 12 [3964976]) E))))) (N (N (N (N (N (k 4217 [8,0,6,7,1,4] [163909,172133,180837,189253,205669]) (v 2162809 7)) (N (v 1097868 1) E)) (N (N (v 589929 4) E) (N (k 1540735 [22,6] [3309684]) E))) (N (N (N (k 250213 [9,4] [688453,696649]) (k 2408507 [4,0,15,10] [1745188,2032180,2036292])) (N (v 1380412 21) E)) (N (N (v 794737 15) E) (N (u 1908793) E)))) (N (N (N (N (v 204852 6) (k 1115 [11,10,4,0,1] [4620341,4636756,4644956,4653156,4661365,4694141,1360746,2413431,2667391,4421237])) (N (v 1253461 12) E)) (N (N (v 704629 7) E) (N (v 1769588 4) E))) (N (N (N (u 458820) (k 2564133 [0,12,6,2,3,15,10,4] [1810485,5144633,5152868,5161062,5177461,5185657,2109749,2105909,1540970])) (N (v 1516400 1) E)) (N (N (k 795207 [4,16,9] [1646664]) E) (N (v 2023508 4) E)))))) (N (N (N (N (N (N (v 41285 2) (k 2097495 [11,6,4,1] [4292688,4300888,4309373,4268921])) (N (w 1085496 [4,0]) E)) (N (N (k 565300 [9,1,3] [864357,1024325]) E) (N (v 1613856 15) E))) (N (N (N (u 291177) (v 2351228 1)) (N (w 1351797 [4,0]) E)) (N (N (w 819336 [4,0]) E) (N (u 1869157) E)))) (N (N (N (N (v 164400 10) (k 2228345 [6,11,4] [4554821,4395382,1352826])) (N (v 1204316 10) E)) (N (N (v 680061 15) E) (N (v 1736804 4) E))) (N (N (N (u 426052) (v 2408565 7)) (N (j 1447285 7 [2983024]) E)) (N (N (v 950345 6) E) (N (k 1836389 [6,4,3,2] [4030537,4038944,3817772,3760745]) E))))) (N (N (N (N (N (k 4437 [6,5,4] [229749,180857]) (k 2098543 [18,11,1,10,4] [4423740,4431941,4440164,4448364])) (N (w 1155124 [0,4]) E)) (N (N (u 622677) E) (N (v 1675324 13) E))) (N (N (N (v 368736 1) (v 2457700 4)) (N (v 1405024 1) E)) (N (N (w 892984 [0,4,9]) E) (N (v 1925729 10) E)))) (N (N (N (N (v 233776 10) (v 2330740 4)) (N (k 1238135 [4,10,16] [2514996,2588728,2597172]) E)) (N (N (k 246891 [9,1,2,3,15,4] [1540133,1548340,1556565,1564773,1572981,1581356,713012,1241445,733750]) E) (N (u 1810553) E))) (N (N (N (j 487528 4 [754517,758629]) (v 2596949 12)) (N (w 1544309 [0,4]) E)) (N (N (y 1012041 [2064452]) E) (N (k 2072678 [31,22] [4161616]) E))))))) (N (N (N (N (N (N (N (v 24649 12) (v 2121840 2)) (N (v 1065524 12) E)) (N (N (v 532605 15) E) (N (v 1593429 12) E))) (N (N (N (k 249961 [9,2] [589845,598373,614761]) (v 2351180 3)) (N (v 1331284 4) E)) (N (N (v 802941 15) E) (N (w 1835067 [4,6,0]) E)))) (N (N (N (N (v 152137 12) (v 2252916 4)) (N (w 1204276 [18,0]) E)) (N (N (j 679988 9 [929893]) E) (N (v 1712212 4) E))) (N (N (N (u 250983) (y 2494837 [5046368,5054568,5050480,5058680,5005904])) (N (y 1446781 [2949156,2966640]) E)) (N (N (v 938052 4) E) (N (v 1987120 10) E))))) (N (N (N (N (N (j 78661 2 [196720]) (k 2098535 [11,4,1,10] [4390985,4399216,4407416,4244030])) (N (v 1134648 29) E)) (N (N (u 590441) E) (N (v 1658932 12) E))) (N (N (N (j 250217 9 [720917]) (u 2449720)) (N (k 295 [11,4,12,6] [16437,2818133,2834525,2842720,2850920,2822261,2838653,237877,2892125,2990453,242229,2994773,2896509,975690,2130775,2134903,3023957,3028085,3057015]) E)) (N (N (v 868425 6) E) (N (j 1925225 3 [3866916]) E)))) (N (N (N (N (v 221232 8) (v 2306140 2)) (N (v 1237117 15) E)) (N (N (j 741465 4 [1507396]) E) (N (k 343 [11,14,4,6] [1172314,2163559,2265975,2577279,3605861,3622261,3638903,3655295]) E))) (N (N (N (k 246327 [11,4] [983125,991325,999520,1007720,987253,995453,1016157,1048949,1053269,1020541,738133,742261]) (u 2580544)) (N (v 1528704 1) E)) (N (N (k 795253 [4,9,0,15,10] [2031674,1933620,1962294,2040133,2056521,2073173,2081369,230213]) E) (N (k 2023540 [11,15,4,6] [1295194,2245479,4130149]) E)))))) (N (N (N (N (N (N (k 4213 [6,4,5,2,8] [131145,139360,147560]) (v 2155104 3)) (N (j 1097796 18 [2064964]) E)) (N (N (k 246359 [11,14,4] [762725,840565]) E) (N (w 1540679 [7,13,6]) E))) (N (N (N (u 250183) (v 2416709 6)) (N (w 1364036 [18,0]) E)) (N (N (k 794727 [4,20,6,0,21] [1704016,1712216]) E) (N (v 1892441 12) E)))) (N (N (N (N (v 180280 29) (v 2282336 3)) (N (w 1237045 [22,6,4]) E)) (N (N (w 704596 [9,15]) E) (N (v 1712253 15) E))) (N (N (N (u 446584) (v 2408569 7)) (N (v 1500016 1) E)) (N (N (w 950581 [9,0,4]) E) (N (k 2023477 [18,5,12,7,4,6] [2203749,2220389,4064101]) E))))) (N (N (N (N (N (j 119165 7 [262204,270960]) (v 2207852 3)) (N (v 1155164 10) E)) (N (N (v 622716 1) E) (N (u 1695817) E))) (N (N (N (j 250735 3 [786484,794684,802884,811084,819316,827516,696900]) (u 2482256)) (N (f 1426791 [2883700]) E)) (N (N (v 901205 12) E) (N (j 1957968 3 [3932720]) E)))) (N (N (N (N (k 249927 [2,19] [524400,532600]) (k 2351156 [12,22,18,10,15,6,0,2] [4718682,4726887])) (N (w 1302580 [0,4]) E)) (N (N (u 766053) E) (N (v 1826948 4) E))) (N (N (N (v 508512 1) (w 2613321 [0,4])) (N (w 1564741 [0,4]) E)) (N (N (k 795255 [4,20,0,15,10] [1794120,1958468]) E) (N (v 2085500 1) E))))))))))
noncomputable def x127 : Nat → Bool := checkNode m127Mask m127Goal (Nat.sub (Nat.shiftLeft 1 m127Pairs.length) 1) symMain 643 10 m127Ws m127D 10 m127Cuts 6
noncomputable def y127 : Nat → Nat → Bool := checkRange m127Mask m127Goal (Nat.sub (Nat.shiftLeft 1 m127Pairs.length) 1) symMain 643 10 m127Ws m127D 10 m127Cuts 6
theorem s127 (s n : Nat) (h : y127 s n = true) : ac x127 s n := cr_sound h
theorem q19 : ac x127 0 40 := s127 0 40 (by decide +kernel)
theorem q20 : ac x127 40 40 := s127 40 40 (by decide +kernel)
theorem q21 : ac x127 80 40 := s127 80 40 (by decide +kernel)
theorem q22 : ac x127 120 40 := s127 120 40 (by decide +kernel)
theorem q23 : ac x127 160 40 := s127 160 40 (by decide +kernel)
theorem q24 : ac x127 200 40 := s127 200 40 (by decide +kernel)
theorem q25 : ac x127 240 40 := s127 240 40 (by decide +kernel)
theorem q26 : ac x127 280 40 := s127 280 40 (by decide +kernel)
theorem q27 : ac x127 320 40 := s127 320 40 (by decide +kernel)
theorem q28 : ac x127 360 40 := s127 360 40 (by decide +kernel)
theorem q29 : ac x127 400 40 := s127 400 40 (by decide +kernel)
theorem q30 : ac x127 440 40 := s127 440 40 (by decide +kernel)
theorem q31 : ac x127 480 40 := s127 480 40 (by decide +kernel)
theorem q32 : ac x127 520 40 := s127 520 40 (by decide +kernel)
theorem q33 : ac x127 560 40 := s127 560 40 (by decide +kernel)
theorem q34 : ac x127 600 40 := s127 600 40 (by decide +kernel)
theorem q35 : ac x127 640 3 := s127 640 3 (by decide +kernel)
theorem m127All : ac x127 0 643 := (tm 0 320 323 (tm 0 160 160 (tm 0 80 80 (tm 0 40 40 q19 q20) (tm 80 40 40 q21 q22)) (tm 160 80 80 (tm 160 40 40 q23 q24) (tm 240 40 40 q25 q26))) (tm 320 160 163 (tm 320 80 80 (tm 320 40 40 q27 q28) (tm 400 40 40 q29 q30)) (tm 480 80 83 (tm 480 40 40 q31 q32) (tm 560 40 43 q33 (tm 600 40 3 q34 q35)))))
theorem m127Low : LowerM m127Mask m127Raw m127Goal 11 :=
  dagLow (pairs := m127Pairs) (sym := symMain) (ncuts := 33) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m127Ess m127CutValid m127All (by decide +kernel)

def m191Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m191Goal : Word := Nat.land gAll m191Mask
def m191Raw : List Word := mkR m191Mask [v0,v1,v2,v3,v4,v5,v7]
theorem m191Ess : ∀ a ∈ m191Raw, Essential m191Mask m191Goal m191Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,385]) (by decide +kernel)
def m191Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,33025,33152,33282,33408,33796,33920,34824,34944,40992,41088,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,41249,43048,45104,45200,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,34567,36366,39964,47160,2307,2309,2314,2316,2328,2337,2344,4355,4357,4372,4376,4385,4400,4496,4611,4614,4618,4628,4632,4656,4752,8707,8710,8714,8737,8744,8752,9221,9222,9228,9236,9249,9256,9264,33027,33029,33057,33168,33283,33286,33290,33424,33797,33798,33804,33812,33936,34826,34828]
def m191Ws : List Wire := mkWs m191Raw [(0x1e00001fff88a78823186f27f00c0f,0x22e449024d188228803082f03500405),(0x1e003ffe000197b804d2193d93030f0,0x44e20870e042986b800d009149301050),(0x3e01fc0000003e7f8196c61c1ec0c300,0x9e443c2141853a7f809642141ec04100),(0xc0000000003ff7dd961807e0e0f30003,0xc8809142822e77dd121807c0e0a10002),(0xfffc0679e67e0f800ff00003c,0x3111220f1b08679467e0f000b4000028),(0x1fff0000047e07800ffff000c03c0,0x9c3840c3045803800bd6a00040280),(0xfffe0000000078007fff0000000ffc00,0x211000081000000045600000000aa800)]
def m191Cuts : BTree CutSpec := (N (N (N (N (N (mc m191Raw 0x33330000333300000000000000000000333300003333 8) (mc m191Raw 0x111100001111000000000000000000001111000011110000 5)) (N (mc m191Raw 0x5500550055005500 4) E)) (N (N (mc m191Raw 0x555555555555555500000000000000005555555555555555 8) E) (N (mc m191Raw 0xf0f0f0f0 4) E))) (N (N (N (mc m191Raw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f 9) E) (N (mc m191Raw 0xf0f00000f0f000000000000000000000f0f00000f0f 8) E)) (N (N (mc m191Raw 0x5555555500000000000000000000000055555555 5) E) (N (mc m191Raw 0x505050500000000000000000000000005050505 4) E)))) (N (N (N (N (mc m191Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9) (mc m191Raw 0x50505050505050500000000000000000505050505050505 6)) (N (mc m191Raw 0x1100000011000000000000000000000011000000110000 4) E)) (N (N (mc m191Raw 0x5500550055005500000000000000000055005500550055 7) E) (N (mc m191Raw 0x55005500000000000000000000000000550055 4) E))) (N (N (N (mc m191Raw 0xffffffff000000000000000000000000ffffffff 8) E) (N (mc m191Raw 0x333333333333333300000000000000003333333333333333 9) E)) (N (N (mc m191Raw 0xffffffffffffffff 7) E) (N (mc m191Raw 0xffff0000ffff00000000000000000000ffff0000ffff 9) E)))))
theorem m191CutValid : ∀ ci < 18, ValidCut m191Mask m191Raw m191Goal (btreeGet ⟨0,0,[]⟩ 5 m191Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 7610375 m217Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
  · exact cv 14861832 m187Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 14861960 m190Low (by decide +kernel)
  · exact cv 14860424 m182Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 7606279 m217Low (by decide +kernel)
  · exact cv 1451527 m249Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 291096 m86Low (by decide +kernel)
  · exact cv 14845576 m175Low (by decide +kernel)
  · exact cv 269755911 m89Low (by decide +kernel)
  · exact cv 291101 m87Low (by decide +kernel)
noncomputable def m191D : BTree NodeRec := (N (N (N (N (N (N (N (k 0 [0,1,2,3,4] [8279,270439,450671,492645,533863,623983]) (k 258152 [0,7] [426309])) (N (k 5749 [9,12,10,3] [74022,123182,213300,221494,254278]) E)) (N (N (v 4221 7) E) (N (w 135289 [8,0,2,3]) E))) (N (N (N (k 12394 [1,2] [49512]) (k 266328 [0,12,1,4,3] [598071,442935,524902])) (N (k 135258 [8,0,2,1,3] [336245,180853,353124]) E)) (N (N (j 86326 7 [205172]) E) (N (w 225380 [9,12,15]) E)))) (N (N (N (N (w 12376 [0,12]) (u 274792)) (N (u 143464) E)) (N (N (v 69764 16) E) (N (u 209000) E))) (N (N (N (u 41080) (k 1391 [0,7,2,3,1,4] [630837,647284])) (N (k 135287 [8,1,6,2,12] [368744,336248,386180]) E)) (N (N (k 4725 [5,10,11,12,6] [237658,246048,196918,254326]) E) (N (k 1125 [9,10,11,3,1,7] [499819,401701,409895,483625,516455,262759]) E))))) (N (N (N (N (N (v 4209 7) (k 266295 [5,2,12,6,8] [548984,565608])) (N (k 135256 [0,8,2,3,4] [286823,303702,311911]) E)) (N (N (v 69684 15) E) (N (k 135782 [8,9,2,3,7] [418165,303720,74357,222069]) E))) (N (N (N (k 4215 [13,12,2,8] [90216,98424]) (u 299112)) (N (u 168040) E)) (N (N (k 86388 [9,8,2] [188778]) E) (N (w 233560 [12,11]) E)))) (N (N (N (N (u 20840) (k 266297 [12,0,5] [581748])) (N (j 139879 2 [319592]) E)) (N (N (j 86122 3 [189044]) E) (N (j 217192 1 [426356,320360]) E))) (N (N (N (w 53269 [1,2,12,8]) (w 315496 [7,11])) (N (u 185460) E)) (N (N (v 114976 7) E) (N (v 250421 3) E)))))) (N (N (N (N (N (N (k 87 [0,5,2,3,6] [16497,24693,82039,106617,131197,139391,172405,230005,263797]) (k 1383 [10,11,1,3,4,7,12] [24629,540727,573497,589912,614490,229685,434743,516726])) (N (k 103 [5,0,2,3,7,8] [278616,327770,24693,360567,393337,172405,402020,410214,434807]) E)) (N (N (k 4223 [6,15] [114708,147508,155716,163972]) E) (N (k 135780 [9,2,3,7,8] [352602,385383,213605]) E))) (N (N (N (w 12662 [1,2,12,8]) (j 294967 5 [606312])) (N (k 164213 [2,13] [344168]) E)) (N (N (v 98676 3) E) (N (k 225397 [12,0,5,2] [475224]) E)))) (N (N (N (N (k 12378 [1,2] [49512]) (k 270696 [1,17] [557416])) (N (w 139862 [9,15]) E)) (N (N (k 4469 [8,0,6,2,1,3] [180330,196918,213364,221558]) E) (N (k 135799 [5,12,2,8] [442472,418180,197188,312184]) E))) (N (N (N (k 4217 [14,0,1] [114709,123254]) (k 311349 [8,0,2,3,1] [639080])) (N (j 180328 1 [344424,377972]) E)) (N (N (v 114778 12) E) (N (k 245867 [9,10,3] [508469]) E))))) (N (N (N (N (N (k 4213 [10,5,11,6,8,12] [32856,41050,57448,65642,74102]) (j 270456 2 [557416])) (N (k 139367 [2,3] [295016]) E)) (N (N (v 69700 7) E) (N (k 205173 [12,2] [426088,205124]) E))) (N (N (N (u 41064) (k 266330 [12,0,1,2,4] [565573,238149])) (N (k 164708 [9,7,2] [189285]) E)) (N (N (k 86390 [3,7] [205124]) E) (N (w 225892 [9,12,7]) E)))) (N (N (N (N (w 12392 [0,8]) (v 286836 16)) (N (u 155752) E)) (N (N (u 90740) E) (N (k 111 [0,5,7,2,3] [458852,467061,483940]) E))) (N (N (N (u 53622) (w 311412 [9,12,15])) (N (k 181380 [8,1,2,12] [377192]) E)) (N (N (j 115062 7 [205124]) E) (N (k 246119 [12,0,1,2,3,4] [73797,524392,418117,508477,254533]) E)))))))
noncomputable def x191 : Nat → Bool := checkNode m191Mask m191Goal (Nat.sub (Nat.shiftLeft 1 m191Pairs.length) 1) id 80 10 m191Ws m191D 7 m191Cuts 5
noncomputable def y191 : Nat → Nat → Bool := checkRange m191Mask m191Goal (Nat.sub (Nat.shiftLeft 1 m191Pairs.length) 1) id 80 10 m191Ws m191D 7 m191Cuts 5
theorem s191 (s n : Nat) (h : y191 s n = true) : ac x191 s n := cr_sound h
theorem q36 : ac x191 0 40 := s191 0 40 (by decide +kernel)
theorem q37 : ac x191 40 40 := s191 40 40 (by decide +kernel)
theorem m191All : ac x191 0 80 := (tm 0 40 40 q36 q37)
theorem m191Low : LowerM m191Mask m191Raw m191Goal 11 :=
  dagLow (pairs := m191Pairs) (sym := id) (ncuts := 18) (by decide +kernel) (by decide +kernel) (sym_id_ok _ _) m191Ess m191CutValid m191All (by decide +kernel)

def m223Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def m223Goal : Word := Nat.land gAll m223Mask
def m223Raw : List Word := mkR m223Mask [v0,v1,v2,v3,v4,v6,v7]
theorem m223Ess : ∀ a ∈ m223Raw, Essential m223Mask m223Goal m223Raw a :=
  checkAllEss_sound (ps := [2057,4114,16452,265,273,321,385]) (by decide +kernel)
def m223Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,34824,34944,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,49600,49730,49856,50368,51272,51392,53392,53440,3847,3854,5895,7452,7694,7708,18183,19274,19982,20042,23114,23580,34567,36366,39964,51786,2307,2309,2314,2316,2328,2376,4355,4357,4372,4376,4496,4611,4614,4618,4628,4632,4674,4752,16643,16645,16706,16712,16832,17413,17414,17420,17428,17474,17480,17600,20500,20504,20546,20552,20624,20672,33027,33029,33168,33216,33283,33286,33290,33346,33424,33472,33797,33798,33804]
def m223Ws : List Wire := mkWs m223Raw [(0x78003e03ff88678082302727f030cf,0x20980046046188228000300503501045),(0x1f800001fc005bfb8304d11bd930c030,0x4788848a9c22dbeb8100d11b49304010),(0xe0001fc000003dbf841962dc1ec30300,0xe11023c428c53cbf8009624c1ec10100),(0x1ff7dd98618ce0e0fc0003,0x82014910511e77dd08218ce0e0a40002),(0x7e001ffe0261e607e0f00ff000c3c,0x822620163882414207e0600b4000428),(0x7fffe000047e07f800fff00000fc0,0x14459c38801043405f8009b200000a80),(0xfff80000000078007ffff000000ff000,0x186610210200000076d60000000aa000)]
def m223Cuts : BTree CutSpec := (N (N (N (N (N (mc m223Raw 0x3030303000000000303030300000000030303030000000003030303 8) (mc m223Raw 0x333333330000000033333333 6)) (N (mc m223Raw 0x5555000000000000555500000000000055550000000000005555 5) (mc m223Raw 0x11111111000000001111111100000000111111110000000011111111 5))) (N (N (mc m223Raw 0xffff000000000000ffff000000000000ffff000000000000ffff 8) (mc m223Raw 0x55000000000000005500000000000000550000000000000055 4)) (N (mc m223Raw 0x1111000000000000111100000000000011110000000000001111 4) E))) (N (N (N (mc m223Raw 0xffffffff00000000ffffffff 8) (mc m223Raw 0x300030000000000030003 4)) (N (mc m223Raw 0xffff0000000000000000000000000000ffff 6) E)) (N (N (mc m223Raw 0x550055000000000055005500000000005500550000000000550055 7) (mc m223Raw 0xf0f0f0f0 4)) (N (mc m223Raw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f 9) E)))) (N (N (N (N (mc m223Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) (mc m223Raw 0x33333333000000003333333300000000333333330000000033333333 9)) (N (mc m223Raw 0x550055000000000055005500 4) (mc m223Raw 0x33330000000000003333 4))) (N (N (mc m223Raw 0x55555555000000005555555500000000555555550000000055555555 8) (mc m223Raw 0xf0f00000000000000000000000000000f0f 5)) (N (mc m223Raw 0x3333000000000000333300000000000033330000000000003333 6) E))) (N (N (N (mc m223Raw 0xffffffff000000000000000000000000ffffffff 8) (mc m223Raw 0x5555555500000000000000000000000055555555 5)) (N (mc m223Raw 0xcccc000000000000cccc 4) E)) (N (N (mc m223Raw 0x30300000000000000000000000000000303 4) (mc m223Raw 0x110011000000000011001100000000001100110000000000110011 4)) (N (mc m223Raw 0x3333333300000000000000000000000033333333 6) E)))))
theorem m223CutValid : ∀ ci < 26, ValidCut m223Mask m223Raw m223Goal (btreeGet ⟨0,0,[]⟩ 5 m223Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16270848 m217Low (by decide +kernel)
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 14706256 m159Low (by decide +kernel)
  · exact cv 16270984 m222Low (by decide +kernel)
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 1847296 m81Low (by decide +kernel)
  · exact cv 14706256 m158Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 14681736 m143Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 553368 m86Low (by decide +kernel)
  · exact cv 14706192 m155Low (by decide +kernel)
  · exact cv 105532 m187Low (by decide +kernel)
  · exact cv 28947 m87Low (by decide +kernel)
  · exact cv 24788 m87Low (by decide +kernel)
  · exact cv 108606 m187Low (by decide +kernel)
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 553352 m86Low (by decide +kernel)
  · exact cv 786951 m89Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 549344 m86Low (by decide +kernel)
  · exact cv 225555 m55Low (by decide +kernel)
  · exact cv 24784 m86Low (by decide +kernel)
noncomputable def m223D : BTree NodeRec := (N (N (N (N (N (N (N (N (k 0 [0,1,2,3,4,5] [8214,12326,540743,544855,893031,1057879,1123431,1127783]) (v 520252 9)) (N (j 245850 14 [402260]) E)) (N (N (k 83303 [4,14] [237636,270440,197172,254532]) (k 561273 [11,7,1,3,5] [1318981,827973,1033029,537702])) (N (v 389444 3) E))) (N (N (N (u 57465) (v 585832 22)) (N (k 319562 [25,1] [663912]) E)) (N (N (v 188477 24) E) (N (u 454744) E)))) (N (N (N (N (k 4187 [12,14,1,3,2] [73796,90229,107381]) (u 553320)) (N (k 270439 [10,19,8] [172884]) E)) (N (N (k 139353 [11,9] [336485]) E) (N (k 271991 [21,2,4] [860208,557108,868408,876604,802900,884856,631100,778564,696884,836180,263268]) E))) (N (N (N (u 90469) (u 618600)) (N (y 352376 [213844]) E)) (N (N (k 5223 [11,6,14,3] [466992,475192,180292,434293,246084,361028,483957]) E) (N (k 446569 [9,0,3,4] [991349,328260,1000309]) E))))) (N (N (N (N (N (w 12852 [12,11]) (v 536664 11)) (N (k 274549 [0,1] [565336,569448,573560]) E)) (N (N (v 143701 17) E) (N (v 405578 11) E))) (N (N (N (k 4421 [7,6,11,0,4,12] [172119,180325,204903,221289,33069,229717,246117,263527]) (u 602202)) (N (u 319609) E)) (N (N (k 5207 [7,6,11,12] [434293,229700,418933]) E) (N (u 471128) E)))) (N (N (N (N (v 45160 9) (u 569688)) (N (v 303224 9) E)) (N (N (k 139605 [11,6,14,3,9] [368741,303706]) E) (N (y 426104 [271460]) E))) (N (N (N (k 82261 [10,12,1,11] [237669]) (u 634984)) (N (k 270693 [7,6,19,8] [762164,778613,783221]) E)) (N (N (k 5479 [6,11,0,2,3] [499761,507965,516184,524378,434293,532601,377412,483957,263285]) E) (N (j 503882 11 [406612]) E)))))) (N (N (N (N (N (N (w 4167 [11,12,13]) (k 528501 [7,1,5,2,22,11] [557125,1073225,1089624,1106010,1093736,1110122,1024325,803397,807749,435286,439398])) (N (k 71 [6,7,0,2,4,8] [548965,589927,598121,639093,704631,729209,164148,754021,795237,811637,853623]) E)) (N (N (k 4453 [18,11,6,0,2,3,9] [286794,180309,319575,327769,344167,147757,360789,377189,107115,419175]) (k 561781 [7,1,2,3,22,11] [700485,1192009,1290346,840005,696901,1188425,1286746,836421,484438,488550])) (N (j 397429 5 [770628,238676]) E))) (N (N (N (k 70196 [23,11] [155722]) (k 561224 [18,21,0,6,1,2,11,4] [1204277,1220663,475193,1237095,521030,889703])) (N (v 319592 5) E)) (N (N (v 188521 4) E) (N (k 446554 [9,0,1,3,4] [942437,946549,287300,291412,959333,963445]) E)))) (N (N (N (N (u 37733) (k 561207 [11,17,6,8,9] [1138808,1155416])) (N (k 299125 [1,17] [614488,622712]) E)) (N (N (k 139367 [9,1,14,19] [352344]) E) (N (v 426040 22) E))) (N (N (N (u 102504) (v 626757 11)) (N (v 364628 5) E)) (N (N (w 229432 [5,11]) E) (N (j 492405 3 [336980]) E))))) (N (N (N (N (N (v 20576 4) (u 544837)) (N (v 278648 9) E)) (N (N (u 143973) E) (N (j 405877 3 [843824,786756,255060]) E))) (N (N (N (k 82021 [11,1,17,8,9] [188506,196965]) (u 610408)) (N (k 270455 [20,11,17,9] [712792,721016,205652]) E)) (N (N (v 217152 24) E) (N (k 446567 [9,1,8,17,11] [974936,942456,320340,349028]) E)))) (N (N (N (N (k 4199 [11,6,14,3,16] [122968,131193]) (k 561209 [11,6,0,3] [475208,1171573,1188725])) (N (k 270453 [0,6,2,3,9,8,11] [647240,655434,671848,680042,557173,688249,696693,180804]) E)) (N (N (k 139621 [9,11,14,1] [385073,393277,401482,368741,409705,311898,197221,336489]) E) (N (k 446552 [0,9,5,2,3,4] [909399,913511,927079]) E))) (N (N (N (k 82277 [11,6,8] [237669,254309]) (k 561271 [7,11,22] [1302648,1270120])) (N (u 381029) E)) (N (N (v 245821 24) E) (N (k 503929 [3,11] [414820]) E))))))) (N (N (N (N (N (N (N (k 22 [6,0,2,3,4] [16455,24651,41047,65627,114791,139371,164165,278885,427095,459879,492903]) (k 1111 [7,1,2,5] [548917,1065077,794933,799285,426822,430934,1041271])) (N (j 245881 4 [410452]) E)) (N (N (u 131176) (v 655429 11)) (N (k 270949 [7,6,8] [802933,762164,230212]) E))) (N (N (N (k 4203 [12,11,17,2] [148020]) (u 582517)) (N (u 328040) E)) (N (N (u 188490) E) (N (u 451943) E)))) (N (N (N (N (j 32836 12 [82789]) (k 1127 [0,1,2,10,5,4,11,3] [639029,1130551,1163321,1196104,1253450,1065077,1294455,1310841,811317,1008181,1327733,459590,496470,856951])) (N (k 270441 [20,7,2] [606325,631157]) E)) (N (N (u 164453) E) (N (v 426032 8) E))) (N (N (N (k 82023 [20,17,11,9] [213096]) (k 561226 [11,0,1,3,5] [1261637,1155397,1270133,819781,1016645,1287029,529494])) (N (k 270457 [20,0,2,3] [737364,745589,221764]) E)) (N (N (w 229424 [12,0,2,3]) E) (N (u 491637) E))))) (N (N (N (N (N (k 4183 [11,6,14,3,15] [49248,57448]) (k 532568 [14,11] [1097797,455766])) (N (v 278616 11) E)) (N (N (u 143957) E) (N (v 405625 11) E))) (N (N (N (w 82007 [3,19]) (k 598071 [6,11] [1228904])) (N (j 319861 3 [197460]) E)) (N (N (k 213109 [14,11] [442432,450664,368980,238164]) E) (N (j 467813 4 [304212,316516]) E)))) (N (N (N (N (k 33653 [24,14,3] [82516]) (k 565592 [1,11,12] [1147240])) (N (w 299381 [14,2]) E)) (N (N (u 180325) E) (N (k 103 [6,0,2,3,4,9] [901208,933978,639077,966759,983145,643189,970871,987257,278836,282948,1008229,1012341,1042039]) E))) (N (N (N (u 114789) (v 627573 4)) (N (k 377140 [7,6] [770149]) E)) (N (N (v 245809 24) E) (N (j 503925 5 [369748,373860]) E)))))) (N (N (N (N (N (N (k 4171 [12,11,0,3,4] [33332]) (f 532553 [1081432,1085544])) (N (k 270437 [7,6,2,19,8] [557173,581753]) E)) (N (N (k 139338 [9,17] [295253,156221,303701,311909]) E) (N (k 270965 [6,0,2,10,8,11] [819274,802933,827513,835957,246596,783221]) E))) (N (N (N (u 73802) (k 598069 [6,11] [1212506])) (N (k 319594 [1,17] [663896,189268]) E)) (N (N (j 140647 2 [368708]) E) (N (k 467301 [17,20] [950360,295764]) E)))) (N (N (N (N (j 32885 23 [98408]) (j 565368 17 [1147224])) (N (v 303192 11) E)) (N (N (u 172120) E) (N (v 426044 8) E))) (N (N (N (w 82025 [20,11]) (j 627061 7 [1278056])) (N (v 364661 2) E)) (N (N (j 230005 4 [197204,254804]) E) (N (k 447077 [6,0,4,2,3,11,9] [1015882,1024117,1032313,959082,701045,1004153,361284,381780]) E))))) (N (N (N (N (N (w 20584 [5,11]) (f 532570 [1114472])) (N (u 274553) E)) (N (N (k 139351 [1,9,17,8,11] [295272]) E) (N (v 417840 8) E))) (N (N (N (v 90202 17) (j 598119 21 [1245288])) (N (v 352344 11) E)) (N (N (u 217192) E) (N (k 483416 [1,11] [950632,357204]) E)))) (N (N (N (N (w 57432 [9,11]) (k 581749 [0,11] [1179752])) (N (v 319560 5) E)) (N (N (v 188465 24) E) (N (k 450647 [17,4] [917592]) E))) (N (N (N (u 123237) (j 647288 17 [1278312])) (N (j 377205 3 [770116,786756]) E)) (N (N (k 245848 [5,17,2] [271461]) E) (N (k 448119 [10,1,2] [557108,1048636,1024084,926600,418916,423028]) E))))))))
noncomputable def x223 : Nat → Bool := checkNode m223Mask m223Goal (Nat.sub (Nat.shiftLeft 1 m223Pairs.length) 1) symMain 163 10 m223Ws m223D 8 m223Cuts 5
noncomputable def y223 : Nat → Nat → Bool := checkRange m223Mask m223Goal (Nat.sub (Nat.shiftLeft 1 m223Pairs.length) 1) symMain 163 10 m223Ws m223D 8 m223Cuts 5
theorem s223 (s n : Nat) (h : y223 s n = true) : ac x223 s n := cr_sound h
theorem q38 : ac x223 0 40 := s223 0 40 (by decide +kernel)
theorem q39 : ac x223 40 40 := s223 40 40 (by decide +kernel)
theorem q40 : ac x223 80 40 := s223 80 40 (by decide +kernel)
theorem q41 : ac x223 120 40 := s223 120 40 (by decide +kernel)
theorem q42 : ac x223 160 3 := s223 160 3 (by decide +kernel)
theorem m223All : ac x223 0 163 := (tm 0 80 83 (tm 0 40 40 q38 q39) (tm 80 40 43 q40 (tm 120 40 3 q41 q42)))
theorem m223Low : LowerM m223Mask m223Raw m223Goal 11 :=
  dagLow (pairs := m223Pairs) (sym := symMain) (ncuts := 26) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m223Ess m223CutValid m223All (by decide +kernel)

def m247Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def m247Goal : Word := Nat.land gAll m247Mask
def m247Raw : List Word := mkR m247Mask [v0,v1,v2,v4,v5,v6,v7]
theorem m247Ess : ∀ a ∈ m247Raw, Essential m247Mask m247Goal m247Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,321,385]) (by decide +kernel)
def m247Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,40992,41088,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,21058,21524,24865,24928,25154,25184,25696,28720,28768,33539,34053,34310,37264,37520,37908,38032,41249,45104,45200,49600,49730,49856,50368,53392,53440,57440,57536,5895,9991,18183,34567,4355,4357,4372,4385,4400,4496,4611,4614,4628,4656,4674,4752,8707,8710,8737,8752,8770,8800,9221,9222,9236,9249,9264,9312,16643,16645,16673,16706,16736,16832,17413,17414,17428,17474,17504,17600,20500,20528,20546,20576,20624,20672,33027,33029,33057,33168,33216,33283,33286,33346,33424,33472,33797,33798,33812]
def m247Ws : List Wire := mkWs m247Raw [(0xf8007e00007fe0245830e379c0c303,0x2138008e48a097e0041810a178c04101),(0x1f00000007ff81e0c0a8c7649e43003c,0x47088512126983e0402847608a410014),(0xe0001f81f80001e103310b98e78c0cc0,0xe210238438430de001300988a7840440),(0x7e000001ffe261bc60c1f07c0300f,0x88426200a11668021bc2081e0500100a),(0x1ffe000581c07f01ff83000f0,0x214829c58430080c07b017501000a0),(0x7fffe0000009fe007ffe000003f00,0x14859c710608001de005e64000002a00),(0xfff800000000011ffff80000003fc000,0x18c6104000104017b2c00000002a8000)]
def m247Cuts : BTree CutSpec := (N (N (N (N (N (mc m247Raw 0x55005500550055005500550055005500550055005500550055005500550055 10) (mc m247Raw 0xff000000ff0000000000000000000000ff000000ff 6)) (N (mc m247Raw 0x30003000000000003000300000000 4) (mc m247Raw 0x300030000000000030003 4))) (N (N (mc m247Raw 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 9) (mc m247Raw 0x330000003300000000000000000000003300000033 5)) (N (mc m247Raw 0x3300000033000000330000003300000033000000330000003300000033 6) (mc m247Raw 0x300000003000000030000000300000003000000030000000300000003 4)))) (N (N (N (mc m247Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9) (mc m247Raw 0x30003000000000003000300000000000300030000000000030003 5)) (N (mc m247Raw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f 7) (mc m247Raw 0x33000000330000003300000033 4))) (N (N (mc m247Raw 0x33003300330033003300330033003300330033003300330033003300330033 9) (mc m247Raw 0xf0000000f00000000000000000000000f0000000f 5)) (N (mc m247Raw 0x330033000000000033003300000000003300330000000000330033 6) (mc m247Raw 0x33003300000000000000000000000000330033 4))))) (N (N (N (N (mc m247Raw 0xff00ff00ff00ff00ff00ff00ff00ff 9) (mc m247Raw 0xff00ff0000000000ff00ff 6)) (N (mc m247Raw 0x1100000011000000000000000000000011000000110000 4) (mc m247Raw 0xf000f000f000f000f000f000f000f 7))) (N (N (mc m247Raw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f 9) (mc m247Raw 0x110000001100000000000000000000001100000011 4)) (N (mc m247Raw 0x3300330033003300000000000000000033003300330033 7) (mc m247Raw 0x55000000550000005500000055 4)))) (N (N (N (mc m247Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) (mc m247Raw 0x50000000500000000000000000000000500000005 4)) (N (mc m247Raw 0x330033003300330033003300330033 7) (mc m247Raw 0xff000000ff000000ff000000ff 5))) (N (N (mc m247Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) (mc m247Raw 0x3300330000000000330033 5)) (N (mc m247Raw 0x500000005000000000000000000000005000000050000000000000000 4) (mc m247Raw 0xf000f000f000f 4))))))
theorem m247CutValid : ∀ ci < 32, ValidCut m247Mask m247Raw m247Goal (btreeGet ⟨0,0,[]⟩ 5 m247Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16433288 m246Low (by decide +kernel)
  · exact cv 1753224 m119Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 14868560 m183Low (by decide +kernel)
  · exact cv 16433160 m243Low (by decide +kernel)
  · exact cv 15917072 m243Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 1511431 m241Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 14707202 m155Low (by decide +kernel)
  · exact cv 1449991 m241Low (by decide +kernel)
  · exact cv 12613648 m155Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 14844040 m167Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
  · exact cv 1855489 m81Low (by decide +kernel)
  · exact cv 1318919 m89Low (by decide +kernel)
  · exact cv 1855490 m81Low (by decide +kernel)
  · exact cv 1314823 m89Low (by decide +kernel)
  · exact cv 1049606 m89Low (by decide +kernel)
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 549184 m86Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
  · exact cv 29096 m86Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 28944 m86Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
noncomputable def m247D : BTree NodeRec := (N (N (N (N (N (N (N (N (k 0 [0,1,2,3,4,5,6] [8487,213303,418119,606551,688487,610871,422471,217687,692839,729927,844631,975719,734295,1057895,980327]) (w 488053 [15,9,2])) (N (u 259431) E)) (N (N (k 106597 [15,20,1,3] [271991]) E) (N (w 385112 [8,9]) E))) (N (N (N (k 4453 [15,8,13] [119653,140149]) E) (N (w 303733 [15,11,8]) E)) (N (N (w 107879 [8,9,20,15]) E) (N (v 454773 8) E)))) (N (N (N (N (v 24672 3) E) (N (k 210295 [9,8,23] [533060]) E)) (N (N (k 106853 [9,15,1,2,3] [337527]) E) (N (k 421961 [19,9,1,3] [861815]) E))) (N (N (N (w 94264 [29,8,9]) E) (N (k 345463 [9,11,20,3,5] [90997,476037,173173,541829,714117]) E)) (N (N (w 209001 [24,15]) E) (N (k 487497 [9,8,1,3] [196697,205141]) E))))) (N (N (N (N (N (k 4181 [8,0,18,2,4] [42343]) E) (N (k 209525 [8,0,2,1,4,23] [516404,566903]) E)) (N (N (k 106613 [9,8,1,3] [303193]) E) (N (w 365157 [8,15,2]) E))) (N (N (N (w 74069 [8,9]) E) (N (k 359 [11,0,8,2,3,4,5] [49221,294997,467045,614517,147781,508261,696917,705125,668759,382071,722295]) E)) (N (N (k 208969 [8,0,14,2,4] [435559]) E) (N (v 462904 17) E)))) (N (N (N (N (v 45952 3) E) (N (k 303701 [15,20,1,3,4] [632439]) E)) (N (N (w 107607 [8,18,15,0,2]) E) (N (k 422005 [15,9,1,0,3] [893000,901241]) E))) (N (N (N (w 110709 [8,21]) E) (N (w 364645 [8,15]) E)) (N (N (w 242037 [8,30,0,4]) E) (N (k 487529 [8,9,0,3] [1024117]) E)))))) (N (N (N (N (N (N (k 4165 [9,8,10,3] [24697]) (k 528457 [8,0,4,17,2] [680309,968311])) (N (j 255607 1 [525412]) E)) (N (N (k 106601 [9,15,1,3] [288375]) E) (N (v 397433 15) E))) (N (N (N (k 4469 [8,0,2,4,1] [155765,164181,144213,173431]) E) (N (k 304759 [8,13,0,23,4] [680008,271237,337029,632197]) E)) (N (N (w 108151 [15,9,20,2,3,8]) E) (N (v 462896 17) E)))) (N (N (N (N (u 38247) E) (N (k 343 [13,15,0,1,3,9,4,5] [20549,262229,450661,614517,131397,328021,623189,647781,655989,578663,664695,673399]) E)) (N (N (w 107093 [9,8,3]) E) (N (v 430152 8) E))) (N (N (N (k 311 [9,10,11,0,3,6,12,2,4] [16453,221257,245845,254041,262245,278633,295029,311417,328037,344661,352885,361559,369767,377975,394599,402807,411255]) E) (N (w 364617 [8,9]) E)) (N (N (w 235127 [23,8]) E) (N (w 495701 [8,9,27]) E))))) (N (N (N (N (N (k 4213 [8,0,2,4] [57429,65632,73832,61557,91511]) E) (N (k 210007 [8,9,10] [115012]) E)) (N (N (k 106617 [21,8,1,3] [319573]) E) (N (w 413744 [31,15,8]) E))) (N (N (N (k 5223 [19,9,7,1,3,20,15] [41845,91013,124021,173189,128373,177541]) E) (N (k 344677 [8,0,2,3,4,23] [516404,714359]) E)) (N (N (w 208985 [24,9]) E) (N (k 462969 [23,8] [868684,639332]) E)))) (N (N (N (N (w 54101 [8,9]) E) (N (v 315496 4) E)) (N (N (k 107639 [8,15,0,2,9,12] [57396,385084]) E) (N (v 442489 8) E))) (N (N (N (w 106581 [8,9]) E) (N (k 364661 [9,8] [778320,786520]) E)) (N (N (k 209269 [8,0,2,3,4] [516404,532837,542327]) E) (N (w 487531 [9,8,3]) E))))))) (N (N (N (N (N (N (N (k 295 [7,0,8,2,4,3,1] [16453,32853,20581,49269,106837,131429,147829,135749,111189,152181,181351,189559,194167]) (k 1127 [8,0,1,2,3,4,5,6,17] [467013,1065033,471125,1069145,770149,1073257,774261,1077369,557381,561493,705093,709205,402535,672887,677223,406903,927351])) (N (w 254309 [8,9]) E)) (N (N (w 132727 [23,8]) E) (N (k 364665 [8,9,0,1] [802937]) E))) (N (N (N (w 66421 [8,15]) E) (N (k 304247 [15,8,13] [139588]) E)) (N (N (k 107895 [8,23,0,2,4] [271237,287625,337029]) E) (N (k 423543 [0,1,2,3,10,9,23,16,8,4] [933936,942132,950328,958524,475253,966777,479365,970889,565621,569733,713333,717445,271221,861049,275333,865161,636037,632181]) E)))) (N (N (N (N (k 24680 [8,0,2,4] [83303]) E) (N (k 210551 [8,23,0,9,4,1] [492092]) E)) (N (N (w 165495 [8,23,2]) E) (N (k 427639 [20,9] [868424]) E))) (N (N (N (w 94280 [8,9]) E) (N (k 839 [8,9,3,0,4,1,2,5,6] [245829,737353,454741,745561,753765,761961,770165,794745,344389,651605,811381,549445,819813,398695,829047]) E)) (N (N (k 209013 [8,0,23,2,4] [476791]) E) (N (k 487513 [9,25,8,3,15,0,26] [999509,196697]) E))))) (N (N (N (N (N (w 17767 [22,15]) E) (N (j 280183 1 [525412]) E)) (N (N (w 147545 [26,9,8]) E) (N (k 366199 [15,8,2,9] [835632]) E))) (N (N (N (w 75127 [20,1,9]) E) (N (k 344661 [9,8,4,1] [164693,533349]) E)) (N (N (w 214375 [14,8]) E) (N (v 462908 16) E)))) (N (N (N (N (k 4437 [8,0,2,18,3,4] [115541,124263]) E) (N (k 312951 [8,6] [639080]) E)) (N (N (w 107623 [15,9,22,20]) E) (N (w 442440 [15,1,9]) E))) (N (N (N (w 111477 [9,8]) E) (N (w 364649 [15,8,9]) E)) (N (N (w 243319 [14,8]) E) (N (v 508021 15) E)))))) (N (N (N (N (N (N (w 8313 [28,9,8]) (w 528489 [24,9])) (N (w 209493 [8,9,4]) E)) (N (N (w 140919 [12,9]) E) (N (w 364917 [9,8,1]) E))) (N (N (N (v 73845 15) E) (N (k 335944 [8,13,0,4,17] [640117]) E)) (N (N (k 327 [8,0,13,3,4,6,1,5,14] [32837,426057,245845,442457,450661,458857,467061,483449,106821,508277,549461,557685,574551,365671,583015,591223,599671]) E) (N (v 462900 8) E)))) (N (N (N (N (k 25975 [22,15] [99200,82824]) E) (N (w 303221 [15,11,8,3]) E)) (N (N (k 107125 [9,8,1] [238169]) E) (N (w 421993 [19,8]) E))) (N (N (N (k 106569 [21,8,3,5] [229493,238453]) E) (N (w 364633 [8,15,9,0]) E)) (N (N (k 209017 [8,0,14,2,4] [491893,501367]) E) (N (w 487515 [9,27,5,3,8]) E))))) (N (N (N (N (N (v 24661 9) E) (N (k 210279 [9,20,3,1,5] [41845,435065,476037,500617,124021,541829,566661]) E)) (N (N (w 155733 [8,21]) E) (N (k 855 [15,9,0,1,2,3,10,6,16,4] [262213,852041,266325,856153,753765,876649,884853,909433,627029,623173,181335,582759,722039,587111,726391,927351]) E))) (N (N (N (k 5239 [9,8,4] [196664,204872,164420]) E) (N (j 353911 3 [525412]) E)) (N (N (w 208997 [15,8]) E) (N (k 871 [9,1,10,0,3,2,4,6] [294981,983113,618581,991321,1007707,770149,1015913,1032299,884853,1040505,352581,659797,811365,696901,1049205,189527,590951,603495,415095,833143]) E)))) (N (N (N (N (w 54631 [20,3,9]) E) (N (w 303717 [15,8,3]) E)) (N (N (v 188476 12) E) (N (k 422009 [19,20,1,3] [917621]) E))) (N (N (N (w 106585 [21,8]) E) (N (v 385104 6) E)) (N (N (k 254260 [8,0,2,4,23] [525671]) E) (N (w 487545 [15,9,1,2]) E))))))))
noncomputable def x247 : Nat → Bool := checkNode m247Mask m247Goal (Nat.sub (Nat.shiftLeft 1 m247Pairs.length) 1) symMain 132 11 m247Ws m247D 8 m247Cuts 5
noncomputable def y247 : Nat → Nat → Bool := checkRange m247Mask m247Goal (Nat.sub (Nat.shiftLeft 1 m247Pairs.length) 1) symMain 132 11 m247Ws m247D 8 m247Cuts 5
theorem s247 (s n : Nat) (h : y247 s n = true) : ac x247 s n := cr_sound h
theorem q43 : ac x247 0 40 := s247 0 40 (by decide +kernel)
theorem q44 : ac x247 40 40 := s247 40 40 (by decide +kernel)
theorem q45 : ac x247 80 40 := s247 80 40 (by decide +kernel)
theorem q46 : ac x247 120 12 := s247 120 12 (by decide +kernel)
theorem m247All : ac x247 0 132 := (tm 0 80 52 (tm 0 40 40 q43 q44) (tm 80 40 12 q45 q46))
theorem m247Low : LowerM m247Mask m247Raw m247Goal 12 :=
  dagLow (pairs := m247Pairs) (sym := symMain) (ncuts := 32) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m247Ess m247CutValid m247All (by decide +kernel)

def m251Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def m251Goal : Word := Nat.land gAll m251Mask
def m251Raw : List Word := mkR m251Mask [v0,v1,v3,v4,v5,v6,v7]
theorem m251Ess : ∀ a ∈ m251Raw, Essential m251Mask m251Goal m251Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,321,385]) (by decide +kernel)
def m251Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,16641,16704,20496,20544,33025,33152,33282,33408,34824,34944,40992,41088,2819,2826,4867,6424,6666,6680,8963,8993,10529,10536,10762,10792,12577,12592,12848,17155,17218,18760,21058,22552,22600,24865,24928,25154,25184,28720,28768,33539,35338,37264,37520,38936,39056,41249,43048,45104,45200,49600,49730,49856,51272,51392,53392,53440,57440,57536,14648,14904,19274,23114,26984,27210,27240,30776,30824,47160,51786,59496,2307,2314,2328,2337,2344,2376,4355,4376,4385,4400,4496,4611,4618,4632,4656,4674,4752,8707,8714,8737,8744,8752,8770,8800,16643,16673,16706,16712,16736,16832,20504,20528,20546,20552,20576,20624,20672,33027,33057,33168,33216,33283,33290,33346,33424,33472,34826,34840,34856,34888]
def m251Ws : List Wire := mkWs m251Raw [(0x780fc001ffc0540222863b3cf0330f,0x9800c282524000002082091c501105),(0xf80003ffe0011b80c05985ccf70c0f0,0x13884151a610d0b00401885845704050),(0xf0000000000ffffc305901a0f3b30003,0xf10092050c2dbffc104901a0e3a10002),(0x7f0007ff00e2cc19e61c703c00c3c,0x2422300859a10a0c419e208602800428),(0x3f80002fcf01e07e07fc0c00c0,0x401124ae10c62f4d00e07607b8040080),(0x7ffc0000037f3fe007ff800000f00,0x8a45cf30200835f3be005d7000000a00),(0xfff8000000003803ffff8000000ff000,0xc66080041000002eb160000000aa000)]
def m251Cuts : BTree CutSpec := (N (N (N (N (N (N (mc m251Raw 0xf0f00000f0f000000000000000000000f0f00000f0f 8) (mc m251Raw 0x30300000000000000000000000000000303 4)) (N (mc m251Raw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f 9) E)) (N (N (mc m251Raw 0x3030303000000000303030300000000 5) (mc m251Raw 0xf0f00000000000000000000000000000f0f 5)) (N (mc m251Raw 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f 6) E))) (N (N (N (mc m251Raw 0x50500000505000000000000000000000505000005050000000000000000 5) (mc m251Raw 0x3030000030300000000000000000000030300000303 5)) (N (mc m251Raw 0x303030303030303030303030303030303030303030303030303030303030303 9) E)) (N (N (mc m251Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) (mc m251Raw 0xf0f0f0f0f0f0f0f 5)) (N (mc m251Raw 0x50005000000000005000500000000000500050000000000050005 4) E)))) (N (N (N (N (mc m251Raw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f 9) (mc m251Raw 0x300030000000000030003 4)) (N (mc m251Raw 0x50505050505050500000000000000000505050505050505 6) E)) (N (N (mc m251Raw 0x505050505050505050505050505050505050505050505050505050505050505 8) (mc m251Raw 0x303030300000000000000000000000003030303 5)) (N (mc m251Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6) E))) (N (N (N (mc m251Raw 0x500000005000000000000000000000005000000050000000000000000 4) (mc m251Raw 0xf0f0f0f 4)) (N (mc m251Raw 0x50005000500050005000500050005 4) E)) (N (N (mc m251Raw 0x30303030303030300000000000000000303030303030303 6) E) (N (mc m251Raw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f 7) E))))) (N (N (N (N (N (mc m251Raw 0x3030303000000000303030300000000030303030000000003030303 8) (mc m251Raw 0x300000003000000030000000300000003000000030000000300000003 4)) (N (mc m251Raw 0x5000500050005000500050005000500 4) E)) (N (N (mc m251Raw 0x500050005000500000000000000000005000500050005 5) (mc m251Raw 0xf0f0f0f0000000000000000000000000f0f0f0f 6)) (N (mc m251Raw 0x5050505000000000505050500000000050505050000000005050505 5) E))) (N (N (N (mc m251Raw 0xf000f000f000f000f000f000f000f 7) (mc m251Raw 0x300030003000300000000000000000003000300030003 4)) (N (mc m251Raw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f 9) E)) (N (N (mc m251Raw 0x30300000303000003030000030300000303000003030000030300000303 6) (mc m251Raw 0x5050000050500000000000000000000050500000505 5)) (N (mc m251Raw 0x505050500000000000000000000000005050505 4) E)))) (N (N (N (N (mc m251Raw 0x5000500050005000500050005000500050005000500050005000500050005 7) (mc m251Raw 0x303000000000000030300000000000003030000000000000303 5)) (N (mc m251Raw 0x50000000500000000000000000000000500000005 4) E)) (N (N (mc m251Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 8) (mc m251Raw 0xf000000000000000f000000000000000f000000000000000f 4)) (N (mc m251Raw 0xf0f0f0f000000000f0f0f0f 6) E))) (N (N (N (mc m251Raw 0x30003000000000003000300000000 4) (mc m251Raw 0xf000f000f000f 4)) (N (mc m251Raw 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f 9) E)) (N (N (mc m251Raw 0xf000f00000000000f000f 5) E) (N (mc m251Raw 0xf000f000f000f0000000000000000000f000f000f000f 6) E))))))
theorem m251CutValid : ∀ ci < 46, ValidCut m251Mask m251Raw m251Goal (btreeGet ⟨0,0,[]⟩ 6 m251Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 7606279 m217Low (by decide +kernel)
  · exact cv 16270848 m217Low (by decide +kernel)
  · exact cv 16433160 m243Low (by decide +kernel)
  · exact cv 10440705 m241Low (by decide +kernel)
  · exact cv 1075058183 m89Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 1857537 m89Low (by decide +kernel)
  · exact cv 1512999 m123Low (by decide +kernel)
  · exact cv 1754632 m123Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 29099 m87Low (by decide +kernel)
  · exact cv 1835363 m87Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 14861832 m187Low (by decide +kernel)
  · exact cv 135270824 m86Low (by decide +kernel)
  · exact cv 291101 m87Low (by decide +kernel)
  · exact cv 1855489 m81Low (by decide +kernel)
  · exact cv 16434688 m249Low (by decide +kernel)
  · exact cv 105532 m187Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 1512967 m249Low (by decide +kernel)
  · exact cv 29067 m87Low (by decide +kernel)
  · exact cv 160139 m55Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
  · exact cv 16590 m87Low (by decide +kernel)
  · exact cv 279024 m86Low (by decide +kernel)
  · exact cv 291096 m86Low (by decide +kernel)
  · exact cv 1511431 m241Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
  · exact cv 1847296 m81Low (by decide +kernel)
  · exact cv 29096 m86Low (by decide +kernel)
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 1850368 m89Low (by decide +kernel)
  · exact cv 788999 m89Low (by decide +kernel)
  · exact cv 1835360 m86Low (by decide +kernel)
  · exact cv 16584 m86Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 786951 m89Low (by decide +kernel)
  · exact cv 14697992 m155Low (by decide +kernel)
  · exact cv 1849344 m89Low (by decide +kernel)
  · exact cv 29064 m86Low (by decide +kernel)
  · exact cv 33123 m55Low (by decide +kernel)
  · exact cv 1316359 m89Low (by decide +kernel)
noncomputable def m251D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (N (N (k 0 [0,1,2] [8215,9986075,10182695,10690603,11755575,14065723,14467143,15040587,15155287,15491163,15868003,16015463,17875051,17879151,18161959,18227511,18645335,11759975,14070127,18166327,18752071,18756183,10187367,10695279,18649927,13159,9991023,18834519,15160423,15496303,14472551,15045999]) (v 8384616 8)) (N (k 3862903 [8,4,20] [8396864,8061000,8118612]) E)) (N (N (u 2093108) E) (N (v 6267253 21) E))) (N (N (N (z 1040692) E) (N (u 5239623) E)) (N (N (k 3051639 [0,4] [6299768]) E) (N (k 7323753 [7,0,27] [12165429]) E)))) (N (N (N (N (y 491901 [1056804]) (k 8009335 [7,4] [17834032,17842225,17850424,17858617,17073016,17384314])) (N (k 4967 [6,1,9,5,3] [9445448,123188,401717,8855892,9453965,5653381,6439817,8520837,9381253]) E)) (N (N (k 2424919 [0,1] [1867832,5251144,5259352,5267552,5275752,5292152,5300360,1171752,4997472,5136744,5316984]) E) (N (k 6811700 [1,5,0,17] [13639737,13647930,13656152,13664346,13680760,13688954]) E))) (N (N (N (u 1568874) E) (N (k 5722949 [17,7,4] [8196949]) E)) (N (N (v 3666036 4) E) (N (k 7831640 [0,17,1,10] [15736903,15753319,14020935,15479143,15762245]) E))))) (N (N (N (N (N (k 229493 [17,1,0,6] [90152,475221,532776,541013]) (k 8610153 [8,21,0] [17309797,17318005])) (N (v 4452416 10) E)) (N (N (v 2355240 4) E) (N (j 6549572 5 [13115448,13123704]) E))) (N (N (N (j 1114239 11 [2531348,2605352]) E) (N (k 5469287 [2,1] [11018344,11026552,10953060]) E)) (N (N (k 3224677 [23,20,10] [6823968,2982188,6595404,6693972]) E) (N (w 7594341 [17,6,1]) E)))) (N (N (N (N (v 774704 11) (k 9121914 [36,4] [18284888])) (N (v 4956236 10) E)) (N (N (k 2830424 [1,17,0,2] [5775382,4940073,1990997,3072345,3547509,3834233,5784126,5792326,5800789,5808985,5817429,5825653]) E) (N (k 7037047 [17,1,3] [14164072,14172280,14139680,13652264]) E))) (N (N (N (v 1826906 2) E) (N (u 6025336) E)) (N (N (v 3924309 20) E) (N (k 8011896 [7,0,10] [16261464,16269658,16277861,16294249,16302453,16318841,8016997,14824565]) E)))))) (N (N (N (N (N (N (u 115028) (k 8373095 [4,16,1,11] [17047601,17055801,17064025])) (N (k 4473 [1,6,3,8,16] [8658965,8699989,5955879,8716598,8724823,2171479,3228251,8758101]) E)) (N (N (j 2212709 23 [4441172]) E) (N (u 6418552) E))) (N (N (N (u 1175576) E) (N (k 5369973 [1,7] [2408536]) E)) (N (N (k 3223852 [7,10] [4538388,6561813,6570021,6504789,2933081,6578773,6586969,6595413,6603637]) E) (N (w 7459173 [7,4]) E)))) (N (N (N (N (v 639072 2) (w 9040455 [7,4])) (N (k 4800561 [0,1] [1798172,2072612,4325452,1503316,9707620,9715820,9724020,9732228,2081060,5980468,7045436,7299652,9052756,8225604,7336788]) E)) (N (N (k 2736232 [16,2,1] [5431672]) E) (N (k 6914169 [17,7,0] [12821640]) E))) (N (N (N (v 1663861 20) E) (N (k 5881989 [0,6,1,8] [11804744,5349464,11812968,11829368,11846280]) E)) (N (N (v 3789128 11) E) (N (w 7991350 [8,4]) E))))) (N (N (N (N (N (v 389444 17) (k 8008535 [0,7,1,10,13] [17571888,17580081,1130548,16154677,17588278,17637432,17645625,16564284,17678397,17686590,1548357,17702985,1552469,17707097,17727589,17735785,8438084,8634693,8442452,8639061,17744736,16704354,10388325,16999272,17171305,17326954,10511461,11551849,10515813,11556201])) (N (v 4583456 11) E)) (N (N (k 2424898 [7,0,1,6,22] [90140,4988957,4899114,4997461,5013849,5022293]) E) (N (v 6680705 11) E))) (N (N (N (k 1372297 [20,23,10] [2891820,2924836,2933032,2941252,2957652,918068,2974532,2982740]) E) (N (k 5632058 [17,8,4,16,21,2] [11280453,11288901,8556885,8548949]) E)) (N (N (y 3429225 [7086116,6996564,6587208]) E) (N (k 7721029 [16,6] [15474808]) E)))) (N (N (N (N (v 893048 8) (v 9277837 17)) (N (u 5107832) E)) (N (N (w 3010620 [8,17]) E) (N (k 7034231 [3,1,0,11,27,8] [14352436,14426168,14434612,14377526]) E))) (N (N (N (w 1962006 [8,17]) E) (N (v 6156401 11) E)) (N (N (v 4059200 44) E) (N (k 8007737 [1,17,0,5,10] [4947990,16523333,16531529,16547925,16556119,16564313,16572533,16580727,16588921,5685541,13209909,13435479,15286903,8024917,8590167,10154841,14898039]) E))))))) (N (N (N (N (N (N (N (k 8565 [17,7] [139572]) (u 8450133)) (N (k 3863671 [4,17,9] [8200524]) E)) (N (N (v 2154572 10) E) (N (u 6344824) E))) (N (N (N (k 4169 [0,1,3] [901142,2236485,2244679,516169,2261067,2269297,2277491,2367605,2490487,2523257,2588795,2613373,2621567,2629925,2638455,2671231,2696311,2712703]) E) (N (v 5304376 23) E)) (N (N (k 3052357 [7,17] [4923958]) E) (N (v 7401592 21) E)))) (N (N (N (N (u 586056) (u 8974424)) (N (k 4747348 [7,3,1,6] [9109589,581948,844093,9429333,9478517,7455829]) E)) (N (N (u 2679348) E) (N (u 6877220) E))) (N (N (N (v 1630496 11) E) (N (k 5816457 [33,3] [11673668,11681892,10871364]) E)) (N (N (k 3731576 [6,1] [7479669,7488369,5620597,6407033,7496573,7505013]) E) (N (w 7925864 [0,1,17]) E))))) (N (N (N (N (N (k 323669 [6,0] [663852,33332,680788]) (k 8007783 [7,0,21,10,27] [14721096,17440864,17449064,17465465,17473673,17269096,17293674,16486773,16675193,17482117,17490313,8057973,14840965])) (N (k 4440437 [13,0,1] [9052209,9056306,2986042,2981949,6017094,7065678,6013237,7061817,8257860,8335685,8331590,8753481,8749390,9069141,9077337]) E)) (N (N (k 4213 [7,0,1,3] [3923993,4857882,4931611,4948026,4972608,4980802,81989,5029959,5038152,5111881,5128266,5234763,1130581,5242967,5324889,5357659,5382248,5415018,5464181,5472375,5529721,5537915,5546325,5579095,5587289,5603703,5612119,5628535,5636933,5645399,5653623]) E) (N (k 6574186 [6,0,17] [13197640,12952200]) E))) (N (N (N (k 1372245 [6,12,17] [2761540]) E) (N (y 5566568 [11043704]) E)) (N (N (k 3428420 [7,1] [6955093,6963317,6627626,6971989,6988629,6996825]) E) (N (u 7663752) E)))) (N (N (N (N (u 843892) (k 9236501 [32,6] [18489402,18497649,1351797,1089657,18505853,8967029])) (N (v 4993149 11) E)) (N (N (v 2945893 23) E) (N (w 7118921 [17,0,1]) E))) (N (N (N (u 1896788) E) (N (f 6074488 [12198520]) E)) (N (N (v 3989600 2) E) (N (k 8012114 [7,1,17] [16097308,16392236,16400984]) E)))))) (N (N (N (N (N (N (v 192836 6) (j 8549463 2 [17178672,17113140,17186872,17195068,17203268,17211464])) (N (k 4386917 [23,20,13] [6148132,1351748,1794120,8790092,6955092,7225636,1589572,8798548]) E)) (N (N (y 2265973 [4555320,4244324]) E) (N (k 6484004 [5,4] [12984410]) E))) (N (N (N (k 1114231 [11,1] [2498656,2506856,2515064,2351392,2375976,909620]) E) (N (y 5432181 [8188212]) E)) (N (N (v 3318597 17) E) (N (k 7532618 [17,4] [7942741]) E)))) (N (N (N (N (k 446591 [0,11] [1351700,1450036,1458244,1466452,1474692,1417512,1048968]) (w 9105529 [17,37,23])) (N (w 4882516 [7,0,10]) E)) (N (N (k 2425669 [7,17,1] [4923962,5571413]) E) (N (k 6950996 [5,0,1,10] [14032962,14057546,13132666]) E))) (N (N (N (k 1659269 [0,6,1] [3547240,3555464,3563808,3440940,3367544]) E) (N (w 5959784 [0,4]) E)) (N (N (k 3862586 [17,1] [7741525,7749749,7758165,6644285,7766613,7774837]) E) (N (u 8056952) E))))) (N (N (N (N (N (f 450681 [925740]) (v 8843300 23)) (N (v 4644936 44) E)) (N (N (k 2424905 [7,17,0,6] [5120085]) E) (N (k 5878143 [6,11,1,0,8] [6115380,13336644,13508693,13525109,7561557,8720964,1581909,12641160]) E))) (N (N (N (u 1499236) E) (N (k 5632869 [17,1,4,8] [9466469,9474917]) E)) (N (N (v 3600710 1) E) (N (u 7790728) E)))) (N (N (N (N (v 954500 4) (k 9367673 [19,7,16] [11596072])) (N (u 5169991) E)) (N (N (u 3076185) E) (N (k 7246455 [28,21,23,8] [14557240,14565496]) E))) (N (N (N (v 2011701 10) E) (N (j 6197621 21 [12460320]) E)) (N (N (j 4108612 13 [8265761,8273965,8282181,8290377,8249649,8253746,2953530,2949437,7823938,7897674]) E) (N (k 8298832 [17,1,0,6] [16621909,7812181]) E)))))))) (N (N (N (N (N (N (N (N (u 24697) (v 8376426 1)) (N (v 4218925 17) E)) (N (N (k 2060852 [7,17] [4268106,4219190,4277093]) E) (N (j 6320213 1 [12656760]) E))) (N (N (N (v 1073440 11) E) (N (k 5091941 [6,1,16,5,9] [123461,10289765,10503029,10560631,10577527]) E)) (N (N (k 3051817 [7,10,4] [6365221,6373717,6251093,2572889]) E) (N (k 7233895 [19,1,4,29,16] [14754181,14697349,14762893,14771333]) E)))) (N (N (N (N (u 552984) (k 8941623 [7,1,17] [16097624])) (N (k 4747316 [7,0,1,6,10,17] [90136,5775386,1613909,9511001,9412949,9462133]) E)) (N (N (u 2650488) E) (N (k 6811701 [0,5,4,17] [13705288,13713512,13042056]) E))) (N (N (N (k 1373061 [20,23,10] [3219744,2941228,3195988]) E) (N (k 5787989 [7,4,21] [11592264]) E)) (N (N (v 3698777 17) E) (N (k 7831671 [17,3,25] [15778168]) E))))) (N (N (N (N (N (v 282932 17) (v 8679488 17)) (N (v 4477013 17) E)) (N (N (v 2376324 4) E) (N (u 6578245) E))) (N (N (N (v 1339480 17) E) (N (j 5534069 2 [10969976]) E)) (N (N (v 3432533 23) E) (N (v 7577725 11) E)))) (N (N (N (N (v 815420 17) (v 9203744 8)) (N (k 5005669 [7,4,16,17] [10035274,10043479,8360277]) E)) (N (N (w 2830425 [17,2]) E) (N (v 7106612 1) E))) (N (N (N (j 1847596 4 [3744072]) E) (N (k 6045770 [4,0,24] [12132984]) E)) (N (N (y 3924601 [7938148]) E) (N (u 8126841) E)))))) (N (N (N (N (N (N (v 159800 17) (k 8548421 [7,1,0,6,10,17] [17113173,17121369,17130069,17138293])) (N (k 4325686 [7,1,10,4] [1527893,7573845,8708693]) E)) (N (N (v 1958028 16) E) (N (j 6438970 4 [12919112]) E))) (N (N (N (v 1183832 17) E) (N (u 5402712) E)) (N (N (v 3305524 10) E) (N (k 7234663 [7,6,9] [10289460,14942548]) E)))) (N (N (N (N (v 671829 17) (v 9072696 24)) (N (k 5247 [7,0,10,20] [9773108,9781301,9789500,9797693,9805892,9814085,9822284,9830484,9838724,5587508,6021685,8340036,8618565,9339476]) E)) (N (N (v 2774101 17) E) (N (v 6955128 4) E))) (N (N (N (k 1659265 [6,0,1] [3481644,3489892,3498100,3514500,3531092,3334776]) E) (N (k 5881993 [20,0,11] [2580568,5255460,11870504,9228628,11879048]) E)) (N (N (k 3818357 [3,1,0,13,8] [7676010,7659814,4702529,6766925]) E) (N (j 8016248 20 [4891192]) E))))) (N (N (N (N (N (u 409924) (v 8794232 8)) (N (v 4616512 10) E)) (N (N (f 2519111 [5054584]) E) (N (k 6713433 [4,11,0] [13443140,5726500,8041300,12608648]) E))) (N (N (N (u 1471300) E) (N (u 5664853) E)) (N (N (u 3567956) E) (N (u 7757924) E)))) (N (N (N (N (v 827533 11) (w 9322569 [32,6])) (N (w 5133157 [7,19]) E)) (N (N (k 2831493 [16,6,1,8] [5825128,5923464,4588352]) E) (N (w 7237721 [17,7,0]) E))) (N (N (N (u 1991236) E) (N (v 6185248 11) E)) (N (N (u 4079957) E) (N (w 8257655 [16,4]) E))))))) (N (N (N (N (N (N (N (k 94256 [7,1,17] [180820]) (k 8372315 [7,17,0,21] [16982117,16990325,16896357,16970101])) (N (k 4264041 [17,23,13] [8593476,7168292]) E)) (N (N (u 2155060) E) (N (u 6385785) E))) (N (N (N (u 1143076) E) (N (k 5092727 [7,3,15,0] [10257269,10322821,10544501,10577285]) E)) (N (N (v 3240000 11) E) (N (k 7434344 [7,21,0,15,4,17] [14566249]) E)))) (N (N (N (N (u 618856) (u 9007177)) (N (k 4804694 [0,1,2] [4145444,4149588,9642340,9646452]) E)) (N (N (u 2711672) E) (N (k 5879159 [0,1,5,10,27,8,4] [13836336,5468212,12148789,13844536,13852729,13877308,13377605,13885513,10309749,13893753,13418821,13820277,5632566,13296190,7721558,10257269,12067705,12796808,13075338,13567349]) E))) (N (N (N (u 1667116) E) (N (v 5861432 24) E)) (N (N (k 3760436 [0,4] [7544880,5718344]) E) (N (k 7934020 [7,6,11,21,10,16] [15934279]) E))))) (N (N (N (N (N (u 352568) (k 8007785 [7,0,21,10] [17506405,17514613,13476455,15311479])) (N (w 4550708 [1,3]) E)) (N (N (j 2429290 8 [4890952]) E) (N (v 5877885 11) E))) (N (N (N (v 1388664 8) E) (N (k 5583741 [6,11] [11104341,11214965]) E)) (N (N (u 3502404) E) (N (w 7696521 [26,8]) E)))) (N (N (N (N (k 827514 [0,13,4] [934456]) (v 9113661 10)) (N (w 5054809 [17,8,4]) E)) (N (N (k 2830918 [7,1,10] [3997996,5792344]) E) (N (v 7118949 8) E))) (N (N (N (y 1843597 [3874852]) E) (N (v 6123889 11) E)) (N (N (v 4026440 44) E) (N (k 8012122 [7,1,17] [6333016,16269944]) E)))))) (N (N (N (N (N (N (k 4153 [1,6,17,3,16,5] [24598,467013,507975,516169,524405,548985,565629,598645,615285,631927]) (v 8613976 17)) (N (k 4411717 [17,6,1] [7258436]) E)) (N (N (v 2323316 4) E) (N (j 6516804 5 [13049912,13058152]) E))) (N (N (N (v 1261657 17) E) (N (k 5468997 [12,10,1,5] [10953061]) E)) (N (N (u 3371114) E) (N (k 7561319 [6,0,17] [15147080,15082596]) E)))) (N (N (N (N (f 741685 [1516080]) (v 9138552 13)) (N (j 4923449 4 [9904196]) E)) (N (N (v 2842741 4) E) (N (k 7037043 [1,3,11,0] [13643804,14098516,14114916,14123124,14131332,14139684,13759028]) E))) (N (N (N (v 1798176 11) E) (N (k 5992517 [6,1,5] [12001397,12009593,9196661]) E)) (N (N (w 3891541 [20,0]) E) (N (k 8077920 [0,1,7,6] [16195612]) E))))) (N (N (N (N (N (k 446570 [6,32,1] [934186,991601,1007989,1040761,1048957,1065589]) (v 8876080 14)) (N (k 4584535 [17,1] [7369284,7283300]) E)) (N (N (v 2564458 34) E) (N (w 6767991 [2,17]) E))) (N (N (N (u 1523832) E) (N (k 5722183 [7,17,1] [11477048,11486040]) E)) (N (N (u 3633236) E) (N (k 7745653 [0,3,1,17] [13914181,15671367,15720521,15728728,15769690,15454325,15794295,15802489,14012743,15470967,15811397]) E)))) (N (N (N (N (f 827785 [2039852,917560,1737352]) (w 9375849 [34,4])) (N (k 5091701 [5,6,7,17,16,21,3] [10428474,10444871,10469463,10477876,8139093,148037,10494805,10503029,10511447]) E)) (N (N (v 3092602 16) E) (N (w 7303272 [4,16]) E))) (N (N (N (k 2060306 [7,0,1] [4137028,4145236,4153460]) E) (N (u 6254677) E)) (N (N (v 4157524 17) E) (N (v 8351808 17) E))))))))) (N (N (N (N (N (N (N (N (N (v 12357 6) (u 8401000)) (N (k 4202596 [7,4,17] [7938650]) E)) (N (N (k 2060580 [7,1,17] [4235338,4244325]) E) (N (u 6299752) E))) (N (N (N (k 1032532 [0,13] [2138400,2105648]) E) (N (k 5091909 [6,1,5,23] [135285,8868213,115269,10281557,10494837,10527863,10544503]) E)) (N (N (k 3051813 [3,1,4,11,17] [4874296,6332490,6242901,2564697]) E) (N (v 7352441 4) E)))) (N (N (N (N (k 446579 [0,11] [1089564,1097780,1106212,991624,1122868]) (k 8912953 [7,4] [17866868,17400184])) (N (v 4726868 4) E)) (N (N (k 2621544 [23,2,1] [5284200]) E) (N (k 6815834 [2,0] [13672824]) E))) (N (N (N (w 1372725 [4,0]) E) (N (k 5779829 [7,3] [7270741,11060053,11182965]) E)) (N (N (k 3556165 [6,1,12] [7381109,7258420,811341,7389557,5567093,3154765,7365493]) E) (N (w 7865157 [4,16]) E))))) (N (N (N (N (N (w 274517 [0,6]) (v 8663104 17)) (N (v 4452472 23) E)) (N (N (k 1958761 [3,0,1] [4759588,4767812,4358436,4080228,4465268,4784772,4703316]) E) (N (v 5877873 11) E))) (N (N (N (u 1319016) E) (N (u 5517416) E)) (N (N (v 4221 11) E) (N (k 7577721 [19,1,11,4] [15245381,15253621,13889863,15262071]) E)))) (N (N (N (N (k 447615 [6,11,0] [1613876,1622076,1630276,1646908]) (u 9183528)) (N (k 4993093 [6,1] [9777269,10002557,9834869]) E)) (N (N (v 2884437 23) E) (N (k 7037051 [10,11] [13652260,14197036,13783604]) E))) (N (N (N (v 1847384 17) E) (N (k 5877847 [6,1,0,24,8] [12099656,12124234,12140673,12148869,12222601,12238989,12247416,12272005,9294981]) E)) (N (N (u 3944788) E) (N (u 8138872) E)))))) (N (N (N (N (N (N (w 143652 [1,17]) (k 8373607 [8,4] [17080369,17088569])) (N (u 4337988) E)) (N (N (k 1958020 [7,4] [4497972]) E) (N (k 6435189 [6,1] [12886056,12894250,12910650,12927050,11845717,12935257,12943464,12951658,12206197,12959865,7127893]) E))) (N (N (N (v 1183824 2) E) (N (v 5386266 17) E)) (N (N (u 3277401) E) (N (v 7483424 11) E)))) (N (N (N (N (k 446585 [0,1,3,13] [1351701,1138710,1368117,1376341,1384537,1392949,1401145]) (v 9048120 13)) (N (v 4849796 4) E)) (N (N (k 2424955 [16,6,1] [5210472,5448072]) E) (N (v 6955066 17) E))) (N (N (N (v 1716516 4) E) (N (f 5898360 [11838072]) E)) (N (N (k 4425 [1,6,3,0,13] [7643253,4751987,6054519,6791803,7078527,7668597]) E) (N (k 8007735 [1,7,0,17,10] [6324296,6340681,16031818,16080976,16089170,16105560,16138330,16154725,16228457,16253048,16326778,16343173,16351369,4948264,16359760,16384338,16408917,16417112,16441689,16449882,16458085,16474473,16482693,16507273,10445653,11469657,10474581,11506777,7984229,10138729,14808197,15144073]) E))))) (N (N (N (N (N (j 324237 5 [278564,827444,835652,843860,721188,852292]) (v 8794136 17)) (N (v 4599872 10) E)) (N (N (u 2490713) E) (N (v 6680717 11) E))) (N (N (N (v 1445988 8) E) (N (v 5648440 17) E)) (N (N (k 4421 [0,1,6,10] [7118954,5550197,7159927,7200889,7217279,3137837,7250245,7291253,426567,860747,4711027,6038135,6783611,7070335,7373637,7398261,7423095,7431295]) E) (N (k 7745589 [1,6,0,3] [15507569,15515763,13914229,15581303,15605881,15614075,15630461,15638655,14029173]) E)))) (N (N (N (N (j 925988 23 [1146920]) (k 343 [0,1,6,2,14] [18653233,3285045,18661433,18669629,18186309,18677833,18686065,12079221,18694265,18727037,9142581,15827517,18735685,14955125,17752951,18150271,10671223,11727999])) (N (k 5096823 [15,7,0] [10232712]) E)) (N (N (u 3026988) E) (N (k 7221300 [17,1,0,5] [14458984]) E))) (N (N (N (v 1962105 4) E) (N (u 6156409) E)) (N (N (k 3862857 [7,6,17] [8167485,8175701,7856429,590140,852285,8192341,8200565,8209493]) E) (N (k 8257621 [1,0,17,6] [13639737,5694005]) E))))))) (N (N (N (N (N (N (N (k 9077 [7,17] [172373]) (u 8466537)) (N (w 4268086 [1,8]) E)) (N (N (y 2154828 [4194356,4367172]) E) (N (u 6369384) E))) (N (N (N (j 1114187 2 [663604,2253092]) E) (N (k 5092215 [7,3,0,1,6] [81972,1601637,10657912,164148,7426661,10240869,10306437,10528101,10560901]) E)) (N (N (k 3223589 [7,1,17] [278616]) E) (N (v 7417976 21) E)))) (N (N (N (N (v 565333 17) (k 8970329 [6,1] [17973270,2531397])) (N (k 5239 [0,1,5,10] [9609264,9699377,9703474,1130548,1785909,1790006,2527288,9740345,2887738,2523196,2883645,9744446,5550148,5582917,5976134,6385737,9756748,7041102,1486932,2068566,192613,634985,1483060,2064693,7291204,7577925,9044308,8876389,5546548,5972533,5579318,9761336,7037497,6382142,8217156,8311365,8307270,8729161,8725070,7295572,7582294,189285,631657,8873317]) E)) (N (N (u 2691687) E) (N (v 6893624 26) E))) (N (N (N (w 1642617 [6,1]) E) (N (k 5845080 [17,1] [90164,11706436,10895668,11117397,11232117]) E)) (N (N (w 3736693 [1,10]) E) (N (k 7934005 [7,4,16,10] [15900757,15909205]) E))))) (N (N (N (N (N (k 323673 [17,30] [696644]) (k 8716409 [23,21,7] [8065112,5493028,8073556,17277560])) (N (v 4522585 17) E)) (N (N (k 2429242 [1,8,17,22] [4890984]) E) (N (v 6631717 23) E))) (N (N (N (v 1388632 17) E) (N (k 5583685 [6,1,18,5] [11182453]) E)) (N (N (u 3486020) E) (N (w 7676261 [6,17,1,2]) E)))) (N (N (N (N (u 840057) (w 9236549 [17,32])) (N (u 5058901) E)) (N (N (k 2830458 [7,21] [5742936,5849448,4915768]) E) (N (v 7147607 21) E))) (N (N (N (u 1908840) E) (N (k 6045833 [21,0,8] [9310296,5484836,9326932,12231304]) E)) (N (N (v 4010033 13) E) (N (k 8012120 [1,7,0,17] [6349129,16073034,16204117,16245081,16261480,16335210,16425333,16433529,7869525,10130521]) E)))))) (N (N (N (N (N (N (k 103253 [6,12] [254252,393540]) (v 8585284 17)) (N (v 4403240 13) E)) (N (N (j 2306074 20 [4038728]) E) (N (k 6435959 [4,16,1] [11845700,13017160,12726408,7151956,7418468]) E))) (N (N (N (k 1114233 [1,0,3] [2531349,2375702,2539558,2547797,2555993,2564405,2572601,2581045]) E) (N (u 5451850) E)) (N (N (k 3224118 [8,20,10] [6725956]) E) (N (k 7520373 [7,4,21,16] [9924709,9957733]) E)))) (N (N (N (N (v 721028 4) (k 9121864 [32,23] [18260085,8925305])) (N (w 4927572 [44,4]) E)) (N (N (j 2830378 8 [5677384]) E) (N (u 7012426) E))) (N (N (N (k 1659273 [0,4] [3579948,3392120]) E) (N (k 5877817 [6,1] [11968629,11976829,9253749]) E)) (N (N (v 3867221 17) E) (N (k 8011877 [0,1,13] [1396808,1392728,16162912,16171112,16179320,16183432,16188000,16204392]) E))))) (N (N (N (N (N (v 471336 17) (v 8781925 17)) (N (k 4583769 [7,0] [9347133]) E)) (N (N (v 2568296 8) E) (N (k 5878341 [6,1,5,2] [168053,13541701,13549909,11571581,5640821,7250757,13558903,13567351]) E))) (N (N (N (j 1372549 1 [3055656,3063904,3072104,3080312,3088672,2924844]) E) (N (v 5705788 17) E)) (N (N (u 3608660) E) (N (v 7749757 11) E)))) (N (N (N (N (f 987256 [1729144]) (w 9380453 [34,4])) (N (y 5166167 [10395696,1212468,10403896,10412092,10355560]) E)) (N (N (v 3092533 13) E) (N (w 7233627 [7,29,23]) E))) (N (N (N (j 2012245 23 [4047956]) E) (N (j 6234216 4 [12378453]) E)) (N (N (v 4128841 17) E) (N (v 8007744 2) E)))))))) (N (N (N (N (N (N (N (N (u 41049) (y 8376665 [16818792])) (N (k 3863413 [6,1,16] [8495137,8503353,7955034,4662081,6701901]) E)) (N (N (j 2060868 8 [4178230,4202814,3506789,3785321]) E) (N (v 6336885 2) E))) (N (N (N (v 1093932 17) E) (N (k 5091957 [5,6,7,3,16,21] [135253,10477876,131653,10593367]) E)) (N (N (w 3051895 [16,4]) E) (N (k 7233909 [7,0,21,10] [14786650,14803047,14827627,14835831,14852219,8368485,14860661]) E)))) (N (N (N (N (u 569640) (v 8958000 13)) (N (w 4763733 [0,6]) E)) (N (N (v 2662489 17) E) (N (k 6811717 [0,5,17] [13738088,7664468,12756104]) E))) (N (N (N (k 1373269 [6,20] [3252524,3155028]) E) (N (k 5346119 [6,1,5,2,13] [10706996,11640886,11657272,1609861,11665545,10862900,9106053,11412357,11551877,11625869]) E)) (N (N (v 3715124 20) E) (N (k 7746101 [6,1] [15835192,15811189]) E))))) (N (N (N (N (N (u 307541) (v 8691784 7)) (N (v 4493388 10) E)) (N (N (v 2396780 2) E) (N (k 6574152 [6,23] [7168837]) E))) (N (N (N (k 1355828 [1,8] [2408472]) E) (N (k 5461111 [6,0,1,7] [1617972,11116648,11124856,11059556,7459396,11010952]) E)) (N (N (y 3433301 [6906180]) E) (N (w 7639146 [9,4]) E)))) (N (N (N (N (w 827481 [6,17]) (v 9216068 11)) (N (k 4993141 [1,6,3,16,17] [9777237,10068055,10076249,9810261,9818455,10084697]) E)) (N (N (v 2928728 17) E) (N (v 7123000 17) E))) (N (N (N (u 1880164) E) (N (v 6074440 21) E)) (N (N (k 3862603 [17,3] [7971380,7856700]) E) (N (v 8011913 4) E)))))) (N (N (N (N (N (N (k 102793 [5,17] [368964,377172]) (w 8553077 [16,7])) (N (y 4362836 [8684084]) E)) (N (N (u 2269797) E) (N (u 6439016) E))) (N (N (N (v 1183848 8) E) (N (u 5419572) E)) (N (N (u 3317826) E) (N (k 75 [3,1,0,8,4] [15048756,15089749,15097957,15106165,15114365,15122805,9917815]) E)))) (N (N (N (N (k 446587 [0,11] [917560,1138980,1417516,1040776,1425972]) (k 9080933 [6,1,16,5] [18194553])) (N (k 4882493 [8,10] [6029620,8348484,9347924]) E)) (N (N (k 2425207 [16,6,1,8] [5079912]) E) (N (f 6987896 [13123960]) E))) (N (N (N (u 1749332) E) (N (k 5882232 [6,32,1] [11780426,11903345,11846005,11878777,11911549,9237621]) E)) (N (N (v 3842945 11) E) (N (k 8011858 [7,1,17,22] [16097324,16040280]) E))))) (N (N (N (N (N (k 324741 [17,2,1] [794940]) (v 8822884 17)) (N (v 4632640 10) E)) (N (N (u 2519399) E) (N (k 6713450 [6,0,17] [7885652,12625032]) E))) (N (N (N (y 1442644 [2949700]) E) (N (u 5681237) E)) (N (N (v 3579976 23) E) (N (y 7758116 [15573016,15548772]) E)))) (N (N (N (N (v 954452 10) (w 9347157 [17,32])) (N (w 5150327 [15,7]) E)) (N (N (v 3055733 4) E) (N (v 7254120 17) E))) (N (N (N (k 2011700 [7,17] [4038682,4047685,4055909]) E) (N (u 6205544) E)) (N (N (y 4108337 [2121764,8233044,8241268,2097444,8249924]) E) (N (v 8302664 17) E))))))) (N (N (N (N (N (N (N (k 102489 [6,12] [237860,254276,262484]) (v 8499249 17)) (N (k 4264553 [17,4,20] [8626252]) E)) (N (N (k 1958004 [7,0,10] [1958245,3031401,3514741,3793273,4432452,4457317,4465513,4473957,4482165]) E) (N (u 6398025) E))) (N (N (N (v 1138796 2) E) (N (v 5353498 45) E)) (N (N (v 3256696 4) E) (N (w 7233913 [7,4,10,21]) E)))) (N (N (N (N (k 446583 [0,11,1] [1286200,1294408,1302616,1310816,1319016,1327224,1335432,1106208,1138984,1008008]) (k 8937573 [7,4,21,16] [18063465])) (N (k 4804702 [7,6,0,1] [2899988]) E)) (N (N (k 2424951 [0,1,6] [3440696,5480520,5488728,5496928,5505128,5513336,5521544,5185896,5423496]) E) (N (v 6926404 21) E))) (N (N (N (u 1683560) E) (N (k 5877815 [6,1,0,13] [2629704,11771978,11788417,11796613,11862153,11886733,11895160,11919749,11944333,9204869]) E)) (N (N (y 3780916 [6979908]) E) (N (w 7975767 [7,4]) E))))) (N (N (N (N (N (j 323929 30 [761908,663844]) (k 8761461 [17,23,7] [17539144,17310328])) (N (k 4709 [6,1,16] [9150585,4833907,6095479,6832763,7103103,8487797]) E)) (N (N (k 2424890 [8,17,1,22] [4874536,4882730,4956522,4964949]) E) (N (k 6656068 [6,0,8] [1589573,7226181]) E))) (N (N (N (v 1421640 17) E) (N (u 5611656) E)) (N (N (w 3518512 [23,11]) E) (N (v 7704632 27) E)))) (N (N (N (N (v 893000 23) (w 9277540 [36,7,10])) (N (k 5091397 [6,1,5,0] [41029,10199125,10207336,86133,8843637,10241143,10257783]) E)) (N (N (u 2990404) E) (N (v 7032957 11) E))) (N (N (N (k 1844357 [4,16,1] [3809584]) E) (N (v 6136096 11) E)) (N (N (w 3862651 [4,16,20]) E) (N (k 8012165 [1,16,6] [5488696,16490592,16498792,16130664,16302728]) E)))))) (N (N (N (N (N (N (w 233845 [17,0]) (k 8610149 [8,15,0,21] [17277033,17285241])) (N (k 4677 [0,1,3,13] [8831045,8888391,8896585,1486965,8904823,8953977,8986751,3186989,9044341,442951,877131,4792947,6079095,6816379,7094911,8438645,8635255,8758137,8807295,9086071,9102463]) E)) (N (N (j 1958468 8 [3997997,4292948,4407637,4432228,3531381,3809913,4694869,4703065]) E) (N (k 6436471 [4,16] [12206148,13082696]) E))) (N (N (N (j 1114235 11 [2596916,2375972,2605356,917812]) E) (N (k 5469037 [11,10] [10985557,11001957]) E)) (N (N (k 3224421 [20,23,10] [2973996,6579020,6759508]) E) (N (w 7581813 [19,1]) E)))) (N (N (N (N (v 741977 17) (j 9154933 1 [18325624])) (N (w 4956213 [8,4]) E)) (N (N (k 2830410 [1,17,8,22] [5677368,5742968,4883000]) E) (N (y 7045236 [13775412]) E))) (N (N (N (v 1810720 11) E) (N (k 5992565 [17,6,1,7] [94248,12001365,11710760]) E)) (N (N (y 3892309 [7823684]) E) (N (v 8102248 8) E))))) (N (N (N (N (N (v 503848 44) (v 8892484 16)) (N (k 4698509 [30,17] [9412676,9420884,9429092,8192340,7267156]) E)) (N (N (u 2564473) E) (N (v 6791224 8) E))) (N (N (N (j 1372557 11 [3121188,2933036]) E) (N (k 5722199 [6,0,17] [11509832,11490136]) E)) (N (N (u 3649620) E) (N (j 7835784 3 [15704424]) E)))) (N (N (N (N (k 828037 [0,13,4] [2072608,2080816,917564,2015540,2056504,2113860,2130260]) (v 9416753 10)) (N (v 5222456 17) E)) (N (N (f 3051607 [6267016,2539816,4866356]) E) (N (k 7233653 [7,0,10,27] [14655568,14663768,14680169,14688377,13378151,14697079]) E))) (N (N (N (y 2060318 [2293796]) E) (N (j 6266997 3 [12558456]) E)) (N (N (k 4169844 [7,4,17] [7914074]) E) (N (k 8007752 [0,1,5,10] [11276311,11272231,16752695,16900155,16756807,16904267,16932951,16973915,16937063,16978027,16695591,8536375,13451591,14877015,15294823,13455927,8540743,15299159,14881383,16999239,17040231,17044567,17073511]) E)))))))))) (N (N (N (N (N (N (N (N (N (N (k 4149 [7,6,1,3,16,17] [24602,41029,49225,73803,82037,106617,115013,123237,131445,148085,164725,189559]) (j 8376424 7 [16802133,16818521,16826725,16834921])) (N (k 3862905 [7,4,18,17] [8413245,8421476,7930458]) E)) (N (N (y 2060358 [4136992,4219716]) E) (N (k 6152551 [6,1,11] [5619797,12607577,12615784,12623978,12550261,12632185,7479637,12583285]) E))) (N (N (N (k 1032516 [0,4] [2122016,2097456]) E) (N (w 5210997 [6,17,16]) E)) (N (N (v 3051641 4) E) (N (k 7324279 [16,6] [14672760]) E)))) (N (N (N (N (j 492149 16 [999472]) (v 8912945 17)) (N (k 4718989 [9,4,11,3] [9461828,9470036,9478244,8200532]) E)) (N (N (j 2621528 1 [1179944]) E) (N (v 6815802 17) E))) (N (N (N (v 1577276 17) E) (N (j 5723223 2 [10879316,8213060,11527272]) E)) (N (N (v 3645766 1) E) (N (u 7868536) E))))) (N (N (N (N (N (v 262485 17) (v 8650869 4)) (N (v 4452432 10) E)) (N (N (v 2355820 2) E) (N (u 6553720) E))) (N (N (N (k 1114743 [20,23,3] [2646072,2654312,2662960,2564668]) E) (N (u 5505144) E)) (N (N (k 3224709 [4,16,20] [6840352,6603596,6702164]) E) (N (w 7577705 [19,8]) E)))) (N (N (N (N (w 790596 [20,0]) (k 9121929 [13,10] [18374692,8925272,1298724,18383144,8941908])) (N (k 4956276 [7,4] [8421956]) E)) (N (N (u 2884158) E) (N (u 7078008) E))) (N (N (N (k 4203 [6,1,16] [3694725,3752077,3760513,3817861,3850633,3867021,3892101,3900549]) E) (N (k 5877845 [7,0,24] [12083304]) E)) (N (N (w 3924550 [11,1]) E) (N (v 8126810 2) E)))))) (N (N (N (N (N (N (u 135224) (v 8519737 4)) (N (u 4329561) E)) (N (N (v 2212965 23) E) (N (u 6426744) E))) (N (N (N (j 1183770 23 [2383908]) E) (N (u 5378612) E)) (N (N (v 3276837 10) E) (N (w 7234149 [7,4,16]) E)))) (N (N (N (N (f 639096 [1032568]) (k 9048118 [4,0] [18112568])) (N (v 4849772 2) E)) (N (N (v 2736264 8) E) (N (k 6950964 [1,5,0,17] [13918265,13926458,13934696,13942890,13959288,13967482]) E))) (N (N (N (v 1659009 11) E) (N (f 5898344 [11821688]) E)) (N (N (v 3732365 11) E) (N (v 7992172 2) E))))) (N (N (N (N (N (k 324164 [17,7,6] [680261,811845]) (v 8781873 17)) (N (u 4591701) E)) (N (N (k 2490709 [0,1,7,6] [5005352]) E) (N (f 6688888 [12559480]) E))) (N (N (N (v 1445972 17) E) (N (w 5636421 [1,8]) E)) (N (N (j 3429477 23 [6955044,7020836,7061828,6914644,6595400]) E) (N (v 7721044 4) E)))) (N (N (N (N (k 827529 [23,20,11,13,4] [1859648,1868068,1876264,1884484,1892692]) (k 9113673 [32,17,2,5,3] [18636869,18641013,8897093,8901493])) (N (k 5096567 [7,0,1,17,6] [10248312,7385668,10216328]) E)) (N (N (v 3019360 2) E) (N (v 7209268 8) E))) (N (N (N (v 1970296 4) E) (N (u 6164584) E)) (N (N (w 4067652 [17,5]) E) (N (k 8257609 [17,7,0,6] [16539733]) E))))))) (N (N (N (N (N (N (N (k 8821 [17,7,6] [139572,155989]) (u 8450421)) (N (k 4264024 [1,4,7,16,10,17] [8544278,8552502,7528789,6349374,8561222,1565525,2655065,8569941]) E)) (N (N (j 2154820 23 [4350788]) E) (N (k 6153071 [5,1,23,4] [12738613,12755013]) E))) (N (N (N (j 1114183 2 [2253096]) E) (N (k 5300361 [3,13] [10641476]) E)) (N (N (w 3052663 [9,17,4]) E) (N (k 7389291 [17,23,10] [7778868]) E)))) (N (N (N (N (k 565330 [0,1,7,6] [1204252]) (v 8982554 45)) (N (k 4788288 [7,6,0,1] [2900004]) E)) (N (N (f 2691671 [5398648]) E) (N (u 6873162) E))) (N (N (N (w 1642584 [6,1]) E) (N (v 5832804 17) E)) (N (N (v 3736433 11) E) (N (k 7934004 [7,6,11,21,16,10] [15884359]) E))))) (N (N (N (N (N (v 331812 17) (k 8716392 [7,17,0,21] [16503141,17457525,8090725,14849141])) (N (v 4526180 8) E)) (N (N (u 2429013) E) (N (k 5877881 [6,1,11] [6115349,13262917,13279333,13287751,13295975,7201349]) E))) (N (N (N (v 1372289 11) E) (N (w 5574745 [28,8,0]) E)) (N (N (v 3473525 4) E) (N (k 7578181 [6,1,9,5,2] [15360325,15368549,11612541,13825143,15378039]) E)))) (N (N (N (N (u 856168) (v 9240689 11)) (N (k 4993397 [7,6,1,3,16,17] [10117194,5591125,10133591,10149977,8343893,8622423,10158425,10027620]) E)) (N (N (v 2946149 23) E) (N (j 7147591 1 [14311528]) E))) (N (N (N (k 1843589 [1,6] [3825704,3833960,3842184]) E) (N (k 6075016 [1,6] [12214300,12181864,12198264]) E)) (N (N (v 3989640 20) E) (N (v 8192600 17) E)))))) (N (N (N (N (N (N (k 103045 [7,3,17] [418116]) (v 8585272 13)) (N (u 4391252) E)) (N (N (u 2297896) E) (N (u 6484053) E))) (N (N (N (u 1245288) E) (N (v 5443656 5) E)) (N (N (v 3318645 4) E) (N (k 7520341 [6,1,8] [9924725,9974133]) E)))) (N (N (N (N (v 720964 23) (v 9113649 10)) (N (k 5751 [6,1,16,11] [9855024,9871409,9887800,9895993,5603894,6390334,8364612,8389190,9355862]) E)) (N (N (w 2425975 [9,17,1,4,7]) E) (N (u 7016532) E))) (N (N (N (f 1769608 [3383928]) E) (N (k 5882253 [20,0,4,11] [1351716,1466420,11952196,1589332,11870508]) E)) (N (N (v 3866741 4) E) (N (k 8011866 [1,7,17] [16048472,16146808]) E))))) (N (N (N (N (N (w 450922 [36,4]) (v 8851532 11)) (N (v 4644952 1) E)) (N (N (k 2424906 [1,7,0,17] [4940073,4907306,5136725,5161305,5169512,5177706,5185909,5210489,5218901,5227097]) E) (N (f 6754424 [12657784]) E))) (N (N (N (u 1499252) E) (N (v 5705776 13) E)) (N (N (u 3608628) E) (N (k 7749755 [10,11] [13930788,15622444,14062132]) E)))) (N (N (N (N (v 987232 2) (k 9375801 [34,6,3,16,21] [18767957,11583784,18223701,18776677,18748245])) (N (k 5165129 [22,1,0,6] [10379349]) E)) (N (N (k 3051595 [2,17] [712756]) E) (N (u 7274616) E))) (N (N (N (y 2011993 [4087876]) E) (N (k 6152295 [6,1,11] [12329045,12476505,12484712,12492906,12410997,12501113,12370261,12452213]) E)) (N (N (v 4128813 17) E) (N (v 8327541 4) E)))))))) (N (N (N (N (N (N (N (N (k 8309 [17,1,0,7,6] [90152,98393]) (v 8376441 4)) (N (v 4218965 17) E)) (N (N (u 2130789) E) (N (u 6320245) E))) (N (N (N (u 1085484) E) (N (v 5279880 16) E)) (N (N (v 3178837 20) E) (N (v 7373709 11) E)))) (N (N (N (N (k 446581 [0,1,2] [1089561,1138714,1171498,1093689,1142842,1175626,1187920,1196114,1212501,1220696,1228889,1237082,1253480,1261674,1257592,1265786]) (u 8949845)) (N (k 4747317 [7,1,17] [278568,827688]) E)) (N (N (k 2424921 [0,1,7] [1171478,1798185,5333077,5341273,1814821,5349685]) E) (N (f 6848616 [13058424]) E))) (N (N (N (k 1373065 [4,8] [3235908,3204180]) E) (N (k 5345917 [5,10,0,1,8,4] [10338340,11382836,11087941,11210853,11378980,11518260,11084373,11207285,11625559]) E)) (N (N (k 3556471 [23,20] [176196,7381092,7389540]) E) (N (k 7832389 [6,1] [15762008,15786586]) E))))) (N (N (N (N (N (v 299349 17) (k 8611447 [7,4] [17391680,17399880])) (N (u 4493364) E)) (N (N (v 2396200 13) E) (N (k 6590792 [4,0] [12919416]) E))) (N (N (N (v 1347892 17) E) (N (y 5541973 [10989672,10986360]) E)) (N (N (y 3433045 [6906180]) E) (N (w 7639129 [18,4]) E)))) (N (N (N (N (k 4167 [0,1,6,13] [1663018,221269,1671257,1679480,1769594,1777793,1785989,1851529,1900685,901416,1663274,319829,745817,1909121,1974661,2032009,2048397,2065029,2147205,2171785,2188373,2204805]) (k 9122189 [11,0] [1351716,18374700,1458228,18440252,18448452,18456660,18464900,18383148,18334344])) (N (w 5013591 [6,0,17]) E)) (N (N (u 2920824) E) (N (k 7032949 [0,3,1,17] [13635653,14245959,14286921,14295128,14336090,14352485,14360679,14368873,13734215,14377319,7643717]) E))) (N (N (N (v 1843341 11) E) (N (v 6045825 11) E)) (N (N (y 3925077 [7897412]) E) (N (v 8163944 34) E)))))) (N (N (N (N (N (N (v 167992 17) (u 8552537)) (N (k 4362304 [8,10] [8740948]) E)) (N (N (k 2265112 [7,1,17] [4546618,4555365]) E) (N (j 6438986 4 [12919112]) E))) (N (N (N (k 1183834 [2,1] [2449768]) E) (N (w 5410901 [0,4]) E)) (N (N (k 3224116 [1,11,10] [6643770,6651970,6660170,6472005,737609,6512981,2941273,6668661,6676857,369221,787017,6685509,6693717,6701941]) E) (N (k 7508016 [38,6,1] [15032420]) E)))) (N (N (N (N (v 672053 23) (k 9080901 [7,0,17,1,6,13] [41029,18178121,45173,18182265,8835445,8831557])) (N (w 4882485 [8,17]) E)) (N (N (k 2425177 [7,0,1,17] [5595181,5227098]) E) (N (k 6950965 [0,5,4,17] [13983816,13992056,13107592]) E))) (N (N (N (f 1736804 [3351144]) E) (N (u 5931656) E)) (N (N (k 4455 [19,1,4,16] [7692677,7701377,5628805,6415241,7709581,7718021]) E) (N (w 8016472 [8,17]) E))))) (N (N (N (N (N (k 324485 [17,5] [737580,786748,852296]) (y 8781881 [1351700,17653828,17657940,17662052,17670252,16720224,17342824])) (N (k 4583530 [7,10,21] [9232741,9265525,6750781,7139941,7414885,7677033]) E)) (N (N (v 2519143 16) E) (N (k 6713448 [4,17,0,1] [11292726,7528789,8565318,1565525,13460325,12616568]) E))) (N (N (N (u 1479492) E) (N (w 5673816 [6,0]) E)) (N (N (k 3555447 [6,20,0] [7168056,7176264,7184472,7192680,7127432]) E) (N (u 7770404) E)))) (N (N (N (N (f 954412 [1925240]) (k 9322617 [32,6,5] [18702405,18710613,17809735,9151045,18719573])) (N (k 5149815 [4,9,1] [10313864]) E)) (N (N (k 3051541 [7,0,1,17] [90184,4989002,1351765,6119513,6127733,6135929,6144341]) E) (N (w 7245909 [17,28]) E))) (N (N (N (v 1957956 10) E) (N (v 6197361 11) E)) (N (N (y 4080725 [8184100]) E) (N (k 8007739 [17,1,0,11] [16605285,16638085,4948260,16646480,16654680,16478565,16671109,7733812,8049765,14832773]) E))))))) (N (N (N (N (N (N (N (w 102442 [12,3]) (v 8487029 4)) (N (v 4264496 11) E)) (N (N (y 2155348 [4350532,4366924]) E) (N (k 6153575 [1,6,23,11] [12410933,12804153,12550213,12812361,10317941,12820601,12591429,12788085]) E))) (N (N (N (v 1138772 10) E) (N (k 5345333 [1,6,5,16,3] [10707013,10731591,10739785,10756171,10772597,10805367,10821753,10838139,10862917,10887541,10904181,9581687]) E)) (N (N (u 3240508) E) (N (w 7434361 [8,17,23,24]) E)))) (N (N (N (N (k 565354 [21,0,7] [1245544,1270136]) (v 9015397 8)) (N (v 4804697 17) E)) (N (N (v 2708069 23) E) (N (v 6914104 27) E))) (N (N (N (u 1667188) E) (N (k 5869656 [7,10] [11141989,11256693]) E)) (N (N (v 3772484 17) E) (N (v 7934028 2) E))))) (N (N (N (N (N (v 364868 17) (v 8749173 4)) (N (y 4550724 [8184404]) E)) (N (N (k 2424859 [7,1,17] [4940120]) E) (N (k 6656052 [6,11,8,17] [7233605,13328457,11952453]) E))) (N (N (N (u 1413148) E) (N (k 5583991 [9,4,1] [11231336,11239560,11182436]) E)) (N (N (v 3428485 4) E) (N (v 7704624 27) E)))) (N (N (N (N (k 827525 [0,1] [1794088,1802312,1810520,1818720,1826920,1835128,1843336]) (k 9277492 [32,20,3] [18461045,8999797])) (N (w 5083188 [7,4]) E)) (N (N (y 2986032 [2023444,2834476,5988660,5996868]) E) (N (v 7118953 8) E))) (N (N (N (v 1937496 17) E) (N (k 6046085 [21,7,0,4] [12279928,12288288,5484844]) E)) (N (N (v 4026464 2) E) (N (v 8228960 2) E)))))) (N (N (N (N (N (N (w 233589 [0,17,6]) (k 8609895 [17,15,8,10] [17260632])) (N (k 4411765 [7,17] [8143172,7390293]) E)) (N (N (k 1958453 [17,20,10] [3973692,4063828,4285028,4678276]) E) (N (u 6520936) E))) (N (N (N (u 1261881) E) (N (k 5469013 [6,1,5] [10969445]) E)) (N (N (u 3371865) E) (N (k 87 [0,9,1,3,4] [3285045,15163449,10297413,15188041,14590053,15220841,15229041,14651509,15237241,15270013,7684407,14745959,15278455,15319423,15352389,14971509,15385415,13833079,14422911,15393895,10687607,11744383,15410807,15443583]) E)))) (N (N (N (N (w 741689 [11,0]) (v 9146660 17)) (N (k 5759 [7,4,0,20] [9920564,9928757,9936956,9945149,9953348,9961548,9969748,9977972,8405572]) E)) (N (N (u 2855236) E) (N (u 7049508) E))) (N (N (N (k 1660037 [0,1,14,18,4] [3629088,3637536,3465516,3531056,3416696]) E) (N (u 5996665) E)) (N (N (y 3891797 [7823700]) E) (N (k 8077928 [0,1] [16211996,16220520,16224632]) E))))) (N (N (N (N (N (u 495668) (v 8876088 14)) (N (v 4690024 1) E)) (N (N (u 2592872) E) (N (k 5878647 [0,1,5,10,8,4] [13590576,1130548,11796533,11800630,13598776,13606969,13602876,13611070,5611589,13291593,10244197,12054633,12693624,13013114,7397700,7627077,13562213,5616182,13287998,7402068,7631446,10240869,12051305,12690312,13009802,13559141]) E))) (N (N (N (k 1372553 [23,11] [2596916,2842916,3105064]) E) (N (k 5735256 [7,1] [11493404]) E)) (N (N (k 3555701 [4,1,0] [7299121,7331890,2961466,2973757,2134086,176213,626777,6005045,7053625,7348548,7356742,7135866,7365717]) E) (N (j 7835704 17 [15687748]) E)))) (N (N (N (N (k 827789 [0,11] [1351716,1450036,1876268,2056500,1745544]) (k 9376101 [0,1,17,5,3,31,26] [10293365,18780281,15368517,14946677,10289733,18776649,14943045,15373173])) (N (v 5214293 6) E)) (N (N (v 3093045 4) E) (N (w 7233643 [7,4,16]) E))) (N (N (N (v 2064468 17) E) (N (k 6152535 [6,1] [12542065,12550261,12566649,12574845,12583285,12591733]) E)) (N (N (k 3862873 [7,0,4,17] [8347709,8355956,7905882]) E) (N (v 8351820 17) E))))))))) (N (N (N (N (N (N (N (N (N (k 8265 [6,1,17] [57461,65657]) (u 8397157)) (N (k 3863381 [0,1,10,13] [8445985,8454189,1511477,8462393,8470613,8478809,8257844,8331573,3195213,7832146,7946842,4645697,6693709,8151893,8209241]) E)) (N (N (u 2114405) E) (N (u 6299769) E))) (N (N (N (k 828293 [20,0,13,4] [2154528,2162976,1884460,2113860,1753736]) E) (N (v 5263480 23) E)) (N (N (k 3051815 [7,17] [6348888]) E) (N (v 7360602 8) E)))) (N (N (N (N (f 540724 [999800]) (k 107 [3,0,1,11,4] [17883173,17940533,18030677,18055269,18071669,18080044,8651061,14909797,13505079,8778327,15323751,18096983,18146663])) (N (k 4983 [7,6,3,16,20] [81972,270389,548924,729149,8839252,192613,131380,409909,8864084,8135236,1598309,2696041,7423077,9086309]) E)) (N (N (v 2621560 8) E) (N (v 6815864 4) E))) (N (N (N (y 1594229 [2949436]) E) (N (k 5787704 [34,4,10] [11592005]) E)) (N (N (v 3686773 17) E) (N (v 7885173 15) E))))) (N (N (N (N (N (v 282676 5) (v 8663116 17)) (N (j 4476949 1 [929840]) E)) (N (N (y 2375748 [4194596,4088404,4776564]) E) (N (k 6574136 [6,23] [13164598,13172805,7176265,4002358]) E))) (N (N (N (k 1114751 [20,11,10] [2678836,2572860]) E) (N (j 5525877 2 [7278916,10953592]) E)) (N (N (k 3428404 [7,17] [6873162,6881365,6889561,6619434,6898261,6914901,6923125]) E) (N (v 7618677 8) E)))) (N (N (N (N (u 802876) (k 9122133 [6,0,33] [18301228])) (N (k 4993108 [7,6,1,16,10] [10018891,10027365,9843815]) E)) (N (N (v 2884693 23) E) (N (v 7037053 11) E))) (N (N (N (j 1847584 4 [3727460]) E) (N (y 6049909 [12116072]) E)) (N (N (u 3952756) E) (N (j 8126837 7 [16310376]) E)))))) (N (N (N (N (N (N (v 143700 1) (u 8536121)) (N (k 4325461 [6,1,8] [6148133,6975781,3236157,8708678]) E)) (N (N (u 2248778) E) (N (j 6438954 6 [12902760]) E))) (N (N (N (v 1200156 17) E) (N (u 5386329) E)) (N (N (y 3277685 [4555316]) E) (N (v 7483513 4) E)))) (N (N (N (N (v 675960 4) (v 9064532 11)) (N (v 4870212 23) E)) (N (N (z 2773301) E) (N (k 6955114 [2,0] [13951352]) E))) (N (N (N (u 1716548) E) (N (k 5898888 [1,6] [11853852,11821416,11837816]) E)) (N (N (u 3821658) E) (N (v 8016208 22) E))))) (N (N (N (N (N (u 409668) (v 8794208 2)) (N (v 4599896 1) E)) (N (N (k 2424903 [7,1,17,22] [4988968,294968]) E) (N (k 6681221 [4,0] [12592264]) E))) (N (N (N (y 1442088 [2834452]) E) (N (u 5656604) E)) (N (N (v 3559797 20) E) (N (k 7749747 [1,3,11,0] [13922332,15523924,15532132,15540340,15556740,15565092,14037556]) E)))) (N (N (N (N (u 926020) (k 9322553 [32,6,20] [15835448])) (N (w 5132377 [28,8,0]) E)) (N (N (k 2831461 [23,1,8] [5865516,5882156,6013252,6087264,5816936,5915256]) E) (N (k 71 [1,7,0,3] [10264645,14475337,12075093,14491737,14581851,14590053,14598249,14631019,14639217,14647413,14704761,14737533,13361495,14745959,14778741,14868855,14909817,14918213,14950997,14959205,14967413,15000663,15008871,9852279,15017591]) E))) (N (N (N (k 1957917 [8,10] [3932452,3990068,3998276]) E) (N (j 6156661 20 [12378216,12386592]) E)) (N (N (y 4079701 [8184148]) E) (N (w 8257625 [17,0,1]) E))))))) (N (N (N (N (N (N (N (v 86064 7) (w 8466805 [16,21])) (N (v 4269141 23) E)) (N (N (j 2154836 23 [4383556]) E) (N (u 6377576) E))) (N (N (N (k 1114227 [1,11,0] [1798172,2285620,2302028,2310228,2318436,2326636,2334836,2343044,2351396]) E) (N (k 5092439 [7,6,21] [10674232]) E)) (N (N (v 3232580 17) E) (N (k 7389557 [7,4,16,21] [14795370]) E)))) (N (N (N (N (v 565337 17) (u 8999476)) (N (v 4804692 17) E)) (N (N (k 2707829 [0,42,7] [5431400,5439608]) E) (N (v 6894132 8) E))) (N (N (N (k 1658984 [6,1] [3334513,3367285,3391865,3400061,3408757,3417205]) E) (N (k 5845112 [7,10,0] [11125605,11240309]) E)) (N (N (k 3731845 [6,20,0] [7168056,5726296,7528552,7536948,7479944]) E) (N (w 7946581 [7,4]) E))))) (N (N (N (N (N (k 323717 [5,17] [278584,713004,721208]) (k 8716677 [16,6,7,21] [17461368,17457784])) (N (v 4542524 13) E)) (N (N (w 2429250 [34,22]) E) (N (j 6627655 1 [1351732,12710008,13271604,7209540]) E))) (N (N (N (y 1388648 [2810692]) E) (N (k 5583717 [6,1,18,5] [11198837]) E)) (N (N (v 3474265 1) E) (N (k 7578439 [6,12,9,1,5] [10260613,13570437,15196732,15360596,10547845]) E)))) (N (N (N (N (v 840565 20) (v 9261145 17)) (N (v 5066824 17) E)) (N (N (v 2830473 4) E) (N (k 7118938 [17,0,1,2] [14278997,14344549,7652181]) E))) (N (N (N (k 1843593 [16,4] [3735844,3858728]) E) (N (v 6045837 11) E)) (N (N (k 3862619 [17,23,10] [4968740,7807328,7872872,7770676]) E) (N (v 8208761 4) E)))))) (N (N (N (N (N (N (k 103509 [6,12] [262444]) (k 8007754 [17,0,1,5,10] [11452450,11456562,17227847,17231959,17252455,17256567,16417093,16449863,16654665,16421205,16453975,16658777,17269093,17293671,17301865,17273205,17297783,17305977,7848517,8577607,10117705,13468247,14787173,14885479,15131241,15303287,13472583,7852885,8581975,10122073,15307623,14791541,14889847,15135609,17327191,17359991,17364327,17385079])) (N (w 4411461 [17,6,1]) E)) (N (N (v 2306421 4) E) (N (u 6508596) E))) (N (N (N (f 1261606 [2384164]) E) (N (v 5460053 8) E)) (N (N (j 3224121 8 [3989524,3932212,6627396]) E) (N (k 7520629 [7,4,16,27,17] [15130714,15138919,8409445,15065668]) E)))) (N (N (N (N (v 741408 11) (v 9130088 8)) (N (k 4935780 [4,16] [8381252]) E)) (N (N (k 2830408 [17,1] [5693525,5701749,4874536,5677354,5710421,5727061]) E) (N (k 7032885 [1,6,0,3] [14082161,14090355,13635701,14155895,14180473,14188667,14205053,14213247,13750645]) E))) (N (N (N (k 1659277 [0,4,11] [3449132,3400312]) E) (N (v 5980285 11) E)) (N (N (k 3862594 [7,9,6,17] [7790621,7799125,7807321,6652477,7815765,7832661]) E) (N (v 8077416 17) E))))) (N (N (N (N (N (k 446539 [6,0] [950564]) (v 8782688 2)) (N (k 4583799 [8,1] [9363520,9306184,8118612]) E)) (N (N (u 2564441) E) (N (w 6766933 [6,17,1,2]) E))) (N (N (N (v 1523808 2) E) (N (k 5722170 [17,7,2,4] [11460677,7860821,10912581]) E)) (N (N (w 3625284 [6,17]) E) (N (v 7819316 1) E)))) (N (N (N (N (f 987444 [2023456]) (w 9392197 [6,34])) (N (v 5193784 13) E)) (N (N (v 3092569 17) E) (N (k 7233641 [6,1,8] [14606453]) E))) (N (N (N (v 1957980 2) E) (N (u 6234233) E)) (N (N (k 3862871 [8,23,20,10] [8314944,2568264,1511508,7541076,5714492,8331860]) E) (N (k 8343581 [17,7,6,16,21] [16097605,16101717,7791173,7795541]) E)))))))) (N (N (N (N (N (N (N (N (w 8517 [17,6,1]) (j 8376697 16 [16835192])) (N (u 4243513) E)) (N (N (k 1957989 [23,8] [1798188,4317252,4325452,4333652,1098020,2285868,4342084,4358476,4374868,4391476,4399940,4408148]) E) (N (u 6344761) E))) (N (N (N (v 1101856 11) E) (N (k 5092167 [6,1,5,13] [41012,10608694,10625080,1601669,10633353,9089669,10388357,10511493,10593669]) E)) (N (N (u 3199112) E) (N (v 7393909 8) E)))) (N (N (N (N (u 569672) (k 8937525 [1,6,3,16,11] [6111285,17948727,17965141,17981527,17989721,17997915,13340981,18014549,8786775])) (N (k 4747332 [7,17,6] [8544282,7438421,9560153,573756,835901,9421141,9470325,9135189]) E)) (N (N (k 2424923 [23,1] [2924600,1171748,5013856,5161320,5366136,5374516]) E) (N (k 6811732 [0,5,1,10] [13754434,13779018,13067130]) E))) (N (N (N (k 1373317 [1,23,10] [3268640,3006512,3277088,2957612,3171412]) E) (N (v 5820472 23) E)) (N (N (j 3715172 1 [7274820]) E) (N (k 7747199 [17,0,1,11,10] [15851572]) E))))) (N (N (N (N (N (u 315448) (k 8704085 [7,1,17] [17424472,11461452,10441556])) (N (v 4493404 10) E)) (N (N (k 1959045 [6,16,1] [4841512,4104804,4301428,4481668,4588356,4662356]) E) (N (k 6574169 [20,11,0] [7176264,1302820,7184708,12935816]) E))) (N (N (N (v 1356092 17) E) (N (f 5554296 [11027320]) E)) (N (N (k 3428405 [3,11] [6938712,6570552]) E) (N (k 7577983 [19,4,11,1] [15327317,15343749]) E)))) (N (N (N (N (k 840049 [6,1,0] [999476,1695844,1704052]) (v 9216132 4)) (N (w 5029977 [17,1,0]) E)) (N (N (u 2928980) E) (N (u 7131496) E))) (N (N (N (u 1888596) E) (N (f 6074472 [12182136]) E)) (N (N (k 3862615 [20,0,4] [2568264,7987288,7995488,8003688,8011912,4968744,7758168,7799136,7864680]) E) (N (w 8179740 [1,7,17]) E)))))) (N (N (N (N (N (N (u 180564) (k 8548677 [17,7,6] [17134165])) (N (u 4378681) E)) (N (N (u 2281800) E) (N (u 6439033) E))) (N (N (N (f 1184309 [2482776]) E) (N (k 5349701 [6,1] [1634421,10870905,10764589,9130357,10879861]) E)) (N (N (v 3318133 4) E) (N (w 7524423 [7,4]) E)))) (N (N (N (N (z 705076) (k 9081413 [30,12,0,1,17,5,3] [118901,13541701,8851829,115269,8848197,13546357])) (N (w 4882501 [8,17]) E)) (N (N (k 2805896 [1,3] [5096296,5399416]) E) (N (k 6950981 [0,5,17] [14016632,12854408]) E))) (N (N (N (u 1757524) E) (N (v 5947773 11) E)) (N (N (w 3843205 [18,16,1]) E) (N (k 8011864 [17,1,0,2] [16114005,16130421,8008789,14816373]) E))))) (N (N (N (N (N (k 446490 [0,13,4] [909429,917625,934250]) (v 8781885 17)) (N (k 4583543 [8,1,14] [9297984,9306184,9314384,9322584,9265544]) E)) (N (N (u 2543736) E) (N (w 6737988 [6,0,17]) E))) (N (N (N (k 1372545 [0,1,11] [1798188,2285620,3006548,3014756,3022956,3031156,3039364,2826532]) E) (N (u 5690183) E)) (N (N (v 3580008 23) E) (N (k 7749751 [17,1,3] [15589480,15597704,15565088,13930792]) E)))) (N (N (N (N (v 954476 2) (v 9322621 11)) (N (k 5165112 [7,6,17,16,21,5,3] [10346551,10350663,10355527]) E)) (N (N (v 3055957 23) E) (N (k 7245943 [7,25] [14540920]) E))) (N (N (N (u 2016069) E) (N (u 6197369) E)) (N (N (v 4112500 4) E) (N (u 8303208) E))))))) (N (N (N (N (N (N (N (v 118824 17) (v 8499261 17)) (N (j 4265061 3 [8642592,5865516,8335684,8569448]) E)) (N (N (u 2216789) E) (N (k 6153583 [5,1,23,4] [12836917,12853317]) E))) (N (N (N (v 1138820 4) E) (N (k 5349447 [4,0] [10715432]) E)) (N (N (v 3223685 4) E) (N (w 7458905 [34,6]) E)))) (N (N (N (N (j 639048 23 [1155368]) (k 8937589 [6,1,18,11] [13529927,15348599])) (N (k 4804710 [7,0,21] [4157780,9642340,9691508]) E)) (N (N (v 2736216 4) E) (N (v 6914108 8) E))) (N (N (N (u 1663353) E) (N (w 5886584 [36,4]) E)) (N (N (k 3788864 [0,4] [7594068,7545140]) E) (N (v 7934060 21) E))))) (N (N (N (N (N (w 323973 [7,17,1]) (v 8761477 4)) (N (v 4575293 17) E)) (N (N (v 2474581 8) E) (N (k 6656117 [21,8,0] [13001352]) E))) (N (N (N (y 1389396 [2875752]) E) (N (u 5623912) E)) (N (N (y 3518804 [6906436]) E) (N (v 7721012 4) E)))) (N (N (N (N (v 893024 2) (v 9294120 17)) (N (k 5095528 [6,1,5] [10216551,10233191]) E)) (N (N (k 2986324 [23,8] [5996848]) E) (N (k 7196724 [17,0,1,5] [14409816]) E))) (N (N (N (k 4211 [7,0,1,10] [3923996,3981341,4005948,4014148,4022356,4112476,4120676,4309093,4415596,4423796,4489348,4513925,4522124,4530468,4596006,1909093,2998633,3473797,3760521,4612660,4670005,4686404,4711269,4752233,4793445,4834437]) E) (N (k 5877864 [6,1,23] [12312631,12394583,12468327,12509295,7471415,12534103,12599655,12640623,12673863,12690279,12731247,12772439,10663015,11719791,12797287,12830063]) E)) (N (N (v 4051061 4) E) (N (k 8241256 [16,1,12] [16310904]) E)))))) (N (N (N (N (N (N (k 229447 [0,17,6] [33076]) (v 8634489 4)) (N (w 4440137 [32,17,3]) E)) (N (N (y 2343769 [4366644,4449124]) E) (N (u 6541364) E))) (N (N (N (y 1294636 [2359316]) E) (N (u 5492840) E)) (N (N (u 3395652) E) (N (k 7577673 [6,1,18,5] [15196485,15204709,11751805,13898871,15214199]) E)))) (N (N (N (N (v 774192 11) (j 9154941 4 [18341924])) (N (k 4956221 [8,10] [8414020]) E)) (N (N (v 2830416 2) E) (N (y 7045412 [14147608,14106948]) E))) (N (N (N (k 1822837 [6,1] [3661912,3670106]) E) (N (w 5992789 [17,1,0]) E)) (N (N (k 3862602 [1,17,3] [7856162,7864661,7872857,4629041,6660669,7881286,7889493,7905881,7922293,7930489,7947349,7955573]) E) (N (u 8114784) E))))) (N (N (N (N (N (u 503928) (k 8876121 [6,16] [17793108,8503892,17065064])) (N (u 4702292) E)) (N (N (u 2564697) E) (N (v 6803524 23) E))) (N (N (N (v 1560664 17) E) (N (k 5722424 [7,6,16,21,17,11,10] [11485495,11489607,11526983]) E)) (N (N (u 3650116) E) (N (k 7836008 [1,12] [15704440]) E)))) (N (N (N (N (f 1032240 [2089004,2097460,2105668]) (v 9416765 10)) (N (k 5210199 [6,17,0] [10466132]) E)) (N (N (j 3051611 23 [2842676,2539812,2924852]) E) (N (k 7323736 [7,0,10] [13386327,14672487]) E))) (N (N (N (u 2085700) E) (N (u 6267001) E)) (N (N (j 4182065 4 [8380500]) E) (N (u 8376393) E))))))))))) (N (N (N (N (N (N (N (N (N (N (N (k 23 [1,0,3] [16437,204855,458809,647227,892997,1654855,2228297,2744395,3285093,3317863,3645545,3686507,3907697,3915891,4849781,5660791,6103161,6447227,6848637,6856831,7110981,7463239,7635273,7684455,7725429,8528247,8651129,8774015,8823349,8880709,9142885,9167477,9397063,9438055,9487223,9495423,9602167,9766015,9848439,9913983]) (u 8376409)) (N (v 4194368 44) E)) (N (N (u 2093892) E) (N (v 6267509 10) E))) (N (N (N (u 1040708) E) (N (k 5210965 [17,6] [143412,8147252]) E)) (N (N (u 3145848) E) (N (v 7323769 4) E)))) (N (N (N (N (u 524324) (v 8912944 41)) (N (k 4718664 [6,37,21] [9389173]) E)) (N (N (j 2621512 23 [1167656]) E) (N (u 6815801) E))) (N (N (N (y 1569605 [3162428]) E) (N (k 5722981 [34,17,8,4] [8205157]) E)) (N (N (k 3645764 [8,4,0,1] [7147610,7323953,7328050,2969914,2965821,7144042]) E) (N (j 7864391 1 [15745144]) E))))) (N (N (N (N (N (v 262440 17) (u 8650853)) (N (v 4452424 23) E)) (N (N (v 2355796 10) E) (N (v 6553656 44) E))) (N (N (N (k 1114405 [6,0] [2474613,2581113]) E) (N (u 5505128) E)) (N (N (v 3407904 13) E) (N (w 7595639 [17,6]) E)))) (N (N (N (N (k 447103 [11,4,0] [1351732,1368124,1589316,1401404,1524292]) (v 9121921 11)) (N (w 4956244 [7,4]) E)) (N (N (w 2883606 [1,8]) E) (N (u 7077992) E))) (N (N (N (v 1822845 11) E) (N (w 5993847 [17,2,15,7]) E)) (N (N (u 3924313) E) (N (u 8126808) E)))))) (N (N (N (N (N (N (k 102533 [7,1,22] [278584]) (v 8519729 17)) (N (k 4325397 [7,4,20,17] [7790666,6148181,8667225,8675669,8692565]) E)) (N (N (y 2212713 [4449364]) E) (N (j 6414405 5 [12861560]) E))) (N (N (N (k 1114229 [0,1,7] [1798169,2375706,2392144,2400338,2416725,2424920,2433113,2441306,2457704,2465898,2474549]) E) (N (j 5349451 4 [10715428,10764852]) E)) (N (N (w 3276821 [20,17]) E) (N (w 7234133 [7,0,21,10]) E)))) (N (N (N (N (f 639080 [1024376]) (k 8938327 [6,1,11,13] [17965108,18104374,18120760,1585237,18128985,18014516,8757572,8811093,17916757,18089052])) (N (y 4849764 [7307844,8233796]) E)) (N (N (k 2736248 [1,6] [5194088,5439864]) E) (N (k 5879167 [5,0,1,10,4] [13910068,13975605,14000188,14008389,14024788,12829576,13099914]) E))) (N (N (N (w 1664117 [1,4]) E) (N (v 5898312 23) E)) (N (N (v 3732353 11) E) (N (v 7991352 13) E))))) (N (N (N (N (N (u 389460) (v 8781872 13)) (N (k 4583497 [7,17,6] [9191509,7406677]) E)) (N (N (w 2490397 [1,7]) E) (N (k 6680709 [0,3,27] [12165208,13385848,12551304]) E))) (N (N (N (k 1441836 [0,1] [925732,929860,2900052,2908252,2916452,2920564]) E) (N (v 5636165 8) E)) (N (N (u 3538980) E) (N (u 7733368) E)))) (N (N (N (N (v 893064 4) (k 9113671 [32,7,6,33] [10608725,10612869,18399573,18403717,8889173,8893573])) (N (u 5104999) E)) (N (N (k 2831205 [23,1,8] [5873964,6005060,5726808,6046304,5800552,5898872]) E) (N (v 7209016 27) E))) (N (N (N (f 1962069 [3948664]) E) (N (k 6156405 [1,6] [12337256,12345464]) E)) (N (N (k 3862853 [7,6,17] [737341,159829,7971117,139572,418101,8143172,8152149]) E) (N (w 8257605 [17,22]) E))))))) (N (N (N (N (N (N (N (w 65844 [7,17]) (v 8450165 4)) (N (k 4471 [1,3,4,11,0,17] [5685320,8536152,8577114,5582949,8585321,7520613,7692677,8602160,4670001,6324796,6709821,6341182,8610374,8311397,8618601,1549157,2638697,8635493]) E)) (N (N (v 2154580 4) E) (N (v 6344826 21) E))) (N (N (N (w 1114181 [17,6,1]) E) (N (v 5300280 13) E)) (N (N (w 3052631 [17,30]) E) (N (v 7401608 21) E)))) (N (N (N (N (v 565328 2) (k 8970325 [6,1,11,0] [17973274,1351749,1089609,6959429])) (N (k 4747365 [6,20] [9584704,1613892,9592904,2728012,7438420,9109604,1630532,7446868,9126244,8176468]) E)) (N (N (k 2424936 [7,0,10] [5390935,5407335]) E) (N (u 6877300) E))) (N (N (N (k 4197 [6,1,0] [3293272,3301489,3309689]) E) (N (u 5832772) E)) (N (N (v 3735925 20) E) (N (k 99 [5,4,1,0,10,8] [15876148,15892533,15917116,15925316,15941708,15880276,15896661,15921244,15949924,15966309,15974508,15954036,15970421,15978620,15983447]) E))))) (N (N (N (N (N (j 327980 19 [671780]) (v 8716384 2)) (N (j 4522033 23 [9060452,5996836,8249924]) E)) (N (N (k 2424858 [1,8] [4866133,2924633,4874552,4882746,4899138,4907338,4915562,4924229]) E) (N (k 6574201 [21,8,0] [12960392]) E))) (N (N (N (u 1377092) E) (N (k 5345365 [7,4,21,16] [11157593]) E)) (N (N (w 3473493 [23,1]) E) (N (w 7659653 [27,8]) E)))) (N (N (N (N (k 840053 [1,6] [1720424,1728632]) (w 9240634 [0,4])) (N (k 4993349 [6,1] [5591157,9343349]) E)) (N (N (u 2945897) E) (N (k 7118936 [0,17,1,10] [14303303,14319703,13742407,14328151]) E))) (N (N (N (y 1880404 [3785060,3801460]) E) (N (u 6095480) E)) (N (N (v 3989608 20) E) (N (v 8192044 17) E)))))) (N (N (N (N (N (N (w 103029 [9,4,12,3]) (v 8585264 13)) (N (v 4390988 13) E)) (N (N (k 1958182 [8,17] [4603944,3932456,4252260]) E) (N (u 6488154) E))) (N (N (N (v 1245280 2) E) (N (k 5349749 [7,4,1] [10895432,1634389,10846509,7450965]) E)) (N (N (y 3318613 [2949436]) E) (N (w 7532631 [6,0,17]) E)))) (N (N (N (N (z 720948) (k 311 [0,1,2,13] [18235441,892981,18243639,18473017,18546749,18554943,18169925,18620487,18628681,18239601,897141,18247799,18477177,18550909,18559103,8880437,8884853,10601287,11633483,15983475,17564535,18097019,18101119,10605687,11637887])) (N (k 4882564 [7,4] [8356420]) E)) (N (N (k 2425943 [17,30,1,7] [5562948]) E) (N (y 7012418 [14041172,14049396]) E))) (N (N (N (f 1769576 [3375720]) E) (N (v 5959968 11) E)) (N (N (v 3866709 17) E) (N (w 8053109 [20,9]) E))))) (N (N (N (N (N (v 458796 11) (k 8781897 [13,3] [1351748,17711180,17657940,17719388,8467284,17032296])) (N (v 4644944 10) E)) (N (N (w 2555989 [0,6]) E) (N (k 6750293 [4,0,1,8] [1351748,13516920,6988068,8713044,12649608]) E))) (N (N (N (v 1499244 2) E) (N (y 5633111 [11419696,1617972,11427896,11436092,9138756,10355560,11388008]) E)) (N (N (k 3555455 [20,4,0] [6148116,7225396,7233604,7241812]) E) (N (k 7749753 [1,3,0] [13488149,13930518]) E)))) (N (N (N (N (k 827781 [0,11,1] [1286200,1982560,1990760,1998968,2007328,1868076,2015540,1712776]) (k 583 [1,15,0,2,3,8,5] [10264629,18759737,18190421,18784345,18800741,18808937,10301557,18817145,11575613,18215253,18825573,10555765,14918197,18739797,15356533,13787991,15393639,17818487,9442679,15013495])) (N (w 5165114 [17,22,5,3]) E)) (N (N (w 3051591 [2,17]) E) (N (v 7274552 17) E))) (N (N (N (v 2011989 23) E) (N (v 6226208 11) E)) (N (N (v 4128801 17) E) (N (k 8298840 [17,1,0] [16630101,16662901,7877717]) E)))))))) (N (N (N (N (N (N (N (N (w 8267 [17,23]) (v 8376437 4)) (N (u 4218937) E)) (N (N (u 2129994) E) (N (u 6324344) E))) (N (N (N (k 828297 [4,0] [2179116]) E) (N (k 5276791 [16,7,1,4,17] [10567816]) E)) (N (N (w 3178533 [20,17]) E) (N (w 7373189 [18,21,4]) E)))) (N (N (N (N (u 541236) (k 8941625 [17,1,0,4] [17907797,8671829])) (N (u 4751449) E)) (N (N (k 2621816 [0,35,7] [5284200,5308792]) E) (N (v 6848584 23) E))) (N (N (N (v 1605920 11) E) (N (k 5788021 [34,3,8] [11076453,11199349]) E)) (N (N (j 3698794 21 [7148100]) E) (N (v 7831673 8) E))))) (N (N (N (N (N (k 230005 [7,17,6] [590136,606549]) (v 8679496 6)) (N (j 4440191 36 [8962068,8994868,9003076,9011276,9019476,9027676,9035908]) E)) (N (N (k 1959013 [0,1] [4333604,4800552,4374820,4809308,4096612,4817516,4473460,4825732,4645972]) E) (N (k 6574138 [6,0] [13189448,13197672,12911240]) E))) (N (N (N (j 1115255 5 [2416692,2555964,2703668]) E) (N (k 5460861 [6,11] [11092053,11100261,10977912]) E)) (N (N (u 3432537) E) (N (k 7577975 [19,4,1,11] [5627989,15286361,15294568,15302762,14696581,15310985,7692629,14754181]) E)))) (N (N (N (N (v 803132 17) (v 9203760 10)) (N (k 5013578 [17,4] [7918165]) E)) (N (N (k 2830426 [7,1,17] [5849464,4579888,4907576]) E) (N (w 7032917 [7,0,21]) E))) (N (N (N (v 1868104 17) E) (N (w 6062712 [24,4]) E)) (N (N (u 3965028) E) (N (k 8011898 [7,21] [16056664,16146792,4956728,16335464]) E)))))) (N (N (N (N (N (N (j 102745 30 [344120]) (k 8552533 [0,1,7,6] [1204280])) (N (k 4325719 [8,23] [6148148,8732736,2576456,1527892,8675636,7573844,6976052,8749652]) E)) (N (N (k 1958180 [7,1,17] [4538392,4562970,4579402,4227412,4391253,4588405]) E) (N (u 6455624) E))) (N (N (N (v 1183833 17) E) (N (k 5349497 [7,0,4,10] [10780694,10829909,9597017]) E)) (N (N (v 3305540 20) E) (N (k 7235191 [7,4] [15024176,14860868]) E)))) (N (N (N (N (v 671833 17) (k 295 [12,1,0,5,3] [16437,18169925,18186341,10195061,8823093,13537653,11559485,18203205,18211429,10523253,13574983,15385447,17556343,9401463,15005303])) (N (w 4882484 [7,0,17]) E)) (N (N (k 2425175 [23,7,1] [1798204,1815100,5071720]) E) (N (k 6955130 [16,5] [13951352]) E))) (N (N (N (f 1736748 [3342440]) E) (N (u 5931304) E)) (N (N (v 3833962 21) E) (N (w 8016464 [34,17]) E))))) (N (N (N (N (N (j 324437 6 [696620,812116]) (v 8781880 13)) (N (w 4583513 [7,0,4]) E)) (N (N (u 2523256) E) (N (w 6717508 [6,0,17]) E))) (N (N (N (y 1442132 [2966340]) E) (N (k 5632087 [6,17,0] [8556888,11354968]) E)) (N (N (j 3560565 1 [7143748]) E) (N (j 7757940 11 [15548708,14045748]) E)))) (N (N (N (N (k 827777 [0,1] [1916972,1097780,1933396,1941604,1949804,1958004,1966212,1688200]) (v 9322609 11)) (N (k 5091429 [6,1,9,5] [10306679,10323575]) E)) (N (N (k 4217 [1,0,5,3] [6111253,4857878,4931607,6152261,6168647,548937,6176843,6185045,6258775,2523225,6275163,6283381,6291575,6307961,6316155,6324517,6340903,6357289,6381911,6390135,6398551,6414967,6423365,6431831,6440055]) E) (N (k 7233625 [1,6,7,0,28] [14499925,14483545,14508149,14532727,9891961,12099877,14549623,14574421]) E))) (N (N (N (v 1957948 10) E) (N (k 6152279 [6,1] [12402801,12410997,12435577,12443773,12452213]) E)) (N (N (w 4079989 [4,9]) E) (N (v 8257657 4) E))))))) (N (N (N (N (N (N (N (k 4151 [12,6,1,16,5,3] [213034,221269,229465,270469,286857,24872,213290,319829,336217,352645,360841,385621,402037,410245,426837,435077,443477,451717]) (u 8487013)) (N (v 4292676 8) E)) (N (N (j 2155332 20 [4383300]) E) (N (v 6386293 2) E))) (N (N (N (v 1138764 10) E) (N (k 43 [3,0,1,5,4,2] [10698805,10920005,11149397,11165797,11264117,11444597,11559477,11575893,11616893,11633479,11690871,11723863,9499767,11740535]) E)) (N (N (v 3240072 4) E) (N (k 7434346 [17,3,21] [14730060]) E)))) (N (N (N (N (v 565352 8) (k 8937557 [6,1,11,0] [6115381,17965125,18038885,18047096,6951221,8700485,13513543,15332199])) (N (u 4817252) E)) (N (N (u 2707833) E) (N (v 6914096 27) E))) (N (N (N (u 1667172) E) (N (k 5346679 [7,3,15,0] [11747416,11608404,11133813,11248517]) E)) (N (N (k 3768368 [0,4] [7553092]) E) (N (w 7963463 [7,4]) E))))) (N (N (N (N (N (k 323721 [17,5] [737604]) (k 8749157 [7,21,0] [13918265])) (N (v 4550716 13) E)) (N (N (v 2429765 8) E) (N (k 5877887 [6,11,1,0,8] [6115348,13320244,13336644,13344853,13353077,11944277,12968328,7218005]) E))) (N (N (N (y 1388832 [2834460,2293796]) E) (N (u 5603445) E)) (N (N (u 3502420) E) (N (k 7579255 [0,1,5,10,27,18,8,4] [15417392,15425588,15433784,15437884,14696517,15265865,10326133,15216761,14770501,15380853,14701110,15262270,14774870,10322805,15213433,15377781]) E)))) (N (N (N (N (v 827521 11) (k 9113663 [32,3] [18481172,18563124,18571332,18579556,18587781,18604173,18436485,18612621,8991877])) (N (k 4994175 [7,4,0,1] [10174516,10088516,10084916,10158660]) E)) (N (N (k 2830949 [23,8] [5980208,2924604,2015540,6005060,6013268,5710424]) E) (N (k 7118951 [17,3,25] [14344568]) E))) (N (N (N (j 1933348 5 [3883096]) E) (N (v 6123901 11) E)) (N (N (u 4026456) E) (N (k 8012133 [0,1] [5259320,16466016,16117864,16281736,5263660,16470624,16114280,16278136]) E)))))) (N (N (N (N (N (N (k 229445 [6,1,17,0] [475253,483449,491893,500349]) (w 8614008 [3,8])) (N (w 4411749 [17,19,1,3,4]) E)) (N (N (j 2306933 4 [4055892,4277092]) E) (N (v 6520888 44) E))) (N (N (N (v 1261877 23) E) (N (v 5472613 2) E)) (N (N (y 3371861 [2965820]) E) (N (u 7569480) E)))) (N (N (N (N (v 754224 11) (j 9121881 3 [18301220])) (N (v 4948036 16) E)) (N (N (y 2843221 [5718340]) E) (N (j 7045204 11 [14106916,13767220]) E))) (N (N (N (v 1798432 11) E) (N (w 5996661 [1,7,17]) E)) (N (N (u 3891545) E) (N (u 8093724) E))))) (N (N (N (N (N (y 491889 [999476]) (v 8876081 17)) (N (k 4584567 [17,1,3,4] [9388136]) E)) (N (N (k 2564469 [0,1,9] [5193832,5202040]) E) (N (k 5878599 [6,12,1,5,0] [41012,10244229,7373124,13562245,12034620,13541972,10531461,12673912,5649285,9377157]) E))) (N (N (N (v 1524000 11) E) (N (v 5734456 17) E)) (N (N (w 3626101 [1,17]) E) (N (k 7831623 [1,3,17] [15679544,15696008,15712616]) E)))) (N (N (N (N (y 1015852 [925732]) (k 9375865 [7,0,26,3] [9449829,13804647,15402103])) (N (k 5210170 [17,3,6] [10436693,7975509]) E)) (N (N (z 3092773) E) (N (v 7303274 2) E))) (N (N (N (v 2064452 10) E) (N (u 6254709) E)) (N (N (u 4153940) E) (N (v 8351816 33) E))))))))) (N (N (N (N (N (N (N (N (N (w 8261 [17,6,1,0]) (u 8397145)) (N (k 3863365 [7,17,6] [8143156,5567061,6685517,8303445]) E)) (N (N (u 2113610) E) (N (v 6299754 2) E))) (N (N (N (v 1065248 11) E) (N (k 5260407 [3,17,1] [10535032,7393860]) E)) (N (N (v 3162186 17) E) (N (k 7352613 [7,25] [14729306]) E)))) (N (N (N (N (u 540700) (v 8929396 17)) (N (v 4726884 3) E)) (N (N (u 2638184) E) (N (u 6832504) E))) (N (N (N (k 1372740 [13,1,0] [2867573,2982265,3195765,3203961]) E) (N (k 5345877 [1,3,15,0,5,8,4] [11583544,11600213,11608437,11067989,11190885,11403893,11543413,9459063]) E)) (N (N (v 3686517 1) E) (N (k 7831642 [17,0,1,2] [15712597,15778165,15787093]) E))))) (N (N (N (N (N (k 229757 [17,1,6] [90148,573492,581700,532772,590132,500309]) (y 8663112 [16195636])) (N (k 4440185 [32,10] [8962069,8970301,8978517,8462662,8765774]) E)) (N (N (v 2375716 13) E) (N (k 5877879 [6,1,11,0] [13156408,13180986,13205576,13213770,11796565,13221977,13230184,13238378,12148853,13246585,11919701,12271989,12878216,5968454,7160661]) E))) (N (N (N (v 1319472 11) E) (N (k 5460805 [6,1,5,12] [11059573,10945128,9417333,9433973]) E)) (N (N (k 4223 [7,0,10] [6111252,6455317,6864948,6930485,6946884,7004261,7028869,6553896,6611242,2048357,3113321,3588485,3867017,7037541,7070565,7078761,7095397,7103621]) E) (N (k 7618629 [19,1,4] [13873445]) E)))) (N (N (N (N (k 802868 [0,1,8,6] [1204248]) (v 9121933 11)) (N (v 4997245 11) E)) (N (N (u 2884441) E) (N (y 7094572 [14147604]) E))) (N (N (N (w 1847400 [4,16]) E) (N (k 6045768 [6,1,25] [12107893]) E)) (N (N (y 3924569 [7913588]) E) (N (u 8126825) E)))))) (N (N (N (N (N (N (u 143684) (v 8536113 17)) (N (y 4330325 [8683828]) E)) (N (N (k 2245172 [7,4,17] [4505674]) E) (N (v 6438952 44) E))) (N (N (N (k 1183826 [1,7] [2408476]) E) (N (w 5386314 [1,8]) E)) (N (N (u 3277653) E) (N (w 7483497 [34,4,23]) E)))) (N (N (N (N (k 671765 [7,0,1] [1204312,1359992]) (k 9048153 [10,13,11] [1089604,18137172,18022980,8766036])) (N (y 4800569 [1351700,9748548,6238292]) E)) (N (N (k 2425173 [0,1,8] [2924589,5374253,5554485,5562709,4964938,5022290,5218906,5456490,5571669]) E) (N (u 6955112) E))) (N (N (N (u 1716520) E) (N (u 5915256) E)) (N (N (k 3817589 [1,0,3,13,17] [4759601,7651418,4768049,6799677,7659846]) E) (N (k 8011850 [1,8,17] [16040272,16048472,16056696,4883000,16065104,16073304]) E))))) (N (N (N (N (N (v 409652 7) (v 8794152 23)) (N (v 4599888 10) E)) (N (N (w 2490965 [23,1]) E) (N (k 6680965 [4,21,0] [8122708,12584072]) E))) (N (N (N (v 1442084 23) E) (N (k 5649240 [1,8] [11321372]) E)) (N (N (k 3555434 [6,1] [7127413,3146301,7135861,7152757]) E) (N (v 7749745 11) E)))) (N (N (N (N (u 925992) (v 9322545 10)) (N (k 5091413 [7,6,3,16,21] [10272857,10281813,10290021]) E)) (N (N (k 2831445 [7,17,1] [4924232]) E) (N (w 7225448 [1,17,23]) E))) (N (N (N (v 1962277 17) E) (N (v 6156413 11) E)) (N (N (u 4079677) E) (N (w 8257623 [23,17]) E))))))) (N (N (N (N (N (N (N (j 82261 17 [180272]) (v 8466553 4)) (N (w 4268614 [11,1]) E)) (N (N (u 2179908) E) (N (j 6365253 5 [12763240]) E))) (N (N (N (v 1114225 11) E) (N (k 5324920 [7,3,0] [10249061,10314613,10536293,10569077]) E)) (N (N (k 3223637 [7,3,17] [6472516]) E) (N (w 7389307 [4,16,21]) E)))) (N (N (N (N (u 565336) (j 8970331 4 [17973540,18006580])) (N (k 4800560 [0,1,5,10] [1490964,4128790,7045166,7049278,1495108,4132934,9617492,9625685,9633878,9650265,9658460,9666654,9674852,9683046,9678964,9687158,7586101,8319541,8315446,8737337,8733246,7590470]) E)) (N (N (k 2424938 [7,0,21] [4915498,4956490,5169496,5177690,5316965,5366121,5423477,5448057,5456485]) E) (N (k 6893705 [26,8,0] [9392484,12780680]) E))) (N (N (N (k 4199 [6,1,0,14,18] [3326056,3424385,3432585,3473793,3539333,3572105,3588493,3597189,3622021]) E) (N (v 5849156 7) E)) (N (N (v 3731597 11) E) (N (w 7946325 [7,4]) E))))) (N (N (N (N (N (v 344388 17) (v 8716425 4)) (N (j 4441207 23 [1536052,9093180,8151652]) E)) (N (N (u 2441576) E) (N (v 6627429 8) E))) (N (N (N (v 1388640 2) E) (N (v 5587317 2) E)) (N (N (j 3474261 1 [6979908]) E) (N (w 7677559 [2,17]) E)))) (N (N (N (N (u 840061) (k 9236597 [32,3] [1351717,1093673,10645589,18530393,17658149,18141481])) (N (k 5054551 [6,17,0] [10141768,10125672,10044532]) E)) (N (N (v 2830469 4) E) (N (u 7147863) E))) (N (N (N (u 1908872) E) (N (u 6111880) E)) (N (N (j 4010566 1 [5722420]) E) (N (v 8208757 4) E)))))) (N (N (N (N (N (N (k 103301 [7,3,17] [303404,368956,418116]) (v 8585288 17)) (N (k 4661 [12,6,1,17,16,3] [8831045,8839285,803117,8847685,8855909,8864117,2187847,3244619,5636725,6070903,6423161,6808187,7373637,8430453,8873079]) E)) (N (N (y 2306122 [4038696,4268628,4506228]) E) (N (y 6504520 [13025332]) E))) (N (N (N (k 1261589 [7,1] [2408536]) E) (N (k 5345349 [6,1,5,0] [10707013,10928213,10936424,9506933,9572725,11051845,11068245,11084669,11109495,11134327]) E)) (N (N (w 3359044 [11,1]) E) (N (v 7520381 11) E)))) (N (N (N (N (k 446837 [0,1,11,13,4] [1490976,1097761,1499170,917549,1122593,1425709,1507637,1524025,1532501,1540697,1065594]) (y 9126005 [18268264])) (N (k 4923441 [6,16] [9879652,8373060]) E)) (N (N (u 2834760) E) (N (k 59 [3,0,1] [14073909,14229589,14237813,14385277,7635253,13628279,14394239,14419319,14443903]) E))) (N (N (N (v 1785900 44) E) (N (w 5980277 [6,1]) E)) (N (N (v 3867253 4) E) (N (v 8077408 2) E))))) (N (N (N (N (N (w 446537 [17,6,1]) (v 8781929 17)) (N (u 4669501) E)) (N (N (u 2568312) E) (N (k 6766917 [6,17,12] [7258436]) E))) (N (N (N (v 1523752 23) E) (N (k 5345653 [5,4,7,21,16,10,17] [11452474,11468871,11501655,11518264,8163669,10904133,11535173,11543397,11551831]) E)) (N (N (k 3555653 [6,1] [696381,176245,393525,7258436,7266685,5575285,7283829]) E) (N (j 7749759 11 [13488148,15646772,15622440]) E)))) (N (N (N (N (v 987424 11) (k 9375833 [34,0,3] [18792517,14926661])) (N (v 5193776 13) E)) (N (N (v 3092565 17) E) (N (w 7233637 [7,4]) E))) (N (N (N (j 2012277 16 [4056148]) E) (N (v 6234218 6) E)) (N (N (v 4108629 17) E) (N (k 8007746 [5,6,7,21,16,3,17] [10338332,16695325,16359749,16384327,16646473,16363861,16388439,16650585,7782981,7787349,16704599]) E)))))))) (N (N (N (N (N (N (N (N (k 8313 [7,17,0,6] [65625]) (k 8376693 [16,20] [16827000])) (N (v 4243489 17) E)) (N (N (j 2061429 16 [4244292,4277332]) E) (N (k 6153063 [1,6,23,11] [12329013,12697657,5619781,12705865,10252389,12062825,12714104,12722298,7504197,12681573]) E))) (N (N (N (k 828549 [0,1,13,4] [2211872,1933360,2220320,1892652,2130244,1761928]) E) (N (j 5293143 5 [10486884]) E)) (N (N (k 3052119 [20,0,4] [6406280,6373708,2581052]) E) (N (k 7389274 [7,21,10,17] [7926373,14795381]) E)))) (N (N (N (N (u 569656) (v 8958008 13)) (N (k 4747325 [8,10] [8168260]) E)) (N (N (z 2662709) E) (N (f 6865000 [12764280]) E))) (N (N (N (v 1622316 17) E) (N (k 5816374 [4,0] [11649080]) E)) (N (N (u 3715140) E) (N (w 7913528 [6,1]) E))))) (N (N (N (N (N (k 230519 [17,5,23] [475188,639032,491828,541236,606804,623204]) (k 8007755 [17,5,6,7,16,21] [17416277,17420389,10363172,16441685,16445797,10428980,11452988,10433092,11457100,7963477,7967845])) (N (u 4493396) E)) (N (N (v 2396804 4) E) (N (k 6574154 [6,0,17] [13189448,12927624]) E))) (N (N (N (u 1355836) E) (N (y 5554280 [11019128]) E)) (N (N (u 3433333) E) (N (w 7639177 [18,4]) E)))) (N (N (N (N (k 827512 [6,1] [1687921,1712501,1737081,1745277,1753973,1762421]) (w 9216084 [11,0])) (N (w 5029975 [4,17]) E)) (N (N (u 2928964) E) (N (j 7123064 3 [14270824]) E))) (N (N (N (j 1880180 11 [3727652,3785044]) E) (N (v 6074456 21) E)) (N (N (w 3981876 [5,17]) E) (N (k 8012112 [7,0,1,6,17] [16367644,16375837,16064842,16187733,16236889,7803989]) E)))))) (N (N (N (N (N (N (v 180548 17) (w 8548423 [1,17,7])) (N (k 4326229 [6,1,13,8] [1527861,8765497,8749365,3203405,8692277]) E)) (N (N (k 2265114 [7,1,17] [4571464]) E) (N (j 6439018 2 [12902712]) E))) (N (N (N (k 1183850 [21,7] [2449768]) E) (N (u 5419588) E)) (N (N (u 3317834) E) (N (k 7520308 [7,6,21,16,10] [15056967,15065445,9983079]) E)))) (N (N (N (N (y 704812 [1114132]) (w 9093241 [37,17])) (N (w 4882500 [7,0,17]) E)) (N (N (k 2425431 [0,1,3,8] [5619848,5349948,5554756,5088104,5391224]) E) (N (v 6950972 4) E))) (N (N (N (f 1736836 [3522900,3359352]) E) (N (v 5947761 11) E)) (N (N (v 3842957 11) E) (N (w 8044588 [1,7]) E))))) (N (N (N (N (N (k 4165 [6,1,0,13] [901146,41029,942151,958537,966731,974952,983146,1073265,1081459,1130613,1278071,1343609,1409147,1433725,1441919,1483125,1548919,1581695,1598583,1606783]) (v 8822892 2)) (N (v 4583541 4) E)) (N (N (f 2519623 [5095544]) E) (N (k 6713465 [8,21,0,24] [13484100,12633224]) E))) (N (N (N (v 1372301 11) E) (N (k 5632312 [6,8,17,16,21,11,10] [11313463,11354439,11387719]) E)) (N (N (u 3579992) E) (N (u 7782424) E)))) (N (N (N (N (f 954468 [1696376]) (w 9347925 [6,42,11])) (N (k 5091445 [7,6,16,21,5,17,22,3] [10338360,10362938,81989,10371145,86101,10375257,10388567]) E)) (N (N (v 3055737 4) E) (N (w 7254122 [21,2]) E))) (N (N (N (u 2015258) E) (N (u 6205560) E)) (N (N (u 4112468) E) (N (u 8303200) E))))))) (N (N (N (N (N (N (N (f 114980 [245800]) (u 8499257)) (N (v 4309068 17) E)) (N (N (j 2212420 8 [3523173,3801705,4440917,4449113]) E) (N (u 6398073) E))) (N (N (N (u 1138804) E) (N (u 5353593) E)) (N (N (u 3240788) E) (N (k 7234117 [7,6,3] [14925913,14934357,14942565,14574169]) E)))) (N (N (N (N (f 639032 [1147176]) (w 9027689 [29,7])) (N (v 4804708 8) E)) (N (N (v 2736200 4) E) (N (z 6926420) E))) (N (N (N (u 1683576) E) (N (k 5881930 [4,0,13] [11780728]) E)) (N (N (k 3732101 [4,0] [7585856,2580556,7536948,7569720,5554500,7602504,7360852]) E) (N (w 7934053 [7,4,27]) E))))) (N (N (N (N (N (v 376884 17) (v 8765512 17)) (N (k 4571257 [32,6] [9158717,8503622]) E)) (N (N (j 2474346 8 [4890936]) E) (N (k 6656085 [20,0] [1351716,7233604,1466660,7242052,12993160]) E))) (N (N (N (y 1389380 [2810200]) E) (N (k 5584503 [9,4] [11255912,11198820]) E)) (N (N (y 3518788 [6980164]) E) (N (k 7579263 [5,0,1,10,18,4] [15450164,15458364,15466565,15482964]) E)))) (N (N (N (N (v 893016 23) (j 9277573 13 [1351716,17596456,9007188,1462564,18596136,9023828])) (N (v 5095509 8) E)) (N (N (j 2986308 23 [5988656,5718600]) E) (N (k 7033727 [17,0,1,11,10] [14401588]) E))) (N (N (N (v 4209 11) E) (N (w 5877849 [6,8]) E)) (N (N (k 3862838 [7,10,1] [1511509,8110197,6725949,7541077,8118645,7881290,5558869,8036953]) E) (N (v 8241248 2) E)))))) (N (N (N (N (N (N (v 234109 6) (u 8634473)) (N (w 4440135 [33,12,13]) E)) (N (N (y 2343765 [4350260,4440932]) E) (N (y 6537288 [13090868]) E))) (N (N (N (k 1294388 [0,13,4] [2384164]) E) (N (y 5488725 [10993768]) E)) (N (N (k 3224425 [10,13] [6799428,6587212,6767700]) E) (N (v 7581821 11) E)))) (N (N (N (N (k 447095 [6,11,0,13] [1556528,1351732,1564776,1573424,1393212,1507908]) (u 9158776)) (N (w 4956220 [6,8]) E)) (N (N (j 2867576 20 [4891192]) E) (N (v 7045252 4) E))) (N (N (N (k 4201 [6,1] [3653749,3678333]) E) (N (w 5992773 [17,12,0,1]) E)) (N (N (k 3862599 [7,3,22] [7790632]) E) (N (k 8011881 [23,20] [2564184,5263652,7991636,16237152,16245352]) E))))) (N (N (N (N (N (u 503912) (v 8892516 17)) (N (v 4702276 8) E)) (N (N (v 2564693 23) E) (N (k 6791225 [0,4] [1351700,13615172,13275220,13017480]) E))) (N (N (N (k 1556516 [7,1] [3129432]) E) (N (y 5750856 [11498312]) E)) (N (N (v 3649652 4) E) (N (u 7848296) E)))) (N (N (N (N (v 1032224 11) (w 9416761 [32,6])) (N (w 5223252 [7,1,17]) E)) (N (N (u 3129480) E) (N (v 7323728 2) E))) (N (N (N (j 2060342 20 [4178756]) E) (N (u 6275192) E)) (N (N (k 3862901 [6,1,16,11] [8372273,7774794,7922266]) E) (N (k 8372279 [1,3,0,17,8] [8552501,11288645,16760905,16769109,16785497,16793704,16842858,16851061,16859257,11280709,16867669,16875865,16884085,16892281]) E)))))))))) (N (N (N (N (N (N (N (N (N (N (k 8218 [17,6,7] [32837]) (y 8397141 [16810088])) (N (u 4202557) E)) (N (N (u 2106180) E) (N (u 6299737) E))) (N (N (N (v 1057056 11) E) (N (j 5211223 2 [8155716,10486884]) E)) (N (N (k 3051643 [16,4] [3735604]) E) (N (k 7233657 [7,0,10,21,29] [9891945,14712953,14721317,13394535]) E)))) (N (N (N (N (v 446577 11) (v 8912952 41)) (N (w 4726852 [16,8]) E)) (N (N (v 2621536 2) E) (N (u 6815832) E))) (N (N (N (j 1569653 1 [2965820]) E) (N (k 5345845 [3,12,1,0,5,4] [11567477,11051589,11174501,11395701,11535221,9409655]) E)) (N (N (v 3646549 17) E) (N (v 7864423 21) E))))) (N (N (N (N (N (k 229497 [17,1,0,6] [557141]) (j 8610903 2 [17334336,16203844,17342536,17350732,7946580,7950948])) (N (u 4452440) E)) (N (N (v 2355844 4) E) (N (w 6549604 [16,11]) E))) (N (N (N (v 1318968 17) E) (N (j 5469543 2 [11042920,10969444]) E)) (N (N (v 3416096 14) E) (N (v 7577713 11) E)))) (N (N (N (N (k 447607 [5,0,6] [1212468,1384508]) (v 9183268 4)) (N (k 27 [3,1,0,4] [9994309,10010708,10051685,10059893,10092669,10101061,10109301,9770103,10167423]) E)) (N (N (w 2884166 [11,1]) E) (N (k 7037049 [1,3,0] [13447189,13651990]) E))) (N (N (N (k 1843333 [16,6,11] [3702872,3711080,3719456,3735852]) E) (N (w 6037608 [7,4]) E)) (N (N (y 3924565 [7897428]) E) (N (k 8126821 [0,7] [16126056,16285816]) E)))))) (N (N (N (N (N (N (k 102537 [7,3] [295204,303428,311636]) (u 8519769)) (N (y 4329813 [8683844]) E)) (N (N (v 2212981 16) E) (N (k 5877866 [6,1,16] [11895109,12247397,12878197,12968317,7119429,9261941,13010039,13034623,13076087,13100671]) E))) (N (N (N (u 1187876) E) (N (k 5349493 [7,0,1,4,17] [10780698,90184,10788938,1618005,10797145,7442773]) E)) (N (N (u 3277397) E) (N (k 7234165 [7,0,10,21] [14975008,14983273,14991481,13419367,14771063]) E)))) (N (N (N (N (v 639112 4) (v 9052216 23)) (N (v 4849780 8) E)) (N (N (v 2424953 4) E) (N (u 6955065) E))) (N (N (N (k 1659017 [16,20,11,14,18,4] [3440932,3449128,3457348,3465556]) E) (N (u 5907064) E)) (N (N (k 3732613 [4,0,1,10] [7360836,7504520]) E) (N (k 103 [5,0,1,3] [4849717,16023607,16515129,16597051,16678976,16687170,10330181,16736327,16744520,17096777,17219658,17408075,4853845,16027735,16519257,16601179,14647397,17432679,17498217,17522795,14651509,17436791,17502329,17526907,7725365,8528183,10109241,10420549,11444553,13427031,14778725,14868839,15122793,15278455,13431351,10424901,11448905,7729749,8532567,10113625,15282791,14783093,14873207,15127161,17556295,17564503,17752951,17560663,17818727,17822839,17757543,17827447]) E))))) (N (N (N (N (N (v 402245 17) (j 8781878 32 [17596440,17604648,17608760,17612896,17621096,17629304,17633416])) (N (k 4583511 [8,1,13] [9207872,2584648,9216080,9224280,9232760]) E)) (N (N (u 2498600) E) (N (k 6680713 [29,8] [12567688]) E))) (N (N (N (v 1445980 2) E) (N (k 5632071 [7,17,1] [11305016,11288920,11314008]) E)) (N (N (k 3429509 [16,4] [6922836,6603592]) E) (N (k 91 [3,0,1] [15499317,15655013,15663221,15818877,15827509,13906807,14447487,15447671,15844991]) E)))) (N (N (N (N (v 925760 11) (w 9314373 [17,32])) (N (f 5120120 [10224504]) E)) (N (N (k 2831209 [1,3,17] [6062124,5808744,5907064]) E) (N (k 7034239 [17,1,0,11,10] [14450740]) E))) (N (N (N (v 1962101 4) E) (N (u 6164600) E)) (N (N (u 4068437) E) (N (u 8265813) E))))))) (N (N (N (N (N (N (N (v 74069 17) (k 8372311 [7,21,0,10,27] [16941161,16949369,16888165,16929129,16957813,16966009])) (N (v 4268054 11) E)) (N (N (u 2171716) E) (N (j 6365237 5 [12746856]) E))) (N (N (N (v 1122600 17) E) (N (v 5316676 17) E)) (N (N (k 4219 [1,5,0,10] [6455333,5668902,6463573,729177,6479973,2883689,6537349,6545545,4858148,4931877,5669158,6553900,6611246,360789,778585,2031973,3096937,3572101,3850633,6636084,6709813,6718006,6734393,6742596,6775366,6783845,6792041,6808661,6816869,6833285]) E) (N (k 7389303 [21,7,16,18] [14844024]) E)))) (N (N (N (N (v 598044 17) (k 8970327 [4,0] [17973544])) (N (u 4788296) E)) (N (N (u 2695288) E) (N (k 5878871 [6,1,5,2,0,26,8] [10199092,13795384,10309765,13803657,12042556,13549908,10563973,13812276,13820549,12772216,5657477,9385349]) E))) (N (N (N (v 1642609 11) E) (N (k 5346167 [7,3,0,1,4] [10772532,11698264,1609829,11714680,10887476,11567444,7434853,11109221,11223941]) E)) (N (N (v 3736445 11) E) (N (w 7938119 [7,4]) E))))) (N (N (N (N (N (v 328532 6) (w 8724853 [21,9])) (N (v 4522581 17) E)) (N (N (v 2429240 1) E) (N (k 6627397 [6,1] [1351717,13271333]) E))) (N (N (N (k 1372293 [23,8,1] [2785368,2793568,2801768,2818168,2826528,2842924,909876,2859844,2868052]) E) (N (k 5345381 [6,1,18,5] [11174725,11191141,11207549,11224183,11249271]) E)) (N (N (y 3474005 [6979908]) E) (N (w 7676229 [6,17,12]) E)))) (N (N (N (N (u 856184) (v 9240701 11)) (N (k 5054538 [17,1,4] [10125653,7909973,10036068]) E)) (N (N (v 2946165 16) E) (N (u 7151720) E))) (N (N (N (v 1908776 44) E) (N (v 6103068 38) E)) (N (N (k 3862617 [1,0,17,10,13] [4968470,8028209,5714213,8036934]) E) (N (k 8012117 [7,1,17,22] [16097304]) E)))))) (N (N (N (N (N (N (w 205124 [5,3,17]) (v 8585276 17)) (N (j 4387941 4 [6955044,8814632,8798500,8753476,8692276]) E)) (N (N (k 1958452 [7,17] [4620314,4628554,3989805,4030788,4260180,4399445,4497780,4637045,4645717,4662133]) E) (N (u 6484085) E))) (N (N (N (u 1245304) E) (N (k 5350005 [7,4,17] [10911818,10854701,8180053,10879829]) E)) (N (N (k 3224117 [20,11,10] [5677128]) E) (N (w 7520357 [6,1,18]) E)))) (N (N (N (N (v 720980 23) (k 9113655 [32,6,23] [18251848,18276426,10608725,18292825,18309240,18350202,18358401,17588357,18366601,18391181,18399573,18407813,18432397,8909957])) (N (k 4923440 [6,38] [9863252]) E)) (N (N (k 4215 [1,7,0,10] [3981353,5668906,5685320,5734474,5750864,5759058,270421,5767256,5832793,5840986,1785957,5857385,5890168,5931130,5939333,5947529,4530464,4596002,4858152,4931881,5669162,352597,770393,1974629,3047785,3539333,3817865,5956158,5964358,5972581,6021737,6038373,6054761,6071381,6079589,6096005]) E) (N (u 7016564) E))) (N (N (N (v 1769760 11) E) (N (v 5972036 20) E)) (N (N (u 3866965) E) (N (v 8069496 7) E))))) (N (N (N (N (N (k 446535 [6,0,33] [237624,950568]) (v 8851548 11)) (N (v 4583545 4) E)) (N (N (k 2564437 [0,1,30] [5144680,5152888]) E) (N (k 6750325 [27,8,0] [12665992]) E))) (N (N (N (v 1499268 4) E) (N (v 5705784 13) E)) (N (N (v 3608644 23) E) (N (y 7807276 [15573012]) E)))) (N (N (N (N (f 987240 [1720952]) (w 9379925 [17,43])) (N (u 5185621) E)) (N (N (k 3051605 [0,1,3,13] [2539546,1351717,6193205,6201429,6209625,6217848,6226042,6234405,6242869,6251065]) E) (N (w 7246677 [7,6,25]) E))) (N (N (N (u 2039876) E) (N (u 6234201) E)) (N (N (v 4128837 17) E) (N (w 8298885 [14,17,22]) E)))))))) (N (N (N (N (N (N (N (N (u 41000) (k 8376661 [23,20] [16806008,16802408])) (N (v 4218969 17) E)) (N (N (w 2060853 [17,20]) E) (N (k 6153031 [6,1,5,12] [10252405,12681589,10539637]) E))) (N (N (N (k 828501 [6,0,13] [2195756]) E) (N (w 5277303 [3,17]) E)) (N (N (j 3051863 23 [1351732,6144308,6234676]) E) (N (w 7373957 [18,16]) E)))) (N (N (N (N (j 565274 23 [1147176,1155384,1163592]) (j 8942423 5 [17924144,1351732,17932344,17596476,8692052,8696388,10355560])) (N (k 4747324 [7,0,6,3] [9535573,2728025]) E)) (N (N (v 2662485 17) E) (N (v 6811708 4) E))) (N (N (N (u 1613892) E) (N (y 5809239 [10355540,11391844,11387988,11527268]) E)) (N (N (k 3556479 [6,20] [7438388,7446596,7454820,7266628]) E) (N (v 7745661 11) E))))) (N (N (N (N (N (k 230261 [7,17] [622933]) (v 8691776 17)) (N (v 4493380 23) E)) (N (N (v 2396764 10) E) (N (v 6590824 4) E))) (N (N (N (k 1115263 [5,2] [2719796,2727996,2736444]) E) (N (y 5541989 [11002744]) E)) (N (N (u 3449156) E) (N (w 7639144 [4,18]) E)))) (N (N (N (N (w 827434 [0,13,4]) (v 9216060 10)) (N (w 4993125 [6,1,18]) E)) (N (N (k 2830441 [23,8] [5865560,1286436,5873988,5882196]) E) (N (k 7118919 [1,3,17] [14254136,14262392,14279016]) E))) (N (N (N (k 1843585 [6,16,1,11] [3768420,3776628,3793028,3719460,3809620]) E) (N (k 6045829 [0,6,1,27] [12157000,12165208,12173416,12189816,12206728]) E)) (N (N (v 3925109 4) E) (N (v 8011909 4) E)))))) (N (N (N (N (N (N (k 102789 [7,1,17] [295212]) (v 8553045 7)) (N (v 4366420 17) E)) (N (N (u 2269242) E) (N (u 6439001) E))) (N (N (N (u 1220968) E) (N (k 5349499 [5,10] [10780964,10846772,10854980]) E)) (N (N (v 3317818 20) E) (N (w 7512164 [8,4]) E)))) (N (N (N (N (v 672057 11) (w 9085001 [33,17])) (N (k 4882492 [7,0] [6029350,8626741]) E)) (N (N (w 2793517 [8,17]) E) (N (v 6987848 21) E))) (N (N (N (f 1736820 [3342380,3506516]) E) (N (v 5881997 11) E)) (N (N (w 3842437 [18,20,4]) E) (N (v 8011856 2) E))))) (N (N (N (N (N (v 324693 6) (v 8822852 23)) (N (j 4628853 42 [9273408]) E)) (N (N (u 2519367) E) (N (v 6726501 8) E))) (N (N (N (y 1442628 [2966084]) E) (N (k 5632089 [17,6,1,7] [11370581]) E)) (N (N (v 3579960 4) E) (N (y 7757956 [14053940]) E)))) (N (N (N (N (v 958584 4) (k 9347141 [6,42] [17793317])) (N (u 5152904) E)) (N (N (u 3055705) E) (N (k 7245941 [7,0,27,25] [14516328,14524522,12108341]) E))) (N (N (N (k 1957972 [7,0,10] [1941845,3015001,3490165,3768697,4031028,4063797,4072277,4080473,4097109,4105333]) E) (N (k 6197365 [1,6] [12419176,12427384]) E)) (N (N (k 3862869 [0,1,11,10] [8224817,8228914,2945082,2940989,2117702,159829,610393,7770413,2113845,8257860,8298837,7766602,7815762,7889498,156501,607065,8303701]) E) (N (k 8298597 [17,23] [16613448,16622176,16630376,7742276]) E))))))) (N (N (N (N (N (N (N (w 102485 [6,0,33]) (k 8373063 [0,1,11,10] [17006641,16769077,17014841,17023037,1564741,17031241,1568853,17035353,8569157,8573525])) (N (k 4264518 [17,3,1] [8561240]) E)) (N (N (v 1957996 23) E) (N (u 6398009) E))) (N (N (N (u 1138788) E) (N (k 5349445 [6,1,0,5] [10715162,1618037,10723449,9113973]) E)) (N (N (y 3240772 [6521208]) E) (N (v 7434800 11) E)))) (N (N (N (N (u 631160) (k 9015416 [6,1,11] [13521735,15340391])) (N (v 4804700 2) E)) (N (N (v 2424949 4) E) (N (k 6914105 [0,8,4] [13860932,13869140,13083016]) E))) (N (N (N (k 1663349 [1,6] [3375208,3383416]) E) (N (k 55 [0,6,1,3] [892981,11763767,11960377,10190917,11984969,12075093,12091479,12296281,12304488,12869738,13140081,4853877,13148279,13254777,13303933,13312127,7110965,7463223,10101049,13361495,13427063,13500799,13533765,9171573,13574983,13583223,13624191,13788247,10654839,11695231,13829495,13903231]) E)) (N (N (k 3731853 [4,20] [6148132,7225396,6987860,7569716,6373708]) E) (N (k 7934052 [7,6,11,27,16,10] [15958871]) E))))) (N (N (N (N (N (w 323925 [6,0]) (k 8007787 [7,17,0,21] [17530997,17547397,17301864,16511349,17494405,8098933,14857349])) (N (u 4550756) E)) (N (N (u 2466136) E) (N (u 6660169) E))) (N (N (N (j 1388844 8 [2383908,2851144]) E) (N (u 5611624) E)) (N (N (j 3428965 23 [7045168,2932796,2056500,7053636,7061844,6144564,6898244,6971988]) E) (N (v 7704628 8) E)))) (N (N (N (N (u 892968) (k 9277508 [6,35] [9007221,18452853])) (N (k 39 [3,0,1,5,6] [16437,10190917,10264661,10297445,10330229,10420597,10519109,10551909,10584693,10601287,10650487,10667095,9491575,10683767]) E)) (N (N (u 2990388) E) (N (k 7119207 [21,7] [14328696]) E))) (N (N (N (w 1844101 [4,16,20]) E) (N (w 6135928 [0,4]) E)) (N (N (v 4026472 20) E) (N (k 8012137 [23,1,13,17,22] [7762260,16294520]) E)))))) (N (N (N (N (N (N (v 233593 23) (v 8626264 8)) (N (k 4412535 [17,12] [5566564,7364964,5571156,8303204]) E)) (N (N (v 2335364 4) E) (N (w 6516836 [16,11]) E))) (N (N (N (w 1262133 [0,10]) E) (N (v 5480805 2) E)) (N (N (k 3224134 [8,1] [6725956]) E) (N (k 7577657 [19,1] [15171701,15179901,14988149]) E)))) (N (N (N (N (v 741973 17) (k 9121912 [35,6] [18317685,18334077,8950901])) (N (w 4956212 [7,4]) E)) (N (N (y 2843477 [5718340]) E) (N (u 7045220) E))) (N (N (N (v 1810464 11) E) (N (v 5992533 8) E)) (N (N (u 3907924) E) (N (v 8101916 33) E))))) (N (N (N (N (N (k 491893 [1,6] [1015848,1024104,1032312]) (k 8876089 [6,16] [17793092,17801316,17375592])) (N (k 4935 [6,1,5] [41012,221237,516156,688189,8831060,192645,114996,385333,8847700,9404813,7250500,8876677,5645189,6431625,8512645,9373061]) E)) (N (N (v 2592888 8) E) (N (v 6791216 8) E))) (N (N (N (v 1548584 11) E) (N (u 5742620) E)) (N (N (j 3645489 23 [7307348,7315572,5988644,7324228]) E) (N (v 7839812 4) E)))) (N (N (N (N (w 1024308 [11,0]) (k 1111 [7,0,1,6,2] [18841649,14590005,18849849,18858045,18800725,18866265,18845809,14594165,18854009,18862205,14958901,14963317,17826679])) (N (k 5210183 [7,1,17] [10453048,10462036]) E)) (N (N (v 3093049 4) E) (N (v 7233649 11) E))) (N (N (N (u 2064500) E) (N (v 6266993 11) E)) (N (N (u 4169789) E) (N (k 8007751 [17,22,7,6,16,21,2] [16695336,10363176,16408917,16413029,7840597,7844965]) E))))))))) (N (N (N (N (N (N (N (N (N (w 24693 [7,1,17]) (u 8397161)) (N (v 4218913 17) E)) (N (N (w 2060582 [8,17]) E) (N (k 6152559 [6,11,1] [12648533,12664949]) E))) (N (N (N (v 1073184 11) E) (N (w 5260663 [3,17]) E)) (N (N (u 3170392) E) (N (v 7233661 11) E)))) (N (N (N (N (y 540964 [1114136]) (k 8937509 [5,4,8,21,16,10,17] [6111285,17891383,17899577,10338376,16695370,6115413,17895511,17903705,8663381,8659509,17916759])) (N (k 4991 [7,6,3,16,20] [9502772,9519157,9527356,9543741,9551940,9568340,9576549,565564,819517,9404773,9453957,8159812,1606501,2712425,7431269,9102693]) E)) (N (N (k 2621576 [1,6] [5153128,5308792]) E) (N (k 6815866 [16,5] [13672808]) E))) (N (N (N (u 1594233) E) (N (w 5792069 [7,21]) E)) (N (N (k 3556213 [0,1,4,8,10] [4726849,7381077,7405657,7413866,5558566,7209262,7348532,7356726,4694337,6758733,7152250,3171149,7283541]) E) (N (u 7885909) E))))) (N (N (N (N (N (v 282692 8) (k 8610935 [6,16] [17367104,17375304,7954772])) (N (v 4476989 17) E)) (N (N (v 2384500 4) E) (N (u 6578230) E))) (N (N (N (k 1335348 [7,1] [2687064]) E) (N (k 5460821 [6,1,5,26] [11075957,10961512,9466485,9483125]) E)) (N (N (v 3432522 20) E) (N (w 7618935 [21,8]) E)))) (N (N (N (N (k 802884 [11,0] [1638716]) (k 9122181 [32,11,10] [18415648,1351716,18423856,1294392,18321528,18428192,1298732,18317960])) (N (w 5005387 [7,4]) E)) (N (N (v 2884725 16) E) (N (j 7037055 11 [13447188,14221364,14197032]) E))) (N (N (N (u 1859684) E) (N (v 6053992 17) E)) (N (N (v 3924597 4) E) (N (u 8151144) E)))))) (N (N (N (N (N (N (k 102741 [6,0] [327736,237868]) (k 8007753 [5,6,1,0,7,3,17] [10362902,17104965,17145927,16531529,17109077,17150039,16535641,17154373,17158485,17162597,17166709,17171543])) (N (j 4350534 1 [6983988]) E)) (N (N (v 1958021 4) E) (N (u 6447464) E))) (N (N (N (v 1183829 17) E) (N (k 5349495 [7,1,17] [10813528,10780968]) E)) (N (N (k 3223854 [8,10] [3932180,4603940,6619188,6627396]) E) (N (k 7234647 [7,6,21] [14483516,10281268,14934356]) E)))) (N (N (N (N (v 671797 13) (k 8938855 [7,4,21] [18153528])) (N (v 4800588 10) E)) (N (N (v 2773333 17) E) (N (u 6971768) E))) (N (N (N (u 1716564) E) (N (u 5922844) E)) (N (N (v 3821894 1) E) (N (v 8016216 17) E))))) (N (N (N (N (N (u 409684) (u 8794216)) (N (j 4600184 35 [9240896]) E)) (N (N (k 2424904 [1,17,0] [5046343,5062759,5071175,5079399,5087815,5104231]) E) (N (k 5878135 [6,1,11,0,17] [13205576,5611605,13434969,13451368,13467754,13377653,13475961,7520597,13410677,8106564,8614470,1549141,13493109,12600200]) E))) (N (N (N (y 1442116 [2949956]) E) (N (k 5632073 [17,1,0,4] [11337813,9564757]) E)) (N (N (y 3560053 [7143764]) E) (N (v 7757908 4) E)))) (N (N (N (N (u 926036) (v 9322557 10)) (N (w 5133141 [17,6,1]) E)) (N (N (v 3039840 2) E) (N (k 7233609 [7,6,21,16,3] [14483545]) E))) (N (N (N (u 1991220) E) (N (u 6185064) E)) (N (N (u 4088148) E) (N (v 8257653 4) E))))))) (N (N (N (N (N (N (N (k 9335 [17,2] [196656,65596,156244,172644]) (u 8466809)) (N (k 4264026 [17,20,3] [6333260]) E)) (N (N (u 2188100) E) (N (k 6153303 [6,1,5] [10317941,12779641,10572149,12788341]) E))) (N (N (N (j 1138740 11 [2294052]) E) (N (v 5333048 24) E)) (N (N (k 3223653 [0,20,11,13,4] [6488128,6496392,2597164,4866612,6505020,6513476,6529876]) E) (N (k 7233911 [7,21,0,4,10] [14876776,14884970,5607541,14893177,13410677,14754181,14901808,14721596,8393333,14549881]) E)))) (N (N (N (N (k 565338 [2,0,1] [1245544,1249656]) (k 8970581 [6,1] [1593413,18022473,18006317,8802629])) (N (v 4804693 17) E)) (N (N (u 2711656) E) (N (k 6894213 [2,17,0,15,8] [12788872]) E))) (N (N (N (k 1663345 [6,1,16] [3342380,3350628,3358836]) E) (N (k 5346391 [7,4,21] [11731000,11600468]) E)) (N (N (v 3760232 23) E) (N (v 7934012 20) E))))) (N (N (N (N (N (v 352556 17) (w 8716681 [41,17,22])) (N (j 4441215 6 [9109556,9117756,9125956,9134180,8208996]) E)) (N (N (w 2429258 [8,17]) E) (N (w 6627687 [21,8]) E))) (N (N (N (u 1401668) E) (N (v 5595509 2) E)) (N (N (j 3428453 23 [1351716,6881348,6955092,1450276,7012676,7020884]) E) (N (k 7578727 [6,1,9,5,2] [10326149,15401097,15204668,15368532,10580357,15381125]) E)))) (N (N (N (N (w 840821 [1,4]) (v 9236605 11)) (N (w 5054553 [17,1,0]) E)) (N (N (k 2830910 [7,1,17] [5784152]) E) (N (v 7168357 15) E))) (N (N (N (v 1925416 11) E) (N (k 6046072 [6,1,40] [12132682,12255601,12206453,12231033,12263805,9270389]) E)) (N (N (k 3862647 [20,16,18] [8061000,8069208,8077408,8085608]) E) (N (w 8012121 [17,7,1]) E)))))) (N (N (N (N (N (N (k 103557 [7,1,3,17] [311596,377148]) (k 8609863 [17,1,3,8] [17236056,17244280,11460928])) (N (k 4411509 [7,17,1] [7382101]) E)) (N (N (y 2306901 [4383028,4047700,4653940]) E) (N (k 6435967 [4,16,20,11] [13041732,13066340,7680612]) E))) (N (N (N (v 1261653 17) E) (N (k 5460072 [6,1,5] [10945349,10961749,10978157,11011175,11036007]) E)) (N (N (k 3224132 [8,1] [6750314,6529365,2957657,377413,795209,6759253,6767449]) E) (N (k 7561306 [7,17,4] [7934565,15074132]) E)))) (N (N (N (N (v 741410 11) (k 9121866 [36,4] [18284920])) (N (w 4923448 [39,4,1]) E)) (N (N (u 2842709) E) (N (v 7037041 11) E))) (N (N (N (k 1659781 [20,0,14,18,4] [3604512,3612960,3457324,3408504]) E) (N (k 5877833 [6,1,5] [11993157,12017749,12025973,12034373,12042581,11702653,9188213,12051575,12068215]) E)) (N (N (v 3891229 20) E) (N (v 8077432 8) E))))) (N (N (N (N (N (w 446568 [6,1]) (k 8008567 [6,1,16,11] [17760304,17768497,17776696,17784889,17809497,8487236,17040232,17359722])) (N (v 4677696 44) E)) (N (N (u 2564456) E) (N (k 6767735 [2,17,1] [12685432,7283044]) E))) (N (N (N (u 1523816) E) (N (v 5726277 8) E)) (N (N (j 3625341 6 [7274580]) E) (N (w 7745637 [7,0,21]) E)))) (N (N (N (N (v 1007648 11) (w 9375845 [7,4])) (N (v 5193788 22) E)) (N (N (v 3092600 4) E) (N (k 7299189 [6,1] [14614632,14622826]) E))) (N (N (N (k 1957988 [7,0,10] [4128786,1097750,4161566,4169782,4186174,4210758,4227364,4251942,3498357,3776889,4260404,4284981,4293188,4301941]) E) (N (k 6152303 [5,4,1] [12517461,12525685]) E)) (N (N (j 4153408 8 [1519684,8323156,7549252]) E) (N (y 8344663 [16711744,16187460,16719944,16728140,7831892,7836260,10355532]) E)))))))) (N (N (N (N (N (N (N (N (w 8549 [17,19,1]) (k 8372283 [17,1,0] [16908373,16916597,16879957,16925045])) (N (k 3863639 [17,5] [159812,8192332,5575220,8299076]) E)) (N (N (v 2154564 13) E) (N (u 6344777) E))) (N (N (N (v 1102112 11) E) (N (k 5300278 [6,0] [10616888]) E)) (N (N (w 3052151 [20,18,4]) E) (N (k 7389287 [21,7,0,4] [14811256,14819464]) E)))) (N (N (N (N (f 565290 [1147176,1167672,1179976]) (k 8970295 [1,7,17] [17956952])) (N (u 4776025) E)) (N (N (u 2679160) E) (N (y 6873154 [13762596,13770868]) E))) (N (N (N (v 1630240 8) E) (N (v 5816376 13) E)) (N (N (k 4423 [6,1,0,10] [7471224,5582981,7512205,7520645,7561613,2630204,3179069,7578245,7611265,5612421,6398857,7619469,7627909]) E) (N (k 7921716 [17,0,1,5] [15859816]) E))))) (N (N (N (N (N (k 4155 [3,1,6,16,5] [213030,655445,688217,704645,729225,24868,213286,745813,754009,770437,778633,803396,819853,861013,869253,877653,885893]) (v 8708184 17)) (N (v 4493444 4) E)) (N (N (v 2416680 14) E) (N (k 6574184 [4,17,0,1] [10792982,11927893,12280165,12943736,5796422,7193429]) E))) (N (N (N (k 4171 [1,0,3] [1663014,2752597,688217,2769025,2777221,2883721,2990221,901412,1663270,336213,754009,2998657,3047813,3096969,3113357,3138100,3179061,3187268,3212165,3228553,3245141,3261573]) E) (N (k 5461367 [6,0,15,7] [11141224,11075940,11035528]) E)) (N (N (u 3465304) E) (N (k 7659605 [18,4,1] [15335560]) E)))) (N (N (N (N (u 843876) (k 9113657 [32,3] [18481173,18513989,18522229,18538621,17703287,18133375,8958837,10638455,11670655])) (N (w 5030233 [6,8]) E)) (N (N (k 2830456 [7,0,10] [1999205,3080553,3555701,3842425,5899109,5907305,5915749,5923957]) E) (N (k 7123304 [1,12] [14270824]) E))) (N (N (N (y 1880196 [3801428]) E) (N (u 6087288) E)) (N (N (u 3989592) E) (N (w 8179741 [1,7,17]) E)))))) (N (N (N (N (N (N (k 102997 [6,12,17] [393540]) (k 8548709 [34,17,8,6] [17142373])) (N (k 4479 [7,4,16,20,10] [8658964,6111284,6455349,6946884,8781925,7561573,6357564,6734397,8729189,1581925,2671465,8807525]) E)) (N (N (y 2265162 [4571432,4235860]) E) (N (k 6435197 [5,4,1] [12976164,12992597,13000821]) E))) (N (N (N (v 1237592 17) E) (N (u 5431417) E)) (N (N (v 3318137 4) E) (N (k 7524709 [7,4,16,17] [15073354,15081559,8425813]) E)))) (N (N (N (N (v 446589 11) (k 9081445 [12,0,17,1,3,5,31] [10285173,18219129,15360325,14938485,123461,8856389,13554549])) (N (v 4882508 10) E)) (N (N (k 2425463 [16,6,1] [5104488,5407624]) E) (N (f 7004280 [12862584]) E))) (N (N (N (y 1737044 [3506532,3522932]) E) (N (k 5882245 [20,6,0,11] [1302584,11927656,11936032,5255468]) E)) (N (N (k 4469 [1,5,0,10] [7733306,7782466,7839815,7848010,7962699,5550165,7979095,8020057,8044635,8052855,8093819,4612385,6635821,6717743,8102198,8134981,8159561,8216917,8307031,8339801,8364405,8388983,8405369,148037,434759,598601,868939,2146903,3211867,3596919,3891835,8430405,8438613,8487797,8512599,8520823]) E) (N (k 8053077 [20,0,30] [16121976]) E))))) (N (N (N (N (N (z 450677) (y 8781886 [1351700,17694756,17698868])) (N (v 4644928 10) E)) (N (N (u 2519655) E) (N (v 6714229 8) E))) (N (N (N (v 1499220 10) E) (N (k 5632837 [17,1,4] [9417301,9425749]) E)) (N (N (k 3555449 [6,1,8] [6148117,7209286]) E) (N (u 7790696) E)))) (N (N (N (N (f 954484 [1704568]) (k 9323077 [6,1] [18743417,11604349,18719353])) (N (w 5169207 [1,7]) E)) (N (N (k 3051589 [17,7,0,6] [6160473]) E) (N (u 7266424) E))) (N (N (N (u 2016101) E) (N (v 6197373 11) E)) (N (N (u 4112964) E) (N (v 8298629 4) E))))))) (N (N (N (N (N (N (N (u 115012) (u 8499273)) (N (v 4317216 13) E)) (N (N (u 2216793) E) (N (j 6414389 5 [12845176]) E))) (N (N (N (y 1138980 [2359320,2294052]) E) (N (k 5349449 [6,1,5] [10715158,10748021,9597049]) E)) (N (N (v 3223689 4) E) (N (w 7459157 [7,6]) E)))) (N (N (N (N (j 639064 23 [1163560]) (k 8937772 [7,6,11,21,10,16] [18088519])) (N (u 4841844) E)) (N (N (v 2736224 2) E) (N (k 6914121 [0,8] [13869140,12813448]) E))) (N (N (N (u 1663357) E) (N (v 5881985 11) E)) (N (N (v 3792980 17) E) (N (k 7934807 [7,4,0,1,13] [15900724,15990838,15999032,15909172,15913524,15934308,16008044,15958900,15963012]) E))))) (N (N (N (N (N (k 323977 [5,17] [712996,786756,794964]) (k 8008519 [7,17,6,16,3] [81972,16531516,147524,5636404,8429892,17154620,11534924,10498644,5649253,8516965])) (N (k 4725 [7,0,1,3] [9175072,4014113,5963815,5963831,8839237,9183305,1486933,9199703,9248857,9257066,9281653,9289847,9330809,4686113,5964071,6742317,6775087,8102198,8610103,8716606,7295317,7582039,9339225,9355639,164421,451143,614985,885323,2204247,3261019,3621495,3900027,7398229,7627607,7668569,7717751,9372759,9380983]) E)) (N (N (v 2424896 2) E) (N (k 5878103 [6,1,0,8,25] [12099656,13369473,13377669,13394057,13402253,13410693,13419141,12534648,5608325,9360517]) E))) (N (N (N (v 1433960 8) E) (N (k 5345397 [5,4,1,7,16,10,17] [10338360,11272250,10772549,11296839,11329609,9506901,11346007,11362393,11379000,9556309,11395909,11404133,11412567]) E)) (N (N (j 3429221 23 [6881316,7012644,7053636,6988372,6579016]) E) (N (v 7721020 18) E)))) (N (N (N (N (u 893032) (v 9277581 11)) (N (j 5104743 1 [10223736]) E)) (N (N (k 2830953 [8,17] [6029372]) E) (N (v 7200856 17) E))) (N (N (N (k 1957916 [7,0] [3932182,3940437,1798233,3956853,3965049,3973413]) E) (N (k 6152247 [6,1] [12320881,12329077,12353657,12361853,12370293]) E)) (N (N (k 4051317 [1,8] [8126528]) E) (N (k 8012169 [6,16,1,14,17] [16319112]) E)))))) (N (N (N (N (N (N (w 229449 [17,6,1]) (k 8610151 [15,17] [14729304])) (N (k 4440183 [35,8] [8912960,8921160,8929360,8937560,8945784]) E)) (N (N (k 1958757 [1,0] [4718632,4342052,4727380,4072036,4735596,4457076,4743812,4695124]) E) (N (k 6436479 [4,16,21,11] [13107268,13131876]) E))) (N (N (N (v 1114237 11) E) (N (u 5488741) E)) (N (N (k 3224661 [7,17] [4924228,6685780]) E) (N (w 7594309 [17,6,1]) E)))) (N (N (N (N (w 774248 [0,4]) (u 9166884)) (N (w 4956228 [7,4]) E)) (N (N (k 2830418 [7,1,22] [278556,4899384]) E) (N (u 7069720) E))) (N (N (N (w 1826904 [4,16]) E) (N (k 5993591 [17,2,1,7] [12001332,12058744,7410276]) E)) (N (N (w 3924002 [11,3]) E) (N (u 8114792) E))))) (N (N (N (N (N (u 491897) (k 8008807 [7,17,15,6,16] [17162556,11542860,10506580,5657461,8525173])) (N (y 4702308 [7275348]) E)) (N (N (w 2424907 [7,17,1]) E) (N (k 5878655 [5,0,1,10,4] [13631540,13697077,13721660,13729861,13746260,7672404,12731272,13034378]) E))) (N (N (N (k 1372724 [4,1,0] [3145834,2761029,696649,2859381,2974073,3154757,3171189]) E) (N (u 5759815) E)) (N (N (y 3645490 [2142276,7340148,2109764,7328324]) E) (N (w 7831625 [17,0,1]) E)))) (N (N (N (N (u 1040428) (w 9416793 [32,7])) (N (k 5210420 [7,6,17,16,5,21,3] [143429,10461495,10465607,139829,10486599]) E)) (N (N (v 3051637 4) E) (N (u 7332455) E))) (N (N (N (y 2060350 [4194356,4203332]) E) (N (v 6267005 11) E)) (N (N (v 4186196 4) E) (N (k 8376405 [0,1] [16777320,16781432]) E))))))))))))
noncomputable def x251 : Nat → Bool := checkNode m251Mask m251Goal (Nat.sub (Nat.shiftLeft 1 m251Pairs.length) 1) sym251 2304 11 m251Ws m251D 12 m251Cuts 6
noncomputable def y251 : Nat → Nat → Bool := checkRange m251Mask m251Goal (Nat.sub (Nat.shiftLeft 1 m251Pairs.length) 1) sym251 2304 11 m251Ws m251D 12 m251Cuts 6
theorem s251 (s n : Nat) (h : y251 s n = true) : ac x251 s n := cr_sound h
theorem q47 : ac x251 0 40 := s251 0 40 (by decide +kernel)
theorem q48 : ac x251 40 40 := s251 40 40 (by decide +kernel)
theorem q49 : ac x251 80 40 := s251 80 40 (by decide +kernel)
theorem q50 : ac x251 120 40 := s251 120 40 (by decide +kernel)
theorem q51 : ac x251 160 40 := s251 160 40 (by decide +kernel)
theorem q52 : ac x251 200 40 := s251 200 40 (by decide +kernel)
theorem q53 : ac x251 240 40 := s251 240 40 (by decide +kernel)
theorem q54 : ac x251 280 40 := s251 280 40 (by decide +kernel)
theorem q55 : ac x251 320 40 := s251 320 40 (by decide +kernel)
theorem q56 : ac x251 360 40 := s251 360 40 (by decide +kernel)
theorem q57 : ac x251 400 40 := s251 400 40 (by decide +kernel)
theorem q58 : ac x251 440 40 := s251 440 40 (by decide +kernel)
theorem q59 : ac x251 480 40 := s251 480 40 (by decide +kernel)
theorem q60 : ac x251 520 40 := s251 520 40 (by decide +kernel)
theorem q61 : ac x251 560 40 := s251 560 40 (by decide +kernel)
theorem q62 : ac x251 600 40 := s251 600 40 (by decide +kernel)
theorem q63 : ac x251 640 40 := s251 640 40 (by decide +kernel)
theorem q64 : ac x251 680 40 := s251 680 40 (by decide +kernel)
theorem q65 : ac x251 720 40 := s251 720 40 (by decide +kernel)
theorem q66 : ac x251 760 40 := s251 760 40 (by decide +kernel)
theorem q67 : ac x251 800 40 := s251 800 40 (by decide +kernel)
theorem q68 : ac x251 840 40 := s251 840 40 (by decide +kernel)
theorem q69 : ac x251 880 40 := s251 880 40 (by decide +kernel)
theorem q70 : ac x251 920 40 := s251 920 40 (by decide +kernel)
theorem q71 : ac x251 960 40 := s251 960 40 (by decide +kernel)
theorem q72 : ac x251 1000 40 := s251 1000 40 (by decide +kernel)
theorem q73 : ac x251 1040 40 := s251 1040 40 (by decide +kernel)
theorem q74 : ac x251 1080 40 := s251 1080 40 (by decide +kernel)
theorem q75 : ac x251 1120 40 := s251 1120 40 (by decide +kernel)
theorem q76 : ac x251 1160 40 := s251 1160 40 (by decide +kernel)
theorem q77 : ac x251 1200 40 := s251 1200 40 (by decide +kernel)
theorem q78 : ac x251 1240 40 := s251 1240 40 (by decide +kernel)
theorem q79 : ac x251 1280 40 := s251 1280 40 (by decide +kernel)
theorem q80 : ac x251 1320 40 := s251 1320 40 (by decide +kernel)
theorem q81 : ac x251 1360 40 := s251 1360 40 (by decide +kernel)
theorem q82 : ac x251 1400 40 := s251 1400 40 (by decide +kernel)
theorem q83 : ac x251 1440 40 := s251 1440 40 (by decide +kernel)
theorem q84 : ac x251 1480 40 := s251 1480 40 (by decide +kernel)
theorem q85 : ac x251 1520 40 := s251 1520 40 (by decide +kernel)
theorem q86 : ac x251 1560 40 := s251 1560 40 (by decide +kernel)
theorem q87 : ac x251 1600 40 := s251 1600 40 (by decide +kernel)
theorem q88 : ac x251 1640 40 := s251 1640 40 (by decide +kernel)
theorem q89 : ac x251 1680 40 := s251 1680 40 (by decide +kernel)
theorem q90 : ac x251 1720 40 := s251 1720 40 (by decide +kernel)
theorem q91 : ac x251 1760 40 := s251 1760 40 (by decide +kernel)
theorem q92 : ac x251 1800 40 := s251 1800 40 (by decide +kernel)
theorem q93 : ac x251 1840 40 := s251 1840 40 (by decide +kernel)
theorem q94 : ac x251 1880 40 := s251 1880 40 (by decide +kernel)
theorem q95 : ac x251 1920 40 := s251 1920 40 (by decide +kernel)
theorem q96 : ac x251 1960 40 := s251 1960 40 (by decide +kernel)
theorem q97 : ac x251 2000 40 := s251 2000 40 (by decide +kernel)
theorem q98 : ac x251 2040 40 := s251 2040 40 (by decide +kernel)
theorem q99 : ac x251 2080 40 := s251 2080 40 (by decide +kernel)
theorem q100 : ac x251 2120 40 := s251 2120 40 (by decide +kernel)
theorem q101 : ac x251 2160 40 := s251 2160 40 (by decide +kernel)
theorem q102 : ac x251 2200 40 := s251 2200 40 (by decide +kernel)
theorem q103 : ac x251 2240 40 := s251 2240 40 (by decide +kernel)
theorem q104 : ac x251 2280 24 := s251 2280 24 (by decide +kernel)
theorem m251All : ac x251 0 2304 := (tm 0 1160 1144 (tm 0 560 600 (tm 0 280 280 (tm 0 120 160 (tm 0 40 80 q47 (tm 40 40 40 q48 q49)) (tm 120 80 80 (tm 120 40 40 q50 q51) (tm 200 40 40 q52 q53))) (tm 280 120 160 (tm 280 40 80 q54 (tm 320 40 40 q55 q56)) (tm 400 80 80 (tm 400 40 40 q57 q58) (tm 480 40 40 q59 q60)))) (tm 560 280 320 (tm 560 120 160 (tm 560 40 80 q61 (tm 600 40 40 q62 q63)) (tm 680 80 80 (tm 680 40 40 q64 q65) (tm 760 40 40 q66 q67))) (tm 840 160 160 (tm 840 80 80 (tm 840 40 40 q68 q69) (tm 920 40 40 q70 q71)) (tm 1000 80 80 (tm 1000 40 40 q72 q73) (tm 1080 40 40 q74 q75))))) (tm 1160 560 584 (tm 1160 280 280 (tm 1160 120 160 (tm 1160 40 80 q76 (tm 1200 40 40 q77 q78)) (tm 1280 80 80 (tm 1280 40 40 q79 q80) (tm 1360 40 40 q81 q82))) (tm 1440 120 160 (tm 1440 40 80 q83 (tm 1480 40 40 q84 q85)) (tm 1560 80 80 (tm 1560 40 40 q86 q87) (tm 1640 40 40 q88 q89)))) (tm 1720 280 304 (tm 1720 120 160 (tm 1720 40 80 q90 (tm 1760 40 40 q91 q92)) (tm 1840 80 80 (tm 1840 40 40 q93 q94) (tm 1920 40 40 q95 q96))) (tm 2000 160 144 (tm 2000 80 80 (tm 2000 40 40 q97 q98) (tm 2080 40 40 q99 q100)) (tm 2160 80 64 (tm 2160 40 40 q101 q102) (tm 2240 40 24 q103 q104))))))
theorem m251Low : LowerM m251Mask m251Raw m251Goal 12 :=
  dagLow (pairs := m251Pairs) (sym := sym251) (ncuts := 46) (by decide +kernel) (by decide +kernel) (sym251OK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m251Ess m251CutValid m251All (by decide +kernel)

def m254Mask : Word := 0x5555555555555555555555555555555555555555555555555555555555555555
def m254Goal : Word := Nat.land gAll m254Mask
def m254Raw : List Word := mkR m254Mask [v1,v2,v3,v4,v5,v6,v7]
theorem m254Ess : ∀ a ∈ m254Raw, Essential m254Mask m254Goal m254Raw a :=
  checkAllEss_sound (ps := [4114,8228,32904,530,546,1092,642]) (by decide +kernel)
theorem m254Low : LowerM m254Mask m254Raw m254Goal 11 :=
  liftLow (dom := 0x55005500550055005500550055005500550055005500550055005500550055) 16433288 m246Low m254Ess (by decide +kernel) (by decide +kernel)

def m255Mask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def m255Goal : Word := Nat.land gAll m255Mask
def m255Raw : List Word := mkR m255Mask [v0,v1,v2,v3,v4,v5,v6,v7]
theorem m255Ess : ∀ a ∈ m255Raw, Essential m255Mask m255Goal m255Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,321,385]) (by decide +kernel)
def m255Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,34824,34944,40992,41088,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,24865,24928,25154,25184,25696,28720,28768,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,41249,43048,45104,45200,49600,49730,49856,50368,51272,51392,53392,53440,57440,57536,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,18183,19274,19982,20042,23114,23580,26984,27210,27240,27752,30776,30824,34567,36366,39964,47160,51786,59496]
def m255Ws : List Wire := mkWs m255Raw [(0x410c53c0110460c09c61bc9fc030c0f,0x40041140010060401420bc0d4010405),(0x4c67cbdc06009a3046c864f64c0c00f0,0x4c27c35c02001a1046c024524c040050),(0x1c8b73fc08032c40b7318707b0303300,0x1c0953fc00012c0093108507b0101100),(0xfbffbeec302c30033801f8383cc00003,0xfbffbee8102430033801f03828400002),(0x330c3cf0c0cfc183c03e003fc000c03c,0x31083ca040cfc081803c002d00004028),(0xa3f03f0300f001fc003fffc0030003c0,0xa3d02c01007001ec002f5a8001000280),(0xc3ffc003ff0001ffffc000000000fc00,0xc2f68003bf00017a6c8000000000a800),(0xfc000003fffffe000000000003ff0000,0x2ed8ac0000000000002aa0000)]
def m255Cuts : BTree CutSpec := (N (N (N (N (N (N (mc m255Raw 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 12) (mc m255Raw 0xffffffff000000000000000000000000ffffffff 8)) (N (mc m255Raw 0xffffffff00000000ffffffff 8) E)) (N (N (mc m255Raw 0x55005500550055005500550055005500550055005500550055005500550055 10) (mc m255Raw 0xffffffffffffffff 7)) (N (mc m255Raw 0x5050000050500000000000000000000050500000505 5) E))) (N (N (N (mc m255Raw 0xffffffffffffffff0000000000000000ffffffffffffffff 11) (mc m255Raw 0x50000000500000000000000000000000500000005 4)) (N (mc m255Raw 0x3030303000000000303030300000000 5) E)) (N (N (mc m255Raw 0x55555555000000005555555500000000555555550000000055555555 8) (mc m255Raw 0x5500550055005500 4)) (N (mc m255Raw 0x500000005000000000000000000000005000000050000000000000000 4) E)))) (N (N (N (N (mc m255Raw 0x3333333333333333333333333333333333333333333333333333333333333333 12) (mc m255Raw 0xffff0000ffff0000ffff0000ffff 7)) (N (mc m255Raw 0x1100000011000000000000000000000011000000110000 4) E)) (N (N (mc m255Raw 0x555500005555000055550000555500005555000055550000555500005555 8) (mc m255Raw 0x333300000000000000000000000000003333 5)) (N (mc m255Raw 0x33330000333300000000000000000000333300003333 8) E))) (N (N (N (mc m255Raw 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 11) (mc m255Raw 0x30300000000000000000000000000000303 4)) (N (mc m255Raw 0x55550000555500000000000000000000555500005555 6) E)) (N (N (mc m255Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) (mc m255Raw 0x55000000550000005500000055 4)) (N (mc m255Raw 0x5500000055000000550000005500 4) E))))) (N (N (N (N (N (mc m255Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 12) (mc m255Raw 0xffff0000000000000000000000000000ffff 6)) (N (mc m255Raw 0x30003000000000003000300000000 4) E)) (N (N (mc m255Raw 0xf0f00000f0f000000000000000000000f0f00000f0f 8) (mc m255Raw 0xf0f00000000000000000000000000000f0f 5)) (N (mc m255Raw 0xffff0000ffff00000000000000000000ffff0000ffff 9) E))) (N (N (N (mc m255Raw 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff 11) (mc m255Raw 0x11110000111100000000000000000000111100001111 5)) (N (mc m255Raw 0x50500000505000000000000000000000505000005050000000000000000 5) E)) (N (N (mc m255Raw 0x55005500550055005500550055005500 7) (mc m255Raw 0x110000001100000000000000000000001100000011 4)) (N (mc m255Raw 0x550055000000000055005500000000005500550000000000550055 7) E)))) (N (N (N (N (mc m255Raw 0xffffffffffffffffffffffffffffffff 11) (mc m255Raw 0x5555000000000000555500000000000055550000000000005555 5)) (N (mc m255Raw 0x5500000055000000550000005500000055000000550000005500000055 7) E)) (N (N (mc m255Raw 0x3030303000000000303030300000000030303030000000003030303 8) (mc m255Raw 0xf0f0f0f0 4)) (N (mc m255Raw 0x111100001111000000000000000000001111000011110000 5) E))) (N (N (N (mc m255Raw 0x5555555555555555555555555555555555555555555555555555555555555555 11) (mc m255Raw 0xcccc000000000000cccc 4)) (N (mc m255Raw 0x555555555555555500000000000000005555555555555555 8) E)) (N (N (mc m255Raw 0xffff000000000000ffff000000000000ffff000000000000ffff 8) (mc m255Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9)) (N (mc m255Raw 0x550055000000000055005500 4) E))))))
theorem m255CutValid : ∀ ci < 48, ValidCut m255Mask m255Raw m255Goal (btreeGet ⟨0,0,[]⟩ 6 m255Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16433288 m247Low (by decide +kernel)
  · exact cv 16434696 m251Low (by decide +kernel)
  · exact cv 15918608 m251Low (by decide +kernel)
  · exact cv 1754760 m127Low (by decide +kernel)
  · exact cv 14861960 m191Low (by decide +kernel)
  · exact cv 16270984 m223Low (by decide +kernel)
  · exact cv 14870096 m191Low (by decide +kernel)
  · exact cv 16434824 m254Low (by decide +kernel)
  · exact cv 16433288 m246Low (by decide +kernel)
  · exact cv 7606279 m217Low (by decide +kernel)
  · exact cv 14870096 m190Low (by decide +kernel)
  · exact cv 16270848 m217Low (by decide +kernel)
  · exact cv 16270984 m222Low (by decide +kernel)
  · exact cv 135970952 m118Low (by decide +kernel)
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 14706256 m159Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 14868560 m182Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 1075058183 m89Low (by decide +kernel)
  · exact cv 14844043 m167Low (by decide +kernel)
  · exact cv 14861960 m190Low (by decide +kernel)
  · exact cv 1316359 m89Low (by decide +kernel)
  · exact cv 14845576 m175Low (by decide +kernel)
  · exact cv 7610375 m217Low (by decide +kernel)
  · exact cv 269755911 m89Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 134762888 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 14681736 m143Low (by decide +kernel)
  · exact cv 190032 m63Low (by decide +kernel)
  · exact cv 14706256 m158Low (by decide +kernel)
  · exact cv 1855489 m81Low (by decide +kernel)
  · exact cv 1320455 m89Low (by decide +kernel)
  · exact cv 1847296 m81Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 786951 m89Low (by decide +kernel)
  · exact cv 787463 m89Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 1855490 m81Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
noncomputable def m255D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (k 0 [0,1,2,3,4,5,6,7] [8263,1048663,12391,1958007,3138647,3540071,3687543,3143015,4064631,3692151]) (k 2031737 [16,18,1,2,0,4,6,7] [4202565,4210821,1802821])) (N (k 989063 [21,4,27] [2105392]) E)) (N (N (k 87 [8,11,1,2,3,4,5,6,12] [16485,1056871,1073257,20597,1060983,1077369,1171589,1286279,1335433,1368453,1729125,1733237,1794693,1836663,1885831,1890183]) E) (N (w 1568823 [17,27,7,5,15,12,10]) E))) (N (N (N (w 221573 [18,21,4]) E) (N (k 1306696 [28,26,13] [1515657]) E)) (N (N (v 774760 20) E) (N (k 1810537 [9,16,8,2,4] [3678276]) E)))) (N (N (N (N (v 110652 22) E) (N (v 1175604 20) E)) (N (N (w 643209 [17,27,6]) E) (N (k 1696133 [18,9,5,3] [3416112,3424306,3432772]) E))) (N (N (N (v 385080 32) E) (N (v 1417881 21) E)) (N (N (k 525943 [9,8,2,5,3,12,4] [24628,1843253,1851452,1736788,1859733,1262485,1319831,1352601,1713301,1811861]) E) (N (k 1843323 [34,17,18,1,5,2,0,3,4,7] [3940437,3956885,3293476,3727701,3965333,3400244,721749,2966613,3974293]) E))))) (N (N (N (N (N (k 4201 [19,20,9,2,5,1,3,21] [139381,147589,156549]) E) (N (k 1110373 [13,27,1,2,5,19,4,30] [2236474,2244725,2269305,2285701,2302089,2311301,2320263]) E)) (N (N (k 585832 [13,11,4,6,1,2,5] [1189495]) E) (N (w 1626501 [28,20,3,2]) E))) (N (N (N (k 319812 [28,27,4] [663584,667952]) E) (N (w 1368136 [28,13,4,27]) E)) (N (N (k 843913 [17,21,13] [1459082]) E) (N (w 1896552 [18,20,6,1,5]) E)))) (N (N (N (N (v 192564 20) E) (N (k 979047 [13,27,1,26,2,5,8,10,30] [2498616,2531386,2547845,2580617,2613397,2654361,2228600,2670981,2720149,1483653,2729109,2738327]) E)) (N (N (v 693637 27) E) (N (k 1127 [9,2,0,3,5,7,4] [163893,3203189,3547269,680245,684597,1835895,3122055,3622791]) E))) (N (N (N (k 409751 [9,20,16,3,32] [925752,933968,942168,950424,426588]) E) (N (w 1503321 [28,13,20,27]) E)) (N (N (k 979032 [13,1,2,4,5,6,3,7] [1974359,2113639,1978487,2155879,2213239,2160247]) E) (N (k 1399 [11,0,3,1,2,4,6,7,5,16] [1171509,4071479,4104249,3285109,4120695,4194425,3289221,4124807,4198537,1794357,820087,824199,3622791]) E)))))) (N (N (N (N (N (N (k 8329 [17,27,7,3] [73865]) E) (N (k 1077305 [15,13,1,2,4] [2171013]) E)) (N (N (v 553349 47) E) (N (w 1601609 [38,28]) E))) (N (N (N (w 290933 [17,10,21,4]) E) (N (v 1335445 21) E)) (N (N (v 815168 12) E) (N (k 1843257 [18,3,1,8,2,5,25,6,34] [450582,3743861,1908857,3760261,987273,3777413,3528583]) E)))) (N (N (N (N (v 155785 20) E) (N (k 1111671 [13,5,2,1,25,18,3,15] [2244676,2433096,2449557,2465945,2408804,1450580,2474645,2323605,2422421]) E)) (N (N (k 684138 [13,20,12,1,2,4,5,6] [1385077,1389189,1451125,1455237,1468295]) E) (N (k 1570695 [9,17,28,2,15,3,0,5,7] [3481648,3489842,3219508,3498040,3506234,3514428,536677,3522665,3277116,3453268,758117,3408452,3011173,99173,3195753,1787237]) E))) (N (N (N (k 409655 [19,16,2,3,6,35,39,31,30] [860280,868504]) E) (N (k 979557 [18,8,1,6,2,13,5,3,4] [2957370,2965627,2973829,2982025,2990453,2376298,2835063,529029,2732679,2798217,1598325,3008391]) E)) (N (N (v 942130 34) E) (N (v 1994885 20) E))))) (N (N (N (N (N (v 90249 20) E) (N (v 1142921 20) E)) (N (N (k 585851 [17,31,25,0] [1253525,1204616]) E) (N (w 1667144 [17,27,15]) E))) (N (N (N (w 352379 [18,34,1,5]) E) (N (k 979063 [13,20,11,1,2,4,6,8,16,12,31] [2547845,2826377,2551957,2830489,2335096,2670981,2675093,2835589,2839701,2893975]) E)) (N (N (k 864645 [17,27] [1777712,1655108]) E) (N (v 1908873 21) E)))) (N (N (N (N (k 221288 [13,9,2,5,1,6] [468599]) E) (N (w 1273928 [17,27,13]) E)) (N (N (k 741525 [5,13,0,22] [1515608,1523816]) E) (N (z 1794186) E))) (N (N (N (w 483384 [28,40,2,3]) E) (N (v 1536064 13) E)) (N (N (v 1011849 20) E) (N (k 2060344 [17,6,4,16,7] [4137029,930951]) E))))))) (N (N (N (N (N (N (N (w 8313 [28,20,27]) E) (N (k 1058695 [25,13,4] [2138164,2146364,2039876]) E)) (N (N (w 536693 [28,27,5]) E) (N (w 1577605 [18,20,15]) E))) (N (N (N (w 274488 [18,3,1,10]) E) (N (k 1245337 [28,27,13,5] [2302600,2663061,1533077]) E)) (N (N (v 798768 12) E) (N (k 1847416 [18,1,3,5,6] [3711353]) E)))) (N (N (N (N (k 4217 [19,9,2,3,5] [303221,311429,344437,360837,386951]) E) (N (k 1187973 [28,13,2,4] [1402245]) E)) (N (N (w 667765 [17,27]) E) (N (v 1716256 32) E))) (N (N (N (k 5767 [8,11,3,9,2,1,5,16,6,10] [827440,41012,835637,843830,852023,876600,884793,892988,901182,909461,917655,958617,222101,287639,385945,672917,697749]) E) (N (k 979065 [13,11,1,2,5,4,6] [2924661,2928773,2934663]) E)) (N (N (v 929856 12) E) (N (w 1966485 [18,9,34,32]) E))))) (N (N (N (N (N (k 4213 [9,8,2,3,5,22,21,23,10] [24693,172153,180357,204937,223111]) E) (N (u 1122408) E)) (N (N (u 602245) E) (N (w 1642584 [17,18,15,1,3]) E))) (N (N (N (k 340101 [18,9,3,7] [623172]) E) (N (w 1380485 [28,27,3]) E)) (N (N (w 864373 [17,21,7]) E) (N (k 1908858 [30,17,2,1,4,5] [3842437]) E)))) (N (N (N (N (k 192582 [16,32,1,3] [434216]) E) (N (w 1251207 [27,21]) E)) (N (N (v 733300 20) E) (N (k 1773641 [28,26,3,5] [1876105]) E))) (N (N (N (w 458904 [16,20,3,6]) E) (N (k 1511481 [13,15,20,1,2,8,27] [3055765,2433416,2757013,3020181]) E)) (N (N (k 987257 [30,20,4] [2007173,2015877]) E) (N (w 2044053 [6,3,23]) E)))))) (N (N (N (N (N (N (k 10119 [18,20,21,4] [106544]) E) (N (w 1077385 [21,27]) E)) (N (N (w 537461 [28,27]) E) (N (w 1568887 [17,33,25,32,15]) E))) (N (N (N (w 307317 [28,26,3,7]) E) (N (k 1245589 [28,18,25,13,5] [2601113,2597529,1541269]) E)) (N (N (v 827696 12) E) (N (v 1880201 20) E)))) (N (N (N (N (k 147845 [28,3,2] [368777,377477]) E) (N (v 1224792 17) E)) (N (N (v 700496 12) E) (N (v 1736762 40) E))) (N (N (N (v 409657 27) E) (N (k 1474697 [28,27,3,5,4,13] [2401146,2859911,1647749]) E)) (N (N (v 942140 12) E) (N (w 2007173 [18,20]) E))))) (N (N (N (N (N (v 110640 16) E) (N (v 1159216 32) E)) (N (N (v 630845 31) E) (N (v 1683593 21) E))) (N (N (N (k 354183 [28,27,3,4] [761936]) E) (N (w 1417365 [13,28,4,25,16]) E)) (N (N (w 897145 [18,16,1,12]) E) (N (k 1937813 [18,21] [3858488,3891864]) E)))) (N (N (N (N (k 221305 [17,27,5] [499845]) E) (N (v 1290389 21) E)) (N (N (w 741781 [5,25,3]) E) (N (v 1810488 16) E))) (N (N (N (w 499782 [28,44]) E) (N (k 1512085 [17,21,25,27] [2204824,2475162]) E)) (N (N (k 987509 [13,5,6,1,2,31,30] [2072709,2080905,2040453,2056841]) E) (N (w 2076821 [7,20,3]) E)))))))) (N (N (N (N (N (N (N (N (k 4197 [17,18,8,9,2,5,1,3,6,15,12,10] [24693,32889,41093,65673,82293,91013,100231]) (w 2097285 [28,16,2])) (N (k 983143 [13,20,11,1,2,4,6,31] [1982581,2121849,1986693,2125961,2064757,2068869,2131847]) E)) (N (N (w 528521 [17,21,4]) E) (N (w 1577077 [18,41]) E))) (N (N (N (v 266288 32) E) (N (k 1307285 [5,0,13,25] [2646316]) E)) (N (N (v 790560 32) E) (N (k 1143 [9,2,0,3,1,5,7,6,4] [442421,3694647,3735609,3784763,3285109,3793015,3809401,3932283,3547269,3981447,4014217,4038795,704821,3391861,2949685,4055685,1885047,971655,3479431]) E)))) (N (N (N (N (k 4215 [18,24,25,3,5,23,10] [288919]) E) (N (k 1110885 [13,27,1,6,2,5,4,30] [2383946,2392197,2400393,2408821,2315141,1385589,2418567]) E)) (N (N (v 659516 21) E) (N (v 1703986 40) E))) (N (N (N (k 385177 [38,28,3] [811076,353100]) E) (N (v 1445940 20) E)) (N (N (v 917564 12) E) (N (v 1970312 13) E))))) (N (N (N (N (N (w 65669 [17,10,21,4]) E) (N (k 1114229 [20,27,2,13] [2252856,2261096]) E)) (N (N (k 585834 [17,8,4,6] [1204601,1208713,1222535]) E) (N (w 1642554 [17,27,16,15]) E))) (N (N (N (k 305031 [9,13,2,14,22,3,21,27,23,10] [631908]) E) (N (k 1380469 [17,27,16] [2777225]) E)) (N (N (v 856164 20) E) (N (k 1904709 [17,18,30,8,3,1,2,5] [3825784,3833978,1011845,3850375,3866761]) E)))) (N (N (N (N (v 192568 16) E) (N (v 1249397 20) E)) (N (N (v 725129 21) E) (N (k 1773610 [28,26,3] [3563832]) E))) (N (N (N (v 458832 10) E) (N (v 1511472 15) E)) (N (N (k 987253 [20,27,2,15] [1990760]) E) (N (k 2035832 [17,13,16,4,6] [3663751]) E)))))) (N (N (N (N (N (N (w 8565 [17,25,7]) E) (N (k 1077381 [20,21,13] [2187337]) E)) (N (N (k 544903 [18,31] [1114520]) E) (N (w 1609832 [17,25]) E))) (N (N (N (k 4469 [9,18,8,21,2,3,5,23,10] [614708,639365,643973,673671]) E) (N (v 1335596 20) E)) (N (N (k 799044 [17,27,13] [1663008,1671472,1426026]) E) (N (w 1871960 [17,27]) E)))) (N (N (N (N (k 147829 [28,5,2] [352393,336517]) E) (N (v 1216645 21) E)) (N (N (v 692288 12) E) (N (v 1736754 40) E))) (N (N (N (v 426136 13) E) (N (w 1474683 [18,34,1,30,5]) E)) (N (N (v 954501 21) E) (N (k 1843337 [9,18,3,0,2,5,7,4,34] [3559446,4022341,987209,4030597,3502217,729669,2982725,1942663]) E))))) (N (N (N (N (N (v 102533 20) E) (N (w 1115269 [27,28,4]) E)) (N (N (k 587655 [9,8,2,3,5,4,16,12,13,20] [237620,1269820,1278013,1188760,1221530]) E) (N (k 1568905 [15,17,8,9,2,1,3,0] [3366981,3383429,1762117,808071]) E))) (N (N (N (k 352645 [18,21,4] [745520,655684]) E) (N (k 1410181 [13,6,1,2,12,4,0,5,16,31] [2842714,2850965,2859161,2867500,2876053,2884249,2716565]) E)) (N (N (k 866183 [28,20,27] [1684068]) E) (N (k 1937544 [20,30,4] [3891589]) E)))) (N (N (N (N (k 221290 [18,1,3,0,5] [483705]) E) (N (k 1273960 [17,27,13] [2261624]) E)) (N (N (v 753768 20) E) (N (k 1771399 [9,2,0,5,3,7,16,4] [3219508,3629110,3637304,1261669,3645543,3670121,1810789,222053,697445,701797]) E))) (N (N (N (k 483481 [28,26,3,5,40] [1007684,1015878,1024072,1032292,1040486,369228]) E) (N (k 1536073 [17,13,21] [2458008]) E)) (N (N (k 987273 [30,27,21] [2056837]) E) (N (v 2068600 13) E))))))) (N (N (N (N (N (N (N (w 20568 [17,27]) E) (N (v 1065020 21) E)) (N (N (v 544888 13) E) (N (w 1578887 [28,42,27,4]) E))) (N (N (N (w 274569 [18,30,1,5,6]) E) (N (k 1245573 [13,5,9,2,1,0,6,16,12,10,31,30] [2678840,2687125,2695321,2703660,2540106,2638485,2663065,2712981]) E)) (N (N (v 798778 34) E) (N (w 1847433 [18,20,5]) E)))) (N (N (N (N (k 147589 [18,1,3,0,5] [319608,327817,336517]) E) (N (k 1188213 [18,13,1,5] [1425748]) E)) (N (N (v 675892 20) E) (N (v 1724448 32) E))) (N (N (N (v 409653 27) E) (N (k 1460103 [13,9,2,5,4] [2940980]) E)) (N (N (k 525959 [17,18,8,15,1,3,2,4,12,5,6] [1892400,1900594,41012,1908792,1925178,1933372,1753172,1859733,1941657,90420,1769812,1598020,1950357,103317,1160089,1791381]) E) (N (k 1843335 [18,9,3,5,4] [3989560,4006041,3559720,3965337]) E))))) (N (N (N (N (N (k 82053 [28,2,3,0,5] [188536,196745]) E) (N (v 1134725 21) E)) (N (N (v 610380 31) E) (N (w 1642633 [28,26,3]) E))) (N (N (N (k 4741 [18,3,8,1,2,25,5,10] [712762,721019,688261,729225,737669,90741,156281,643973,755591]) E) (N (k 1382279 [28,27,3,5] [2809912]) E)) (N (N (w 864389 [17,27,7]) E) (N (k 1908871 [18,30] [3858488,3842456]) E)))) (N (N (N (N (k 4229 [18,1,8,3,2,5,25,13,10] [450602,458856,475242,41077,491641,508027,180357,516233,524677,534407]) E) (N (w 1266309 [5,13,46,10,27]) E)) (N (N (v 741448 34) E) (N (k 1790037 [17,25] [3596424,3604618]) E))) (N (N (N (k 6023 [28,26,3,5,6] [974896,180276,983096,991292,688212,999577,360764,639300,524852,737876,99221]) E) (N (v 1511484 13) E)) (N (N (u 1000069) E) (N (w 2052213 [18,16,1]) E)))))) (N (N (N (N (N (N (k 4199 [18,5,1,10,3,6,15,12] [123033]) E) (N (k 984439 [9,13,2,7,3,5,4] [2023477,2179205,2130823]) E)) (N (N (v 577592 40) E) (N (w 1626181 [18,21,5]) E))) (N (N (N (k 303493 [28,26,3] [647216,622660,655684]) E) (N (k 1247383 [28,13,4,27] [2744368,2752584,1581412,2524008,2319528]) E)) (N (N (k 684917 [17,6,13,27] [1695776,1704073,1655092,1450618,1585799,1684357]) E) (N (k 1843259 [18,34,1,3,7,6] [450852,713268,2957892]) E)))) (N (N (N (N (v 180869 20) E) (N (w 1213077 [25,28,27]) E)) (N (N (k 692564 [17,13,27] [1433920]) E) (N (k 1736809 [18,21,3,5] [3530816]) E))) (N (N (N (v 409662 20) E) (N (v 1495088 15) E)) (N (N (w 942741 [28,27,4,5,6]) E) (N (w 2019908 [28,27,4]) E))))) (N (N (N (N (N (v 110646 20) E) (N (w 1167481 [31,27,1]) E)) (N (N (k 643192 [17,12,4,5,6] [1304455]) E) (N (k 1569157 [18,17,3,5,1,2,25,0,15] [3399738,2990405,3408261,90693,3179081,1770309,3449733]) E))) (N (N (N (k 5751 [28,26,5,3] [778288,24628,786488,794684,802969,82228,344636,533397,755093]) E) (N (v 1417516 27) E)) (N (N (v 905268 20) E) (N (k 1904775 [17,25,7] [1020005,3924073,3899749,1045093]) E)))) (N (N (N (N (k 221307 [18,30,1,0,5] [483720]) E) (N (w 1291669 [20,25,5,7]) E)) (N (N (v 774224 12) E) (N (v 1822808 31) E))) (N (N (N (v 499812 27) E) (N (v 1560636 13) E)) (N (N (v 1032329 21) E) (N (k 2060441 [17,39,4,3,7] [4186213]) E))))))))) (N (N (N (N (N (N (N (N (N (k 71 [8,9,2,3,5,1,6,10] [16485,114791,131177,163957,278647,295033,442501,548999,581769,606581,680565,705157,771703,820871,968583]) (w 2097221 [18,16,1])) (N (v 1048624 32) E)) (N (N (k 524391 [17,12,25,5,15,10] [1065097]) E) (N (k 1568825 [15,18,1,8,2,3,4] [3162229,3170437,3179141,3187573,3196807]) E))) (N (N (N (k 223111 [28,27,3,5,4] [540720,467864]) E) (N (v 1306777 20) E)) (N (N (k 742805 [28,13,4] [1589280]) E) (N (v 1835076 21) E)))) (N (N (N (N (v 110654 20) E) (N (v 1175612 21) E)) (N (N (k 645271 [29,20,16,4,5,25,13] [1327164,1303464]) E) (N (v 1703984 15) E))) (N (N (N (v 385084 10) E) (N (k 1411223 [13,8,25,16,4,12] [2900020,2908220,2637892,2850932,2352296]) E)) (N (N (v 917557 20) E) (N (k 1966165 [18,34,1,3,5,30] [3948680]) E))))) (N (N (N (N (N (w 65653 [28,20,22]) E) (N (w 1114170 [30,2,10,13,27]) E)) (N (N (w 591479 [9,13,2,5,4]) E) (N (k 1568901 [18,17,2,1,15,0,3,4,5,7,16] [3293242,41029,3301449,3309656,3317850,3219589,3326089,1753925]) E))) (N (N (N (v 327712 23) E) (N (k 979049 [13,9,2,5,1,6] [2769013,2785413,2794373,2803591]) E)) (N (N (k 685959 [9,3,8,5,2,12,13,4,20] [1507381,1630276,1720420,1467290]) E) (N (k 1843321 [17,6,8,9,2,3,1,0,5] [3293206,3817541,3874887,1908809,3907717,3915911,3502217,1004679]) E)))) (N (N (N (N (v 192566 20) E) (N (k 1245240 [13,27,39,1,2,34] [2506869,2515845,2525063]) E)) (N (N (k 689269 [17,13,6] [1458313,1425732,1447045]) E) (N (k 1769605 [9,18,3,2,0,5,7,4] [3555370,3559482,180293,3571785,3219589,3580041,3612811,2974021,688709,693061,1860743]) E))) (N (N (N (k 458808 [25,16] [434764]) E) (N (k 980599 [17,18,8,6,2,1,16,3,15,13,4,5] [3031088,41012,2547765,3039288,3047481,3063868,3072149,3104921,2990420,1688132,3113621,2155400,2425738,537493,2741143,2806681,3011989]) E)) (N (N (k 983127 [13,27,1,26,2,5,30] [1982581,1998969,2023557,2048137,2064757,2089349,2099079]) E) (N (k 2031671 [17,8,16,4,6,3,12,13] [4079736,4087945,4092057,3647639]) E)))))) (N (N (N (N (N (N (v 32905 21) E) (N (v 1081477 21) E)) (N (N (v 544901 21) E) (N (k 1601669 [17,21,1,2] [3227752,3231864]) E))) (N (N (N (w 290949 [28,37,3]) E) (N (v 1335449 21) E)) (N (N (k 798857 [28,13,27,4] [1418122]) E) (N (k 1867893 [18,20,2] [3752024]) E)))) (N (N (N (N (w 156293 [27,21,5]) E) (N (k 1212488 [15,17,27,1,2] [2441349]) E)) (N (N (k 688757 [13,6,2,1,5,12,30,4,20,27] [1392704,1400965,1417353,1425748,1443205]) E) (N (v 1736752 15) E))) (N (N (N (w 426104 [39,3,10]) E) (N (k 1474618 [18,1,13,34,5] [2384746,2843511]) E)) (N (N (k 942136 [17,27,6,7] [1917061]) E) (N (w 1990809 [18,20,5]) E))))) (N (N (N (N (N (k 82057 [36,2,3,5] [213125]) E) (N (w 1114249 [21,27]) E)) (N (N (k 622741 [25,28] [1213080]) E) (N (w 1667176 [17,27,5]) E))) (N (N (N (w 352393 [28,26,3,7]) E) (N (k 1409161 [18,31,1,6] [2343560]) E)) (N (N (v 884784 12) E) (N (k 1904711 [17,30,27] [3883144,1020053,3899797]) E)))) (N (N (N (N (w 231031 [21,18,3]) E) (N (w 1273944 [17,27,13]) E)) (N (N (v 753752 20) E) (N (w 1773707 [28,26,5,3,4]) E))) (N (N (N (v 483388 10) E) (N (v 1536072 33) E)) (N (N (v 1012357 5) E) (N (k 2064453 [17,30] [4145272]) E))))))) (N (N (N (N (N (N (N (k 8325 [17,27,0,2] [49240,57464]) E) (N (v 1065012 20) E)) (N (N (k 536709 [29,27,1,3,2,31] [1097848,1106042,1122437,1130631,1138825]) E) (N (w 1577845 [38,28,27]) E))) (N (N (N (w 274552 [18,13,1,10]) E) (N (w 1327765 [25,28,32,13]) E)) (N (N (v 798770 34) E) (N (w 1851769 [30,27,1]) E)))) (N (N (N (N (w 147573 [18,20]) E) (N (k 1187977 [30,4,1,2] [1418629]) E)) (N (N (k 669575 [29,9,2,3,4] [1359924]) E) (N (k 1696645 [17,27,4] [3457056,3432756]) E))) (N (N (N (v 409648 16) E) (N (w 1458293 [18,20,10,1]) E)) (N (N (v 929864 20) E) (N (w 1967253 [18,34,9,5,32]) E))))) (N (N (N (N (N (w 82041 [36,20]) E) (N (k 1114233 [30,20,4] [2277509]) E)) (N (N (k 599943 [25,0,4,20] [1228876]) E) (N (w 1642586 [18,20,2]) E))) (N (N (N (k 341895 [26,8,1,3,10,5,27] [631908]) E) (N (w 1381253 [28,27,4]) E)) (N (N (k 864377 [28,20,27,5] [1705093]) E) (N (w 1917317 [5,47]) E)))) (N (N (N (N (u 213032) E) (N (k 1245242 [18,30,13,1,0,5,10] [2237048,2540165]) E)) (N (N (k 684151 [13,5,1,2,6,0,4,10,30,12,20] [1491016,1499224,1507477,1532057,1540501,1549205,1582485]) E) (N (k 1773705 [17,25,7] [3588181]) E))) (N (N (N (v 409753 21) E) (N (v 1523861 21) E)) (N (N (v 999557 21) E) (N (k 2031673 [16,8,1,2,4,6] [4112501,4116613,3671943]) E)))))) (N (N (N (N (N (N (v 49200 40) E) (N (w 1077893 [20,25,7]) E)) (N (N (k 538503 [28,27,3,5,4] [1163320]) E) (N (k 1568889 [15,9,18,0,2,3,7] [3260485,3268741,3277189,1745733,3105927]) E))) (N (N (N (w 308855 [9,13,2,14,22,3,21,27]) E) (N (k 1246357 [18,28,13,4,5] [2515544,2605721,2311048,2712469,1549717]) E)) (N (N (k 799877 [17,27,13] [1442954]) E) (N (w 1868677 [28,27,4]) E)))) (N (N (N (N (w 180361 [21,3,2]) E) (N (k 1212569 [28,27] [1459044]) E)) (N (N (v 692361 4) E) (N (v 1736764 15) E))) (N (N (N (v 409660 10) E) (N (k 1474933 [18,1,5,3,13] [2998320,1655108,2409338]) E)) (N (N (k 942233 [18,21,3,5,4] [1647444]) E) (N (k 1843339 [18,9,34,4] [3559716,4047428]) E))))) (N (N (N (N (N (v 110644 20) E) (N (k 1110389 [13,20,1,2,31,4,6,29,16] [2244725,2343033,2248837,2347145,2353031]) E)) (N (N (k 524423 [17,29,4,6,16,5,13] [1294456,1310857,1314969,1321111]) E) (N (w 1679493 [17,33,3]) E))) (N (N (N (v 376912 32) E) (N (w 1417369 [13,46,4,16,27]) E)) (N (N (k 898951 [9,8,3,2,16,12,20,4] [1818676,1826876]) E) (N (w 1904773 [28,26,3]) E)))) (N (N (N (N (v 245893 21) E) (N (w 1290901 [6,18,32,13]) E)) (N (N (k 742293 [28,5,4,13] [1556560,1565272,1573480]) E) (N (k 1810535 [25,8,16,20,3,4,12,13] [3653720,3661992]) E))) (N (N (N (v 499784 40) E) (N (k 980615 [9,8,2,3,5,13,4] [180276,2613301,3129404,2973780,3072149,2212744,2483082,1262485,2892695,2933657,1713301]) E)) (N (N (v 1032325 21) E) (N (k 2060392 [17,6,16,4,3,7] [955783]) E)))))))) (N (N (N (N (N (N (N (N (w 8309 [17,21]) E) (N (w 1056889 [31,27,1]) E)) (N (N (k 524393 [29,9,2,3,1,6] [1081461,1089669,1147765,1156999]) E) (N (w 1577093 [18,20,15,1]) E))) (N (N (N (k 4231 [18,3,1,19,5,6,13] [557112,565368,573577]) E) (N (v 1319212 20) E)) (N (N (k 684405 [17,18,13,12,1,2,6,0,4,5] [1605680,1613874,1622074,1630341,1646729,1655108,1385082,1553031,1680517]) E) (N (k 1843255 [18,1,3,8,5,6,10,13] [3702904,3719305,450856,3727753]) E)))) (N (N (N (N (w 141463 [25,22,27,3,23,10]) E) (N (w 1187914 [30,27,7]) E)) (N (N (k 524425 [29,20,1,2,3,4,6] [1343605,1347717,1353607]) E) (N (k 1704260 [17,21,4,27] [3440672,3445040]) E))) (N (N (N (v 401476 20) E) (N (v 1445948 21) E)) (N (N (k 917653 [28,26,3,5,4,12,20] [1867840,1876040,1630548]) E) (N (w 1966229 [18,34,21]) E))))) (N (N (N (N (N (w 66437 [17,27,10,16,21]) E) (N (u 1122360) E)) (N (N (k 598393 [31,20,4] [1212549]) E) (N (w 1642569 [18,20,3,1,5]) E))) (N (N (N (k 4725 [26,8,1,10,27,3,5] [688261,614708,698247]) E) (N (v 1384585 21) E)) (N (N (k 524901 [17,8,6,27,2,1,12,15] [1736821,1745017,1753221,1761417,1769861,86645,1151609,1688453,1787783]) E) (N (v 1908856 13) E)))) (N (N (N (N (v 192580 21) E) (N (w 1250181 [18,21,34,13]) E)) (N (N (k 690055 [13,4,5] [1400916,1474676]) E) (N (w 1777976 [28,39,4]) E))) (N (N (N (v 458840 43) E) (N (v 1511480 15) E)) (N (N (v 991336 27) E) (N (k 2035849 [17,31,6,3,4] [4096149]) E)))))) (N (N (N (N (N (N (w 9093 [18,20,3]) E) (N (u 1089609) E)) (N (N (v 544905 21) E) (N (w 1601673 [38,17]) E))) (N (N (N (k 303412 [9,18,21,8,2,3,5] [622709,632439]) E) (N (w 1336725 [25,28,5,13,27]) E)) (N (N (v 827424 15) E) (N (k 1867909 [18,9,3,5] [3768457]) E)))) (N (N (N (N (w 172169 [38,21]) E) (N (k 1212565 [17,13] [2457688]) E)) (N (N (j 692357 4 [1409104]) E) (N (w 1736760 [17,27,3]) E))) (N (N (N (v 409656 16) E) (N (k 1474693 [28,26,5,3,4,7,13] [2392954,2851719,1631365]) E)) (N (N (v 942138 34) E) (N (w 2007109 [18,21,3]) E))))) (N (N (N (N (N (k 83847 [9,8,2,3,5,16,22,21,23,10] [229424,237620,245814,254008,262204,270398]) E) (N (k 1116039 [28,4,27] [2326576]) E)) (N (N (v 630844 21) E) (N (k 1679429 [17,27,15] [3375241]) E))) (N (N (N (v 368688 10) E) (N (w 1417306 [30,18,7]) E)) (N (N (k 524933 [17,8,3,1,2,16,12,4,6] [1753205,1802361,1757317,1806473,1812359]) E) (N (u 1941893) E)))) (N (N (N (N (w 237945 [30,27,1]) E) (N (k 1245321 [17,30,5,4] [2588821,2269832,2597525,2606485]) E)) (N (N (w 741529 [21,13]) E) (N (v 1810486 20) E))) (N (N (N (v 499780 27) E) (N (k 1511577 [28,27,5,3] [1704788,2196632,2466970]) E)) (N (N (u 1024645) E) (N (k 2060377 [17,39,7,3,4] [4161685]) E))))))) (N (N (N (N (N (N (N (v 20600 13) E) (N (k 984423 [17,27,5,13,1,2,3,25,7,15] [1982517,2162745,2179205,2195593,2204293,2102151]) E)) (N (N (k 544890 [31,18,1,2,3] [1114501]) E) (N (k 1568885 [9,17,8,2,0,3,5,32,15,33] [24645,3211337,3219589,3235977,1737541,3073159]) E))) (N (N (N (k 4233 [19,2,1,3,4,5,21] [589941,598149]) E) (N (v 1335352 27) E)) (N (N (k 798853 [28,13,2,4,12] [1638464,1401738]) E) (N (k 1847689 [18,30,1,0,12] [3711624]) E)))) (N (N (N (N (v 155768 13) E) (N (k 1189767 [25,27,7] [1442164]) E)) (N (N (k 524677 [17,13,12,3,1,2,4,5,0,6] [1376362,1482871,1486983,1597813,1601925,1688437,1692549,1714055]) E) (N (k 1569397 [9,17,18,2,32,15] [86085,3190857,3453317,82501,3187273,3449733,3114119]) E))) (N (N (N (v 409654 20) E) (N (v 1466420 21) E)) (N (N (v 942128 12) E) (N (k 1990712 [18,9,3] [3997829,3563816]) E))))) (N (N (N (N (N (v 90232 13) E) (N (k 1114245 [21,45,2,5] [2293897]) E)) (N (N (w 585849 [18,20,6,1]) E) (N (k 1568903 [18,20,3,2,5,16,15] [3342408,3350632]) E))) (N (N (N (w 352314 [18,3,1,7]) E) (N (v 1400888 32) E)) (N (N (w 864393 [17,27,15]) E) (N (v 1925176 21) E)))) (N (N (N (N (w 221226 [18,3,1,10,13]) E) (N (k 1245317 [17,27,13,0,2,15] [2555976,2564184,2572392,2245256]) E)) (N (N (v 741464 20) E) (N (v 1794184 13) E))) (N (N (N (v 483376 10) E) (N (k 1511573 [17,21,13] [3080256,3088456,3096649,2180248,2450586]) E)) (N (N (k 987269 [28,26,13,5] [2031753,2040453]) E) (N (k 2031735 [17,6,16,4,7,2,3,15] [4128824,4153433,4169832,4178073,923031]) E)))))) (N (N (N (N (N (N (w 57497 [18,35,3,1,6]) E) (N (k 979034 [13,1,2,4,5,6,8] [2228581,2335093,2232709,1376885,2376549,2380677,2426487,2483847,2430855]) E)) (N (N (k 524421 [17,8,1,2,4,6,12,3,13,16] [1179752,1196138,41077,1237113,1245307,45189,1241225,1249419,1263495]) E) (N (w 1626245 [18,20,9,3]) E))) (N (N (N (v 319536 10) E) (N (v 1368112 32) E)) (N (N (v 843808 15) E) (N (k 1843319 [18,20,15,1,5,2,3,16] [3801192,3293480]) E)))) (N (N (N (N (k 149383 [19,9,3,2,5,16] [393268,401462,409656,417860,426054]) E) (N (k 1111687 [9,13,2,5,8,4] [2285636,2392164,2449557,2352277,1467797]) E)) (N (N (v 713024 12) E) (N (v 1761344 15) E))) (N (N (N (v 409749 21) E) (N (k 1476487 [28,27,20,6,13] [3014745,1679716,2418074]) E)) (N (N (k 119 [8,1,2,3,4,5,6,13] [1966168,2220122,442469,2490471,2760809,1171573,2818167,2916473,446597,2494599,2764937,1368437,2949733,2953861,3024503,3122823,3028871]) E) (N (k 1843845 [9,18,2,0,5,21,3,4] [4051002,528453,3780681,3977355,4047149,741701,3412357,524869,3777097,3973771,738117,3408773,1950855]) E))))) (N (N (N (N (N (v 110648 16) E) (N (k 1169287 [25,4,14] [2359348,2367548]) E)) (N (N (w 649095 [12,20,4,5]) E) (N (w 1695802 [18,34,5]) E))) (N (N (N (v 385072 32) E) (N (v 1417877 21) E)) (N (N (v 905276 16) E) (N (j 1957993 27 [3858724]) E)))) (N (N (N (N (w 221321 [28,27,3]) E) (N (k 1245333 [28,13,26,5,0,22] [2621512,2629785,2286216,2638485,1508501]) E)) (N (N (v 774744 34) E) (N (w 1822888 [25,3,4,16,20]) E))) (N (N (N (w 499814 [44,6]) E) (N (k 1111 [9,2,14,1,8,3,0,5,6,15] [16437,3145783,3153977,3203189,3244151,3252345,3285125,3334279,3358857,3391877,1729077,3465845,775031,3023751,3475335]) E)) (N (N (k 987525 [28,26,27] [2019465,2015881]) E) (N (w 2089061 [4,3,10]) E))))))))))
noncomputable def x255 : Nat → Bool := checkNode m255Mask m255Goal (Nat.sub (Nat.shiftLeft 1 m255Pairs.length) 1) symMain 515 13 m255Ws m255D 10 m255Cuts 6
noncomputable def y255 : Nat → Nat → Bool := checkRange m255Mask m255Goal (Nat.sub (Nat.shiftLeft 1 m255Pairs.length) 1) symMain 515 13 m255Ws m255D 10 m255Cuts 6
theorem s255 (s n : Nat) (h : y255 s n = true) : ac x255 s n := cr_sound h
theorem q105 : ac x255 0 40 := s255 0 40 (by decide +kernel)
theorem q106 : ac x255 40 40 := s255 40 40 (by decide +kernel)
theorem q107 : ac x255 80 40 := s255 80 40 (by decide +kernel)
theorem q108 : ac x255 120 40 := s255 120 40 (by decide +kernel)
theorem q109 : ac x255 160 40 := s255 160 40 (by decide +kernel)
theorem q110 : ac x255 200 40 := s255 200 40 (by decide +kernel)
theorem q111 : ac x255 240 40 := s255 240 40 (by decide +kernel)
theorem q112 : ac x255 280 40 := s255 280 40 (by decide +kernel)
theorem q113 : ac x255 320 40 := s255 320 40 (by decide +kernel)
theorem q114 : ac x255 360 40 := s255 360 40 (by decide +kernel)
theorem q115 : ac x255 400 40 := s255 400 40 (by decide +kernel)
theorem q116 : ac x255 440 40 := s255 440 40 (by decide +kernel)
theorem q117 : ac x255 480 35 := s255 480 35 (by decide +kernel)
theorem m255All : ac x255 0 515 := (tm 0 240 275 (tm 0 120 120 (tm 0 40 80 q105 (tm 40 40 40 q106 q107)) (tm 120 40 80 q108 (tm 160 40 40 q109 q110))) (tm 240 120 155 (tm 240 40 80 q111 (tm 280 40 40 q112 q113)) (tm 360 80 75 (tm 360 40 40 q114 q115) (tm 440 40 35 q116 q117))))
theorem m255Low : LowerM m255Mask m255Raw m255Goal 14 :=
  dagLow (pairs := m255Pairs) (sym := symMain) (ncuts := 48) (by decide +kernel) (by decide +kernel) (symMainOK (by decide +kernel) (by decide +kernel) (by decide +kernel)) m255Ess m255CutValid m255All (by decide +kernel)

def flatEdges : List ℕ := [0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7]

def targetFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < flatEdges.length / 2,
    (List.ofFn x).getD (flatEdges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (flatEdges.getD (2 * i + 1) 0) false = true)

def witness15 : Circuit :=
  ⟨[⟨.or, [7, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 9]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [16, 9]⟩,
    ⟨.or, [1, 17]⟩, ⟨.and, [8, 18]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [13, 21]⟩], 22⟩

theorem witness15Legal : ∀ g ∈ witness15.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness15Correct : ∀ x : Fin 8 → Bool, witness15.eval (List.ofFn x) = targetFn x :=
  forall_fin8_of_fin256 (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem sample8OK : ∀ r : Row, m255Raw.map (bit r) = List.ofFn (fun i : Fin 8 => r.val.testBit i.val) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem goal8OK : ∀ r : Row, bit r m255Goal = targetFn (fun i : Fin 8 => r.val.testBit i.val) := by decide +kernel

theorem mainLower (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFn x) :
    14 ≤ gates.countP (fun g => !isNot g) :=
  physical_lower (vars8 := m255Raw) (goal8 := m255Goal)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa [show m255Mask = fullMask by decide +kernel] using m255Low)
    sample8OK goal8OK gates o legal computes

end PEqualNP.Outside.L_meta_35260

theorem PEqualNP.Outside.L_meta_35260 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  by_cases hnot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hg, hgop⟩ := hnot
    have hlow := PEqualNP.Outside.L_meta_35260.mainLower gates o legal computes
    have hlt : gates.countP (fun w => !PEqualNP.Outside.L_meta_35260.isNot w) < gates.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [PEqualNP.Outside.L_meta_35260.isNot, hgop]⟩
    have hlen : PEqualNP.Outside.L_meta_35260.witness15.gates.length = 15 := rfl
    exact ⟨PEqualNP.Outside.L_meta_35260.witness15.gates, PEqualNP.Outside.L_meta_35260.witness15.output,
      PEqualNP.Outside.L_meta_35260.witness15Legal, by omega, PEqualNP.Outside.L_meta_35260.witness15Correct⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (legal g hg).2⟩, Nat.le_refl _, computes⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)
