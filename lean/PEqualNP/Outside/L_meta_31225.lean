import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_31225_aux.Seven
namespace Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := Nat × Nat
def top : Nat := 0xffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def Valid1 (x : Nat) : Prop := ∀ j, 64 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 32 * 2 ^ 32 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 64) := by
  rw [top_eq_pow]; exact pow_add_testBit 32 32 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 64 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 64
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 64 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 64 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 32 * 2 ^ 32 := by
    have hp : 0 < 2 ^ 32 * 2 ^ 32 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 64 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 64 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
def bit (side : Bool) (i : Fin 64) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
end Basis1868

namespace Conflict1868
open Basis1868

abbrev I := Fin 64
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def D (p n : I) (a : Sig) : Prop := P a p ≠ N a n
def op (d x y : Bool) : Bool := if d then x || y else x && y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  by_contra! hn
  apply hd
  unfold P N
  rw [bop,bop]
  exact congrArg₂ (op d) (not_ne_iff.mp hn.1) (not_ne_iff.mp hn.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_neg {p n a} (hv : Valid a) : D p n (neg a) ↔ D p n a := by
  unfold D P N
  rw [bit_neg _ _ hv,bit_neg _ _ hv]
  cases bit true p a <;> cases bit false n a <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pair_sep {k t S} (hl : Live k t S) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,P,N,bit,target,testBit_top,p.isLt]
  | unary ha _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨_, Finset.mem_insert_self _ _, (d_neg ha.1).mp h⟩
    · exact ⟨_, Finset.mem_insert_of_mem hc, h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_unique_keep {p n a c U} (h : Unique p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Unique p n (insert (neg a) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · exact (hna (h _ (Finset.mem_insert_self _ _) ((d_neg hv).mp hd)).symm).elim
  · exact h _ (Finset.mem_insert_of_mem hu) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_keep {p n a c U} (h : Mark p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Mark p n (insert (neg a) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,neg_unique_keep hm hna hv⟩,q,neg_unique_keep hq hna hv⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_move {p n a U} (h : Mark p n (insert a U) a)
    (ha : a ∉ U) (hv : Valid a) : Mark p n (insert (neg a) U) (neg a) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a U := Finset.subset_insert _ _
  exact ⟨(d_neg hv).mpr hd,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mix : ∀ (d ap an bp bn al ar : Bool), ap ≠ an →
    op d ap bp ≠ op d al bp → op d ar bn ≠ op d an bn →
    bp = bn ∧ op d ap bp ≠ op d an bn := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U))
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : P b p = N b m := not_ne_iff.mp (fun h => hab (hm _ hb h).symm)
  have bq : P b q = N b n := not_ne_iff.mp (fun h => hab (hq _ hb h).symm)
  have zm := unique_diff tail (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  change bit true p (bin d a b) ≠ bit false m (bin d a b) at zm
  change bit true q (bin d a b) ≠ bit false n (bin d a b) at zq
  rw [bop,bop] at zm zq
  change op d (P a p) (P b p) ≠ op d (N a m) (N b m) at zm
  change op d (P a q) (P b q) ≠ op d (N a n) (N b n) at zq
  rw [← bm] at zm
  rw [bq] at zq
  have hh := mix _ _ _ _ _ _ _ hd zm zq
  refine ⟨fun h => h hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2

def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unary_col {k U a} (hv : Valid a) (fresh : neg a ∉ insert a U)
    (col : Colored (insert (neg a) U) k) :
    ∃ l, Colored (insert a U) l ∧ l + (insert a U).card ≤ k + (insert (neg a) U).card := by
  let R := ({a} : Finset Sig) ∩ U
  let f (x : Sig) := if x = a then neg a else x
  have mem (x) (hx : x ∈ insert a U) (_ : x ∉ R) : f x ∈ insert (neg a) U := by
    by_cases e : x = a
    · simp [f,e]
    · simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left e)
  have keep (x p n) (hxr : x ∉ R) (mx : Mark p n (insert a U) x) :
      Mark p n (insert (neg a) U) (f x) := by
    by_cases e : x = a
    · subst x
      have ha : a ∉ U := by simpa [R] using hxr
      simpa [f] using neg_mark_move mx ha hv
    · simpa [f,e] using neg_mark_keep mx e hv
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy hxr hyr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n hxr mx,keep y p n hyr my⟩
    by_cases ex : x = a <;> by_cases ey : y = a
    · exact (hxy (ex.trans ey.symm)).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : neg a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> simp [R,ha,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
theorem live_colored {k t S} (l : Live k t S) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary ha hf _ ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := unary_col ha.1 hf hk
    exact ⟨u,hu,by omega⟩
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail hk
    exact ⟨u,hu,by omega⟩

end Conflict1868

namespace Grid1868
open Basis1868

abbrev Ix := Fin 256
def coord (side : Bool) (i : Nat) := if side then i / 16 * 16 else i % 16
def hop (n mask x : Nat) : Nat := (x ||| ((x <<< n) &&& (mask <<< n))) ||| ((x >>> n) &&& mask)
def safe (s : Bool) (n mask : Nat) : Prop :=
  ∀ i : Ix, (((mask <<< n).testBit i.val = true → n ≤ i.val ∧ coord s (i.val-n) = coord s i.val) ∧
    (mask.testBit i.val = true → i.val+n < 256 ∧ coord s (i.val+n) = coord s i.val))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
instance (s n m) : Decidable (safe s n m) := by unfold safe; infer_instance

def m4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def m5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def m6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m7 : Nat := 0xffffffffffffffffffffffffffffffff
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 16 m4 x))))
end Grid1868

namespace Check1868
open Basis1868
open Grid1868 Conflict1868

abbrev Signs := List (Sig × Nat)

end Check1868

namespace ColorSearch1868
open Basis1868
open Conflict1868 Check1868

def paint (n : Nat) : Signs → (Nat → Nat) → Bool
  | [], _ => true
  | x::xs, bins =>
    (List.range n).any fun i => ((bins i &&& x.2) == 0) &&
      paint n xs (fun j => if i=j then bins j ||| x.2 else bins j)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma paint_ok {n xs} (bins : Nat → Nat) (f : Sig → Nat) (nd : (xs.map Prod.fst).Nodup)
    (bd : ∀ x ∈ xs, f x.1 < n) (ok : ∀ x ∈ xs, bins (f x.1) &&& x.2 = 0)
    (sep : ∀ x ∈ xs, ∀ y ∈ xs, x.1 ≠ y.1 → f x.1 = f y.1 → x.2 &&& y.2 = 0) :
    paint n xs bins = true := by
  induction xs generalizing bins with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hn,hnd⟩ := List.nodup_cons.mp nd
    apply List.any_eq_true.mpr
    refine ⟨f x.1,List.mem_range.mpr (bd _ (by simp)),Bool.and_eq_true_iff.mpr ⟨by
      simp only [beq_iff_eq]; exact ok _ (by simp),?_⟩⟩
    apply ih _ hnd (fun a ha => bd a (List.mem_cons_of_mem _ ha)) _ (fun a ha b hb =>
      sep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    intro y hy
    have hy' := List.mem_cons_of_mem x hy
    by_cases e : f x.1 = f y.1
    · have ne : x.1 ≠ y.1 := fun eq => hn (List.mem_map.mpr ⟨y,hy,eq.symm⟩)
      simp [e,Nat.and_or_distrib_right,ok y hy',sep x (List.mem_cons_self ..) y hy' ne e]
    · simpa [e] using ok y hy'

end ColorSearch1868

namespace Free1868
open Basis1868
open Conflict1868

def flip (s : Bool) (a : Sig) := if s then neg a else a
def sign (a : Sig) := bit true 0 a
def can (a : Sig) := flip (sign a) a

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg2 (a : Sig) : neg (neg a) = a := by
  obtain ⟨u,v⟩ := a
  simp [neg,bnot,Nat.xor_assoc]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip2 (s a) : flip s (flip s a) = a := by cases s <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipFalse (a) : flip false a = a := rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma vf {a} (s) (h : Valid a) : Valid (flip s a) := by cases s <;> first | exact h | exact valid_neg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sign_neg {a} (h : Valid a) : sign (neg a) = !sign a := bit_neg true 0 h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_neg {a} (v : Valid a) : can (neg a) = can a := by
  unfold can
  rw [sign_neg v]
  cases sign a <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_flip {a} (s) (v : Valid a) : can (flip s a) = can a := by
  cases s with
  | false => rfl
  | true => exact can_neg v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can2 {a} (v : Valid a) : can (can a) = can a := can_flip _ v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma recover (a) : flip (sign a) (can a) = a := flip2 _ _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_zero : can zero = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_one : can one = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipProper (s) {a} (ha : proper a) : proper (flip s a) := by
  cases s
  · exact ha
  · refine ⟨valid_neg ha.1,?_,?_⟩
    · intro h
      exact ha.2.2 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.1))
    · intro h
      exact ha.2.1 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.2))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canProper {a} (h : proper a) : proper (can a) := flipProper _ h

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sameClass {a b} (h : can a = can b) : a = b ∨ a = neg b := by
  have ha := recover a
  rw [h] at ha
  unfold can at ha
  cases ea : sign a <;> cases eb : sign b <;> simp [ea,eb,flip,neg2] at ha <;> aesop

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_neg_self (d : Bool) {a} (h : Valid a) :
    bin d a (neg a) = (if d then one else zero) := by
  have op {x : Nat} (hx : Valid1 x) :
      x &&& bnot x = 0 ∧ x ||| bnot x = top := by
    constructor <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      simp only [Nat.testBit_and,Nat.testBit_or,testBit_bnot hx,testBit_top,Nat.zero_testBit] <;>
      by_cases hj : j < 64
    all_goals first | (rw [hx j (by omega)] <;> simp [hj]) | (cases x.testBit j <;> simp [hj])
  cases d
  · exact Prod.ext (op h.1).1 (op h.2).1
  · exact Prod.ext (op h.1).2 (op h.2).2

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma distinctClass {d a b} (ha : proper a) (hab : a ≠ b) (hg : proper (bin d a b)) :
    can a ≠ can b := by
  intro h
  rcases sameClass h with e | e
  · exact hab e
  · have eb : b = neg a := by rw [e,neg2]
    rw [eb,bin_neg_self _ ha.1] at hg
    cases d
    · exact hg.2.1 rfl
    · exact hg.2.2 rfl

def blend (d s t : Bool) (a b : Sig) := can (bin d (flip s a) (flip t b))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive BL : Nat → Finset Sig → Prop where
  | stop : BL 0 {can target}
  | step {k U a b d s t} (ha : proper a) (hb : proper b)
      (ac : can a = a) (bc : can b = b) (hab : a ≠ b)
      (fresh : blend d s t a b ∉ insert a (insert b U))
      (tail : BL k (insert (blend d s t a b) U)) : BL (k+1) (insert a (insert b U))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma compress {k t S} (l : Live k t S) :
    ∃ j T, j+t ≤ k ∧ BL j T ∧ T ⊆ S.image can := by
  induction l with
  | stop => exact ⟨0,_,by omega,BL.stop,by simp⟩
  | @unary k t U a ha _ _ ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    refine ⟨j,T,by omega,h,?_⟩
    simpa only [Finset.image_insert,can_neg ha.1] using sub
  | @binary k t U a b d ha hb hab _ tail ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    let g := bin d a b
    let z := can g
    let w := insert (can a) (insert (can b) (U.image can))
    have hsource : (insert a (insert b U)).image can = w := by simp [w]
    rw [hsource]
    have hs : T ⊆ insert z (U.image can) := by simpa [g,z] using sub
    by_cases need : z ∈ T ∧ z ∉ w
    · have hu : T.erase z ⊆ U.image can := by
        intro c hc
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hc))).resolve_left (Finset.ne_of_mem_erase hc)
      have hp : proper g := live_proper tail _ (Finset.mem_insert_self ..)
      have nz := distinctClass ha hab hp
      have id : blend d (sign a) (sign b) (can a) (can b) = z := by
        simp [blend,recover,z,g]
      have out : BL j (insert (blend d (sign a) (sign b) (can a) (can b)) (T.erase z)) := by
        rw [id,Finset.insert_erase need.1]; exact h
      have fresh : blend d (sign a) (sign b) (can a) (can b) ∉ insert (can a) (insert (can b) (T.erase z)) := by
        rw [id]
        intro zz
        apply need.2
        simp only [Finset.mem_insert] at zz ⊢
        simp only [w,Finset.mem_insert]
        exact zz.imp_right (fun e => e.imp_right (fun h => hu h))
      refine ⟨j+1,_,by omega,BL.step (canProper ha) (canProper hb) (can2 ha.1) (can2 hb.1) nz fresh out,?_⟩
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hu)
    · refine ⟨j,T,by omega,h,?_⟩
      intro c hc
      rcases Finset.mem_insert.mp (hs hc) with rfl | hU
      · exact Classical.byContradiction (fun hn => need ⟨hc,hn⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.forms {k S} (l : BL k S) : ∀ a ∈ S, proper a ∧ can a = a := by
  induction l with
  | stop => simpa using And.intro (canProper target_proper) (can2 valid_target)
  | step ha hb ca cb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha,ca⟩,⟨hb,cb⟩,fun a h => ih _ (Finset.mem_insert_of_mem h)⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_ne {a} (hv : Valid a) : neg a ≠ a := by
  intro h
  have eq := sign_neg hv
  rw [h] at eq
  cases e : sign a <;> simp [e] at eq

def Present (n : Nat) (S : Finset Sig) := ∃ t, Live (n+t) t S

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma insertFlip {n a U} (s : Bool) (ha : proper a)
    (hf : s = true → neg a ∉ insert a U) (h : Present n (insert (flip s a) U)) :
    Present n (insert a U) := by
  cases s
  · exact h
  · obtain ⟨t,hl⟩ := h
    exact ⟨t+1,by simpa [Nat.add_assoc] using Live.unary ha (hf rfl) hl⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.expand {j S} (l : BL j S) : Present j S := by
  induction l with
  | stop =>
    have eq : can target = neg target := by decide +kernel
    rw [eq]
    have hf : neg (neg target) ∉ insert (neg target) (∅ : Finset Sig) := by
      rw [neg2]; simp [Ne.symm (neg_ne valid_target)]
    have t : Live 0 0 (insert (neg (neg target)) ∅) := by rw [neg2]; exact Live.stop
    exact ⟨1,Live.unary (flipProper true target_proper) hf t⟩
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    let x := flip s a
    let y := flip t b
    let g := bin d x y
    let z := can g
    change z ∉ insert a (insert b U) at fresh
    change Present k (insert z U) at ih
    have cx : can x = a := (can_flip s ha.1).trans ca
    have cy : can y = b := (can_flip t hb.1).trans cb
    have vg : Valid g := valid_bin (vf _ ha.1) (vf _ hb.1)
    have zu : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have canonU (c) (hc : c ∈ U) : can c = c := (tail.forms c (Finset.mem_insert_of_mem hc)).2
    have gz : proper z := (tail.forms _ (Finset.mem_insert_self ..)).1
    have hg : proper g := recover g ▸ flipProper (sign g) gz
    have go := insertFlip (sign g) hg (by
      intro act h
      rcases Finset.mem_insert.mp h with gg | inu
      · exact neg_ne vg gg
      · have zz : z = neg g := by change flip (sign g) g = _; rw [act]; rfl
        exact zu (zz ▸ inu)) ih
    have xy : x ≠ y := fun eq => ne (cx.symm.trans ((congrArg can eq).trans cy))
    have gfresh : g ∉ insert x (insert y U) := by
      intro h
      rcases Finset.mem_insert.mp h with hh | h
      · have za : z = a := (congrArg can hh).trans cx
        exact fresh (Finset.mem_insert.mpr (Or.inl za))
      rcases Finset.mem_insert.mp h with hh | inu
      · have zb : z = b := (congrArg can hh).trans cy
        exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl zb)))
      · apply zu
        change can g ∈ U
        rwa [canonU g inu]
    obtain ⟨negCount,live⟩ := go
    have go2 : Present (k+1) (insert x (insert y U)) := by
      refine ⟨negCount,?_⟩
      convert Live.binary (flipProper s ha) (flipProper t hb) xy gfresh live using 1 <;> omega
    have nap : neg a ∉ U := by
      intro hh
      have eq := canonU (neg a) hh
      rw [can_neg ha.1,ca] at eq
      exact neg_ne ha.1 eq.symm
    have nbp : neg b ∉ U := by
      intro hh
      have eq := canonU (neg b) hh
      rw [can_neg hb.1,cb] at eq
      exact neg_ne hb.1 eq.symm
    have xa := insertFlip s ha (U := insert y U) (fun _ hh => by
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact neg_ne ha.1 eq
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact ne (ca.symm.trans ((can_neg ha.1).symm.trans ((congrArg can eq).trans cy)))
      · exact nap hh) go2
    rw [Finset.insert_comm] at xa
    rw [Finset.insert_comm]
    apply insertFlip t hb _ xa
    intro act hh
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact neg_ne hb.1 eq
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact ne ((cb.symm.trans ((can_neg hb.1).symm.trans ((congrArg can eq).trans ca))).symm)
    · exact nbp hh

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma freeColors {k S} (h : BL k S) : ∃ n, Colored S n ∧ n+S.card ≤ k+2 := by
  obtain ⟨t,hl⟩ := h.expand
  obtain ⟨n,c,b⟩ := live_colored hl
  exact ⟨n,c,by omega⟩

end Free1868

namespace FreeSearch1868
open Basis1868
open Conflict1868 Check1868 Free1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma negFlip (u : Bool) (a : Sig) : neg (flip u a) = flip (!u) a := by
  cases u <;> simp [PEqualNP.Outside.L_meta_31225_aux.Seven.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 64 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 64 <;> simp [e]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipBlend {a b} (ha : Valid a) (hb : Valid b) (d s t : Bool) :
    ∃ u v, blend false u v a b = blend d s t a b := by
  cases d
  · exact ⟨s,t,rfl⟩
  · refine ⟨!s,!t,?_⟩
    unfold blend
    rw [← negFlip,← negFlip,← deM (vf s ha) (vf t hb),can_neg (valid_bin (vf s ha) (vf t hb))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_symm (d s t a b) : blend d s t a b = blend d t s b a := by unfold blend; rw [bin_comm]

def keep (a b : Sig) (u v : Bool) (c : Sig) := (c != a || u) && (c != b || v)
def next (v : List Sig) (a b z : Sig) (l r : Bool) := z :: v.filter (keep a b l r)
def oneB (v : List Sig) (go : List Sig → Bool) (a b : Sig) (s t : Bool) :=
  let z := blend false s t a b
  z != zero && !(v.contains z) &&
  ([false,true].any fun l => [false,true].any fun r => go (next v a b z l r))
def pairB (v : List Sig) (go : List Sig → Bool) (a b : Sig) :=
  [false,true].any fun s => [false,true].any fun t => oneB v go a b s t

def baseTest (v : List Sig) := v == [can target]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tailState {a b z : Sig} {U : Finset Sig} {v : List Sig} (nd : v.Nodup)
    (rep : v.toFinset = insert a (insert b U)) (fresh : z ∉ insert a (insert b U)) :
    let w := next v a b z (decide (a ∈ U)) (decide (b ∈ U))
    w.Nodup ∧ w.toFinset = insert z U := by
  classical
  dsimp only
  have ff : (v.filter (keep a b (decide (a ∈ U)) (decide (b ∈ U)))).toFinset = U := by
    ext c
    simp only [List.mem_toFinset,List.mem_filter,keep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne]
    have mem : c ∈ v ↔ c = a ∨ c = b ∨ c ∈ U := by rw [← List.mem_toFinset,rep]; simp
    rw [mem]
    by_cases ea : c = a <;> by_cases eb : c = b <;> simp_all
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun h => fresh (rep ▸ List.mem_toFinset.mpr (List.mem_of_mem_filter h)),nd.filter _⟩
  · simpa only [next,List.toFinset_cons,ff]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma anyBool {f : Bool → Bool} (a) (h : f a = true) : [false,true].any f = true :=
  List.any_eq_true.mpr ⟨a,by cases a <;> simp,h⟩

end FreeSearch1868

namespace Part1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868

end Part1868

namespace Full1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868

end Full1868

namespace Cuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma oneStep {k S} (l : BL k S) (m : Nat) (hm : k ≤ m+1) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) (go : List Sig → Bool)
    (hyp : ∀ w, w.Nodup → ∀ j ≤ m, BL j w.toFinset → go w = true) :
    (baseTest v || scanPairs (pairB v go) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr; right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v go x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      exact hyp _ nw j (by omega) (pw ▸ tail)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])

def excluded (k : Nat) (v : List Sig) := ∀ n ≤ k, ¬ BL n v.toFinset
end Cuts1868

namespace FastCuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868 Cuts1868

end FastCuts1868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Board1868
open Basis1868
def mult : List (Sig × Nat) → Sig
  | [] => zero
  | o::l => let (atLeastOne,atLeastTwo) := mult l
            (atLeastOne ||| o.2,atLeastTwo ||| (atLeastOne &&& o.2))
end Board1868
namespace LinearWide1868
open Basis1868 Board1868
end LinearWide1868
namespace Linear1868
def Linear (f : Nat → Nat) := f 0 = 0 ∧ ∀ x y, f (x ||| y) = f x ||| f y
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linId : Linear id := ⟨rfl,fun _ _ => rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linAnd (mask : Nat) : Linear (fun x => x &&& mask) :=
  ⟨by simp,fun _ _ => Nat.and_or_distrib_right ..⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linLeft (n : Nat) : Linear (fun x => x <<< n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_shiftLeft,Nat.testBit_or]
    by_cases e : n ≤ j <;> simp [e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linRight (n : Nat) : Linear (fun x => x >>> n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp [Nat.testBit_shiftRight,Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOr {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ||| g x) :=
  ⟨by simp [hf.1,hg.1],fun x y => by dsimp only; rw [hf.2,hg.2]; ac_rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linComp {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f (g x)) :=
  ⟨by dsimp only; rw [hg.1,hf.1],fun _ _ => by dsimp only; rw [hg.2,hf.2]⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma trunc_succ (x n : Nat) : x % 2^(n+1) = (x % 2^n) ||| (if x.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_or]
  cases e : x.testBit n <;> by_cases h : j=n <;> by_cases lt : j<n <;>
    simp_all [Nat.testBit_two_pow, show (j < n+1) ↔ j<n ∨ j=n by omega] <;> omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma imagesTrunc {f : Nat→Nat} (hl : Linear f) (x j) (n : Nat) :
    (f (x % 2^n)).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  induction n with
  | zero => simp [Nat.mod_one,hl.1]
  | succ n ih =>
    rw [trunc_succ,hl.2,Nat.testBit_or,Bool.or_eq_true,ih]
    by_cases bit : x.testBit n = true
    · simp only [bit,↓reduceIte]
      constructor
      · rintro (⟨i,hi,hb,hv⟩|h)
        · exact ⟨i,by omega,hb,hv⟩
        · exact ⟨n,by omega,bit,h⟩
      · rintro ⟨i,hi,hb,hv⟩
        by_cases e : i=n
        · exact Or.inr (e ▸ hv)
        · exact Or.inl ⟨i,by omega,hb,hv⟩
    · simp only [bit,↓reduceIte,hl.1,Nat.zero_testBit,Bool.false_eq_true,or_false]
      constructor
      · rintro ⟨i,hi,hb,hv⟩; exact ⟨i,by omega,hb,hv⟩
      · rintro ⟨i,hi,hb,hv⟩
        have ne : i ≠ n := fun e => bit (e ▸ hb)
        exact ⟨i,by omega,hb,hv⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma images {f : Nat→Nat} (hl : Linear f) {x n} (lim : x < 2^n) (j) :
    (f x).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  simpa [Nat.mod_eq_of_lt lim] using imagesTrunc hl x j n
end Linear1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma validBound {x} (h : Valid1 x) : x < 2^64 := by
  have eq : x % 2^64 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 64
    · simp [hj]
    · simp [hj,h j (by omega)]
  rw [← eq]
  exact Nat.mod_lt _ (by decide)
def Sub (x y : Nat) := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linMono {f} (h : Linear f) {x y} (s : Sub x y) : Sub (f x) (f y) := by
  have e : x ||| y = y := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
    cases hx : x.testBit i <;> simp [hx,s i]
  intro i hi
  have e' := congrArg (fun w : Nat => w.testBit i) (h.2 x y)
  simp [e,Nat.testBit_or,hi] at e'
  exact e'
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
abbrev Ix := Fin 26496
abbrev I := Fin 64
def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_31225_aux.Seven.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_31225_aux.Seven.Board1868 (mult)
abbrev Sign := Sig × Nat
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiOne {v : List Sign} {a} (ha : a ∈ v) (i) (hit : a.2.testBit i = true) :
    (mult v).1.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).1 ||| z.2).testBit i = true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl|hh
    · exact Or.inr hit
    · exact Or.inl (ih hh)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiTwo {v : List Sign} {a b} (ha : a∈v) (hb : b∈v) (ne : a ≠ b) (i)
    (x : a.2.testBit i = true) (y : b.2.testBit i = true) : (mult v).2.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).2 ||| ((mult l).1 &&& z.2)).testBit i = true
    rw [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ha with ea|hal
    · subst a
      rcases List.mem_cons.mp hb with eb|hbl
      · exact (ne eb.symm).elim
      · exact Or.inr ⟨multiOne hbl i y,x⟩
    · rcases List.mem_cons.mp hb with eb|hbl
      · subst b
        exact Or.inr ⟨multiOne hal i x,y⟩
      · exact Or.inl (ih hal hbl)

def U (d : Bool) (p n : I) (v : List Sig) (a : Sig) := ∀ c ∈ v, DS d p n c → c=a
def M (d : Bool) (p n : I) (v : List Sig) (a : Sig) :=
  DS d p n a ∧ (∃ j,U d p j v a) ∧ ∃ j,U d j n v a
end WProof1868
namespace Guard3400
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open WProof1868 LinearWide1868
open PEqualNP.Outside.L_meta_31225_aux.Seven.Board1868 (mult)
open PEqualNP.Outside.L_meta_31225_aux.Seven.ColorSearch1868 (paint paint_ok)

end Guard3400
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Check2516
def costly (g : Gate) : Bool := match g.op with | .not => false | _ => true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gateTag {w : List Sig} (hw : ∀ a∈w, Valid a) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ (∃ a∈w, proper a ∧ gv w g=neg a) ∨
      ((if costly g then 1 else 0)=1 ∧ ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g=bin d a b) := by
  by_cases h : costly g=true
  · rcases gate_rep hw g legal with a|a|a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨by simp [h],a⟩)
  · obtain ⟨o,l⟩ := g
    cases o <;> try simp [costly] at h
    have nt (a : Sig) (v : Valid a) (r : represented w a) :
        represented w (neg a) ∨ ∃ a'∈w, proper a' ∧ neg a=neg a' := by
      rcases operand_cases v r with rfl|rfl|⟨mem,hp⟩
      · exact Or.inl (Or.inr (fun hp => hp.2.2 neg_laws.1))
      · exact Or.inl (Or.inr (fun hp => hp.2.1 neg_laws.2))
      · exact Or.inr ⟨a,mem,hp,rfl⟩
    cases l with
    | nil => exact (nt zero valid_zero (Or.inr (fun h => h.2.1 rfl))).imp_right Or.inl
    | cons i l => exact (nt (w.getD i zero) (valid_getD hw i) (get_rep w i)).imp_right Or.inl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pullTag (c : Nat) {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ (∃ a ∈ w, proper a ∧ z=neg a) ∨ (c=1 ∧ ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k+t'+c ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨hc,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tagExtract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.countP costly + t ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pullTag (if costly g then 1 else 0) ht (gateTag hw g (legal g (by simp))) hs
    exact ⟨l,u,T,by cases he : costly g <;> simp [he] at hl ⊢ <;> omega,hu,hT⟩
end Check2516
namespace Check2516
open Basis1868 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
end Check2516
namespace Basis1868
def reindexLoop (f : Fin 64 → Fin 64) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 64 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 64 → Fin 64) (x : Nat) : Nat := reindexLoop f x 64
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindexLoop_testBit (f : Fin 64 → Fin 64) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 64 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 64
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 64 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 64 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 64
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 64 → Fin 64) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 64 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 64 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 64 → Fin 64) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 64 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 64 → Fin 64) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 64 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 64 → Fin 64) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 64 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 64 → Fin 64) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 64
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 64 → Fin 64) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 64 → Fin 64) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 64
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 64 → Fin 64) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)

end Basis1868
namespace Sym1868
open Basis1868
def Good (H J : SigHom) (a : Sig) := Valid a ∧ J.fn (H.fn a) = a
variable {H J : SigHom}
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodNeg {a} (h : Good H J a) : Good H J (neg a) :=
  ⟨valid_neg h.1,by rw [H.hneg h.1,J.hneg (H.valid a),h.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBin {a b} (ha : Good H J a) (hb : Good H J b) {d} : Good H J (bin d a b) :=
  ⟨valid_bin ha.1 hb.1,by rw [H.hbin,J.hbin,ha.2,hb.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inj {a b} (ha : Good H J a) (hb : Good H J b) (e : H.fn a = H.fn b) : a=b := by
  rw [← ha.2,← hb.2,e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma properH {a} (ga : Good H J a) (ha : proper a) : proper (H.fn a) :=
  ⟨H.valid a,fun e => ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero)),
    fun e => ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))⟩
end Sym1868
namespace Moves3400
open Basis1868
open Free1868 Sym1868 Cuts1868
def SignFixed (H : SigHom) := ∀ a, sign (H.fn a)=sign a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip_map (H : SigHom) (s : Bool) {a : Sig} (ha : Valid a) :
    H.fn (flip s a)=flip s (H.fn a) := by cases s <;> first | rfl | exact H.hneg ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_map {H : SigHom} (fix : SignFixed H) {a : Sig} (ha : Valid a) :
    H.fn (can a)=can (H.fn a) := by unfold can; rw [fix a,flip_map H _ ha]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_map {H : SigHom} (fix : SignFixed H) {a b : Sig} (ha : Valid a) (hb : Valid b) (d s t) :
    H.fn (blend d s t a b)=blend d s t (H.fn a) (H.fn b) := by
  unfold blend
  rw [can_map fix (valid_bin (vf s ha) (vf t hb)),H.hbin,flip_map H _ ha,flip_map H _ hb]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodFlip {H J : SigHom} {a} (h : Good H J a) (s : Bool) : Good H J (flip s a) := by
  cases s <;> first | exact h | exact goodNeg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBlend {H J : SigHom} {a b} (ha : Good H J a) (hb : Good H J b) (d s t) :
    Good H J (blend d s t a b) := goodFlip (goodBin (goodFlip ha s) (goodFlip hb t)) _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mapBL {H J : SigHom} (fix : SignFixed H) {k S} (l : BL k S) (hs : ∀ a∈S,Good H J a) :
    BL k (S.image H.fn) := by
  induction l with
  | stop => simpa only [Finset.image_singleton,can_map fix target_proper.1,H.htarget] using (BL.stop : BL 0 {can target})
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    have ga := hs a (Finset.mem_insert_self ..)
    have gb := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have gu (x) (h : x∈U) : Good H J x := hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have gz := goodBlend ga gb d s t
    have ez := blend_map fix ha.1 hb.1 d s t
    have ht := ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,ez] at ht
    rw [Finset.image_insert,Finset.image_insert]
    apply BL.step (properH ga ha) (properH gb hb) _ _ (fun e => ne (inj ga gb e)) _ ht
    · rw [← can_map fix ha.1,ca]
    · rw [← can_map fix hb.1,cb]
    · rw [← ez,← Finset.image_insert,← Finset.image_insert]
      intro h
      obtain ⟨x,hx,xe⟩ := Finset.mem_image.mp h
      exact fresh (inj (hs x hx) gz xe ▸ hx)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fixed (p n : Fin 64 → Fin 64) (z : p 0=0) : SignFixed (pairHom p n) := by
  intro a
  change (reindex p a.1).testBit 0=a.1.testBit 0
  rw [reindex_testBit]
  simp [z]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma move {v w : List Sig} {k : Nat} (H J : SigHom) (fix : SignFixed H)
    (equal : (v.map H.fn).toFinset=w.toFinset)
    (inverse : v.all (fun a => decide (J.fn (H.fn a)=a))=true)
    (old : excluded k w) : excluded k v := by
  intro m hm l
  have h := mapBL (J:=J) fix l (fun a ha => ⟨(l.forms a ha).1.1,
    of_decide_eq_true (List.all_eq_true.mp inverse a (List.mem_toFinset.mp ha))⟩)
  have eq : v.toFinset.image H.fn=(v.map H.fn).toFinset := by
    ext x; simp
  rw [eq,equal] at h
  exact old _ hm h
end Moves3400
namespace Mono1868
open Basis1868

abbrev I := Fin 64
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def pos (x y : Bool) : Prop := x = true ∧ y = false
def D (p n : I) (a : Sig) : Prop := pos (P a p) (N a n)
def op (d x y : Bool) : Bool := if d then x || y else x && y

lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
lemma bor : ∀ (d ap an bp bn : Bool), pos (op d ap bp) (op d an bn) → pos ap an ∨ pos bp bn := by
  unfold pos; decide +kernel
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  unfold D P N at hd
  rw [bop,bop] at hd
  exact bor _ _ _ _ _ hd
lemma pair_sep {k t S} (hl : Live k t S) (ht : t = 0) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,pos,P,N,bit,target,testBit_top,p.isLt]
  | unary => omega
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (ht : t=0) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h ht p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

lemma mix : ∀ (d ap an bp bn al ar bm bq : Bool), pos ap an →
    ¬ pos bp bm → ¬ pos bq bn →
    pos (op d ap bp) (op d al bm) → pos (op d ar bq) (op d an bn) →
    ¬ pos bp bn ∧ pos (op d ap bp) (op d an bn) := by unfold pos; decide +kernel

lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U)) (ht : t = 0)
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : ¬ pos (P b p) (N b m) := fun h => hab (hm _ hb h).symm
  have bq : ¬ pos (P b q) (N b n) := fun h => hab (hq _ hb h).symm
  have zm := unique_diff tail ht (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail ht (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  unfold D P N at zm zq
  rw [bop,bop] at zm zq
  have hh := mix _ _ _ _ _ _ _ _ _ hd bm bq zm zq
  refine ⟨hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2

def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (ht : t=0) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ht ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail ht mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

theorem live_colored {k t S} (l : Live k t S) (ht : t=0) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary => omega
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih ht
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail ht hk
    exact ⟨u,hu,by omega⟩

end Mono1868
end PEqualNP.Outside.L_meta_31225_aux.Seven
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_31225_aux.Seven
def edge (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6)
end PEqualNP.Outside.L_meta_31225_aux.Seven
namespace PEqualNP.Outside.L_meta_31225_aux.Seven
section
open Basis1868 Free1868
namespace Projection8403
def unaryRep (w : List Sig) (z : Sig) := ∃ a∈w,proper a ∧ z=neg a
def binRep (w : List Sig) (z : Sig) := ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b
lemma pullBudget {w : List Sig} {z : Sig} {k t S} {cost : Nat} (h : Live k t S)
    (hz : represented w z ∨ unaryRep w z ∨ (0 < cost ∧ binRep w z)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k + t' + cost ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨positive,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def Can (cost : Nat) (base : Finset Sig) := ∃ k t T,k≤cost+t ∧ Live k t T ∧ T⊆base
lemma mono {m n a b} (h : Can m a) (budget : m≤n) (sub : a⊆b) : Can n b := by
  obtain ⟨u,t,T,cap,run,incl⟩:=h;exact ⟨u,t,T,by omega,run,incl.trans sub⟩
lemma rewind {q basis z cost} (step : represented basis.toList z ∨ unaryRep basis.toList z ∨
      0<cost ∧ binRep basis.toList z) (tail : Can q (insert z basis)) : Can (q+cost) basis := by
  obtain ⟨k,t,T,le,h,sub⟩:=tail
  have avail : ∀a∈T,a∈basis.toList++[z] := by
    intro a ha;rcases Finset.mem_insert.mp (sub ha) with rfl|hm
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr hm)
  obtain ⟨k',t',T',cap,live,old⟩:=pullBudget h step avail
  exact ⟨k',t',T',by omega,live,fun a ha=>Finset.mem_toList.mp (old a ha)⟩
lemma negStep {basis : Finset Sig} {a : Sig} (va : Valid a) (ha : a∈basis) :
    represented basis.toList (neg a) ∨ unaryRep basis.toList (neg a) ∨ 0<0 ∧ binRep basis.toList (neg a) := by
  by_cases p : proper a
  · exact Or.inr (Or.inl ⟨a,Finset.mem_toList.mpr ha,p,rfl⟩)
  · rcases operand_cases va (Or.inr p : represented [] a) with rfl|rfl|⟨bad,_⟩
    · rw [neg_laws.1];exact Or.inl (Or.inr (fun p=>p.2.2 rfl))
    · rw [neg_laws.2];exact Or.inl (Or.inr (fun p=>p.2.1 rfl))
    · cases bad
lemma binaryStep {basis : Finset Sig} {a b : Sig} (d) (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis) :
    represented basis.toList (bin d a b) ∨ unaryRep basis.toList (bin d a b) ∨ 0<1 ∧ binRep basis.toList (bin d a b) := by
  rcases bin_rep d va vb (Or.inl (Finset.mem_toList.mpr ha)) (Or.inl (Finset.mem_toList.mpr hb)) with r|u|v
  · exact Or.inl r
  · exact Or.inr (Or.inl u)
  · exact Or.inr (Or.inr ⟨by decide,v⟩)
def constant (a : Sig) := a=zero ∨ a=one
instance (a : Sig) : Decidable (constant a) := by unfold constant;infer_instance
def mass (H : SigHom) (s : Finset Sig) := (s.filter (fun a=>constant (H.fn a))).card
lemma constant_neg {a : Sig} (va : Valid a) : constant (neg a) ↔ constant a := by
  constructor
  · rintro (e|e)
    · right;simpa only [neg2,neg_laws.1] using (show neg (neg a)=neg zero from congrArg neg e)
    · left;simpa only [neg2,neg_laws.2] using congrArg neg e
  · rintro (rfl|rfl)
    · right;exact neg_laws.1
    · left;exact neg_laws.2
lemma constResult {a b : Sig} (va : Valid a) (vb : Valid b) (d : Bool) (c : constant a ∨ constant b) :
    constant (bin d a b) ∨ bin d a b=a ∨ bin d a b=b := by
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws va
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws vb
  rcases c with (rfl|rfl)|(rfl|rfl) <;> cases d <;> simp_all [constant,bin_comm]
lemma bothResult {a b : Sig} (va : Valid a) (vb : Valid b) (d) (ca : constant a) (cb : constant b) :
    constant (bin d a b) := by
  rcases constResult va vb d (Or.inl ca) with h|h|h
  · exact h
  · simpa only [h] using ca
  · simpa only [h] using cb
lemma constFree {basis : Finset Sig} {a b : Sig} (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis)
    (d) (c : constant a ∨ constant b) : represented basis.toList (bin d a b) := by
  rcases constResult va vb d c with (h|h)|h|h
  · exact Or.inr (fun p=>p.2.1 h)
  · exact Or.inr (fun p=>p.2.2 h)
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr ha
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr hb
end Projection8403
end
section
open Basis1868 Free1868
namespace Projection8403
lemma massInsert (H : SigHom) (a : Sig) (U : Finset Sig) :
    mass H (insert a U) = mass H U + (if a∉U ∧ constant (H.fn a) then 1 else 0) := by
  classical
  by_cases mem : a∈U
  · simp [mem,Finset.insert_eq_of_mem mem]
  · by_cases c : constant (H.fn a)
    · simp [mass,Finset.filter_insert,mem,c,Finset.card_insert_of_notMem]
    · simp [mass,Finset.filter_insert,mem,c]
lemma pushNeg {H : SigHom} {q : Nat} {U : Finset Sig} {a : Sig} (va : Valid a)
    (tail : Can q ((insert (neg a) U).image H.fn)) : Can q ((insert a U).image H.fn) := by
  let pool:=(insert a U).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have sub : (insert (neg a) U).image H.fn⊆insert (neg (H.fn a)) pool := by
    rw [Finset.image_insert,H.hneg va]
    exact Finset.insert_subset_insert _ (Finset.image_mono _ (Finset.subset_insert ..))
  simpa only [Nat.add_zero,pool] using rewind (negStep (H.valid a) ha) (mono tail (Nat.le_refl _) sub)
lemma pushBin {H : SigHom} {q : Nat} {U : Finset Sig} {a b : Sig} (d : Bool) (tail : Can q ((insert (bin d a b) U).image H.fn)) :
    Can (q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1)) ((insert a (insert b U)).image H.fn) := by
  let pool:=(insert a (insert b U)).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have hb : H.fn b∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have sub : (insert (bin d a b) U).image H.fn ⊆ insert (bin d (H.fn a) (H.fn b)) pool := by
    rw [Finset.image_insert,H.hbin]
    apply Finset.insert_subset_insert
    exact Finset.image_mono _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
  by_cases c : constant (H.fn a) ∨ constant (H.fn b)
  · rw [ite_eq_left c]
    apply rewind (Or.inl (constFree (H.valid a) (H.valid b) ha hb d c))
    exact mono tail (Nat.le_refl _) sub
  · rw [ite_eq_right c]
    exact rewind (binaryStep d (H.valid a) (H.valid b) ha hb) (mono tail (Nat.le_refl _) sub)
lemma massNeg {H : SigHom} {U : Finset Sig} {a : Sig} (va : Valid a) (fresh : neg a∉insert a U) :
    mass H (insert a U)≤mass H (insert (neg a) U) := by
  have hz : neg a∉U:=fun zn=>fresh (Finset.mem_insert_of_mem zn)
  rw [massInsert,massInsert,H.hneg va]
  simp only [hz,not_false_eq_true,true_and,constant_neg (H.valid a)]
  by_cases c : constant (H.fn a) <;> by_cases t : a∈U <;> simp [c,t]
lemma massBin {H : SigHom} {U : Finset Sig} {a b : Sig} (d : Bool) (ab : a≠b) (fresh : bin d a b∉insert a (insert b U)) :
    mass H (insert a (insert b U)) + (if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1) ≤
      mass H (insert (bin d a b) U)+1 := by
  have hz : bin d a b∉U:=fun z=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem z))
  rw [massInsert,massInsert,massInsert,H.hbin]
  by_cases ca : constant (H.fn a) <;> by_cases cb : constant (H.fn b)
  all_goals by_cases aa : a∈U <;> by_cases bb : b∈U
  all_goals simp only [Finset.mem_insert,ab,false_or,ca,cb,aa,bb,hz,not_true_eq_false,not_false_eq_true,
    and_false,false_and,true_and,and_true,ite_false,ite_true,or_false,false_or,true_or,or_true,Nat.add_zero]
  all_goals try omega
  all_goals try (have z:=bothResult (H.valid a) (H.valid b) d ca cb; rw [ite_eq_left z]; omega)
  all_goals try (split <;> omega)
  all_goals
    have z := bothResult (H.valid a) (H.valid b) d ca cb
    simp only [z,ite_true]
    omega
theorem projected {k t S} (h : Live k t S) (H : SigHom) :
    ∃ q,q+mass H S+t≤k ∧ Can q (S.image H.fn) := by
  induction h with
  | stop =>
    have nc : ¬constant target:=by rintro (e|e);exact target_proper.2.1 e;exact target_proper.2.2 e
    refine ⟨0,by simp [mass,H.htarget,nc],0,0,{target},by omega,Live.stop,?_⟩
    simp [H.htarget]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massNeg (H:=H) ha.1 hf
    exact ⟨q,by omega,pushNeg ha.1 prog⟩
  | @binary k t U a b d ha hb ab hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massBin (H:=H) d ab hf
    exact ⟨q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1),by omega,pushBin d prog⟩
theorem projectedBL {n S} (run : BL n S) (H : SigHom) :
    ∃k T,k+mass H S≤n ∧ BL k T ∧ T⊆(S.image H.fn).image can := by
  obtain ⟨t,live⟩:=run.expand
  obtain ⟨q,lim,m,u,T,cap,h,sub⟩:=projected live H
  obtain ⟨j,V,size,ok,ss⟩:=compress h
  exact ⟨j,V,by omega,ok,ss.trans (Finset.image_mono _ sub)⟩
end Projection8403
end
section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Check2516 Free1868 FreeSearch1868 Cuts1868
open Projection8403 PEqualNP.Outside.L_meta_31225_aux.Seven
namespace Exact8403
def raw8 : List Sig := [(0x95370889a24a9537, 0x20a020a020a020a), (0x29da1112c49329da, 0x2c002c002c002c), (0x4e632223091c4e63, 0x40b040b040b040b0), (0x707c443c11e0707c, 0x4c004c004c004c0), (0x7f8087c01e007f80, 0x1700170017001700), (0x8000f8001fff8000, 0x9800980098009800), (0xffffe0000000, 0xe000e000e000e000)]
def pos8 : Array Nat := #[5, 7, 9, 10, 11, 13, 14, 18, 19, 20, 21, 22, 25, 26, 28, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 49, 50, 52, 56, 65, 66, 67, 69, 70, 72, 73, 74, 76, 80, 81, 82, 84, 88, 97, 98, 100, 104, 112]
def neg8 : Array Nat := #[0, 1, 2, 3, 4, 6, 8, 12, 16, 17, 24, 32, 48, 64, 68, 96]
def sample8 (s : Bool) (i : Fin 64) : Fin 7 → Bool :=
  let xs:=if s then pos8 else neg8
  fun j=>(xs.getD (i.val % xs.size) 0).testBit j.val
lemma vals : ∀a∈raw8,Valid a := by
  have h : raw8.all (fun x=>decide (x.1≤top ∧ x.2≤top))=true := by decide +kernel
  intro a ha
  have k:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top k.1,valid1_of_le_top k.2⟩
set_option maxHeartbeats 0 in
lemma good8 : ∀(s : Bool) (i : Fin 64), edge (sample8 s i)=s ∧ List.ofFn (sample8 s i)=raw8.map (bit s i) := by decide +kernel
lemma output8 {C : Circuit} (fan : FanInTwo C) (spec : ∀x, C.eval (List.ofFn x)=edge x) :
    target∈execute C.gates raw8 := by
  let w:=execute C.gates raw8
  have hwv:=execute_valid C.gates raw8 vals
  have hp (s : Bool) (i : Fin 64) : bit s i (w.getD C.output zero)=s := by
    rw [←b_read]
    change ((execute C.gates raw8).map _).getD C.output false=s
    rw [execute_bits _ _ _ _ vals (fun g hg=>(fan g hg).1)]
    have h:=spec (sample8 s i)
    rw [(good8 s i).1,(good8 s i).2] at h
    exact h
  have hvout:=valid_getD hwv C.output
  have et : w.getD C.output zero=target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq;intro j
      rw [target,testBit_top]
      by_cases hi : j<64
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)];simp [hi]
    · apply Nat.eq_of_testBit_eq;intro j
      by_cases hi : j<64
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)];exact (Nat.zero_testBit j).symm
  have rep:=get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun h=>h target_proper)
def necessary (v : List Sig) := ∀a∈v,∃p n : Fin 64,∀b∈v,bit true p b≠bit false n b → b=a
lemma allNeeded {k t S} {v : List Sig} (h : Live k t S) (sub : S⊆v.toFinset) (need : necessary v) : S=v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨p,n,uniq⟩:=need a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_31225_aux.Seven.Conflict1868.pair_sep h p n
  exact uniq b (List.mem_toFinset.mp (sub hb)) sep ▸ hb
def necessaryAt (v : List Sig) (pn : List (Nat×Nat)) :=
  (v.zip pn).all fun (a,p,n) => v.all fun b=>bit true (Fin.ofNat 64 p) b == bit false (Fin.ofNat 64 n) b || b==a
lemma needFrom {v : List Sig} {pn : List (Nat×Nat)} (len : v.length≤pn.length) (ok : necessaryAt v pn=true) : necessary v := by
  intro a ha
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ha
  have hp : i<pn.length:=by omega
  have hz : (a,pn[i])∈v.zip pn := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp;omega,by simp [eq]⟩
  have h:=List.all_eq_true.mp ok _ hz
  refine ⟨Fin.ofNat 64 pn[i].1,Fin.ofNat 64 pn[i].2,?_⟩
  intro b hb no
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp h _ hb) with e|e
  · exact False.elim (no (beq_iff_eq.mp e))
  · exact beq_iff_eq.mp e
end Exact8403
end
section
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Cuts1868
open Linear1868
namespace QuickQ

abbrev Move := Bool × Nat × Nat
def update (op : Move) (x : Nat) :=
  (if op.1 then x ||| (x <<< op.2.1) else x ||| (x >>> op.2.1)) &&& op.2.2
def sweep : List Move → Nat → Nat
  | [],x => x
  | h::t,x => sweep t (update h x)
theorem linUpdate (op : Move) : Linear (update op) := by
  rcases op with ⟨b,m,n⟩
  cases b
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x >>> m)) (linAnd n) (linOr linId (linRight m))
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x <<< m)) (linAnd n) (linOr linId (linLeft m))
theorem linSweep (xs : List Move) : Linear (sweep xs) := by
  induction xs with
  | nil => exact linId
  | cons h t ih => exact linComp (f:=sweep t) (g:=update h) ih (linUpdate h)

structure Chart where
  h : Nat
  w : Nat
  spreadP : List Move
  spreadN : List Move
  fillP : List Move
  fillN : List Move

def area (c : Chart) := c.h*c.w
def roof (c : Chart) := 2^(area c)-1
def lanes (c : Chart) := (roof c)/(2^c.w-1)
def row (c : Chart) (i : Nat) := (2^c.w-1) <<< (c.w*i)
def col (c : Chart) (i : Nat) := lanes c <<< i
def positive (c : Chart) (i : Fin (area c)) : Fin 64 := Fin.ofNat 64 (i.val/c.w)
def negative (c : Chart) (i : Fin (area c)) : Fin 64 := Fin.ofNat 64 (i.val % c.w)
def good (c : Chart) :=
  (∀i : Fin 64, sweep c.spreadP (2^i.val) = if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 64, sweep c.spreadN (2^i.val) = if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c), (row c (positive c i).val).testBit i.val=true ∧
      (col c (negative c i).val).testBit i.val=true) ∧
  (∀(i : Fin (area c)) (p : Fin c.h), (row c p.val).testBit i.val=true → (positive c i).val=p.val) ∧
  (∀(i : Fin (area c)) (n : Fin c.w), (col c n.val).testBit i.val=true → (negative c i).val=n.val) ∧
  (∀i : Fin (area c), (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀r : Fin c.h, sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val = 0) ∧
  (∀n : Fin c.w, sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val = 0)
theorem roofBit (c : Chart) (i : Nat) : (roof c).testBit i=decide (i<area c) := by
  simp [roof,Nat.testBit_two_pow_sub_one]
theorem locate {f : Nat→Nat} {mask top x i : Nat} (lin : Linear f) (hm : mask.testBit i=true)
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.1 ⟨j,hj⟩] at x
    by_cases e : j<c.h
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(positive c i).isLt,x,?_⟩
    rw [h.1 (positive c i), ite_eq_left (h.2.2.2.2.2.1 i).1]
    exact (h.2.2.1 i).1
theorem nbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadN a).testBit i.val = a.testBit (negative c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.2.1 ⟨j,hj⟩] at x
    by_cases e : j<c.w
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(negative c i).isLt,x,?_⟩
    rw [h.2.1 (negative c i),ite_eq_left (h.2.2.2.2.2.1 i).2]
    exact (h.2.2.1 i).2
end QuickQ
end
section
open Basis1868
namespace QuickQ
def compactGood (c : Chart) :=
  (∀i : Fin 64,sweep c.spreadP (2^i.val)=if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 64,sweep c.spreadN (2^i.val)=if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c),(row c (positive c i).val).testBit i.val=true ∧ (col c (negative c i).val).testBit i.val=true ∧
      (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀p q : Fin c.h,p≠q → row c p.val &&& row c q.val=0) ∧
  (∀p q : Fin c.w,p≠q → col c p.val &&& col c q.val=0) ∧
  (∀r : Fin c.h,sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val=0) ∧
  (∀n : Fin c.w,sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val=0)
theorem goodOfCompact {c : Chart} (h : compactGood c) : good c := by
  obtain ⟨sp,sn,sel,rows,cols,fp,fn⟩:=h
  refine ⟨sp,sn,fun i=>⟨(sel i).1,(sel i).2.1⟩,?_,?_,fun i=>(sel i).2.2,fp,fn⟩
  · intro i p hp
    let q : Fin c.h:=⟨(positive c i).val,(sel i).2.2.1⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (rows q p (fun eq=>ne (congrArg Fin.val eq)))
    change (row c (positive c i).val &&& row c p.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).1,hp,Nat.zero_testBit] at bad
    contradiction
  · intro i n hn
    let q : Fin c.w:=⟨(negative c i).val,(sel i).2.2.2⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (cols q n (fun eq=>ne (congrArg Fin.val eq)))
    change (col c (negative c i).val &&& col c n.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).2.1,hn,Nat.zero_testBit] at bad
    contradiction
end QuickQ
end
section
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open PEqualNP.Outside.L_meta_31225_aux.Seven.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_31225_aux.Seven.Board1868 (mult)
open PEqualNP.Outside.L_meta_31225_aux.Seven.ColorSearch1868 (paint paint_ok)
namespace QuickQ
def diff (c : Chart) (d : Bool) (a : Sig) : Sig × Nat :=
  let p:=sweep c.spreadP a.1
  let n:=sweep c.spreadN a.2
  (a,if d then p ^^^ n else p &&& (roof c ^^^ n))
def signs (c : Chart) (d : Bool) (v : List Sig) := v.map (diff c d)
def once (s : List (Sig × Nat)) := let t:=mult s;t.1 ^^^ t.2
def hit (c : Chart) (sn : Nat) (z : Sig × Nat) := z.2 &&& sn &&& roof c
def marked (c : Chart) (sn : Nat) (z : Sig × Nat) : Sig × Nat :=
  let u:=hit c sn z
  (z.1,z.2 &&& sweep c.fillP u &&& sweep c.fillN u &&& roof c)
def entries (c : Chart) (d : Bool) (v : List Sig) := let s:=signs c d v;let one:=once s;s.map (marked c one)
def test (c : Chart) (d : Bool) (colors : Nat) (v : List Sig) :=
  let s:=signs c d v
  let counts:=mult s
  (counts.1 &&& roof c)==roof c && paint colors (s.map (marked c (counts.1 ^^^ counts.2))) (fun _=>0)
theorem diffBit {c : Chart} (good : good c) (d : Bool) {a : Sig} (val : Valid a) (i : Fin (area c)) :
    (diff c d a).2.testBit i.val=true ↔ DS d (positive c i) (negative c i) a := by
  have rt : (roof c).testBit i.val=true:=by rw [roofBit];exact decide_eq_true i.isLt
  cases d
  · change Nat.testBit (sweep c.spreadP a.1 &&& (roof c ^^^ sweep c.spreadN a.2)) i.val=true ↔ a.1.testBit (positive c i).val=true ∧ a.2.testBit (negative c i).val=false
    simp [Nat.testBit_and,Nat.testBit_xor,pbit good val.1,nbit good val.2,rt]
  · change Nat.testBit (sweep c.spreadP a.1 ^^^ sweep c.spreadN a.2) i.val=true ↔ a.1.testBit (positive c i).val≠a.2.testBit (negative c i).val
    simp [Nat.testBit_xor,pbit good val.1,nbit good val.2]
theorem hitBound (c : Chart) (sn : Nat) (a : Sig × Nat) : Sub (hit c sn a) (roof c) := by
  intro i hi;simp only [hit,Nat.testBit_and,Bool.and_eq_true] at hi;exact hi.2
theorem uniq {c : Chart} (good : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (hit c (once (signs c d v)) (diff c d a)).testBit i.val=true) :
    U d (positive c i) (negative c i) v a := by
  intro b hb db
  by_contra neq
  have h1 : diff c d a ∈ signs c d v:=List.mem_map_of_mem ha
  have h2 : diff c d b ∈ signs c d v:=List.mem_map_of_mem hb
  have ne : diff c d a ≠ diff c d b:=fun e=>neq (congrArg Prod.fst e).symm
  simp only [hit,Nat.testBit_and,Bool.and_eq_true,once,Nat.testBit_xor] at h
  have first:=multiOne h1 i.val h.1.1
  have second:=multiTwo h1 h2 ne i.val h.1.1 ((diffBit good d (va b hb) i).2 db)
  simp [first,second] at h
theorem entryMark {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (marked c (once (signs c d v)) (diff c d a)).2.testBit i.val=true) :
    M d (positive c i) (negative c i) v a := by
  let u:=hit c (once (signs c d v)) (diff c d a)
  simp only [marked,Nat.testBit_and,Bool.and_eq_true] at h
  let p : Fin c.h:=⟨(positive c i).val,(hg.2.2.2.2.2.1 i).1⟩
  let n : Fin c.w:=⟨(negative c i).val,(hg.2.2.2.2.2.1 i).2⟩
  have rp:=locate (linSweep _) (hg.2.2.1 i).1 (hg.2.2.2.2.2.2.1 p) (hitBound c (once (signs c d v)) (diff c d a)) h.1.1.2
  have rn:=locate (linSweep _) (hg.2.2.1 i).2 (hg.2.2.2.2.2.2.2 n) (hitBound c (once (signs c d v)) (diff c d a)) h.1.2
  refine ⟨(diffBit hg d (va a ha) i).1 h.1.1.1,?_,?_⟩
  · obtain ⟨j,hj,hp⟩:=rp
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : positive c j'=positive c i:=Fin.ext (hg.2.2.2.1 j' p hp)
    exact ⟨negative c j',eq ▸ uniq hg va ha j' hj⟩
  · obtain ⟨j,hj,hn⟩:=rn
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : negative c j'=negative c i:=Fin.ext (hg.2.2.2.2.1 j' n hn)
    exact ⟨positive c j',eq ▸ uniq hg va ha j' hj⟩
theorem entryIds (c d v) : (entries c d v).map Prod.fst=v := by
  simp [entries,signs,marked,diff,Function.comp_def]
theorem hasEntry {c d v a} (ha : a∈entries c d v) : a.1∈v := by
  rw [←entryIds c d v];exact List.mem_map_of_mem ha
theorem overlap {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a)
    {x y} (hx : x∈entries c d v) (hy : y∈entries c d v) (non : x.2 &&& y.2≠0) :
    ∃p n,M d p n v x.1 ∧ M d p n v y.1 := by
  obtain ⟨zx,ax,rfl⟩:=List.mem_map.mp hx
  obtain ⟨zy,ay,rfl⟩:=List.mem_map.mp hy
  obtain ⟨ax',av,rfl⟩:=List.mem_map.mp ax
  obtain ⟨ay',bv,rfl⟩:=List.mem_map.mp ay
  obtain ⟨j,h⟩:=Nat.exists_testBit_of_ne_zero non
  rw [Nat.testBit_and,Bool.and_eq_true] at h
  have u:=h.1
  simp only [marked,Nat.testBit_and,Bool.and_eq_true,roofBit] at u
  let i : Fin (area c):=⟨j,of_decide_eq_true u.2⟩
  exact ⟨positive c i,negative c i,entryMark hg va av i h.1,entryMark hg va bv i h.2⟩

theorem testSigned {c : Chart} (hg : good c) {k m v} (hm : m≤k) (nd : v.Nodup) (h : BL m v.toFinset) :
    test c true (k+2-v.length) v=true := by
  obtain ⟨t,l⟩:=h.expand
  have val : ∀a∈v,Valid a:=fun a ha=>(h.forms _ (List.mem_toFinset.mpr ha)).1.1
  obtain ⟨n,⟨f,bd,ok⟩,le⟩:=freeColors h
  have sz : v.toFinset.card=v.length:=List.toFinset_card_of_nodup nd
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_and,roofBit]
    by_cases hi : i<area c
    · let z : Fin (area c):=⟨i,hi⟩
      obtain ⟨a,ha,hit⟩:=pair_sep l (positive c z) (negative c z)
      have av:=List.mem_toFinset.mp ha
      have hit':=multiOne (List.mem_map_of_mem (f:=diff c true) av) i ((diffBit hg true (val a av) z).2 hit)
      simpa [hi,signs] using hit'
    · simp [hi]
  · change paint (k+2-v.length) (entries c true v) _ =true
    apply paint_ok _ f
    · rwa [entryIds]
    · intro a ha;have := bd _ (List.mem_toFinset.mpr (hasEntry ha));omega
    · simp
    · intro a ha b hb ne eq
      by_contra non
      obtain ⟨p,q,x,y⟩:=overlap hg val ha hb non
      apply ok _ (List.mem_toFinset.mpr (hasEntry ha)) _ (List.mem_toFinset.mpr (hasEntry hb)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_31225_aux.Seven.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_31225_aux.Seven.Conflict1868.Unique] using y⟩
end QuickQ
end
open Basis1868 Free1868 FreeSearch1868 Cuts1868 Check2516 Exact8403 Projection8403
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def chart : QuickQ.Chart := ⟨64, 16, [(false, 0, 0xffffffffffffffff), (true, 480, 0xffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff), (true, 240, 0xffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff), (true, 120, 0xff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff), (true, 60, 0xf000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f), (true, 30, 0x300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003), (true, 15, 0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)], [(false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)], [(false, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)], [(false, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma chart_valid : QuickQ.good chart := by
  apply QuickQ.goodOfCompact
  unfold QuickQ.compactGood
  decide +kernel

def search : ℕ → List Sig → Bool
  | 0, v => baseTest v
  | n + 1, v =>
    QuickQ.test chart true (n + 3 - v.length) v &&
      (baseTest v || scanPairs (pairB v (search n)) v)

lemma search_complete (n : ℕ) (v : List Sig) (nd : v.Nodup) (k : ℕ) (lim : k ≤ n)
    (h : BL k v.toFinset) : search n v = true := by
  induction n generalizing v k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero lim
    subst k
    have hs : v.toFinset = {can target} := by
      generalize eq : v.toFinset = S at h
      cases h
      rfl
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using hs))
    simp [search, baseTest, hv]
  | succ n ih =>
    have pass := QuickQ.testSigned chart_valid lim nd h
    simp only [search, show n+3-v.length = n+1+2-v.length by omega, pass, true_and]
    exact oneStep h n lim v nd rfl (search n) (fun w nw j lj proof => ih w nw j lj proof)

lemma projectedFlip (H : SigHom) (s : Bool) {a : Sig} (valid : Valid a) {q : ℕ} {U : Finset Sig}
    (h : Projection8403.Can q ((insert (flip s a) U).image H.fn)) :
    Projection8403.Can q ((insert a U).image H.fn) := by
  cases s
  · exact h
  · exact pushNeg valid h

lemma constantFlip (H : SigHom) (s : Bool) {a : Sig} (valid : Valid a) :
    constant (H.fn (flip s a)) ↔ constant (H.fn a) := by
  cases s
  · rfl
  · change constant (H.fn (neg a)) ↔ constant (H.fn a)
    rw [H.hneg valid, constant_neg (H.valid a)]

lemma projectedBlend (H : SigHom) (d s t : Bool) {a b : Sig} (ha : Valid a) (hb : Valid b)
    {q : ℕ} {U : Finset Sig}
    (tail : Projection8403.Can q ((insert (blend d s t a b) U).image H.fn)) :
    Projection8403.Can (q + if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1)
      ((insert a (insert b U)).image H.fn) := by
  let x := flip s a
  let y := flip t b
  let z := bin d x y
  have vz : Valid z := valid_bin (vf s ha) (vf t hb)
  have unflipOutput : Projection8403.Can q ((insert z U).image H.fn) :=
    projectedFlip H (sign z) vz tail
  have prev := pushBin d unflipOutput
  change Projection8403.Can
    (q + if constant (H.fn x) ∨ constant (H.fn y) then 0 else 1)
    ((insert x (insert y U)).image H.fn) at prev
  simp only [x, y, constantFlip H s ha, constantFlip H t hb] at prev
  have p := projectedFlip H s ha prev
  rw [Finset.insert_comm] at p ⊢
  exact projectedFlip H t hb p

lemma projectedBLCan (H : SigHom) {n : ℕ} {V : Finset Sig} (h : BL n V) :
    ∃ q, q + mass H V ≤ n ∧ Projection8403.Can q (V.image H.fn) := by
  obtain ⟨t, live⟩ := h.expand
  obtain ⟨q, le, projected⟩ := Projection8403.projected live H
  exact ⟨q, by omega, projected⟩

abbrev Restrictions := List (SigHom × ℕ)

def spentAt (H : SigHom) (a b : Sig) : ℕ :=
  if constant (H.fn a) ∨ constant (H.fn b) then 1 else 0

def updateLoss (rs : Restrictions) (a b : Sig) : Restrictions :=
  rs.map fun (H, u) => (H, u + spentAt H a b)

def preserve (rs : Restrictions) (elapsed : ℕ) (basis : Finset Sig) : Prop :=
  ∀ H u, (H,u) ∈ rs → ∀ q, Projection8403.Can q (basis.image H.fn) → 10 + u ≤ q + elapsed

def withinLoss (rs : Restrictions) (basis : Finset Sig) : Bool :=
  rs.all fun (H, u) => decide (u + mass H basis ≤ 1)

lemma lossOK {rs : Restrictions} {elapsed n k : ℕ} {B : Finset Sig}
    (traceBound : preserve rs elapsed B) (eq : elapsed + n = 11) (fits : k ≤ n)
    (h : BL k B) : withinLoss rs B = true := by
  apply List.all_eq_true.mpr
  rintro ⟨H,u⟩ hm
  obtain ⟨q, le, valid⟩ := projectedBLCan H h
  have lb := traceBound H u hm q valid
  exact decide_eq_true (by omega)

lemma preserveTail {rs : Restrictions} {elapsed : ℕ} {U : Finset Sig} {a b : Sig}
    (ha : Valid a) (hb : Valid b) (d s t : Bool)
    (bound : preserve rs elapsed (insert a (insert b U))) :
    preserve (updateLoss rs a b) (elapsed + 1) (insert (blend d s t a b) U) := by
  intro H w hw q h
  obtain ⟨⟨H',u⟩, hm, eq⟩ := List.mem_map.mp hw
  obtain ⟨same, lossEq⟩ := Prod.mk.inj eq
  subst H'
  have prev := projectedBlend H d s t ha hb h
  have lb := bound H u hm _ prev
  rw [← lossEq]
  unfold spentAt
  split <;> simp_all <;> omega

lemma resourceStep {rs : Restrictions} {elapsed k S} (l : BL k S) (m : ℕ) (hm : k ≤ m+1)
    (v : List Sig) (nd : v.Nodup) (rep : v.toFinset = S) (bound : preserve rs elapsed S)
    (go : Restrictions → List Sig → Bool)
    (hyp : ∀ r w, w.Nodup → ∀ j ≤ m, BL j w.toFinset → preserve r (elapsed+1) w.toFinset →
      go r w = true) :
    (baseTest v || scanPairs (fun a b => pairB v (go (updateLoss rs a b)) a b) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr
    right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (hx : Valid x) (hy : Valid y)
        (id : blend false u w x y = z) (eqS : v.toFinset = insert x (insert y U)) :
        pairB v (go (updateLoss rs x y)) x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      have pr : preserve rs elapsed (insert x (insert y U)) := by rwa [← eqS, rep]
      have pt := preserveTail hx hy false u w pr
      rw [id] at pt
      exact hyp _ _ nw j (by omega) (pw ▸ tail) (pw ▸ pt)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w ha.1 hb.1 id rep
    · exact yes b a w u hb.1 ha.1 ((blend_symm false w u b a).trans id)
        (by rwa [Finset.insert_comm b a])

lemma resourceStepIndexed {rs : Restrictions} {elapsed k S} (l : BL k S) (m : ℕ) (hm : k ≤ m+1)
    (v : List Sig) (nd : v.Nodup) (rep : v.toFinset = S) (bound : preserve rs elapsed S)
    (go : Sig → Sig → List Sig → Bool)
    (hyp : ∀ a b w, w.Nodup → ∀ j ≤ m, BL j w.toFinset →
      preserve (updateLoss rs a b) (elapsed+1) w.toFinset → go a b w = true) :
    (baseTest v || scanPairs (fun a b => pairB v (go a b) a b) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr
    right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (hx : Valid x) (hy : Valid y)
        (id : blend false u w x y = z) (eqS : v.toFinset = insert x (insert y U)) :
        pairB v (go x y) x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      have pr : preserve rs elapsed (insert x (insert y U)) := by rwa [← eqS, rep]
      have pt := preserveTail hx hy false u w pr
      rw [id] at pt
      exact hyp _ _ _ nw j (by omega) (pw ▸ tail) (pw ▸ pt)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w ha.1 hb.1 id rep
    · exact yes b a w u hb.1 ha.1 ((blend_symm false w u b a).trans id)
        (by rwa [Finset.insert_comm b a])

namespace FastMask10536

def covers (f : Fin 64 → Fin 64) (mask : Nat) :=
  (∀ j, mask.testBit (f j).val = true) ∧
    (∀ j, mask.testBit j = true → ∃ k : Fin 64, (f k).val = j)

lemma maskZero {f : Fin 64 → Fin 64} {m : ℕ} (h : covers f m) (v : ℕ) :
    Basis1868.reindex f v = 0 ↔ v &&& m = 0 := by
  constructor
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hm : m.testBit j
    · simp [hm]
    · obtain ⟨k, ek⟩ := h.2 j hm
      have eq := congrArg (fun a : ℕ => a.testBit k.val) he
      rw [Basis1868.reindex_testBit, dif_pos k.isLt, Nat.zero_testBit, ek] at eq
      simp [eq]
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Basis1868.reindex_testBit, Nat.zero_testBit]
    split
    · rename_i hj
      have eq := congrArg (fun a : ℕ => a.testBit (f ⟨j,hj⟩).val) he
      simpa only [Nat.testBit_and, Nat.zero_testBit, h.1, Bool.and_true] using eq
    · rfl

lemma maskOne {f : Fin 64 → Fin 64} {m : ℕ} (h : covers f m) (v : ℕ) :
    Basis1868.reindex f v = top ↔ v &&& m = m := by
  constructor
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases hm : m.testBit j
    · simp [hm]
    · obtain ⟨k, ek⟩ := h.2 j hm
      have eq := congrArg (fun a : ℕ => a.testBit k.val) he
      rw [Basis1868.reindex_testBit, dif_pos k.isLt, Basis1868.testBit_top, ek,
        decide_eq_true k.isLt] at eq
      simp [eq, hm]
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Basis1868.reindex_testBit, Basis1868.testBit_top]
    split
    · rename_i hj
      have eq := congrArg (fun a : ℕ => a.testBit (f ⟨j,hj⟩).val) he
      simpa only [Nat.testBit_and, h.1, Bool.and_true, decide_eq_true hj] using eq
    · rename_i hj
      simp [hj]

structure Restriction where
  p : Fin 64 → Fin 64
  n : Fin 64 → Fin 64
  pm : ℕ
  nm : ℕ
  pc : covers p pm
  nc : covers n nm

def Restriction.hom (r : Restriction) : SigHom := pairHom r.p r.n

def const (r : Restriction) (a : Sig) :=
  (a.1 &&& r.pm == 0 && a.2 &&& r.nm == 0) ||
  (a.1 &&& r.pm == r.pm && a.2 &&& r.nm == r.nm)

lemma const_eq (r : Restriction) (a : Sig) :
    const r a = decide (Projection8403.constant (r.hom.fn a)) := by
  apply Bool.eq_iff_iff.mpr
  simp [const, Projection8403.constant, Restriction.hom, pairHom, zero, one, Prod.ext_iff,
    maskZero r.pc, maskZero r.nc, maskOne r.pc, maskOne r.nc]

def coversFinite (f : Fin 64 → Fin 64) (mask : ℕ) :=
  (∀ j, mask.testBit (f j).val = true) ∧ mask ≤ top ∧
    (∀ j : Fin 64, mask.testBit j.val = true → ∃ k : Fin 64, f k = j)

lemma coversFrom {f : Fin 64 → Fin 64} {mask : ℕ} (h : coversFinite f mask) :
    covers f mask := by
  refine ⟨h.1,?_⟩
  intro j hj
  have up : j < 64 := by
    by_contra! bad
    exact Bool.noConfusion ((valid1_of_le_top h.2.1 j bad).symm.trans hj)
  obtain ⟨k,hk⟩ := h.2.2 ⟨j,up⟩ hj
  exact ⟨k,congrArg Fin.val hk⟩

lemma noCan {q : ℕ} {B : Finset Sig} {w : List Sig}
    (img : B.image can ⊆ insert zero w.toFinset) (need : necessary w)
    (no : ∀ k ≤ 9, ¬ BL k w.toFinset)
    (h : Projection8403.Can q B) : 10 ≤ q := by
  obtain ⟨k,t,S,le,l,sub⟩ := h
  obtain ⟨j,T,jle,live,sv⟩ := compress l
  have incl : T ⊆ insert zero w.toFinset :=
    (sv.trans (Finset.image_mono _ sub)).trans img
  have incl' : T ⊆ w.toFinset := by
    intro b hb
    exact (Finset.mem_insert.mp (incl hb)).resolve_left (live.forms b hb).1.2.1
  obtain ⟨a,p⟩ := live.expand
  have eq := allNeeded p incl' need
  by_contra! small
  exact no j (by omega) (eq ▸ live)

end FastMask10536

open FastMask10536

abbrev FastResources := List (Restriction × ℕ)

def underlying (rs : FastResources) : Restrictions :=
  rs.map fun (r, u) => (r.hom,u)

def fastUpdate (rs : FastResources) (a b : Sig) : FastResources :=
  rs.map fun (r, u) => (r,u + if const r a || const r b then 1 else 0)

lemma fastUpdate_eq (rs : FastResources) (a b : Sig) :
    underlying (fastUpdate rs a b) = updateLoss (underlying rs) a b := by
  induction rs with
  | nil => rfl
  | cons entry rs ih =>
    obtain ⟨r,u⟩ := entry
    simp only [underlying,fastUpdate,updateLoss,List.map_cons,spentAt,const_eq,
      Bool.or_eq_true,decide_eq_true_eq,List.cons.injEq,true_and] at ih ⊢
    exact ih

def fastWithin (rs : FastResources) (w : List Sig) : Bool :=
  rs.all fun (r, u) => decide (u + w.countP (const r) ≤ 1)

lemma maskMass (r : Restriction) {w : List Sig} (nd : w.Nodup) :
    Projection8403.mass r.hom w.toFinset = w.countP (const r) := by
  calc
    _ = (w.filter (const r)).toFinset.card := by
      simp [Projection8403.mass, List.toFinset_filter, const_eq]
    _ = _ := by rw [List.toFinset_card_of_nodup (List.Nodup.filter _ nd), ← List.countP_eq_length_filter]

lemma fastWithin_eq (rs : FastResources) {w : List Sig} (nd : w.Nodup) :
    fastWithin rs w = withinLoss (underlying rs) w.toFinset := by
  induction rs with
  | nil => rfl
  | cons entry rs ih =>
    obtain ⟨r,u⟩ := entry
    simp [fastWithin,underlying,withinLoss,maskMass _ nd] at ih ⊢
    rw [ih]

def fullRaw : List Sig := raw8.map can
lemma fullNeeded : necessary fullRaw := needFrom (pn := [(0, 4), (3, 6), (0, 1), (2, 1), (7, 2), (15, 1), (29, 1)]) (by decide) (by decide +kernel)

def pp0 : Array Nat := #[3, 6, 7, 9, 11, 13, 14, 16, 18, 20, 21, 23, 24, 26, 27, 28, 30, 33, 34, 36, 37, 38, 40, 41, 42, 44, 45, 46, 47]
def nn0 : Array Nat := #[0, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]
def fp0 (j : Fin 64) : Fin 64 := Fin.ofNat 64 pp0[j.val % 29]!
def fn0 (j : Fin 64) : Fin 64 := Fin.ofNat 64 nn0[j.val % 13]!
def h0 : SigHom := pairHom fp0 fn0
def r0 : FastMask10536.Restriction := ⟨fp0, fn0, 0xf7765db56ac8, 0xfdf5,
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel),
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel)⟩

def minor0 : List Sig := [(0x23b69aa91db4d548, 0xff5ffaffd7febff5), (0x68924a6b4492535a, 0x82c41620b105882c), (0x72dc6c7396e3639c, 0xf4ffa7fd3fe9ff4f), (0xf23c1c0f91e0e07c, 0x2c01600b005802c0), (0x3c01ff01e00ff80, 0x3009804c02601300), (0x3ffe0001fff0000, 0xc00e007003801c00)]
lemma needed0 : necessary minor0 := needFrom
  (pn := [(0, 4), (3, 6), (0, 1), (2, 1), (7, 1), (16, 1)]) (by decide) (by decide +kernel)
lemma images0 : ((fullRaw.toFinset.image h0.fn).image can) ⊆ insert zero minor0.toFinset := by
  decide +kernel

def pp1 : Array Nat := #[2, 12, 0, 9, 10, 5, 14, 29, 38, 39, 34, 35, 42, 32, 41, 37, 15, 25, 21, 22, 28, 18, 19, 27, 24, 43, 47, 46, 45]
def nn1 : Array Nat := #[0, 1, 8, 9, 6, 10, 4, 7, 13, 14, 11, 12, 15]
def fp1 (j : Fin 64) : Fin 64 := Fin.ofNat 64 pp1[j.val % 29]!
def fn1 (j : Fin 64) : Fin 64 := Fin.ofNat 64 nn1[j.val % 13]!
def h1 : SigHom := pairHom fp1 fn1
def r1 : FastMask10536.Restriction := ⟨fp1, fn1, 0xeeed3b6cd625, 0xffd3,
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel),
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel)⟩

lemma images1 : ((fullRaw.toFinset.image h1.fn).image can) ⊆ insert zero minor0.toFinset := by
  decide +kernel

def pp3 : Array Nat := #[0, 1, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20, 25, 26, 27, 29, 30, 31, 32, 33, 38, 39, 40, 41, 43, 44, 45, 47]
def nn3 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15]
def fp3 (j : Fin 64) : Fin 64 := Fin.ofNat 64 pp3[j.val % 29]!
def fn3 (j : Fin 64) : Fin 64 := Fin.ofNat 64 nn3[j.val % 13]!
def h3 : SigHom := pairHom fp3 fn3
def r3 : FastMask10536.Restriction := ⟨fp3, fn3, 0xbbc3ee1f8f83, 0xfb3f,
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel),
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel)⟩

def minor3 : List Sig := [(0x53b65aaa9db2d554, 0xf75fbafdd7eebf75), (0x3892ca69c496534e, 0x2c01600b005802c), (0x32dcec7196e7638c, 0x7cfbe7df3ef9f7cf), (0xf23c1c0f91e0e07c, 0x2c01600b005802c0), (0x3c01ff01e00ff80, 0x3009804c02601300), (0x3ffe0001fff0000, 0xc00e007003801c00)]
lemma needed3 : necessary minor3 := needFrom
  (pn := [(0, 4), (2, 6), (0, 1), (2, 2), (7, 1), (16, 1)]) (by decide) (by decide +kernel)
lemma images3 : ((fullRaw.toFinset.image h3.fn).image can) ⊆ insert zero minor3.toFinset := by
  decide +kernel

def pp5 : Array Nat := #[34, 37, 38, 9, 41, 42, 14, 29, 0, 32, 2, 35, 5, 39, 10, 12, 30, 33, 3, 36, 6, 7, 40, 11, 13, 31, 1, 4, 8]
def nn5 : Array Nat := #[0, 13, 4, 14, 6, 7, 8, 10, 1, 9, 2, 5, 3]
def fp5 (j : Fin 64) : Fin 64 := Fin.ofNat 64 pp5[j.val % 29]!
def fn5 (j : Fin 64) : Fin 64 := Fin.ofNat 64 nn5[j.val % 13]!
def h5 : SigHom := pairHom fp5 fn5
def r5 : FastMask10536.Restriction := ⟨fp5, fn5, 0x7ffe0007fff, 0x67ff,
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel),
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel)⟩

lemma images5 : ((fullRaw.toFinset.image h5.fn).image can) ⊆ insert zero minor0.toFinset := by
  decide +kernel

def pp6 : Array Nat := #[21, 28, 18, 9, 27, 24, 14, 16, 7, 26, 3, 23, 13, 20, 11, 6, 15, 25, 2, 22, 12, 0, 19, 10, 5, 17, 8, 4, 1]
def nn6 : Array Nat := #[0, 11, 8, 12, 6, 10, 4, 7, 2, 5, 1, 9, 3]
def fp6 (j : Fin 64) : Fin 64 := Fin.ofNat 64 pp6[j.val % 29]!
def fn6 (j : Fin 64) : Fin 64 := Fin.ofNat 64 nn6[j.val % 13]!
def h6 : SigHom := pairHom fp6 fn6
def r6 : FastMask10536.Restriction := ⟨fp6, fn6, 0x1fffffff, 0x1fff,
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel),
  FastMask10536.coversFrom (by unfold FastMask10536.coversFinite; decide +kernel)⟩

lemma images6 : ((fullRaw.toFinset.image h6.fn).image can) ⊆ insert zero minor0.toFinset := by
  decide +kernel
def reductions : Restrictions := [(h0, 0), (h1, 0), (h3, 0), (h5, 0), (h6, 0)]

def fastReductions : FastResources := [(r0, 0), (r1, 0), (r3, 0), (r5, 0), (r6, 0)]

def sigKey (s : Sig) := s.1 * 2^64 + s.2

def insertSignal (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b :: bs => if sigKey a ≤ sigKey b then a :: b :: bs else b :: insertSignal a bs

def sortSignals : List Sig → List Sig
  | [] => []
  | a :: bs => insertSignal a (sortSignals bs)

lemma insertSignalPerm (a : Sig) (w : List Sig) : (insertSignal a w).Perm (a :: w) := by
  induction w with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : sigKey a ≤ sigKey b
    · simp [insertSignal, h]
    · exact (by simpa [insertSignal, h] using (List.Perm.cons b ih).trans (.swap a b bs))

lemma sortPerm (l : List Sig) : (sortSignals l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertSignalPerm a (sortSignals bs)).trans (.cons a ih)

lemma sortFinset (l : List Sig) : (sortSignals l).toFinset = l.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (sortPerm l).mem_iff (a := a)

lemma liveCard {n : ℕ} {S : Finset Sig} (live : BL n S) : S.card ≤ n + 1 := by
  induction live with
  | stop => simp
  | @step k U a b d s t ha hb ca cb hab fresh tail ih =>
    have hr : blend d s t a b ∉ U := by
      intro mem
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    rw [Finset.card_insert_of_notMem hr] at ih
    have ha := Finset.card_insert_le (s := insert b U) (a := a)
    have hb := Finset.card_insert_le (s := U) (a := b)
    omega

open QuickQ ColorSearch1868 FreeSearch1868 Cuts1868
namespace PaintQ
abbrev Item:=Sig×Nat
def onePaint : List Item→Nat→Bool
  | [],_=>true
  | x::xs,a=>(a &&& x.2)==0 && onePaint xs (a ||| x.2)
def twoPaint : List Item→Nat→Nat→Bool
  | [],_,_=>true
  | x::xs,a,b=>((a &&& x.2)==0 && twoPaint xs (a ||| x.2) b) ||
        ((b &&& x.2)==0 && twoPaint xs a (b ||| x.2))
lemma oneEq (xs : List Item) (f : Nat→Nat) : paint 1 xs f=onePaint xs (f 0) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 1=[0] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      onePaint,ite_true]
lemma twoEq (xs : List Item) (f : Nat→Nat) : paint 2 xs f=twoPaint xs (f 0) (f 1) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 2=[0,1] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      twoPaint,ite_true,Nat.reduceEqDiff,ite_false]
def color (n : Nat) (w : List Item) := if n=1 then onePaint w 0 else if n=2 then twoPaint w 0 0 else paint n w (fun _=>0)
lemma colorEq (n : Nat) (w : List Item) : color n w=paint n w (fun _=>0) := by
  unfold color
  split
  next h=>subst n;exact (oneEq w (fun _=>0)).symm
  next=>split
        next h=>subst n;exact (twoEq w (fun _=>0)).symm
        next=>rfl
def shade (c : Chart) (once : Nat) (x : Item) : Item :=
  let h:=hit c once x
  if h=0 then (x.1,0) else (x.1,x.2 &&& sweep c.fillP h &&& sweep c.fillN h &&& roof c)
lemma shadeEq (c : Chart) (once : Nat) (x : Item) : shade c once x=marked c once x := by
  simp only [shade,marked]
  split
  next h=>rw [h,(linSweep _).1];simp
  next=>rfl
def testRows (c : Chart) (k : Nat) (s : List Item) :=
  let g:=PEqualNP.Outside.L_meta_31225_aux.Seven.Board1868.mult s
  (g.1 &&& roof c)==roof c && color k (s.map (shade c (g.1 ^^^ g.2)))
lemma rowsMap (c d k v) : testRows c k (v.map (diff c d))=test c d k v := by
  simp only [testRows,test,signs,colorEq,funext (shadeEq _ _)]
end PaintQ

open PaintQ
namespace PackQ
def pass (c : Chart) (k : Nat) (hit : List Sig→Bool) (v : List Item) :=
  v.length≤k+1 && testRows c (k+2-v.length) v && !(hit (v.map Prod.fst))
def plain (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) :=
  v.length≤k+1 && test c d (k+2-v.length) v && !(hit v)
lemma passMap (c d k hit v) : pass c k hit (v.map (diff c d))=plain c d k hit v := by
  simp only [pass,plain,List.length_map,rowsMap,List.map_map]
  have id : Prod.fst ∘ diff c d=id:=rfl
  rw [id,List.map_id]
def selected (a b : Sig) (l r : Bool) (v : List Item) := v.filter fun x=>keep a b l r x.1
lemma selectMap (c d a b l r) (v : List Sig) :
    selected a b l r (v.map (diff c d))=(v.filter (keep a b l r)).map (diff c d) := by
  simp only [selected,List.filter_map]
  rfl
def choices (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (w : List Item) (a b z : Sig) :=
  let val:=diff c d z
  [false,true].any fun l=>[false,true].any fun r=>pass c k hit (val::selected a b l r w)
lemma choicesMap (c d k hit v a b z) : choices c d k hit (v.map (diff c d)) a b z=
    [false,true].any (fun l=>[false,true].any fun r=>plain c d k hit (next v a b z l r)) := by
  simp only [choices,selectMap,next,← List.map_cons,passMap]
def forkS (c : Chart) (k : Nat) (hit : List Sig→Bool) (ws : List Item) (v : List Sig) (a b : Item) :=
  [false,true].any fun s=>[false,true].any fun t=>
    let z:=blend false s t a.1 b.1
    z != zero && !(v.contains z) && choices c true k hit ws a.1 b.1 z
lemma forkSMap (c k hit v a b) :
    forkS c k hit (v.map (diff c true)) v (diff c true a) (diff c true b)=pairB v (plain c true k hit) a b := by
  simp only [forkS,pairB,oneB,choicesMap];rfl
lemma scanMap {α β : Type} (f : α→β) (u : β→β→Bool) (g : α→α→Bool)
    (all : ∀a b,u (f a) (f b)=g a b) (v : List α) :
    scanPairs u (v.map f)=scanPairs g v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [scanPairs,List.any_map,Function.comp_def,all,ih]
end PackQ

open PackQ
namespace GroupQ
def passes (c : Chart) (lookup : List Sig→Bool) (colors len : Nat) (rest : List Item) (g : Sig) (a : Item) :=
  let cover:=g.1 ||| a.2
  (cover &&& roof c)==roof c &&
    let one:=cover ^^^ (g.2 ||| (g.1 &&& a.2))
    color colors (shade c one a::rest.map (shade c one)) && !lookup (a.1::rest.map Prod.fst)
def arrangements (c : Chart) (k : Nat) (lookup : List Sig→Bool) (ws : List Item) (a b : Sig) (zs : List Item) :=
  [false,true].any fun l=>[false,true].any fun r=>
    let rest:=selected a b l r ws
    let m:=rest.length+1
    m≤k+1 && zs.any (passes c lookup (k+2-m) m rest (Board1868.mult rest))
lemma swapOrder {α β : Type} (xs : List α) (ys : List β) (p : α→β→Bool) :
    (xs.any fun x=>ys.any (p x))=(ys.any fun y=>xs.any (fun x=>p x y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨x,hx,y,hy,h⟩ <;> exact ⟨y,hy,x,hx,h⟩
lemma passHead (c k lookup rest a) : pass c k lookup (a::rest)=
    (rest.length+1≤k+1 && passes c lookup (k+2-(rest.length+1)) (rest.length+1) rest (Board1868.mult rest) a) := by
  simp only [pass,testRows,passes,List.length_cons,List.map_cons,Board1868.mult,Bool.and_assoc]
lemma arrangements_eq (c d k lookup ws a b) (zs : List Sig) :
    arrangements c k lookup ws a b (zs.map (diff c d))=
    zs.any (choices c d k lookup ws a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [arrangements,choices,List.any_eq_true,List.any_map,Function.comp_apply,
    passHead,Bool.and_eq_true,List.mem_map,exists_exists_and_eq_and]
  constructor
  · rintro ⟨l,hl,r,hr,bnd,z,hz,h⟩
    exact ⟨z,hz,l,hl,r,hr,bnd,h⟩
  · rintro ⟨z,hz,l,hl,r,hr,bnd,h⟩
    exact ⟨l,hl,r,hr,bnd,z,hz,h⟩
def generators (d : Bool) (a b : Sig) : List Sig :=
  if d then [false,true].flatMap (fun s=>[false,true].map (fun t=>blend false s t a b))
  else [bin false a b,bin true a b]
def fresh (d : Bool) (v : List Sig) (z : Sig) := z != zero && (d || z != one) && !(v.contains z)
def fork (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) (ws : List Item) (a b : Item) :=
  let zs:=(generators d a.1 b.1).filter (fresh d v)
  arrangements c k hit ws a.1 b.1 (zs.map (diff c d))
lemma forkSEQ (c k hit v ws a b) : fork c true k hit v ws a b=forkS c k hit ws v a b := by
  simp only [fork,arrangements_eq,generators,ite_true,forkS,List.any_filter,List.any_flatMap,List.any_map,
    Function.comp_def,fresh,Bool.true_or,Bool.and_true,Bool.and_assoc]
end GroupQ
abbrev Loss := List Nat
abbrev Env := Bool
abbrev Entry := Loss × List Sig

def attachLoss (e : Env) (u : Loss) : FastResources :=
  if e then
  [(r0,u.getD 0 0),(r1,u.getD 1 0),(r3,u.getD 2 0),(r5,u.getD 3 0),(r6,u.getD 4 0)] else []

def resources (e : Env) (u : Loss) : Restrictions := underlying (attachLoss e u)

def addLoss (e : Env) (u : Loss) (a b : Sig) : Loss :=
  (fastUpdate (attachLoss e u) a b).map Prod.snd

lemma lossStep (e : Env) (u : Loss) (a b : Sig) :
    resources e (addLoss e u a b) = updateLoss (resources e u) a b := by
  cases e
  · rfl
  · change underlying (fastUpdate (attachLoss true u) a b) = updateLoss (underlying (attachLoss true u)) a b
    exact fastUpdate_eq _ _ _

def within (e : Env) (u : Loss) (w : List Sig) : Bool := fastWithin (attachLoss e u) w

lemma within_eq (e : Env) (u : Loss) {w : List Sig} (nd : w.Nodup) :
    within e u w = withinLoss (resources e u) w.toFinset := fastWithin_eq _ nd

def tableBucket (w : List Sig) : Nat :=
  (w.foldl (fun a s => a + s.1 + s.2) 0) % 32

def tableHit (w : Entry) (tab : Nat → List Entry) : Bool :=
  (tab (tableBucket w.2)).contains w

def levelMem (w : Entry) (tab : Nat → List Entry) : Prop :=
  ∃ b, w ∈ tab b

lemma hit_mem {w : Entry} {tab : Nat → List Entry} (h : tableHit w tab = true) :
    levelMem w tab := ⟨_, List.contains_iff_mem.mp h⟩

def absentR (c : QuickQ.Chart) (e : Env) (tab : Nat → List Entry) (n : Nat)
    (u : Loss) (w : List Sig) : Bool :=
  PackQ.plain c true n (fun v => tableHit (u,sortSignals v) tab || !within e u v) w

def testRow (c : QuickQ.Chart) (env : Env) (tab : Nat → List Entry)
    (n : Nat) (p : Entry) : Bool :=
  let ws := p.2.map (QuickQ.diff c true)
  !(baseTest p.2 || scanPairs
    (fun a b =>
      let u := addLoss env p.1 a.1 b.1
      GroupQ.fork c true n
        (fun v => tableHit (u,sortSignals v) tab || !within env u v) p.2 ws a b) ws)

lemma testRow_eq (c : QuickQ.Chart) (env : Env) (tab : Nat → List Entry)
    (n : Nat) (p : Entry) :
    testRow c env tab n p =
      !(baseTest p.2 || scanPairs (fun a b => pairB p.2
        (absentR c env tab n (addLoss env p.1 a b)) a b) p.2) := by
  dsimp only [testRow]
  rw [PackQ.scanMap]
  intro a b
  rw [GroupQ.forkSEQ]
  exact PackQ.forkSMap _ _ _ _ _ _

def verifiedR (env : Env) (cap n : Nat) (tab : Nat → List Entry) :=
  ∀ u w, levelMem (u,w) tab → w.Nodup →
    preserve (resources env u) (cap - n) w.toFinset →
    ∀ j ≤ n, ¬ BL j w.toFinset

lemma emptyR (env : Env) (cap : Nat) : verifiedR env cap 0 (fun _ => []) := by
  intro u w h
  obtain ⟨i, hi⟩ := h
  simp at hi

lemma checkedTier (c : QuickQ.Chart) (cg : QuickQ.good c) (e : Env)
    {cap n : ℕ} (fits : n + 1 ≤ cap) (fullBudget : e = true → cap = 11) {tab next : Nat → List Entry}
    (prev : verifiedR e cap n tab)
    (checked : ∀ p, levelMem p next → testRow c e tab n p = true) :
    verifiedR e cap (n+1) next := by
  intro u v hv nd bound j lj live
  have ne := testRow_eq c e tab n (u,v)
  have fail := ne ▸ checked _ hv
  have elapsed : cap-(n+1)+1 = cap-n := by omega
  have nextOK : ∀ r w, w.Nodup → ∀ k ≤ n, BL k w.toFinset →
      preserve r (cap-(n+1)+1) w.toFinset →
      ∀ a b, r = updateLoss (resources e u) a b →
        absentR c e tab n (addLoss e u a b) w = true := by
    intro r w wn k lim hw ri a b hr
    let tags := addLoss e u a b
    have hres : resources e tags = r := (lossStep e u a b).trans hr.symm
    have wp : within e tags w = true := by
      cases h : e
      · rfl
      · have hc := fullBudget h
        have same : resources true tags = r := by rw [← h]; exact hres
        rw [within_eq _ _ wn,same]
        exact lossOK ri (by omega) lim hw
    have missing : tableHit (tags,sortSignals w) tab = false := by
      cases hh : tableHit (tags,sortSignals w) tab
      · rfl
      · have eq := sortFinset w
        have sorted := (sortPerm w).nodup_iff.mpr wn
        apply False.elim
        exact prev _ _ (hit_mem hh) sorted
          (by rw [eq,hres,← elapsed]; exact ri) k lim (eq.symm ▸ hw)
    have width : w.length ≤ n+1 := by
      have wc := liveCard hw
      rw [List.toFinset_card_of_nodup wn] at wc
      omega
    simp [absentR,PackQ.plain, width, QuickQ.testSigned cg lim wn hw,wp,missing,tags]
  have reach := resourceStepIndexed live n lj v nd rfl bound
    (fun a b => absentR c e tab n (addLoss e u a b))
    (fun a b w wnd k kl hw hbound => nextOK _ _ wnd k kl hw hbound a b rfl)
  change !(baseTest v || scanPairs (fun a b => pairB v
        (absentR c e tab n (addLoss e u a b)) a b) v) = true at fail
  simp [reach] at fail

def bucketOf (b : List (List Entry)) (i : ℕ) := b.getD i []

lemma bucketMem {b : List (List Entry)} {i : Nat} {w : Entry}
    (h : w ∈ bucketOf b i) : w ∈ b.flatten := by
  unfold bucketOf at h
  by_cases hi : i < b.length
  · rw [List.getD_eq_getElem b [] hi] at h
    exact List.mem_flatten.mpr ⟨b[i], List.getElem_mem hi, h⟩
  · simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)] at h

lemma checkBuckets (check : Entry → Bool) {b : List (List Entry)}
    (ok : b.all (fun xs => xs.all check) = true) :
    ∀ p, levelMem p (bucketOf b) → check p = true := by
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have eq := List.all_flatten (l := b) (f := check)
  exact List.all_eq_true.mp (eq.trans ok) p (bucketMem hi)

def M0w0 : Sig := (0x1ff00000ff80,0x3001800c00600300)
def M0w1 : Sig := (0x600000030000,0xc0f607b03d81ec0f)
def M0w2 : Sig := (0x3fe00001ff0000,0xc006003001800c00)
def M0w3 : Sig := (0x40055002002a80,0x0)
def M0w4 : Sig := (0x496000024b0000,0x0)
def M0w5 : Sig := (0x80002004000100,0xd05e82f417a0bd05)
def M0w6 : Sig := (0x800a6004005300,0x0)
def M0w7 : Sig := (0x801ff00400ff80,0x3001800c00600300)
def M0w8 : Sig := (0x92400004920000,0x8004002001000800)
def M0w9 : Sig := (0xc0607006030380,0xd0fe87f43fa1fd0f)
def M0w10 : Sig := (0xdb600006db0000,0x8004002001000800)
def M0w11 : Sig := (0x100138008009c00,0x0)
def M0w12 : Sig := (0x122928809149440,0xb005802c01600b0)
def M0w13 : Sig := (0x1238000091c0000,0x0)
def M0w14 : Sig := (0x18282a00c141500,0xd35e9af4d7a6bd35)
def M0w15 : Sig := (0x1a292a80d149540,0xdb5edaf6d7b6bdb5)
def M0w16 : Sig := (0x1c003f00e001f80,0x1008804402201100)
def M0w17 : Sig := (0x1c013f00e009f80,0x1008804402201100)
def M0w18 : Sig := (0x1c01ff00e00ff80,0x3009804c02601300)
def M0w19 : Sig := (0x1c063f00e031f80,0xd0fe87f43fa1fd0f)
def M0w20 : Sig := (0x1c283f00e141f80,0xd35e9af4d7a6bd35)
def M0w21 : Sig := (0x1c2e2f00e171780,0xd3fe9ff4ffa7fd3f)
def M0w22 : Sig := (0x1c3e0000e1f0000,0xc00e007003801c00)
def M0w23 : Sig := (0x1c3e0700e1f0380,0xd0fe87f43fa1fd0f)
def M0w24 : Sig := (0x1c3e2a00e1f1500,0xd35e9af4d7a6bd35)
def M0w25 : Sig := (0x1c3e3f00e1f1f80,0xd00e807403a01d00)
def M0w26 : Sig := (0x2001c001000e000,0x2001000800400200)
def M0w27 : Sig := (0x204108010208400,0x7d1be8df46fa37d1)
def M0w28 : Sig := (0x23c000011e00000,0x0)
def M0w29 : Sig := (0x23fe00011ff0000,0xc006003001800c00)
def M0w30 : Sig := (0x2c00c7016006380,0x3009804c02601300)
def M0w31 : Sig := (0x2c01ff01600ff80,0x3009804c02601300)
def M0w32 : Sig := (0x2c06c7016036380,0xf0ff87fc3fe1ff0f)
def M0w33 : Sig := (0x2dc600016e30000,0xc00e007003801c00)
def M0w34 : Sig := (0x2dc607016e30380,0xd0fe87f43fa1fd0f)
def M0w35 : Sig := (0x2dc6c7016e36380,0xf00f807c03e01f00)
def M0w36 : Sig := (0x2ffe00017ff0000,0xc00e007003801c00)
def M0w37 : Sig := (0x324908019248400,0x7d1be8df46fa37d1)
def M0w38 : Sig := (0x326908019348400,0xff5ffaffd7febff5)
def M0w39 : Sig := (0x326928819349440,0x7f1bf8dfc6fe37f1)
def M0w40 : Sig := (0x33ff08019ff8400,0xfd1fe8ff47fa3fd1)
def M0w41 : Sig := (0x34015901a00ac80,0x3009804c02601300)
def M0w42 : Sig := (0x36495901b24ac80,0x7d1be8df46fa37d1)
def M0w43 : Sig := (0x36da0001b6d0000,0x400a005002801400)
def M0w44 : Sig := (0x36db0801b6d8400,0x7d1be8df46fa37d1)
def M0w45 : Sig := (0x37fe0001bff0000,0xc00e007003801c00)
def M0w46 : Sig := (0x3801aa01c00d500,0x3009804c02601300)
def M0w47 : Sig := (0x3801ff01c00ff80,0x3009804c02601300)
def M0w48 : Sig := (0x3829aa01c14d500,0xf35f9afcd7e6bf35)
def M0w49 : Sig := (0x3a692a01d349500,0xff5ffaffd7febff5)
def M0w50 : Sig := (0x3b680001db40000,0xc00e007003801c00)
def M0w51 : Sig := (0x3b682a01db41500,0xd35e9af4d7a6bd35)
def M0w52 : Sig := (0x3b690801db48400,0xfd1fe8ff47fa3fd1)
def M0w53 : Sig := (0x3b692881db49440,0xcb0e5872c3961cb0)
def M0w54 : Sig := (0x3b69aa01db4d500,0xf00f807c03e01f00)
def M0w55 : Sig := (0x3bfe0001dff0000,0xc00e007003801c00)
def M0w56 : Sig := (0x3c000001e000000,0x8004002001000)
def M0w57 : Sig := (0x3c017f01e00bf80,0x3009804c02601300)
def M0w58 : Sig := (0x3c01bf01e00df80,0x3009804c02601300)
def M0w59 : Sig := (0x3c01ef01e00f780,0x3009804c02601300)
def M0w60 : Sig := (0x3c01ff01e00ff80,0x3009804c02601300)
def M0w61 : Sig := (0x3c07ff01e03ff80,0xf0ff87fc3fe1ff0f)
def M0w62 : Sig := (0x3c29ff01e14ff80,0xf35f9afcd7e6bf35)
def M0w63 : Sig := (0x3c3fff01e1fff80,0xf00f807c03e01f00)
def M0w64 : Sig := (0x3c97ff01e4bff80,0x3009804c02601300)
def M0w65 : Sig := (0x3dc7ff01ee3ff80,0xf00f807c03e01f00)
def M0w66 : Sig := (0x3e39ff01f1cff80,0x3009804c02601300)
def M0w67 : Sig := (0x3edbff01f6dff80,0x700b805c02e01700)
def M0w68 : Sig := (0x3efe0001f7f0000,0xc00e007003801c00)
def M0w69 : Sig := (0x3f69ff01fb4ff80,0xf00f807c03e01f00)
def M0w70 : Sig := (0x3f7e0001fbf0000,0xc00e007003801c00)
def M0w71 : Sig := (0x3fc1ff01fe0ff80,0x3009804c02601300)
def M0w72 : Sig := (0x3fee0001ff70000,0xc00e007003801c00)
def M0w73 : Sig := (0x3ffe0001fff0000,0xc00e007003801c00)
def M0w74 : Sig := (0x3ffe0701fff0380,0xd0fe87f43fa1fd0f)
def M0w75 : Sig := (0x3ffe2a01fff1500,0xd35e9af4d7a6bd35)
def M0w76 : Sig := (0x3ffe3f01fff1f80,0xd00e807403a01d00)
def M0w77 : Sig := (0x3ffe5501fff2a80,0xc00e007003801c00)
def M0w78 : Sig := (0x3ffea601fff5300,0xc00e007003801c00)
def M0w79 : Sig := (0x3ffec701fff6380,0xf00f807c03e01f00)
def M0w80 : Sig := (0x3fff0801fff8400,0xfd1fe8ff47fa3fd1)
def M0w81 : Sig := (0x3fff2881fff9440,0xcb0e5872c3961cb0)
def M0w82 : Sig := (0x3fff3801fff9c00,0xc00e007003801c00)
def M0w83 : Sig := (0x3fff5901fffac80,0xf00f807c03e01f00)
def M0w84 : Sig := (0x3fffaa01fffd500,0xf00f807c03e01f00)
def M0w85 : Sig := (0x3fffff01fffff80,0xf00f807c03e01f00)
def M0w86 : Sig := (0x802020840101042,0x200100080040020)
def M0w87 : Sig := (0x882426044121302,0x82c41620b105882c)
def M0w88 : Sig := (0x8c2627046131382,0xd2fe97f4bfa5fd2f)
def M0w89 : Sig := (0x124c241092612084,0x743ba1dd0ee87743)
def M0w90 : Sig := (0x12cc647096632384,0xf4ffa7fd3fe9ff4f)
def M0w91 : Sig := (0x136cb4909b65a484,0x7d3be9df4efa77d3)
def M0w92 : Sig := (0x2000000900000048,0xf507a83d41ea0f5)
def M0w93 : Sig := (0x20001aa90000d548,0x3f51fa8fd47ea3f5)
def M0w94 : Sig := (0x20001ff90000ffc8,0x3f51fa8fd47ea3f5)
def M0w95 : Sig := (0x2036800901b40048,0xcf567ab3d59eacf5)
def M0w96 : Sig := (0x203fe00901ff0048,0xcf567ab3d59eacf5)
def M0w97 : Sig := (0x20920a2904905148,0x8244122091048824)
def M0w98 : Sig := (0x20920a6904905348,0x8244122091048824)
def M0w99 : Sig := (0x20921aa90490d548,0xbf55faafd57eabf5)
def M0w100 : Sig := (0x20924a2904925148,0x8244122091048824)
def M0w101 : Sig := (0x20b68a2905b45148,0xcf567ab3d59eacf5)
def M0w102 : Sig := (0x21229aa90914d548,0x3f51fa8fd47ea3f5)
def M0w103 : Sig := (0x2136928909b49448,0xcf567ab3d59eacf5)
def M0w104 : Sig := (0x21829aa90c14d548,0xff5ffaffd7febff5)
def M0w105 : Sig := (0x21928aa90c945548,0xd35e9af4d7a6bd35)
def M0w106 : Sig := (0x21b682a90db41548,0xdf5efaf7d7bebdf5)
def M0w107 : Sig := (0x2234180911a0c048,0x2c01600b005802c0)
def M0w108 : Sig := (0x22341aa911a0d548,0x3f51fa8fd47ea3f5)
def M0w109 : Sig := (0x2236980911b4c048,0xef577abbd5deaef5)
def M0w110 : Sig := (0x2294082114a04108,0xf45fa2fd17e8bf45)
def M0w111 : Sig := (0x22941aa914a0d548,0xff5ffaffd7febff5)
def M0w112 : Sig := (0x22960a2914b05148,0xf65fb2fd97ecbf65)
def M0w113 : Sig := (0x22b4182915a0c148,0xfc5fe2ff17f8bfc5)
def M0w114 : Sig := (0x22b6882915b44148,0xff5ffaffd7febff5)
def M0w115 : Sig := (0x22d40c7116a06388,0xf45fa2fd17e8bf45)
def M0w116 : Sig := (0x22d4687116a34388,0xf4ffa7fd3fe9ff4f)
def M0w117 : Sig := (0x22dc682116e34108,0xf45fa2fd17e8bf45)
def M0w118 : Sig := (0x23249aa91924d548,0x7f5bfadfd6feb7f5)
def M0w119 : Sig := (0x2336908919b48448,0xff5ffaffd7febff5)
def M0w120 : Sig := (0x23369a8919b4d448,0x2f01780bc05e02f0)
def M0w121 : Sig := (0x23801aa91c00d548,0x3f59facfd67eb3f5)
def M0w122 : Sig := (0x23941aa11ca0d508,0xf45fa2fd17e8bf45)
def M0w123 : Sig := (0x23b498a11da4c508,0xfd5feaff57fabfd5)
def M0w124 : Sig := (0x23b680091db40048,0xcf5e7af3d79ebcf5)
def M0w125 : Sig := (0x23b688211db44108,0xf45fa2fd17e8bf45)
def M0w126 : Sig := (0x23b69aa91db4d548,0xff5ffaffd7febff5)
def M0w127 : Sig := (0x23b69ae91db4d748,0xff5ffaffd7febff5)
def M0w128 : Sig := (0x23b69ba91db4dd48,0xff5ffaffd7febff5)
def M0w129 : Sig := (0x23b79aa91dbcd548,0xff5ffaffd7febff5)
def M0w130 : Sig := (0x23be9aa91df4d548,0xff5ffaffd7febff5)
def M0w131 : Sig := (0x23c01ff91e00ffc8,0x3f59facfd67eb3f5)
def M0w132 : Sig := (0x23d41ff11ea0ff88,0xf45fa2fd17e8bf45)
def M0w133 : Sig := (0x23f69ff91fb4ffc8,0xff5ffaffd7febff5)
def M0w134 : Sig := (0x23ffe0091fff0048,0xcf5e7af3d79ebcf5)
def M0w135 : Sig := (0x23ffe8211fff4108,0xf45fa2fd17e8bf45)
def M0w136 : Sig := (0x23fffaa91fffd548,0xff5ffaffd7febff5)
def M0w137 : Sig := (0x28920a294490514a,0x8244122091048824)
def M0w138 : Sig := (0x28924a694492534a,0x82c41620b105882c)
def M0w139 : Sig := (0x4800404240020212,0x80040020010008)
def M0w140 : Sig := (0x5048645282432294,0xa005002801400a)
def M0w141 : Sig := (0x50c8647286432394,0xd0fe87f43fa1fd0f)
def M0w142 : Sig := (0x52c86c7296436394,0x30a9854c2a61530a)
def M0w143 : Sig := (0x52dc645296e32294,0xc0ae05702b815c0a)
def M0w144 : Sig := (0x53c87ff29e43ff94,0x30a9854c2a61530a)
def M0w145 : Sig := (0x53ffe4529fff2294,0xc0ae05702b815c0a)
def M0w146 : Sig := (0x6010080b00804058,0x0)
def M0w147 : Sig := (0x60900a6b04805358,0x0)
def M0w148 : Sig := (0x6090486304824318,0x80c406203101880c)
def M0w149 : Sig := (0x6090486b04824358,0x80c406203101880c)
def M0w150 : Sig := (0x60920a2b04905158,0x8244122091048824)
def M0w151 : Sig := (0x60924a6b04925358,0x82c41620b105882c)
def M0w152 : Sig := (0x60d0687306834398,0xd0fe87f43fa1fd0f)
def M0w153 : Sig := (0x6294486314a24318,0xf4dfa6fd37e9bf4d)
def M0w154 : Sig := (0x63b69aab1db4d558,0xff5ffaffd7febff5)
def M0w155 : Sig := (0x63d01ffb1e80ffd8,0x3009804c02601300)
def M0w156 : Sig := (0x63ffe80b1fff4058,0xc00e007003801c00)
def M0w157 : Sig := (0x68000a6b4000535a,0x2c01600b005802c)
def M0w158 : Sig := (0x68001aeb4000d75a,0x3fd1fe8ff47fa3fd)
def M0w159 : Sig := (0x6812400b4092005a,0x82c41620b105882c)
def M0w160 : Sig := (0x68800a6b4400535a,0x2c01600b005802c)
def M0w161 : Sig := (0x68824a6b4412535a,0x82c41620b105882c)
def M0w162 : Sig := (0x68904a6b4482535a,0x82c41620b105882c)
def M0w163 : Sig := (0x68920a6b4490535a,0x82c41620b105882c)
def M0w164 : Sig := (0x6892486b4492435a,0x82c41620b105882c)
def M0w165 : Sig := (0x68924a2b4492515a,0x82c41620b105882c)
def M0w166 : Sig := (0x68924a6b4492535a,0x82c41620b105882c)
def M0w167 : Sig := (0x68bfea6b45ff535a,0xc2c61630b1858c2c)
def M0w168 : Sig := (0x68d24f7b46927bda,0x82c41620b105882c)
def M0w169 : Sig := (0x68db6a6b46db535a,0x82c41620b105882c)
def M0w170 : Sig := (0x69925beb4c92df5a,0x82c41620b105882c)
def M0w171 : Sig := (0x69b3ca6b4d9e535a,0x82c41620b105882c)
def M0w172 : Sig := (0x6abe4a6b55f2535a,0x82c41620b105882c)
def M0w173 : Sig := (0x6bb6daeb5db6d75a,0xffdffefff7ffbffd)
def M0w174 : Sig := (0x6bd25ffb5e92ffda,0xb2cd966cb3659b2c)
def M0w175 : Sig := (0x6bffea6b5fff535a,0xc2ce1670b3859c2c)
def M0w176 : Sig := (0x70000c738000639c,0x34f1a78d3c69e34f)
def M0w177 : Sig := (0x70001efb8000f7dc,0x3ff1ff8ffc7fe3ff)
def M0w178 : Sig := (0x70001ff38000ff9c,0x34f1a78d3c69e34f)
def M0w179 : Sig := (0x701c600380e3001c,0xc4f627b13d89ec4f)
def M0w180 : Sig := (0x703ee00b81f7005c,0xcff67fb3fd9fecff)
def M0w181 : Sig := (0x70486c738243639c,0x34f1a78d3c69e34f)
def M0w182 : Sig := (0x70904c738482639c,0xb4f5a7ad3d69eb4f)
def M0w183 : Sig := (0x70c06c738603639c,0xf4ffa7fd3fe9ff4f)
def M0w184 : Sig := (0x70d86c7386c3639c,0x80e407203901c80e)
def M0w185 : Sig := (0x721c0c0390e0601c,0x2401200900480240)
def M0w186 : Sig := (0x721c0c0b90e0605c,0x2401200900480240)
def M0w187 : Sig := (0x721c0c7390e0639c,0x34f1a78d3c69e34f)
def M0w188 : Sig := (0x723c1c0b91e0e05c,0x2c01600b005802c0)
def M0w189 : Sig := (0x725c641392e3209c,0xf4ffa7fd3fe9ff4f)
def M0w190 : Sig := (0x725c6c5392e3629c,0x24a125092849424a)
def M0w191 : Sig := (0x72940c7394a0639c,0xf4ffa7fd3fe9ff4f)
def M0w192 : Sig := (0x729c0c2394e0611c,0xf45fa2fd17e8bf45)
def M0w193 : Sig := (0x729c682394e3411c,0xf4ffa7fd3fe9ff4f)
def M0w194 : Sig := (0x72c00c739600639c,0x34f9a7cd3e69f34f)
def M0w195 : Sig := (0x72dc6c7396e3639c,0xf4ffa7fd3fe9ff4f)
def M0w196 : Sig := (0x72dc6c7b96e363dc,0xf4ffa7fd3fe9ff4f)
def M0w197 : Sig := (0x72dc6d7396e36b9c,0xf4ffa7fd3fe9ff4f)
def M0w198 : Sig := (0x72dc6e7396e3739c,0xf4ffa7fd3fe9ff4f)
def M0w199 : Sig := (0x72dd6c7396eb639c,0xf4ffa7fd3fe9ff4f)
def M0w200 : Sig := (0x72fc6c7397e3639c,0xf4ffa7fd3fe9ff4f)
def M0w201 : Sig := (0x73c01ff39e00ff9c,0x34f9a7cd3e69f34f)
def M0w202 : Sig := (0x73dc1ff39ee0ff9c,0x3409a04d02681340)
def M0w203 : Sig := (0x73dc7ff39ee3ff9c,0xf4ffa7fd3fe9ff4f)
def M0w204 : Sig := (0x73fcfcf39fe7e79c,0xfdffefff7ffbffdf)
def M0w205 : Sig := (0x73fefefb9ff7f7dc,0xffffffffffffffff)
def M0w206 : Sig := (0x73ffec739fff639c,0xf4ffa7fd3fe9ff4f)
def M0w207 : Sig := (0x78000e7bc00073de,0x36f1b78dbc6de36f)
def M0w208 : Sig := (0x78da6e7bc6d373de,0x82e41720b905c82e)
def M0w209 : Sig := (0x7ade6e7bd6f373de,0xf6ffb7fdbfedff6f)
def M0w210 : Sig := (0x8020100c01008060,0x800400200100080)
def M0w211 : Sig := (0x922c14049160a024,0x2c01600b005802c0)
def M0w212 : Sig := (0x926c34149361a0a4,0x7c3be1df0ef877c3)
def M0w213 : Sig := (0x932c94849964a424,0x7d1be8df46fa37d1)
def M0w214 : Sig := (0x936c15949b60aca4,0x3c09e04f027813c0)
def M0w215 : Sig := (0xd008040680402034,0x0)
def M0w216 : Sig := (0xd3c81ff69e40ffb4,0x3009804c02601300)
def M0w217 : Sig := (0xd3ffe4069fff2034,0xc00e007003801c00)
def M0w218 : Sig := (0xf0001c0f8000e07c,0x2c01600b005802c0)
def M0w219 : Sig := (0xf0001c7f8000e3fc,0x3cf1e78f3c79e3cf)
def M0w220 : Sig := (0xf0001eaf8000f57c,0x3f51fa8fd47ea3f5)
def M0w221 : Sig := (0xf03c000f81e0007c,0xc006003001800c0)
def M0w222 : Sig := (0xf03e800f81f4007c,0xcf567ab3d59eacf5)
def M0w223 : Sig := (0xf0d86c7f86c363fc,0x80e407203901c80e)
def M0w224 : Sig := (0xf21c1c0f90e0e07c,0x2c01600b005802c0)
def M0w225 : Sig := (0xf2341c0f91a0e07c,0x2c01600b005802c0)
def M0w226 : Sig := (0xf23c000f91e0007c,0xc006003001800c0)
def M0w227 : Sig := (0xf23c0c0f91e0607c,0x2c01600b005802c0)
def M0w228 : Sig := (0xf23c140f91e0a07c,0x2c01600b005802c0)
def M0w229 : Sig := (0xf23c180f91e0c07c,0x2c01600b005802c0)
def M0w230 : Sig := (0xf23c1c0f91e0e07c,0x2c01600b005802c0)
def M0w231 : Sig := (0xf23c1c7f91e0e3fc,0x3cf1e78f3c79e3cf)
def M0w232 : Sig := (0xf23c1eaf91e0f57c,0x3f51fa8fd47ea3f5)
def M0w233 : Sig := (0xf23c1fff91e0fffc,0x3c01e00f007803c0)
def M0w234 : Sig := (0xf23e9c0f91f4e07c,0xef577abbd5deaef5)
def M0w235 : Sig := (0xf27c1d5f93e0eafc,0x2c01600b005802c0)
def M0w236 : Sig := (0xf27c7c5f93e3e2fc,0x2ca1650b285942ca)
def M0w237 : Sig := (0xf27d7c0f93ebe07c,0x2c01600b005802c0)
def M0w238 : Sig := (0xf2bc1c2f95e0e17c,0xfc5fe2ff17f8bfc5)
def M0w239 : Sig := (0xf2bc1e6f95e0f37c,0x2c01600b005802c0)
def M0w240 : Sig := (0xf2dc6c7796e363bc,0xf4ffa7fd3fe9ff4f)
def M0w241 : Sig := (0xf2fc6c7f97e363fc,0xfcffe7ff3ff9ffcf)
def M0w242 : Sig := (0xf2fc7c7f97e3e3fc,0xfcffe7ff3ff9ffcf)
def M0w243 : Sig := (0xf33c1f8f99e0fc7c,0x2c01600b005802c0)
def M0w244 : Sig := (0xf33e9e8f99f4f47c,0x2f01780bc05e02f0)
def M0w245 : Sig := (0xf33f9c0f99fce07c,0x2c01600b005802c0)
def M0w246 : Sig := (0xf3be9eaf9df4f57c,0xff5ffaffd7febff5)
def M0w247 : Sig := (0xf3fc1fff9fe0fffc,0x3c09e04f027813c0)
def M0w248 : Sig := (0xf3fffc0f9fffe07c,0xec0f607b03d81ec0)
def M0w249 : Sig := (0xf3ffffff9ffffffc,0xfc0fe07f03f81fc0)
def M0w250 : Sig := (0xf89a4e6fc4d2737e,0x82c41620b105882c)
def M0w251 : Sig := (0xfabe5e6fd5f2f37e,0xaec5762bb15d8aec)
def M0t0 : Nat → List Entry := fun _ => []
lemma M0v0 : verifiedR false 9 0 M0t0 := emptyR _ _
def M0g1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t1 : Nat → List Entry := bucketOf M0g1
set_option maxRecDepth 160000 in
lemma M0v1 : verifiedR false 9 1 M0t1 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v0
  apply checkBuckets
  simp only [M0g1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M0g2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t2 : Nat → List Entry := bucketOf M0g2
set_option maxRecDepth 160000 in
lemma M0v2 : verifiedR false 9 2 M0t2 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v1
  apply checkBuckets
  simp only [M0g2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M0g3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t3 : Nat → List Entry := bucketOf M0g3
set_option maxRecDepth 160000 in
lemma M0v3 : verifiedR false 9 3 M0t3 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v2
  apply checkBuckets
  simp only [M0g3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M0g4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t4 : Nat → List Entry := bucketOf M0g4
set_option maxRecDepth 160000 in
lemma M0v4 : verifiedR false 9 4 M0t4 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v3
  apply checkBuckets
  simp only [M0g4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M0p5b25c0 : List Entry := [([],[M0w9,M0w85,M0w126,M0w166,M0w176,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p5b25c0Ok : M0p5b25c0.all (testRow chart false M0t4 4) = true := by decide +kernel
def M0b5_25 : List Entry := M0p5b25c0
def M0g5 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], M0b5_25, [], [], [], [], [], []]
def M0t5 : Nat → List Entry := bucketOf M0g5
set_option maxRecDepth 160000 in
lemma M0v5 : verifiedR false 9 5 M0t5 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v4
  apply checkBuckets
  simp only [M0g5, M0b5_25, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p5b25c0Ok]
def M0p6b0c0 : List Entry := [([],[M0w9,M0w14,M0w37,M0w60,M0w73,M0w195]),
([],[M0w37,M0w73,M0w95,M0w179,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b0c0Ok : M0p6b0c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_0 : List Entry := M0p6b0c0
def M0p6b2c0 : List Entry := [([],[M0w60,M0w73,M0w120,M0w126,M0w166,M0w195,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b2c0Ok : M0p6b2c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_2 : List Entry := M0p6b2c0
def M0p6b6c0 : List Entry := [([],[M0w54,M0w73,M0w126,M0w166,M0w195,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b6c0Ok : M0p6b6c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_6 : List Entry := M0p6b6c0
def M0p6b7c0 : List Entry := [([],[M0w22,M0w60,M0w93,M0w126,M0w166,M0w195,M0w247]),
([],[M0w22,M0w73,M0w95,M0w126,M0w166,M0w195,M0w247]),
([],[M0w60,M0w73,M0w108,M0w126,M0w166,M0w195,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b7c0Ok : M0p6b7c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_7 : List Entry := M0p6b7c0
def M0p6b10c0 : List Entry := [([],[M0w14,M0w73,M0w126,M0w166,M0w195,M0w203,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b10c0Ok : M0p6b10c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_10 : List Entry := M0p6b10c0
def M0p6b13c0 : List Entry := [([],[M0w14,M0w37,M0w60,M0w73,M0w195,M0w248])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b13c0Ok : M0p6b13c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_13 : List Entry := M0p6b13c0
def M0p6b14c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w195,M0w223,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b14c0Ok : M0p6b14c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_14 : List Entry := M0p6b14c0
def M0p6b17c0 : List Entry := [([],[M0w85,M0w126,M0w166,M0w176,M0w195,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b17c0Ok : M0p6b17c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_17 : List Entry := M0p6b17c0
def M0p6b19c0 : List Entry := [([],[M0w73,M0w95,M0w110,M0w166,M0w195,M0w230,M0w247]),
([],[M0w73,M0w110,M0w126,M0w166,M0w203,M0w230,M0w247]),
([],[M0w73,M0w122,M0w126,M0w166,M0w195,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b19c0Ok : M0p6b19c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_19 : List Entry := M0p6b19c0
def M0p6b21c0 : List Entry := [([],[M0w27,M0w60,M0w73,M0w111,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w111,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w245]),
([],[M0w37,M0w66,M0w73,M0w126,M0w195,M0w230]),
([],[M0w37,M0w73,M0w85,M0w95,M0w195,M0w230]),
([],[M0w40,M0w60,M0w73,M0w126,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b21c0Ok : M0p6b21c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_21 : List Entry := M0p6b21c0
def M0p6b22c0 : List Entry := [([],[M0w9,M0w73,M0w95,M0w126,M0w166,M0w195,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b22c0Ok : M0p6b22c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_22 : List Entry := M0p6b22c0
def M0p6b23c0 : List Entry := [([],[M0w60,M0w93,M0w110,M0w166,M0w176,M0w230]),
([],[M0w73,M0w95,M0w110,M0w166,M0w179,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b23c0Ok : M0p6b23c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_23 : List Entry := M0p6b23c0
def M0p6b25c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w176,M0w247]),
([],[M0w9,M0w60,M0w85,M0w126,M0w166,M0w176,M0w230]),
([],[M0w9,M0w73,M0w85,M0w126,M0w166,M0w195,M0w247]),
([],[M0w38,M0w60,M0w73,M0w126,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b25c0Ok : M0p6b25c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_25 : List Entry := M0p6b25c0
def M0p6b27c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w95,M0w110,M0w166,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b27c0Ok : M0p6b27c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_27 : List Entry := M0p6b27c0
def M0p6b28c0 : List Entry := [([],[M0w38,M0w60,M0w73,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b28c0Ok : M0p6b28c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_28 : List Entry := M0p6b28c0
def M0p6b31c0 : List Entry := [([],[M0w14,M0w60,M0w73,M0w93,M0w166,M0w195,M0w247]),
([],[M0w14,M0w60,M0w85,M0w93,M0w166,M0w195,M0w230]),
([],[M0w14,M0w60,M0w93,M0w166,M0w195,M0w248]),
([],[M0w14,M0w73,M0w85,M0w126,M0w166,M0w195,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p6b31c0Ok : M0p6b31c0.all (testRow chart false M0t5 5) = true := by decide +kernel
def M0b6_31 : List Entry := M0p6b31c0
def M0g6 : List (List Entry) := [M0b6_0, [], M0b6_2, [], [], [], M0b6_6, M0b6_7, [], [], M0b6_10, [], [], M0b6_13, M0b6_14, [], [], M0b6_17, [], M0b6_19, [], M0b6_21, M0b6_22, M0b6_23, [], M0b6_25, [], M0b6_27, M0b6_28, [], [], M0b6_31]
def M0t6 : Nat → List Entry := bucketOf M0g6
set_option maxRecDepth 160000 in
lemma M0v6 : verifiedR false 9 6 M0t6 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v5
  apply checkBuckets
  simp only [M0g6, M0b6_0, M0b6_2, M0b6_6, M0b6_7, M0b6_10, M0b6_13, M0b6_14, M0b6_17, M0b6_19, M0b6_21, M0b6_22, M0b6_23, M0b6_25, M0b6_27, M0b6_28, M0b6_31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p6b0c0Ok, M0p6b2c0Ok, M0p6b6c0Ok, M0p6b7c0Ok, M0p6b10c0Ok, M0p6b13c0Ok, M0p6b14c0Ok, M0p6b17c0Ok, M0p6b19c0Ok, M0p6b21c0Ok, M0p6b22c0Ok, M0p6b23c0Ok, M0p6b25c0Ok, M0p6b27c0Ok, M0p6b28c0Ok, M0p6b31c0Ok]
def M0p7b0c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w176,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w179,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w203,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w206,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w230,M0w242]),
([],[M0w60,M0w73,M0w126,M0w150,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b0c0Ok : M0p7b0c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_0 : List Entry := M0p7b0c0
def M0p7b1c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w230,M0w251]),
([],[M0w60,M0w73,M0w126,M0w158,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b1c0Ok : M0p7b1c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_1 : List Entry := M0p7b1c0
def M0p7b2c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w110,M0w126,M0w195,M0w230]),
([],[M0w49,M0w60,M0w73,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w120,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w126,M0w156,M0w166,M0w195,M0w230]),
([],[M0w73,M0w126,M0w155,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b2c0Ok : M0p7b2c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_2 : List Entry := M0p7b2c0
def M0p7b3c0 : List Entry := [([],[M0w60,M0w73,M0w93,M0w126,M0w166,M0w195,M0w230,M0w247]),
([],[M0w60,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230,M0w248]),
([],[M0w60,M0w93,M0w126,M0w166,M0w195,M0w230,M0w248]),
([],[M0w73,M0w95,M0w126,M0w166,M0w195,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b3c0Ok : M0p7b3c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_3 : List Entry := M0p7b3c0
def M0p7b4c0 : List Entry := [([],[M0w9,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w97,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b4c0Ok : M0p7b4c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_4 : List Entry := M0p7b4c0
def M0p7b5c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w107,M0w126,M0w166,M0w195]),
([],[M0w12,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w177,M0w195,M0w230]),
([],[M0w60,M0w126,M0w166,M0w177,M0w195,M0w230]),
([],[M0w73,M0w126,M0w166,M0w180,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b5c0Ok : M0p7b5c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_5 : List Entry := M0p7b5c0
def M0p7b6c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w80,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w249]),
([],[M0w73,M0w85,M0w126,M0w166,M0w195,M0w230,M0w247]),
([],[M0w73,M0w126,M0w166,M0w195,M0w202,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b6c0Ok : M0p7b6c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_6 : List Entry := M0p7b6c0
def M0p7b7c0 : List Entry := [([],[M0w0,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w2,M0w60,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w16,M0w60,M0w73,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w16,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w22,M0w60,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w22,M0w60,M0w93,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c0Ok : M0p7b7c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b7c1 : List Entry := [([],[M0w30,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w33,M0w60,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w41,M0w60,M0w73,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w92,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w94,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c1Ok : M0p7b7c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b7c2 : List Entry := [([],[M0w60,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w96,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w99,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w101,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w102,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w103,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c2Ok : M0p7b7c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b7c3 : List Entry := [([],[M0w60,M0w73,M0w104,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w105,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w106,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w108,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w109,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w111,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c3Ok : M0p7b7c3.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b7c4 : List Entry := [([],[M0w60,M0w73,M0w114,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w118,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w119,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w121,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w123,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w124,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c4Ok : M0p7b7c4.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b7c5 : List Entry := [([],[M0w60,M0w73,M0w126,M0w131,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w134,M0w166,M0w195,M0w230]),
([],[M0w60,M0w85,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w73,M0w85,M0w95,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c5Ok : M0p7b7c5.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_7 : List Entry := M0p7b7c0 ++ M0p7b7c1 ++ M0p7b7c2 ++ M0p7b7c3 ++ M0p7b7c4 ++ M0p7b7c5
def M0p7b8c0 : List Entry := [([],[M0w60,M0w73,M0w93,M0w140,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w95,M0w140,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w142,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w143,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w144,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w145,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b8c0Ok : M0p7b8c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b8c1 : List Entry := [([],[M0w60,M0w73,M0w126,M0w149,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w151,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w195,M0w214,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b8c1Ok : M0p7b8c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_8 : List Entry := M0p7b8c0 ++ M0p7b8c1
def M0p7b9c0 : List Entry := [([],[M0w21,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w195,M0w230,M0w246])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b9c0Ok : M0p7b9c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_9 : List Entry := M0p7b9c0
def M0p7b10c0 : List Entry := [([],[M0w7,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w14,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w179,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w203,M0w230]),
([],[M0w16,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w17,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c0Ok : M0p7b10c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c1 : List Entry := [([],[M0w18,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w22,M0w60,M0w73,M0w126,M0w166,M0w195,M0w247]),
([],[M0w25,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w29,M0w60,M0w126,M0w166,M0w195,M0w230]),
([],[M0w30,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w31,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c1Ok : M0p7b10c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c2 : List Entry := [([],[M0w33,M0w60,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w35,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w36,M0w60,M0w126,M0w166,M0w195,M0w230]),
([],[M0w45,M0w60,M0w126,M0w166,M0w195,M0w230]),
([],[M0w46,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w47,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c2Ok : M0p7b10c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c3 : List Entry := [([],[M0w50,M0w60,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w54,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w55,M0w60,M0w126,M0w166,M0w195,M0w230]),
([],[M0w57,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w58,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w59,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c3Ok : M0p7b10c3.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c4 : List Entry := [([],[M0w60,M0w63,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w64,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w65,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w68,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w69,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w70,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c4Ok : M0p7b10c4.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c5 : List Entry := [([],[M0w60,M0w72,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w79,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w82,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w83,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w84,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c5Ok : M0p7b10c5.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c6 : List Entry := [([],[M0w60,M0w73,M0w104,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w111,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w114,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w119,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w160,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w161,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c6Ok : M0p7b10c6.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c7 : List Entry := [([],[M0w60,M0w73,M0w126,M0w162,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w163,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w164,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w165,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w183,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w186,M0w195])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c7Ok : M0p7b10c7.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c8 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w188,M0w195]),
([],[M0w60,M0w73,M0w126,M0w166,M0w189,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w191,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w193,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w224]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w225])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c8Ok : M0p7b10c8.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c9 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w226]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w227]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w228]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w229]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w233]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w235])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c9Ok : M0p7b10c9.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c10 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w237]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w239]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w243]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w245]),
([],[M0w60,M0w73,M0w126,M0w166,M0w196,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w197,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c10Ok : M0p7b10c10.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c11 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w198,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w199,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w200,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w230,M0w240]),
([],[M0w60,M0w73,M0w126,M0w166,M0w230,M0w241]),
([],[M0w60,M0w73,M0w126,M0w167,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c11Ok : M0p7b10c11.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c12 : List Entry := [([],[M0w60,M0w73,M0w126,M0w168,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w169,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w170,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w171,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w172,M0w195,M0w230]),
([],[M0w60,M0w73,M0w127,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c12Ok : M0p7b10c12.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c13 : List Entry := [([],[M0w60,M0w73,M0w128,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w129,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w130,M0w166,M0w195,M0w230]),
([],[M0w60,M0w76,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w77,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w78,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c13Ok : M0p7b10c13.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b10c14 : List Entry := [([],[M0w60,M0w82,M0w126,M0w166,M0w195,M0w230]),
([],[M0w64,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w66,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w67,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w71,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c14Ok : M0p7b10c14.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_10 : List Entry := M0p7b10c0 ++ M0p7b10c1 ++ M0p7b10c2 ++ M0p7b10c3 ++ M0p7b10c4 ++ M0p7b10c5 ++ M0p7b10c6 ++ M0p7b10c7 ++ M0p7b10c8 ++ M0p7b10c9 ++ M0p7b10c10 ++ M0p7b10c11 ++ M0p7b10c12 ++ M0p7b10c13 ++ M0p7b10c14
def M0p7b11c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w192,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w238]),
([],[M0w60,M0w73,M0w126,M0w195,M0w212,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b11c0Ok : M0p7b11c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_11 : List Entry := M0p7b11c0
def M0p7b13c0 : List Entry := [([],[M0w14,M0w37,M0w60,M0w73,M0w195,M0w230]),
([],[M0w21,M0w60,M0w73,M0w126,M0w166,M0w195]),
([],[M0w60,M0w73,M0w93,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w93,M0w126,M0w166,M0w174,M0w195,M0w230]),
([],[M0w60,M0w73,M0w95,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w141,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b13c0Ok : M0p7b13c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_13 : List Entry := M0p7b13c0
def M0p7b14c0 : List Entry := [([],[M0w32,M0w60,M0w73,M0w126,M0w166,M0w230]),
([],[M0w60,M0w73,M0w89,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w195,M0w230,M0w250])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b14c0Ok : M0p7b14c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_14 : List Entry := M0p7b14c0
def M0p7b15c0 : List Entry := [([],[M0w5,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w153,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b15c0Ok : M0p7b15c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_15 : List Entry := M0p7b15c0
def M0p7b16c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w204,M0w230]),
([],[M0w60,M0w73,M0w85,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w98,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w100,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w190,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b16c0Ok : M0p7b16c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b16c1 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w236]),
([],[M0w60,M0w73,M0w126,M0w195,M0w208,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b16c1Ok : M0p7b16c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_16 : List Entry := M0p7b16c0 ++ M0p7b16c1
def M0p7b17c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w230,M0w248]),
([],[M0w60,M0w73,M0w126,M0w152,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w176,M0w195,M0w230,M0w247]),
([],[M0w60,M0w73,M0w126,M0w166,M0w179,M0w195,M0w230,M0w248]),
([],[M0w73,M0w126,M0w166,M0w195,M0w203,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b17c0Ok : M0p7b17c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_17 : List Entry := M0p7b17c0
def M0p7b18c0 : List Entry := [([],[M0w9,M0w14,M0w60,M0w73,M0w126,M0w166,M0w195]),
([],[M0w37,M0w60,M0w73,M0w93,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w95,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w90,M0w126,M0w166,M0w230]),
([],[M0w60,M0w73,M0w126,M0w137,M0w195,M0w230]),
([],[M0w60,M0w93,M0w126,M0w166,M0w176,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b18c0Ok : M0p7b18c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b18c1 : List Entry := [([],[M0w73,M0w95,M0w126,M0w166,M0w179,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b18c1Ok : M0p7b18c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_18 : List Entry := M0p7b18c0 ++ M0p7b18c1
def M0p7b19c0 : List Entry := [([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w221,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w230,M0w247])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b19c0Ok : M0p7b19c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_19 : List Entry := M0p7b19c0
def M0p7b20c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w184,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b20c0Ok : M0p7b20c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_20 : List Entry := M0p7b20c0
def M0p7b21c0 : List Entry := [([],[M0w2,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w2,M0w60,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w8,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w10,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w13,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w22,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c0Ok : M0p7b21c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b21c1 : List Entry := [([],[M0w33,M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w37,M0w50,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w85,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w95,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w133,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c1Ok : M0p7b21c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b21c2 : List Entry := [([],[M0w42,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w44,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w50,M0w60,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w176,M0w230,M0w242]),
([],[M0w60,M0w73,M0w126,M0w166,M0w178,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c2Ok : M0p7b21c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b21c3 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w181,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w182,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w183,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w187,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w191,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w194,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c3Ok : M0p7b21c3.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b21c4 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w201,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w219,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w231]),
([],[M0w60,M0w85,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w73,M0w85,M0w126,M0w166,M0w179,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c4Ok : M0p7b21c4.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_21 : List Entry := M0p7b21c0 ++ M0p7b21c1 ++ M0p7b21c2 ++ M0p7b21c3 ++ M0p7b21c4
def M0p7b22c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w116,M0w126,M0w166,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w244])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b22c0Ok : M0p7b22c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_22 : List Entry := M0p7b22c0
def M0p7b23c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w86,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w93,M0w110,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w95,M0w110,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w176,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w179,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b23c0Ok : M0p7b23c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b23c1 : List Entry := [([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w203,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w206,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w230,M0w242]),
([],[M0w60,M0w73,M0w110,M0w133,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w110,M0w136,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w112,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b23c1Ok : M0p7b23c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b23c2 : List Entry := [([],[M0w60,M0w73,M0w113,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w115,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w117,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w122,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w125,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w132,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b23c2Ok : M0p7b23c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b23c3 : List Entry := [([],[M0w60,M0w73,M0w126,M0w135,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w207,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b23c3Ok : M0p7b23c3.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_23 : List Entry := M0p7b23c0 ++ M0p7b23c1 ++ M0p7b23c2 ++ M0p7b23c3
def M0p7b25c0 : List Entry := [([],[M0w1,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w9,M0w60,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w176,M0w230]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w218]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w221]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b25c0Ok : M0p7b25c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b25c1 : List Entry := [([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w247]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w248]),
([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w206,M0w230]),
([],[M0w19,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w23,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w34,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b25c1Ok : M0p7b25c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b25c2 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w148,M0w195,M0w230]),
([],[M0w60,M0w61,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w74,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w195,M0w213,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b25c2Ok : M0p7b25c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_25 : List Entry := M0p7b25c0 ++ M0p7b25c1 ++ M0p7b25c2
def M0p7b26c0 : List Entry := [([],[M0w12,M0w60,M0w73,M0w126,M0w166,M0w176,M0w230]),
([],[M0w53,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w81,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w138,M0w195,M0w230]),
([],[M0w60,M0w73,M0w154,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b26c0Ok : M0p7b26c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_26 : List Entry := M0p7b26c0
def M0p7b27c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w110,M0w126,M0w166,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w157,M0w195,M0w230]),
([],[M0w39,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w52,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w80,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w91,M0w126,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b27c0Ok : M0p7b27c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b27c1 : List Entry := [([],[M0w60,M0w73,M0w93,M0w166,M0w195,M0w230,M0w246]),
([],[M0w60,M0w73,M0w97,M0w126,M0w176,M0w195,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w211,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w220,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w222,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w232])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b27c1Ok : M0p7b27c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b27c2 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w234])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b27c2Ok : M0p7b27c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_27 : List Entry := M0p7b27c0 ++ M0p7b27c1 ++ M0p7b27c2
def M0p7b28c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w147,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b28c0Ok : M0p7b28c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_28 : List Entry := M0p7b28c0
def M0p7b29c0 : List Entry := [([],[M0w60,M0w73,M0w97,M0w110,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w175,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b29c0Ok : M0p7b29c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_29 : List Entry := M0p7b29c0
def M0p7b30c0 : List Entry := [([],[M0w9,M0w12,M0w60,M0w73,M0w126,M0w166,M0w230]),
([],[M0w60,M0w126,M0w166,M0w195,M0w217,M0w230]),
([],[M0w73,M0w126,M0w166,M0w195,M0w216,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b30c0Ok : M0p7b30c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_30 : List Entry := M0p7b30c0
def M0p7b31c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w97,M0w126,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w93,M0w166,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w185,M0w195]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w218]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w221])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c0Ok : M0p7b31c0.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b31c1 : List Entry := [([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w247]),
([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w248]),
([],[M0w14,M0w60,M0w73,M0w136,M0w166,M0w195,M0w230]),
([],[M0w15,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w20,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c1Ok : M0p7b31c1.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b31c2 : List Entry := [([],[M0w24,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w37,M0w60,M0w73,M0w126,M0w184,M0w195,M0w230]),
([],[M0w48,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w49,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w51,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w62,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c2Ok : M0p7b31c2.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0p7b31c3 : List Entry := [([],[M0w60,M0w73,M0w75,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w88,M0w126,M0w166,M0w195])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c3Ok : M0p7b31c3.all (testRow chart false M0t6 6) = true := by decide +kernel
def M0b7_31 : List Entry := M0p7b31c0 ++ M0p7b31c1 ++ M0p7b31c2 ++ M0p7b31c3
def M0g7 : List (List Entry) := [M0b7_0, M0b7_1, M0b7_2, M0b7_3, M0b7_4, M0b7_5, M0b7_6, M0b7_7, M0b7_8, M0b7_9, M0b7_10, M0b7_11, [], M0b7_13, M0b7_14, M0b7_15, M0b7_16, M0b7_17, M0b7_18, M0b7_19, M0b7_20, M0b7_21, M0b7_22, M0b7_23, [], M0b7_25, M0b7_26, M0b7_27, M0b7_28, M0b7_29, M0b7_30, M0b7_31]
def M0t7 : Nat → List Entry := bucketOf M0g7
set_option maxRecDepth 160000 in
lemma M0v7 : verifiedR false 9 7 M0t7 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v6
  apply checkBuckets
  simp only [M0g7, M0b7_0, M0b7_1, M0b7_2, M0b7_3, M0b7_4, M0b7_5, M0b7_6, M0b7_7, M0b7_8, M0b7_9, M0b7_10, M0b7_11, M0b7_13, M0b7_14, M0b7_15, M0b7_16, M0b7_17, M0b7_18, M0b7_19, M0b7_20, M0b7_21, M0b7_22, M0b7_23, M0b7_25, M0b7_26, M0b7_27, M0b7_28, M0b7_29, M0b7_30, M0b7_31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p7b0c0Ok, M0p7b1c0Ok, M0p7b2c0Ok, M0p7b3c0Ok, M0p7b4c0Ok, M0p7b5c0Ok, M0p7b6c0Ok, M0p7b7c0Ok, M0p7b7c1Ok, M0p7b7c2Ok, M0p7b7c3Ok, M0p7b7c4Ok, M0p7b7c5Ok, M0p7b8c0Ok, M0p7b8c1Ok, M0p7b9c0Ok, M0p7b10c0Ok, M0p7b10c1Ok, M0p7b10c2Ok, M0p7b10c3Ok, M0p7b10c4Ok, M0p7b10c5Ok, M0p7b10c6Ok, M0p7b10c7Ok, M0p7b10c8Ok, M0p7b10c9Ok, M0p7b10c10Ok, M0p7b10c11Ok, M0p7b10c12Ok, M0p7b10c13Ok, M0p7b10c14Ok, M0p7b11c0Ok, M0p7b13c0Ok, M0p7b14c0Ok, M0p7b15c0Ok, M0p7b16c0Ok, M0p7b16c1Ok, M0p7b17c0Ok, M0p7b18c0Ok, M0p7b18c1Ok, M0p7b19c0Ok, M0p7b20c0Ok, M0p7b21c0Ok, M0p7b21c1Ok, M0p7b21c2Ok, M0p7b21c3Ok, M0p7b21c4Ok, M0p7b22c0Ok, M0p7b23c0Ok, M0p7b23c1Ok, M0p7b23c2Ok, M0p7b23c3Ok, M0p7b25c0Ok, M0p7b25c1Ok, M0p7b25c2Ok, M0p7b26c0Ok, M0p7b27c0Ok, M0p7b27c1Ok, M0p7b27c2Ok, M0p7b28c0Ok, M0p7b29c0Ok, M0p7b30c0Ok, M0p7b31c0Ok, M0p7b31c1Ok, M0p7b31c2Ok, M0p7b31c3Ok]
def M0p8b1c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w173,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b1c0Ok : M0p8b1c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_1 : List Entry := M0p8b1c0
def M0p8b2c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w146,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b2c0Ok : M0p8b2c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_2 : List Entry := M0p8b2c0
def M0p8b4c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w139,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b4c0Ok : M0p8b4c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_4 : List Entry := M0p8b4c0
def M0p8b5c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w205,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b5c0Ok : M0p8b5c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_5 : List Entry := M0p8b5c0
def M0p8b6c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w185,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w218,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w221,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w247]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w248])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b6c0Ok : M0p8b6c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_6 : List Entry := M0p8b6c0
def M0p8b7c0 : List Entry := [([],[M0w60,M0w73,M0w93,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w95,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w133,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w136,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b7c0Ok : M0p8b7c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_7 : List Entry := M0p8b7c0
def M0p8b8c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w140,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b8c0Ok : M0p8b8c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_8 : List Entry := M0p8b8c0
def M0p8b10c0 : List Entry := [([],[M0w0,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w2,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w3,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w4,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w6,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w8,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c0Ok : M0p8b10c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0p8b10c1 : List Entry := [([],[M0w11,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w13,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w16,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w22,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w26,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w28,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c1Ok : M0p8b10c1.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0p8b10c2 : List Entry := [([],[M0w30,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w33,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w41,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w43,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w46,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w50,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c2Ok : M0p8b10c2.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0p8b10c3 : List Entry := [([],[M0w56,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w85,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w210,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c3Ok : M0p8b10c3.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_10 : List Entry := M0p8b10c0 ++ M0p8b10c1 ++ M0p8b10c2 ++ M0p8b10c3
def M0p8b12c0 : List Entry := [([],[M0w60,M0w73,M0w86,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b12c0Ok : M0p8b12c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_12 : List Entry := M0p8b12c0
def M0p8b14c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w148,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w211,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b14c0Ok : M0p8b14c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_14 : List Entry := M0p8b14c0
def M0p8b16c0 : List Entry := [([],[M0w60,M0w73,M0w97,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w157,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w159,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w174,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w175,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b16c0Ok : M0p8b16c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_16 : List Entry := M0p8b16c0
def M0p8b17c0 : List Entry := [([],[M0w60,M0w73,M0w89,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b17c0Ok : M0p8b17c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_17 : List Entry := M0p8b17c0
def M0p8b18c0 : List Entry := [([],[M0w60,M0w73,M0w107,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b18c0Ok : M0p8b18c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_18 : List Entry := M0p8b18c0
def M0p8b20c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w251])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b20c0Ok : M0p8b20c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_20 : List Entry := M0p8b20c0
def M0p8b21c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w176,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w179,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w203,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w206,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b21c0Ok : M0p8b21c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_21 : List Entry := M0p8b21c0
def M0p8b22c0 : List Entry := [([],[M0w60,M0w73,M0w97,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b22c0Ok : M0p8b22c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_22 : List Entry := M0p8b22c0
def M0p8b23c0 : List Entry := [([],[M0w60,M0w73,M0w110,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w209,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b23c0Ok : M0p8b23c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_23 : List Entry := M0p8b23c0
def M0p8b24c0 : List Entry := [([],[M0w60,M0w73,M0w87,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b24c0Ok : M0p8b24c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_24 : List Entry := M0p8b24c0
def M0p8b25c0 : List Entry := [([],[M0w9,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b25c0Ok : M0p8b25c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_25 : List Entry := M0p8b25c0
def M0p8b26c0 : List Entry := [([],[M0w12,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b26c0Ok : M0p8b26c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_26 : List Entry := M0p8b26c0
def M0p8b27c0 : List Entry := [([],[M0w37,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230]),
([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230,M0w246])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b27c0Ok : M0p8b27c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_27 : List Entry := M0p8b27c0
def M0p8b30c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w215,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b30c0Ok : M0p8b30c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_30 : List Entry := M0p8b30c0
def M0p8b31c0 : List Entry := [([],[M0w14,M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p8b31c0Ok : M0p8b31c0.all (testRow chart false M0t7 7) = true := by decide +kernel
def M0b8_31 : List Entry := M0p8b31c0
def M0g8 : List (List Entry) := [[], M0b8_1, M0b8_2, [], M0b8_4, M0b8_5, M0b8_6, M0b8_7, M0b8_8, [], M0b8_10, [], M0b8_12, [], M0b8_14, [], M0b8_16, M0b8_17, M0b8_18, [], M0b8_20, M0b8_21, M0b8_22, M0b8_23, M0b8_24, M0b8_25, M0b8_26, M0b8_27, [], [], M0b8_30, M0b8_31]
def M0t8 : Nat → List Entry := bucketOf M0g8
set_option maxRecDepth 160000 in
lemma M0v8 : verifiedR false 9 8 M0t8 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v7
  apply checkBuckets
  simp only [M0g8, M0b8_1, M0b8_2, M0b8_4, M0b8_5, M0b8_6, M0b8_7, M0b8_8, M0b8_10, M0b8_12, M0b8_14, M0b8_16, M0b8_17, M0b8_18, M0b8_20, M0b8_21, M0b8_22, M0b8_23, M0b8_24, M0b8_25, M0b8_26, M0b8_27, M0b8_30, M0b8_31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p8b1c0Ok, M0p8b2c0Ok, M0p8b4c0Ok, M0p8b5c0Ok, M0p8b6c0Ok, M0p8b7c0Ok, M0p8b8c0Ok, M0p8b10c0Ok, M0p8b10c1Ok, M0p8b10c2Ok, M0p8b10c3Ok, M0p8b12c0Ok, M0p8b14c0Ok, M0p8b16c0Ok, M0p8b17c0Ok, M0p8b18c0Ok, M0p8b20c0Ok, M0p8b21c0Ok, M0p8b22c0Ok, M0p8b23c0Ok, M0p8b24c0Ok, M0p8b25c0Ok, M0p8b26c0Ok, M0p8b27c0Ok, M0p8b30c0Ok, M0p8b31c0Ok]
def M0p9b10c0 : List Entry := [([],[M0w60,M0w73,M0w126,M0w166,M0w195,M0w230])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M0p9b10c0Ok : M0p9b10c0.all (testRow chart false M0t8 8) = true := by decide +kernel
def M0b9_10 : List Entry := M0p9b10c0
def M0g9 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], M0b9_10, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t9 : Nat → List Entry := bucketOf M0g9
set_option maxRecDepth 160000 in
lemma M0v9 : verifiedR false 9 9 M0t9 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M0v8
  apply checkBuckets
  simp only [M0g9, M0b9_10, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p9b10c0Ok]
lemma cert0 : ∀ j ≤ 9, ¬ BL j minor0.toFinset := by
  intro j hj live
  have eq := sortFinset minor0
  exact M0v9 [] (sortSignals minor0) (hit_mem (by decide +kernel)) (by decide +kernel)
    (by simp [preserve,resources,attachLoss,underlying]) j hj (eq.symm ▸ live)

def M3w0 : Sig := (0x1ff00000ff80,0x3001800c00600300)
def M3w1 : Sig := (0x3fe00001ff0000,0xc006003001800c00)
def M3w2 : Sig := (0x40055002002a80,0x0)
def M3w3 : Sig := (0x49a000024d0000,0x0)
def M3w4 : Sig := (0x800a6004005300,0x0)
def M3w5 : Sig := (0x92c00004960000,0x0)
def M3w6 : Sig := (0xc0e07006070380,0x50fa87d43ea1f50f)
def M3w7 : Sig := (0x100138008009c00,0x0)
def M3w8 : Sig := (0x1001ff00800ff80,0x3001800c00600300)
def M3w9 : Sig := (0x123000009180000,0x8004002001000800)
def M3w10 : Sig := (0x18242a00c121500,0xd35e9af4d7a6bd35)
def M3w11 : Sig := (0x1c003f00e001f80,0x1008804402201100)
def M3w12 : Sig := (0x1c007f00e003f80,0x1008804402201100)
def M3w13 : Sig := (0x1c01ff00e00ff80,0x3009804c02601300)
def M3w14 : Sig := (0x1c0e3f00e071f80,0x50fa87d43ea1f50f)
def M3w15 : Sig := (0x1c243f00e121f80,0xd35e9af4d7a6bd35)
def M3w16 : Sig := (0x1c2e2f00e171780,0xd3fe9ff4ffa7fd3f)
def M3w17 : Sig := (0x1c3e0000e1f0000,0xc00e007003801c00)
def M3w18 : Sig := (0x1c3e0700e1f0380,0xd0fe87f43fa1fd0f)
def M3w19 : Sig := (0x1c3e2a00e1f1500,0xd35e9af4d7a6bd35)
def M3w20 : Sig := (0x2001c001000e000,0x2001000800400200)
def M3w21 : Sig := (0x23c000011e00000,0x0)
def M3w22 : Sig := (0x23fe00011ff0000,0xc006003001800c00)
def M3w23 : Sig := (0x24c241012612080,0x7c3be1df0ef877c3)
def M3w24 : Sig := (0x2c00c7016006380,0x3009804c02601300)
def M3w25 : Sig := (0x2c0ec7016076380,0x70fb87dc3ee1f70f)
def M3w26 : Sig := (0x2cc2c7016616380,0x7c3be1df0ef877c3)
def M3w27 : Sig := (0x2cce47016672380,0x7cfbe7df3ef9f7cf)
def M3w28 : Sig := (0x2dce00016e70000,0x400a005002801400)
def M3w29 : Sig := (0x2dce07016e70380,0x50fa87d43ea1f50f)
def M3w30 : Sig := (0x2dce41016e72080,0x7c3be1df0ef877c3)
def M3w31 : Sig := (0x2dee00016f70000,0x400a005002801400)
def M3w32 : Sig := (0x2ffe00017ff0000,0xc00e007003801c00)
def M3w33 : Sig := (0x34015901a00ac80,0x3009804c02601300)
def M3w34 : Sig := (0x3401ff01a00ff80,0x3009804c02601300)
def M3w35 : Sig := (0x34c35901a61ac80,0x7c3be1df0ef877c3)
def M3w36 : Sig := (0x36d20001b690000,0xc00e007003801c00)
def M3w37 : Sig := (0x36d24101b692080,0xfc3fe1ff0ff87fc3)
def M3w38 : Sig := (0x36d35901b69ac80,0xf00f807c03e01f00)
def M3w39 : Sig := (0x37fe0001bff0000,0xc00e007003801c00)
def M3w40 : Sig := (0x3801aa01c00d500,0x3009804c02601300)
def M3w41 : Sig := (0x3801ff01c00ff80,0x3009804c02601300)
def M3w42 : Sig := (0x3825aa01c12d500,0xf35f9afcd7e6bf35)
def M3w43 : Sig := (0x3b640001db20000,0xc00e007003801c00)
def M3w44 : Sig := (0x3b642a01db21500,0xd35e9af4d7a6bd35)
def M3w45 : Sig := (0x3b65aa01db2d500,0xf00f807c03e01f00)
def M3w46 : Sig := (0x3bfe0001dff0000,0xc00e007003801c00)
def M3w47 : Sig := (0x3c000001e000000,0x8004002001000)
def M3w48 : Sig := (0x3c00ff01e007f80,0x3009804c02601300)
def M3w49 : Sig := (0x3c017f01e00bf80,0x3009804c02601300)
def M3w50 : Sig := (0x3c01ef01e00f780,0x3009804c02601300)
def M3w51 : Sig := (0x3c01ff01e00ff80,0x3009804c02601300)
def M3w52 : Sig := (0x3c0fff01e07ff80,0x70fb87dc3ee1f70f)
def M3w53 : Sig := (0x3c3fff01e1fff80,0xf00f807c03e01f00)
def M3w54 : Sig := (0x3c9bff01e4dff80,0x3009804c02601300)
def M3w55 : Sig := (0x3cc3ff01e61ff80,0x7c3be1df0ef877c3)
def M3w56 : Sig := (0x3d2dff01e96ff80,0x3009804c02601300)
def M3w57 : Sig := (0x3dcfff01ee7ff80,0x700b805c02e01700)
def M3w58 : Sig := (0x3dfe0001eff0000,0xc00e007003801c00)
def M3w59 : Sig := (0x3ed3ff01f69ff80,0xf00f807c03e01f00)
def M3w60 : Sig := (0x3efe0001f7f0000,0xc00e007003801c00)
def M3w61 : Sig := (0x3f65ff01fb2ff80,0xf00f807c03e01f00)
def M3w62 : Sig := (0x3fc1ff01fe0ff80,0x3009804c02601300)
def M3w63 : Sig := (0x3fee0001ff70000,0xc00e007003801c00)
def M3w64 : Sig := (0x3ffe0001fff0000,0xc00e007003801c00)
def M3w65 : Sig := (0x3ffe0701fff0380,0xd0fe87f43fa1fd0f)
def M3w66 : Sig := (0x3ffe2a01fff1500,0xd35e9af4d7a6bd35)
def M3w67 : Sig := (0x3ffe3f01fff1f80,0xd00e807403a01d00)
def M3w68 : Sig := (0x3ffe5501fff2a80,0xc00e007003801c00)
def M3w69 : Sig := (0x3ffea601fff5300,0xc00e007003801c00)
def M3w70 : Sig := (0x3ffec701fff6380,0xf00f807c03e01f00)
def M3w71 : Sig := (0x3fff3801fff9c00,0xc00e007003801c00)
def M3w72 : Sig := (0x3fff5901fffac80,0xf00f807c03e01f00)
def M3w73 : Sig := (0x3fffaa01fffd500,0xf00f807c03e01f00)
def M3w74 : Sig := (0x3fffff01fffff80,0xf00f807c03e01f00)
def M3w75 : Sig := (0x802020840101042,0x200100080040020)
def M3w76 : Sig := (0x882c26044161302,0x2c01600b005802c)
def M3w77 : Sig := (0x8c2e27046171382,0x52fa97d4bea5f52f)
def M3w78 : Sig := (0x982c2e04c161702,0xd3de9ef4f7a7bd3d)
def M3w79 : Sig := (0x9c2c3f04e161f82,0x12c89644b225912c)
def M3w80 : Sig := (0xbc2dff05e16ff82,0x32c9964cb265932c)
def M3w81 : Sig := (0x10924a2884925144,0x240120090048024)
def M3w82 : Sig := (0x11924aa88c925544,0xd35e9af4d7a6bd35)
def M3w83 : Sig := (0x1294482094a24104,0x745ba2dd16e8b745)
def M3w84 : Sig := (0x13925aa89c92d544,0x3249924c92649324)
def M3w85 : Sig := (0x13964aa09cb25504,0xf75fbafdd7eebf75)
def M3w86 : Sig := (0x13d25ff89e92ffc4,0x3249924c92649324)
def M3w87 : Sig := (0x2048a45102452288,0x8a045022811408a)
def M3w88 : Sig := (0x20c8e47106472388,0x58fac7d63eb1f58f)
def M3w89 : Sig := (0x224ca45112652288,0x7cbbe5df2ef977cb)
def M3w90 : Sig := (0x22dce45116e72288,0x48aa45522a91548a)
def M3w91 : Sig := (0x23ffe4511fff2288,0xc8ae45722b915c8a)
def M3w92 : Sig := (0x280080414004020a,0x80040020010008)
def M3w93 : Sig := (0x30000c718000638c,0x3cf1e78f3c79e3cf)
def M3w94 : Sig := (0x30001ff18000ff8c,0x3cf1e78f3c79e3cf)
def M3w95 : Sig := (0x301008098080404c,0x0)
def M3w96 : Sig := (0x301ce00180e7000c,0x4cf267933c99e4cf)
def M3w97 : Sig := (0x3048ac718245638c,0x3cf1e78f3c79e3cf)
def M3w98 : Sig := (0x3090c8618486430c,0xc006003001800c)
def M3w99 : Sig := (0x3090cc718486638c,0x3cf1e78f3c79e3cf)
def M3w100 : Sig := (0x30924a298492514c,0x240120090048024)
def M3w101 : Sig := (0x3092c8618496430c,0xc006003001800c)
def M3w102 : Sig := (0x3092ca698496534c,0x2c01600b005802c)
def M3w103 : Sig := (0x30c0ec718607638c,0x7cfbe7df3ef9f7cf)
def M3w104 : Sig := (0x30d0e8718687438c,0x50fa87d43ea1f50f)
def M3w105 : Sig := (0x321c0c0190e0600c,0x2c01600b005802c0)
def M3w106 : Sig := (0x321c0c7190e0638c,0x3cf1e78f3c79e3cf)
def M3w107 : Sig := (0x324c2c719261638c,0x7cfbe7df3ef9f7cf)
def M3w108 : Sig := (0x325c2c1192e1608c,0x7c3be1df0ef877c3)
def M3w109 : Sig := (0x325cac5192e5628c,0x2ca1650b285942ca)
def M3w110 : Sig := (0x325ce41192e7208c,0x7cfbe7df3ef9f7cf)
def M3w111 : Sig := (0x32944c7194a2638c,0x7cfbe7df3ef9f7cf)
def M3w112 : Sig := (0x329ce82194e7410c,0x7cfbe7df3ef9f7cf)
def M3w113 : Sig := (0x32c00c719600638c,0x3cf9e7cf3e79f3cf)
def M3w114 : Sig := (0x32d0cc719686638c,0x30c9864c3261930c)
def M3w115 : Sig := (0x32dc0c7196e0638c,0x3c09e04f027813c0)
def M3w116 : Sig := (0x32dcec7196e7638c,0x7cfbe7df3ef9f7cf)
def M3w117 : Sig := (0x32dcec7996e763cc,0x7cfbe7df3ef9f7cf)
def M3w118 : Sig := (0x32dced7196e76b8c,0x7cfbe7df3ef9f7cf)
def M3w119 : Sig := (0x32dcee7196e7738c,0x7cfbe7df3ef9f7cf)
def M3w120 : Sig := (0x32ddec7196ef638c,0x7cfbe7df3ef9f7cf)
def M3w121 : Sig := (0x32deec7196f7638c,0x7cfbe7df3ef9f7cf)
def M3w122 : Sig := (0x32deee7996f773cc,0x7efbf7dfbefdf7ef)
def M3w123 : Sig := (0x32fcec7197e7638c,0x7cfbe7df3ef9f7cf)
def M3w124 : Sig := (0x32ffec7197ff638c,0xfcffe7ff3ff9ffcf)
def M3w125 : Sig := (0x33d01ff99e80ffcc,0x3009804c02601300)
def M3w126 : Sig := (0x33d0dff19e86ff8c,0x30c9864c3261930c)
def M3w127 : Sig := (0x33dc1ff19ee0ff8c,0x3c09e04f027813c0)
def M3w128 : Sig := (0x33dcfff19ee7ff8c,0x7cfbe7df3ef9f7cf)
def M3w129 : Sig := (0x33ffe8099fff404c,0xc00e007003801c00)
def M3w130 : Sig := (0x33ffec719fff638c,0xfcffe7ff3ff9ffcf)
def M3w131 : Sig := (0x38000a69c000534e,0x2c01600b005802c)
def M3w132 : Sig := (0x38000e79c00073ce,0x3ef1f78fbc7de3ef)
def M3w133 : Sig := (0x38001ff9c000ffce,0x32c1960cb065832c)
def M3w134 : Sig := (0x3812c009c096004e,0x2c01600b005802c)
def M3w135 : Sig := (0x3882ca69c416534e,0x2c01600b005802c)
def M3w136 : Sig := (0x38924a69c492534e,0x2c01600b005802c)
def M3w137 : Sig := (0x3892c869c496434e,0x2c01600b005802c)
def M3w138 : Sig := (0x3892ca29c496514e,0x2c01600b005802c)
def M3w139 : Sig := (0x3892ca61c496530e,0x2c01600b005802c)
def M3w140 : Sig := (0x3892ca69c496534e,0x2c01600b005802c)
def M3w141 : Sig := (0x3892dff9c496ffce,0x32c1960cb065832c)
def M3w142 : Sig := (0x38d2cf79c6967bce,0x2c01600b005802c)
def M3w143 : Sig := (0x38d2ea79c69753ce,0x52fa97d4bea5f52f)
def M3w144 : Sig := (0x38daee79c6d773ce,0xae05702b815c0ae)
def M3w145 : Sig := (0x38dbea69c6df534e,0x2c01600b005802c)
def M3w146 : Sig := (0x3992dbe9cc96df4e,0x2c01600b005802c)
def M3w147 : Sig := (0x39d2cbf9ce965fce,0x12c89644b225912c)
def M3w148 : Sig := (0x3abeca69d5f6534e,0x2c01600b005802c)
def M3w149 : Sig := (0x3ad2ce79d69673ce,0x32c9964cb265932c)
def M3w150 : Sig := (0x3adeee79d6f773ce,0x7efbf7dfbefdf7ef)
def M3w151 : Sig := (0x3b92dae9dc96d74e,0x32c9964cb265932c)
def M3w152 : Sig := (0x3bc01ff9de00ffce,0x32c9964cb265932c)
def M3w153 : Sig := (0x3bd2dff9de96ffce,0x32c9964cb265932c)
def M3w154 : Sig := (0x3bffea69dfff534e,0xc2ce1670b3859c2c)
def M3w155 : Sig := (0x4122128a09109450,0x83041820c1060830)
def M3w156 : Sig := (0x41a252aa0d129550,0xd35e9af4d7a6bd35)
def M3w157 : Sig := (0x4324108219208410,0xf51fa8fd47ea3f51)
def M3w158 : Sig := (0x4326128a19309450,0xf71fb8fdc7ee3f71)
def M3w159 : Sig := (0x436415921b20ac90,0xf51fa8fd47ea3f51)
def M3w160 : Sig := (0x436c34921b61a490,0xfd3fe9ff4ffa7fd3)
def M3w161 : Sig := (0x436d30821b698410,0xf51fa8fd47ea3f51)
def M3w162 : Sig := (0x43a41aa21d20d510,0xf51fa8fd47ea3f51)
def M3w163 : Sig := (0x43a652a21d329510,0xf75fbafdd7eebf75)
def M3w164 : Sig := (0x43b650821db28410,0xf51fa8fd47ea3f51)
def M3w165 : Sig := (0x43b6528a1db29450,0xc30e1870c3861c30)
def M3w166 : Sig := (0x43e41ff21f20ff90,0xf51fa8fd47ea3f51)
def M3w167 : Sig := (0x43fff0821fff8410,0xf51fa8fd47ea3f51)
def M3w168 : Sig := (0x43fff28a1fff9450,0xc30e1870c3861c30)
def M3w169 : Sig := (0x50001aaa8000d554,0x3751ba8dd46ea375)
def M3w170 : Sig := (0x50001ffa8000ffd4,0x3751ba8dd46ea375)
def M3w171 : Sig := (0x5036400a81b20054,0xc7563ab1d58eac75)
def M3w172 : Sig := (0x50925aaa8492d554,0x3751ba8dd46ea375)
def M3w173 : Sig := (0x51221aaa8910d554,0xb755baadd56eab75)
def M3w174 : Sig := (0x51825aaa8c12d554,0xf75fbafdd7eebf75)
def M3w175 : Sig := (0x5234180a91a0c054,0x2401200900480240)
def M3w176 : Sig := (0x52341aaa91a0d554,0x3751ba8dd46ea375)
def M3w177 : Sig := (0x52b6482a95b24154,0xf75fbafdd7eebf75)
def M3w178 : Sig := (0x53241aaa9920d554,0xf75fbafdd7eebf75)
def M3w179 : Sig := (0x5334188a99a0c454,0xf51fa8fd47ea3f51)
def M3w180 : Sig := (0x53361a8a99b0d454,0xa7053829c14e0a70)
def M3w181 : Sig := (0x5336508a99b28454,0xf75fbafdd7eebf75)
def M3w182 : Sig := (0x53801aaa9c00d554,0x3759bacdd66eb375)
def M3w183 : Sig := (0x53b65aaa9db2d554,0xf75fbafdd7eebf75)
def M3w184 : Sig := (0x53b65aea9db2d754,0xf75fbafdd7eebf75)
def M3w185 : Sig := (0x53b65baa9db2dd54,0xf75fbafdd7eebf75)
def M3w186 : Sig := (0x53b6daaa9db6d554,0xf75fbafdd7eebf75)
def M3w187 : Sig := (0x53be5aaa9df2d554,0xf75fbafdd7eebf75)
def M3w188 : Sig := (0x53c01ffa9e00ffd4,0x3759bacdd66eb375)
def M3w189 : Sig := (0x53f41ffa9fa0ffd4,0x3409a04d02681340)
def M3w190 : Sig := (0x53f65ffa9fb2ffd4,0xf75fbafdd7eebf75)
def M3w191 : Sig := (0x53fffaaa9fffd554,0xf75fbafdd7eebf75)
def M3w192 : Sig := (0x70001efb8000f7dc,0x3ff1ff8ffc7fe3ff)
def M3w193 : Sig := (0x703ee00b81f7005c,0xcff67fb3fd9fecff)
def M3w194 : Sig := (0x7234180b91a0c05c,0x2401200900480240)
def M3w195 : Sig := (0x723c1c0b91e0e05c,0x2c01600b005802c0)
def M3w196 : Sig := (0x73b65aab9db2d55c,0xf75fbafdd7eebf75)
def M3w197 : Sig := (0x73b6daeb9db6d75c,0xf7dfbefdf7efbf7d)
def M3w198 : Sig := (0x73fefefb9ff7f7dc,0xffffffffffffffff)
def M3w199 : Sig := (0x78001aebc000d75e,0x37d1be8df46fa37d)
def M3w200 : Sig := (0x7892daebc496d75e,0x37d1be8df46fa37d)
def M3w201 : Sig := (0x79b2daebcd96d75e,0x83c41e20f107883c)
def M3w202 : Sig := (0x7bb6daebddb6d75e,0xf7dfbefdf7efbf7d)
def M3w203 : Sig := (0xa008040500402028,0x800400200100080)
def M3w204 : Sig := (0xc020100e01008070,0x0)
def M3w205 : Sig := (0xc22c14061160a030,0x2c01600b005802c0)
def M3w206 : Sig := (0xc26c34161361a0b0,0x7c3be1df0ef877c3)
def M3w207 : Sig := (0xc32c14861960a430,0xfd1fe8ff47fa3fd1)
def M3w208 : Sig := (0xc36c15961b60acb0,0x3c09e04f027813c0)
def M3w209 : Sig := (0xc3e01ffe1f00fff0,0x3009804c02601300)
def M3w210 : Sig := (0xc3ec1ff61f60ffb0,0x3c09e04f027813c0)
def M3w211 : Sig := (0xc3fff00e1fff8070,0xc00e007003801c00)
def M3w212 : Sig := (0xd3b65aae9db2d574,0xf75fbafdd7eebf75)
def M3w213 : Sig := (0xf0001c0f8000e07c,0x2c01600b005802c0)
def M3w214 : Sig := (0xf0001c7f8000e3fc,0x3cf1e78f3c79e3cf)
def M3w215 : Sig := (0xf0001eaf8000f57c,0x3f51fa8fd47ea3f5)
def M3w216 : Sig := (0xf03c000f81e0007c,0xc006003001800c0)
def M3w217 : Sig := (0xf22c1c0f9160e07c,0x2c01600b005802c0)
def M3w218 : Sig := (0xf2341c0f91a0e07c,0x2c01600b005802c0)
def M3w219 : Sig := (0xf23c000f91e0007c,0xc006003001800c0)
def M3w220 : Sig := (0xf23c0c0f91e0607c,0x2c01600b005802c0)
def M3w221 : Sig := (0xf23c140f91e0a07c,0x2c01600b005802c0)
def M3w222 : Sig := (0xf23c180f91e0c07c,0x2c01600b005802c0)
def M3w223 : Sig := (0xf23c1c0f91e0e07c,0x2c01600b005802c0)
def M3w224 : Sig := (0xf23c1c7f91e0e3fc,0x3cf1e78f3c79e3cf)
def M3w225 : Sig := (0xf23c1eaf91e0f57c,0x3f51fa8fd47ea3f5)
def M3w226 : Sig := (0xf23c1fff91e0fffc,0x3c01e00f007803c0)
def M3w227 : Sig := (0xf27c1d5f93e0eafc,0x2c01600b005802c0)
def M3w228 : Sig := (0xf27c3c1f93e1e0fc,0x7c3be1df0ef877c3)
def M3w229 : Sig := (0xf27cbc5f93e5e2fc,0x2ca1650b285942ca)
def M3w230 : Sig := (0xf27dbc0f93ede07c,0x2c01600b005802c0)
def M3w231 : Sig := (0xf2bc1e6f95e0f37c,0x2c01600b005802c0)
def M3w232 : Sig := (0xf2bedc0f95f6e07c,0x2c01600b005802c0)
def M3w233 : Sig := (0xf2fc1c7f97e0e3fc,0x3c09e04f027813c0)
def M3w234 : Sig := (0xf2fcfc7f97e7e3fc,0x7cfbe7df3ef9f7cf)
def M3w235 : Sig := (0xf33c1f8f99e0fc7c,0x2c01600b005802c0)
def M3w236 : Sig := (0xf33e1e8f99f0f47c,0xaf05782bc15e0af0)
def M3w237 : Sig := (0xf37c1d9f9be0ecfc,0x3c09e04f027813c0)
def M3w238 : Sig := (0xf3bc1eaf9de0f57c,0x3c09e04f027813c0)
def M3w239 : Sig := (0xf3be5aaf9df2d57c,0xff5ffaffd7febff5)
def M3w240 : Sig := (0xf3be5eaf9df2f57c,0xff5ffaffd7febff5)
def M3w241 : Sig := (0xf3c01fff9e00fffc,0x3c09e04f027813c0)
def M3w242 : Sig := (0xf3fc1fff9fe0fffc,0x3c09e04f027813c0)
def M3w243 : Sig := (0xf3fffc0f9fffe07c,0xec0f607b03d81ec0)
def M3w244 : Sig := (0xf8b2da6fc596d37e,0x2c01600b005802c)
def M3w245 : Sig := (0xfabede6fd5f6f37e,0x2ec1760bb05d82ec)
def M3t0 : Nat → List Entry := fun _ => []
lemma M3v0 : verifiedR false 9 0 M3t0 := emptyR _ _
def M3g1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M3t1 : Nat → List Entry := bucketOf M3g1
set_option maxRecDepth 160000 in
lemma M3v1 : verifiedR false 9 1 M3t1 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v0
  apply checkBuckets
  simp only [M3g1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M3g2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M3t2 : Nat → List Entry := bucketOf M3g2
set_option maxRecDepth 160000 in
lemma M3v2 : verifiedR false 9 2 M3t2 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v1
  apply checkBuckets
  simp only [M3g2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M3g3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M3t3 : Nat → List Entry := bucketOf M3g3
set_option maxRecDepth 160000 in
lemma M3v3 : verifiedR false 9 3 M3t3 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v2
  apply checkBuckets
  simp only [M3g3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M3g4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M3t4 : Nat → List Entry := bucketOf M3g4
set_option maxRecDepth 160000 in
lemma M3v4 : verifiedR false 9 4 M3t4 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v3
  apply checkBuckets
  simp only [M3g4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M3g5 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M3t5 : Nat → List Entry := bucketOf M3g5
set_option maxRecDepth 160000 in
lemma M3v5 : verifiedR false 9 5 M3t5 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v4
  apply checkBuckets
  simp only [M3g5, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def M3p6b0c0 : List Entry := [([],[M3w10,M3w23,M3w51,M3w64,M3w87,M3w140,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b0c0Ok : M3p6b0c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_0 : List Entry := M3p6b0c0
def M3p6b3c0 : List Entry := [([],[M3w23,M3w36,M3w51,M3w74,M3w116,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w116,M3w178,M3w223]),
([],[M3w23,M3w51,M3w64,M3w116,M3w183,M3w232]),
([],[M3w23,M3w56,M3w64,M3w116,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b3c0Ok : M3p6b3c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_3 : List Entry := M3p6b3c0
def M3p6b4c0 : List Entry := [([],[M3w23,M3w51,M3w64,M3w116,M3w157,M3w169,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b4c0Ok : M3p6b4c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_4 : List Entry := M3p6b4c0
def M3p6b5c0 : List Entry := [([],[M3w16,M3w23,M3w51,M3w64,M3w140,M3w183])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b5c0Ok : M3p6b5c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_5 : List Entry := M3p6b5c0
def M3p6b6c0 : List Entry := [([],[M3w10,M3w40,M3w64,M3w74,M3w116,M3w140,M3w223]),
([],[M3w10,M3w51,M3w64,M3w112,M3w140,M3w223]),
([],[M3w10,M3w51,M3w64,M3w116,M3w142,M3w223]),
([],[M3w10,M3w51,M3w68,M3w116,M3w140,M3w223]),
([],[M3w23,M3w51,M3w93,M3w140,M3w169,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b6c0Ok : M3p6b6c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_6 : List Entry := M3p6b6c0
def M3p6b7c0 : List Entry := [([],[M3w10,M3w27,M3w51,M3w64,M3w140,M3w183]),
([],[M3w10,M3w51,M3w64,M3w116,M3w153,M3w157,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b7c0Ok : M3p6b7c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_7 : List Entry := M3p6b7c0
def M3p6b9c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w93,M3w140,M3w183,M3w242]),
([],[M3w6,M3w51,M3w74,M3w93,M3w140,M3w183,M3w223]),
([],[M3w6,M3w64,M3w74,M3w116,M3w140,M3w183,M3w242]),
([],[M3w10,M3w64,M3w116,M3w140,M3w153,M3w183,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b9c0Ok : M3p6b9c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_9 : List Entry := M3p6b9c0
def M3p6b10c0 : List Entry := [([],[M3w6,M3w10,M3w23,M3w51,M3w64,M3w140,M3w183]),
([],[M3w10,M3w23,M3w51,M3w64,M3w76,M3w116,M3w183])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b10c0Ok : M3p6b10c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_10 : List Entry := M3p6b10c0
def M3p6b13c0 : List Entry := [([],[M3w51,M3w116,M3w129,M3w157,M3w183,M3w223]),
([],[M3w51,M3w116,M3w140,M3w157,M3w192,M3w223]),
([],[M3w64,M3w116,M3w125,M3w157,M3w183,M3w223]),
([],[M3w64,M3w116,M3w140,M3w157,M3w193,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b13c0Ok : M3p6b13c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_13 : List Entry := M3p6b13c0
def M3p6b15c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w169,M3w242]),
([],[M3w10,M3w51,M3w74,M3w116,M3w140,M3w169,M3w223]),
([],[M3w10,M3w51,M3w74,M3w116,M3w140,M3w183,M3w213]),
([],[M3w74,M3w93,M3w116,M3w140,M3w153,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b15c0Ok : M3p6b15c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_15 : List Entry := M3p6b15c0
def M3p6b17c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w157,M3w183,M3w205,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b17c0Ok : M3p6b17c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_17 : List Entry := M3p6b17c0
def M3p6b18c0 : List Entry := [([],[M3w51,M3w64,M3w93,M3w140,M3w155,M3w157,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b18c0Ok : M3p6b18c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_18 : List Entry := M3p6b18c0
def M3p6b21c0 : List Entry := [([],[M3w16,M3w51,M3w64,M3w116,M3w140,M3w157]),
([],[M3w17,M3w51,M3w93,M3w116,M3w140,M3w183,M3w242]),
([],[M3w27,M3w51,M3w64,M3w157,M3w183,M3w223]),
([],[M3w51,M3w93,M3w116,M3w140,M3w178,M3w223]),
([],[M3w51,M3w93,M3w116,M3w140,M3w183,M3w232]),
([],[M3w56,M3w93,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b21c0Ok : M3p6b21c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_21 : List Entry := M3p6b21c0
def M3p6b22c0 : List Entry := [([],[M3w24,M3w64,M3w93,M3w140,M3w183,M3w223,M3w242]),
([],[M3w51,M3w93,M3w116,M3w131,M3w157,M3w183,M3w223]),
([],[M3w51,M3w93,M3w116,M3w140,M3w157,M3w169,M3w223]),
([],[M3w64,M3w112,M3w140,M3w183,M3w223,M3w242]),
([],[M3w64,M3w116,M3w142,M3w183,M3w223,M3w242]),
([],[M3w68,M3w116,M3w140,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b22c0Ok : M3p6b22c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_22 : List Entry := M3p6b22c0
def M3p6b23c0 : List Entry := [([],[M3w64,M3w116,M3w140,M3w157,M3w190,M3w223,M3w242]),
([],[M3w64,M3w116,M3w153,M3w157,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b23c0Ok : M3p6b23c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_23 : List Entry := M3p6b23c0
def M3p6b24c0 : List Entry := [([],[M3w6,M3w23,M3w51,M3w64,M3w157,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b24c0Ok : M3p6b24c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_24 : List Entry := M3p6b24c0
def M3p6b26c0 : List Entry := [([],[M3w6,M3w10,M3w51,M3w64,M3w116,M3w140,M3w157]),
([],[M3w51,M3w64,M3w93,M3w140,M3w177,M3w223]),
([],[M3w51,M3w64,M3w93,M3w140,M3w183,M3w235]),
([],[M3w51,M3w64,M3w93,M3w146,M3w183,M3w223]),
([],[M3w51,M3w64,M3w103,M3w140,M3w183,M3w242]),
([],[M3w51,M3w64,M3w116,M3w140,M3w174,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b26c0Ok : M3p6b26c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3p6b26c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w148,M3w183,M3w242]),
([],[M3w51,M3w74,M3w103,M3w140,M3w183,M3w223]),
([],[M3w51,M3w74,M3w116,M3w140,M3w174,M3w223]),
([],[M3w51,M3w74,M3w116,M3w148,M3w183,M3w223]),
([],[M3w64,M3w74,M3w116,M3w140,M3w177,M3w223]),
([],[M3w64,M3w74,M3w116,M3w140,M3w183,M3w235])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b26c1Ok : M3p6b26c1.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3p6b26c2 : List Entry := [([],[M3w64,M3w74,M3w116,M3w146,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b26c2Ok : M3p6b26c2.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_26 : List Entry := M3p6b26c0 ++ M3p6b26c1 ++ M3p6b26c2
def M3p6b29c0 : List Entry := [([],[M3w23,M3w51,M3w64,M3w93,M3w153,M3w183,M3w223]),
([],[M3w23,M3w51,M3w140,M3w183,M3w192,M3w223]),
([],[M3w23,M3w64,M3w74,M3w116,M3w153,M3w183,M3w223]),
([],[M3w23,M3w64,M3w74,M3w128,M3w140,M3w183,M3w223]),
([],[M3w23,M3w64,M3w140,M3w183,M3w193,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b29c0Ok : M3p6b29c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_29 : List Entry := M3p6b29c0
def M3p6b31c0 : List Entry := [([],[M3w10,M3w51,M3w116,M3w129,M3w140,M3w183]),
([],[M3w10,M3w64,M3w116,M3w125,M3w140,M3w183]),
([],[M3w74,M3w116,M3w140,M3w169,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p6b31c0Ok : M3p6b31c0.all (testRow chart false M3t5 5) = true := by decide +kernel
def M3b6_31 : List Entry := M3p6b31c0
def M3g6 : List (List Entry) := [M3b6_0, [], [], M3b6_3, M3b6_4, M3b6_5, M3b6_6, M3b6_7, [], M3b6_9, M3b6_10, [], [], M3b6_13, [], M3b6_15, [], M3b6_17, M3b6_18, [], [], M3b6_21, M3b6_22, M3b6_23, M3b6_24, [], M3b6_26, [], [], M3b6_29, [], M3b6_31]
def M3t6 : Nat → List Entry := bucketOf M3g6
set_option maxRecDepth 160000 in
lemma M3v6 : verifiedR false 9 6 M3t6 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v5
  apply checkBuckets
  simp only [M3g6, M3b6_0, M3b6_3, M3b6_4, M3b6_5, M3b6_6, M3b6_7, M3b6_9, M3b6_10, M3b6_13, M3b6_15, M3b6_17, M3b6_18, M3b6_21, M3b6_22, M3b6_23, M3b6_24, M3b6_26, M3b6_29, M3b6_31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M3p6b0c0Ok, M3p6b3c0Ok, M3p6b4c0Ok, M3p6b5c0Ok, M3p6b6c0Ok, M3p6b7c0Ok, M3p6b9c0Ok, M3p6b10c0Ok, M3p6b13c0Ok, M3p6b15c0Ok, M3p6b17c0Ok, M3p6b18c0Ok, M3p6b21c0Ok, M3p6b22c0Ok, M3p6b23c0Ok, M3p6b24c0Ok, M3p6b26c0Ok, M3p6b26c1Ok, M3p6b26c2Ok, M3p6b29c0Ok, M3p6b31c0Ok]
def M3p7b0c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w229])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b0c0Ok : M3p7b0c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_0 : List Entry := M3p7b0c0
def M3p7b1c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w175,M3w183]),
([],[M3w10,M3w51,M3w64,M3w76,M3w116,M3w140,M3w183]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w202,M3w223]),
([],[M3w51,M3w64,M3w116,M3w183,M3w207,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b1c0Ok : M3p7b1c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_1 : List Entry := M3p7b1c0
def M3p7b2c0 : List Entry := [([],[M3w6,M3w10,M3w51,M3w64,M3w116,M3w140,M3w183]),
([],[M3w51,M3w64,M3w81,M3w116,M3w153,M3w183,M3w223]),
([],[M3w51,M3w64,M3w84,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w86,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w196,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w223,M3w239])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b2c0Ok : M3p7b2c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_2 : List Entry := M3p7b2c0
def M3p7b3c0 : List Entry := [([],[M3w1,M3w51,M3w116,M3w140,M3w169,M3w183,M3w223]),
([],[M3w5,M3w23,M3w51,M3w64,M3w116,M3w183,M3w223]),
([],[M3w23,M3w36,M3w51,M3w64,M3w116,M3w183,M3w223]),
([],[M3w28,M3w51,M3w116,M3w140,M3w169,M3w183,M3w223]),
([],[M3w37,M3w51,M3w64,M3w116,M3w183,M3w223]),
([],[M3w51,M3w64,M3w83,M3w93,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b3c0Ok : M3p7b3c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b3c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w223,M3w240]),
([],[M3w51,M3w64,M3w116,M3w140,M3w169,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w170,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w172,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w173,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w174,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b3c1Ok : M3p7b3c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b3c2 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w176,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w178,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w182,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w188,M3w223]),
([],[M3w51,M3w64,M3w116,M3w160,M3w183,M3w223]),
([],[M3w51,M3w74,M3w116,M3w140,M3w169,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b3c2Ok : M3p7b3c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b3c3 : List Entry := [([],[M3w64,M3w74,M3w116,M3w140,M3w171,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b3c3Ok : M3p7b3c3.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_3 : List Entry := M3p7b3c0 ++ M3p7b3c1 ++ M3p7b3c2 ++ M3p7b3c3
def M3p7b4c0 : List Entry := [([],[M3w23,M3w51,M3w64,M3w116,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w242,M3w245])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b4c0Ok : M3p7b4c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_4 : List Entry := M3p7b4c0
def M3p7b5c0 : List Entry := [([],[M3w51,M3w64,M3w93,M3w140,M3w183,M3w223,M3w234]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w214,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w224])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b5c0Ok : M3p7b5c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_5 : List Entry := M3p7b5c0
def M3p7b6c0 : List Entry := [([],[M3w2,M3w10,M3w51,M3w64,M3w116,M3w140,M3w223]),
([],[M3w10,M3w40,M3w51,M3w64,M3w116,M3w140,M3w223]),
([],[M3w23,M3w51,M3w64,M3w116,M3w140,M3w169,M3w183,M3w223]),
([],[M3w42,M3w51,M3w64,M3w116,M3w140,M3w223]),
([],[M3w51,M3w64,M3w105,M3w116,M3w140,M3w183,M3w242]),
([],[M3w51,M3w64,M3w115,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b6c0Ok : M3p7b6c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b6c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w125,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w127,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w236]),
([],[M3w51,M3w116,M3w129,M3w140,M3w183,M3w223]),
([],[M3w64,M3w116,M3w125,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b6c1Ok : M3p7b6c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_6 : List Entry := M3p7b6c0 ++ M3p7b6c1
def M3p7b7c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w157,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b7c0Ok : M3p7b7c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_7 : List Entry := M3p7b7c0
def M3p7b8c0 : List Entry := [([],[M3w51,M3w64,M3w79,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w80,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b8c0Ok : M3p7b8c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_8 : List Entry := M3p7b8c0
def M3p7b9c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w6,M3w51,M3w64,M3w93,M3w140,M3w183,M3w223]),
([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w183,M3w216]),
([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w183,M3w242]),
([],[M3w6,M3w51,M3w64,M3w130,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b9c0Ok : M3p7b9c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b9c1 : List Entry := [([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w153,M3w183,M3w223]),
([],[M3w14,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w18,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w25,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w27,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w29,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b9c1Ok : M3p7b9c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b9c2 : List Entry := [([],[M3w51,M3w52,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w65,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w108,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b9c2Ok : M3p7b9c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_9 : List Entry := M3p7b9c0 ++ M3p7b9c1 ++ M3p7b9c2
def M3p7b10c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w85,M3w116,M3w140,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w205,M3w242]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w208,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w210,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w197,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b10c0Ok : M3p7b10c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b10c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w183,M3w223,M3w244]),
([],[M3w51,M3w116,M3w140,M3w183,M3w211,M3w223]),
([],[M3w64,M3w116,M3w140,M3w183,M3w209,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b10c1Ok : M3p7b10c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_10 : List Entry := M3p7b10c0 ++ M3p7b10c1
def M3p7b11c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w140,M3w150,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w81,M3w116,M3w183,M3w223]),
([],[M3w51,M3w64,M3w77,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w169,M3w223,M3w240]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w215,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w225])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b11c0Ok : M3p7b11c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_11 : List Entry := M3p7b11c0
def M3p7b12c0 : List Entry := [([],[M3w51,M3w64,M3w90,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w91,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b12c0Ok : M3p7b12c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_12 : List Entry := M3p7b12c0
def M3p7b13c0 : List Entry := [([],[M3w23,M3w51,M3w64,M3w116,M3w183,M3w223,M3w245]),
([],[M3w23,M3w51,M3w64,M3w140,M3w183,M3w223,M3w234]),
([],[M3w51,M3w64,M3w83,M3w116,M3w140,M3w183,M3w223,M3w245]),
([],[M3w51,M3w64,M3w95,M3w116,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w198,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w171,M3w183,M3w223,M3w245])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b13c0Ok : M3p7b13c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b13c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w190,M3w223,M3w245]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w206,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b13c1Ok : M3p7b13c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_13 : List Entry := M3p7b13c0 ++ M3p7b13c1
def M3p7b14c0 : List Entry := [([],[M3w27,M3w51,M3w64,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w175,M3w183,M3w242]),
([],[M3w64,M3w116,M3w140,M3w183,M3w189,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b14c0Ok : M3p7b14c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_14 : List Entry := M3p7b14c0
def M3p7b15c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w10,M3w51,M3w64,M3w83,M3w116,M3w140,M3w223]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w169,M3w223]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w213]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w216]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b15c0Ok : M3p7b15c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b15c1 : List Entry := [([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w242]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w243]),
([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w191,M3w223]),
([],[M3w15,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w19,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w44,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b15c1Ok : M3p7b15c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b15c2 : List Entry := [([],[M3w51,M3w64,M3w66,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w93,M3w116,M3w140,M3w153,M3w183,M3w223]),
([],[M3w51,M3w64,M3w96,M3w116,M3w140,M3w154,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w128,M3w140,M3w154,M3w183,M3w223]),
([],[M3w51,M3w93,M3w116,M3w131,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b15c2Ok : M3p7b15c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_15 : List Entry := M3p7b15c0 ++ M3p7b15c1 ++ M3p7b15c2
def M3p7b16c0 : List Entry := [([],[M3w51,M3w64,M3w100,M3w116,M3w183,M3w223]),
([],[M3w51,M3w64,M3w109,M3w116,M3w140,M3w183,M3w223]),
([],[M3w64,M3w116,M3w140,M3w153,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b16c0Ok : M3p7b16c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_16 : List Entry := M3p7b16c0
def M3p7b17c0 : List Entry := [([],[M3w6,M3w23,M3w51,M3w64,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w76,M3w116,M3w183,M3w223]),
([],[M3w51,M3w64,M3w76,M3w83,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w88,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w93,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w51,M3w64,M3w96,M3w116,M3w140,M3w183,M3w223,M3w243])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b17c0Ok : M3p7b17c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b17c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w157,M3w183,M3w205,M3w223]),
([],[M3w51,M3w93,M3w116,M3w140,M3w183,M3w223,M3w243]),
([],[M3w64,M3w96,M3w116,M3w140,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b17c1Ok : M3p7b17c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_17 : List Entry := M3p7b17c0 ++ M3p7b17c1
def M3p7b18c0 : List Entry := [([],[M3w10,M3w23,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w89,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w98,M3w116,M3w153,M3w183,M3w223]),
([],[M3w51,M3w64,M3w114,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w126,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w155,M3w157,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b18c0Ok : M3p7b18c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b18c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w158,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b18c1Ok : M3p7b18c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_18 : List Entry := M3p7b18c0 ++ M3p7b18c1
def M3p7b19c0 : List Entry := [([],[M3w51,M3w64,M3w82,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w171,M3w183,M3w205,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b19c0Ok : M3p7b19c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_19 : List Entry := M3p7b19c0
def M3p7b20c0 : List Entry := [([],[M3w0,M3w64,M3w116,M3w140,M3w153,M3w183,M3w223]),
([],[M3w11,M3w64,M3w116,M3w140,M3w153,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w87,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w133,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w141,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w142,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b20c0Ok : M3p7b20c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b20c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w146,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w147,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w149,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w151,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w152,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w153,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b20c1Ok : M3p7b20c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b20c2 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w154,M3w155,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w201,M3w223]),
([],[M3w51,M3w74,M3w116,M3w140,M3w154,M3w183,M3w223]),
([],[M3w64,M3w74,M3w116,M3w140,M3w153,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b20c2Ok : M3p7b20c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_20 : List Entry := M3p7b20c0 ++ M3p7b20c1 ++ M3p7b20c2
def M3p7b21c0 : List Entry := [([],[M3w1,M3w51,M3w93,M3w116,M3w140,M3w183,M3w223]),
([],[M3w5,M3w51,M3w93,M3w116,M3w140,M3w183,M3w223]),
([],[M3w17,M3w51,M3w64,M3w96,M3w116,M3w140,M3w183,M3w223]),
([],[M3w17,M3w51,M3w93,M3w116,M3w140,M3w183,M3w223]),
([],[M3w36,M3w51,M3w64,M3w96,M3w116,M3w140,M3w183,M3w223]),
([],[M3w43,M3w51,M3w93,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b21c0Ok : M3p7b21c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b21c1 : List Entry := [([],[M3w51,M3w64,M3w93,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w94,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w97,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w99,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w103,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w104,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b21c1Ok : M3p7b21c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b21c2 : List Entry := [([],[M3w51,M3w64,M3w106,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w169,M3w202,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w192,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w199,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w200,M3w223]),
([],[M3w51,M3w74,M3w93,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b21c2Ok : M3p7b21c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b21c3 : List Entry := [([],[M3w51,M3w116,M3w140,M3w183,M3w192,M3w223]),
([],[M3w64,M3w74,M3w116,M3w128,M3w140,M3w183,M3w223]),
([],[M3w64,M3w116,M3w140,M3w183,M3w193,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b21c3Ok : M3p7b21c3.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_21 : List Entry := M3p7b21c0 ++ M3p7b21c1 ++ M3p7b21c2 ++ M3p7b21c3
def M3p7b22c0 : List Entry := [([],[M3w0,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w2,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w24,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w243]),
([],[M3w24,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w33,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w40,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w243])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b22c0Ok : M3p7b22c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b22c1 : List Entry := [([],[M3w51,M3w64,M3w87,M3w116,M3w140,M3w183,M3w223,M3w245]),
([],[M3w51,M3w64,M3w93,M3w116,M3w140,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w144,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w163,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w233]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w235])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b22c1Ok : M3p7b22c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b22c2 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w237]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w238]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w241]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w51,M3w74,M3w116,M3w140,M3w183,M3w213,M3w223]),
([],[M3w64,M3w74,M3w116,M3w140,M3w183,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b22c2Ok : M3p7b22c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_22 : List Entry := M3p7b22c0 ++ M3p7b22c1 ++ M3p7b22c2
def M3p7b23c0 : List Entry := [([],[M3w51,M3w64,M3w93,M3w140,M3w150,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w143,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w183,M3w223,M3w242]),
([],[M3w51,M3w116,M3w132,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b23c0Ok : M3p7b23c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_23 : List Entry := M3p7b23c0
def M3p7b24c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w87,M3w116,M3w140,M3w223]),
([],[M3w51,M3w64,M3w101,M3w116,M3w183,M3w223]),
([],[M3w51,M3w64,M3w102,M3w116,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b24c0Ok : M3p7b24c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_24 : List Entry := M3p7b24c0
def M3p7b25c0 : List Entry := [([],[M3w16,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w98,M3w116,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w228])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b25c0Ok : M3p7b25c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_25 : List Entry := M3p7b25c0
def M3p7b26c0 : List Entry := [([],[M3w7,M3w51,M3w64,M3w93,M3w140,M3w183,M3w223]),
([],[M3w7,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w8,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w11,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w12,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w13,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c0Ok : M3p7b26c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c1 : List Entry := [([],[M3w17,M3w51,M3w64,M3w116,M3w140,M3w183,M3w242]),
([],[M3w21,M3w51,M3w64,M3w116,M3w140,M3w183,M3w242]),
([],[M3w21,M3w51,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w22,M3w51,M3w116,M3w140,M3w183,M3w223]),
([],[M3w24,M3w51,M3w64,M3w93,M3w140,M3w183,M3w223]),
([],[M3w28,M3w51,M3w74,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c1Ok : M3p7b26c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c2 : List Entry := [([],[M3w31,M3w51,M3w116,M3w140,M3w183,M3w223]),
([],[M3w32,M3w51,M3w116,M3w140,M3w183,M3w223]),
([],[M3w33,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w34,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w36,M3w51,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w38,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c2Ok : M3p7b26c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c3 : List Entry := [([],[M3w39,M3w51,M3w116,M3w140,M3w183,M3w223]),
([],[M3w40,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w41,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w43,M3w51,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w45,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w46,M3w51,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c3Ok : M3p7b26c3.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c4 : List Entry := [([],[M3w48,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w49,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w50,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w53,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w56,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w58,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c4Ok : M3p7b26c4.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c5 : List Entry := [([],[M3w51,M3w59,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w60,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w61,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w63,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w68,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w70,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c5Ok : M3p7b26c5.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c6 : List Entry := [([],[M3w51,M3w64,M3w72,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w73,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w93,M3w140,M3w155,M3w183,M3w223]),
([],[M3w51,M3w64,M3w103,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w107,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c6Ok : M3p7b26c6.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c7 : List Entry := [([],[M3w51,M3w64,M3w110,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w111,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w112,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w113,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w135,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w136,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c7Ok : M3p7b26c7.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c8 : List Entry := [([],[M3w51,M3w64,M3w116,M3w137,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w138,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w139,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w165,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w168,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w174,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c8Ok : M3p7b26c8.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c9 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w177,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w178,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w181,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w194]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w195]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w217])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c9Ok : M3p7b26c9.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c10 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w218]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w219]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w220]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w221]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w222]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w226])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c10Ok : M3p7b26c10.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c11 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w227]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w230]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w231]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w232]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w235]),
([],[M3w51,M3w64,M3w116,M3w140,M3w184,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c11Ok : M3p7b26c11.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c12 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w185,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w186,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w187,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w212,M3w223]),
([],[M3w51,M3w64,M3w116,M3w142,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w145,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c12Ok : M3p7b26c12.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c13 : List Entry := [([],[M3w51,M3w64,M3w116,M3w146,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w148,M3w183,M3w223]),
([],[M3w51,M3w64,M3w117,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w118,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w119,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w120,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c13Ok : M3p7b26c13.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c14 : List Entry := [([],[M3w51,M3w64,M3w121,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w122,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w123,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w124,M3w140,M3w183,M3w223]),
([],[M3w51,M3w67,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w68,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c14Ok : M3p7b26c14.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b26c15 : List Entry := [([],[M3w51,M3w69,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w71,M3w116,M3w140,M3w183,M3w223]),
([],[M3w54,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w56,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w57,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w62,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b26c15Ok : M3p7b26c15.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_26 : List Entry := M3p7b26c0 ++ M3p7b26c1 ++ M3p7b26c2 ++ M3p7b26c3 ++ M3p7b26c4 ++ M3p7b26c5 ++ M3p7b26c6 ++ M3p7b26c7 ++ M3p7b26c8 ++ M3p7b26c9 ++ M3p7b26c10 ++ M3p7b26c11 ++ M3p7b26c12 ++ M3p7b26c13 ++ M3p7b26c14 ++ M3p7b26c15
def M3p7b27c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w131,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w134,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w169,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w171,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w190,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b27c0Ok : M3p7b27c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b27c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w191,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w159,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w161,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w162,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w164,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w166,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b27c1Ok : M3p7b27c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b27c2 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w167,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w153,M3w157,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w154,M3w157,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b27c2Ok : M3p7b27c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_27 : List Entry := M3p7b27c0 ++ M3p7b27c1 ++ M3p7b27c2
def M3p7b29c0 : List Entry := [([],[M3w16,M3w51,M3w64,M3w116,M3w140,M3w183]),
([],[M3w23,M3w51,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w93,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w96,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w116,M3w134,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b29c0Ok : M3p7b29c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b29c1 : List Entry := [([],[M3w23,M3w51,M3w64,M3w116,M3w153,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w128,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w130,M3w140,M3w183,M3w223]),
([],[M3w23,M3w51,M3w64,M3w140,M3w183,M3w198,M3w223]),
([],[M3w26,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w30,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b29c1Ok : M3p7b29c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b29c2 : List Entry := [([],[M3w35,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w55,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w78,M3w116,M3w140,M3w183]),
([],[M3w51,M3w64,M3w83,M3w116,M3w131,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w83,M3w116,M3w140,M3w154,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b29c2Ok : M3p7b29c2.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_29 : List Entry := M3p7b29c0 ++ M3p7b29c1 ++ M3p7b29c2
def M3p7b30c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w180,M3w183,M3w223]),
([],[M3w51,M3w93,M3w116,M3w140,M3w169,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b30c0Ok : M3p7b30c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_30 : List Entry := M3p7b30c0
def M3p7b31c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w95,M3w116,M3w140,M3w183]),
([],[M3w10,M3w51,M3w64,M3w105,M3w116,M3w140,M3w183]),
([],[M3w51,M3w64,M3w116,M3w140,M3w156,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w169,M3w183,M3w223,M3w242]),
([],[M3w51,M3w64,M3w116,M3w140,M3w171,M3w183,M3w213,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w171,M3w183,M3w223,M3w243])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b31c0Ok : M3p7b31c0.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3p7b31c1 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w179,M3w183,M3w223]),
([],[M3w64,M3w116,M3w140,M3w183,M3w190,M3w223,M3w242])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p7b31c1Ok : M3p7b31c1.all (testRow chart false M3t6 6) = true := by decide +kernel
def M3b7_31 : List Entry := M3p7b31c0 ++ M3p7b31c1
def M3g7 : List (List Entry) := [M3b7_0, M3b7_1, M3b7_2, M3b7_3, M3b7_4, M3b7_5, M3b7_6, M3b7_7, M3b7_8, M3b7_9, M3b7_10, M3b7_11, M3b7_12, M3b7_13, M3b7_14, M3b7_15, M3b7_16, M3b7_17, M3b7_18, M3b7_19, M3b7_20, M3b7_21, M3b7_22, M3b7_23, M3b7_24, M3b7_25, M3b7_26, M3b7_27, [], M3b7_29, M3b7_30, M3b7_31]
def M3t7 : Nat → List Entry := bucketOf M3g7
set_option maxRecDepth 160000 in
lemma M3v7 : verifiedR false 9 7 M3t7 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v6
  apply checkBuckets
  simp only [M3g7, M3b7_0, M3b7_1, M3b7_2, M3b7_3, M3b7_4, M3b7_5, M3b7_6, M3b7_7, M3b7_8, M3b7_9, M3b7_10, M3b7_11, M3b7_12, M3b7_13, M3b7_14, M3b7_15, M3b7_16, M3b7_17, M3b7_18, M3b7_19, M3b7_20, M3b7_21, M3b7_22, M3b7_23, M3b7_24, M3b7_25, M3b7_26, M3b7_27, M3b7_29, M3b7_30, M3b7_31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M3p7b0c0Ok, M3p7b1c0Ok, M3p7b2c0Ok, M3p7b3c0Ok, M3p7b3c1Ok, M3p7b3c2Ok, M3p7b3c3Ok, M3p7b4c0Ok, M3p7b5c0Ok, M3p7b6c0Ok, M3p7b6c1Ok, M3p7b7c0Ok, M3p7b8c0Ok, M3p7b9c0Ok, M3p7b9c1Ok, M3p7b9c2Ok, M3p7b10c0Ok, M3p7b10c1Ok, M3p7b11c0Ok, M3p7b12c0Ok, M3p7b13c0Ok, M3p7b13c1Ok, M3p7b14c0Ok, M3p7b15c0Ok, M3p7b15c1Ok, M3p7b15c2Ok, M3p7b16c0Ok, M3p7b17c0Ok, M3p7b17c1Ok, M3p7b18c0Ok, M3p7b18c1Ok, M3p7b19c0Ok, M3p7b20c0Ok, M3p7b20c1Ok, M3p7b20c2Ok, M3p7b21c0Ok, M3p7b21c1Ok, M3p7b21c2Ok, M3p7b21c3Ok, M3p7b22c0Ok, M3p7b22c1Ok, M3p7b22c2Ok, M3p7b23c0Ok, M3p7b24c0Ok, M3p7b25c0Ok, M3p7b26c0Ok, M3p7b26c1Ok, M3p7b26c2Ok, M3p7b26c3Ok, M3p7b26c4Ok, M3p7b26c5Ok, M3p7b26c6Ok, M3p7b26c7Ok, M3p7b26c8Ok, M3p7b26c9Ok, M3p7b26c10Ok, M3p7b26c11Ok, M3p7b26c12Ok, M3p7b26c13Ok, M3p7b26c14Ok, M3p7b26c15Ok, M3p7b27c0Ok, M3p7b27c1Ok, M3p7b27c2Ok, M3p7b29c0Ok, M3p7b29c1Ok, M3p7b29c2Ok, M3p7b30c0Ok, M3p7b31c0Ok, M3p7b31c1Ok]
def M3p8b2c0 : List Entry := [([],[M3w51,M3w64,M3w81,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w203,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b2c0Ok : M3p8b2c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_2 : List Entry := M3p8b2c0
def M3p8b3c0 : List Entry := [([],[M3w51,M3w64,M3w83,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w169,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w171,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w190,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w191,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b3c0Ok : M3p8b3c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_3 : List Entry := M3p8b3c0
def M3p8b4c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w245])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b4c0Ok : M3p8b4c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_4 : List Entry := M3p8b4c0
def M3p8b5c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w234])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b5c0Ok : M3p8b5c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_5 : List Entry := M3p8b5c0
def M3p8b6c0 : List Entry := [([],[M3w51,M3w64,M3w95,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w105,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b6c0Ok : M3p8b6c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_6 : List Entry := M3p8b6c0
def M3p8b8c0 : List Entry := [([],[M3w51,M3w64,M3w76,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b8c0Ok : M3p8b8c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_8 : List Entry := M3p8b8c0
def M3p8b9c0 : List Entry := [([],[M3w6,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b9c0Ok : M3p8b9c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_9 : List Entry := M3p8b9c0
def M3p8b10c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w204,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w205,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b10c0Ok : M3p8b10c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_10 : List Entry := M3p8b10c0
def M3p8b11c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w240])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b11c0Ok : M3p8b11c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_11 : List Entry := M3p8b11c0
def M3p8b12c0 : List Entry := [([],[M3w51,M3w64,M3w87,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w92,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b12c0Ok : M3p8b12c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_12 : List Entry := M3p8b12c0
def M3p8b14c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w175,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b14c0Ok : M3p8b14c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_14 : List Entry := M3p8b14c0
def M3p8b15c0 : List Entry := [([],[M3w10,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b15c0Ok : M3p8b15c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_15 : List Entry := M3p8b15c0
def M3p8b18c0 : List Entry := [([],[M3w51,M3w64,M3w98,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b18c0Ok : M3p8b18c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_18 : List Entry := M3p8b18c0
def M3p8b20c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w131,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w134,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w153,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w154,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b20c0Ok : M3p8b20c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_20 : List Entry := M3p8b20c0
def M3p8b21c0 : List Entry := [([],[M3w51,M3w64,M3w93,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w96,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w128,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w130,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w198,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w202,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b21c0Ok : M3p8b21c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_21 : List Entry := M3p8b21c0
def M3p8b22c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w213,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w216,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w242]),
([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223,M3w243])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b22c0Ok : M3p8b22c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_22 : List Entry := M3p8b22c0
def M3p8b23c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w150,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b23c0Ok : M3p8b23c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_23 : List Entry := M3p8b23c0
def M3p8b26c0 : List Entry := [([],[M3w0,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w1,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w2,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w3,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w4,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w5,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b26c0Ok : M3p8b26c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3p8b26c1 : List Entry := [([],[M3w7,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w9,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w11,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w17,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w20,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w21,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b26c1Ok : M3p8b26c1.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3p8b26c2 : List Entry := [([],[M3w24,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w28,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w33,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w36,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w40,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w43,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b26c2Ok : M3p8b26c2.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3p8b26c3 : List Entry := [([],[M3w47,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w74,M3w116,M3w140,M3w183,M3w223]),
([],[M3w51,M3w64,M3w116,M3w140,M3w155,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b26c3Ok : M3p8b26c3.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_26 : List Entry := M3p8b26c0 ++ M3p8b26c1 ++ M3p8b26c2 ++ M3p8b26c3
def M3p8b27c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w157,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b27c0Ok : M3p8b27c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_27 : List Entry := M3p8b27c0
def M3p8b28c0 : List Entry := [([],[M3w51,M3w64,M3w75,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b28c0Ok : M3p8b28c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_28 : List Entry := M3p8b28c0
def M3p8b29c0 : List Entry := [([],[M3w23,M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p8b29c0Ok : M3p8b29c0.all (testRow chart false M3t7 7) = true := by decide +kernel
def M3b8_29 : List Entry := M3p8b29c0
def M3g8 : List (List Entry) := [[], [], M3b8_2, M3b8_3, M3b8_4, M3b8_5, M3b8_6, [], M3b8_8, M3b8_9, M3b8_10, M3b8_11, M3b8_12, [], M3b8_14, M3b8_15, [], [], M3b8_18, [], M3b8_20, M3b8_21, M3b8_22, M3b8_23, [], [], M3b8_26, M3b8_27, M3b8_28, M3b8_29, [], []]
def M3t8 : Nat → List Entry := bucketOf M3g8
set_option maxRecDepth 160000 in
lemma M3v8 : verifiedR false 9 8 M3t8 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v7
  apply checkBuckets
  simp only [M3g8, M3b8_2, M3b8_3, M3b8_4, M3b8_5, M3b8_6, M3b8_8, M3b8_9, M3b8_10, M3b8_11, M3b8_12, M3b8_14, M3b8_15, M3b8_18, M3b8_20, M3b8_21, M3b8_22, M3b8_23, M3b8_26, M3b8_27, M3b8_28, M3b8_29, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M3p8b2c0Ok, M3p8b3c0Ok, M3p8b4c0Ok, M3p8b5c0Ok, M3p8b6c0Ok, M3p8b8c0Ok, M3p8b9c0Ok, M3p8b10c0Ok, M3p8b11c0Ok, M3p8b12c0Ok, M3p8b14c0Ok, M3p8b15c0Ok, M3p8b18c0Ok, M3p8b20c0Ok, M3p8b21c0Ok, M3p8b22c0Ok, M3p8b23c0Ok, M3p8b26c0Ok, M3p8b26c1Ok, M3p8b26c2Ok, M3p8b26c3Ok, M3p8b27c0Ok, M3p8b28c0Ok, M3p8b29c0Ok]
def M3p9b26c0 : List Entry := [([],[M3w51,M3w64,M3w116,M3w140,M3w183,M3w223])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma M3p9b26c0Ok : M3p9b26c0.all (testRow chart false M3t8 8) = true := by decide +kernel
def M3b9_26 : List Entry := M3p9b26c0
def M3g9 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], M3b9_26, [], [], [], [], []]
def M3t9 : Nat → List Entry := bucketOf M3g9
set_option maxRecDepth 160000 in
lemma M3v9 : verifiedR false 9 9 M3t9 := by
  apply checkedTier chart chart_valid false (by decide) (by decide) M3v8
  apply checkBuckets
  simp only [M3g9, M3b9_26, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M3p9b26c0Ok]
lemma cert3 : ∀ j ≤ 9, ¬ BL j minor3.toFinset := by
  intro j hj live
  have eq := sortFinset minor3
  exact M3v9 [] (sortSignals minor3) (hit_mem (by decide +kernel)) (by decide +kernel)
    (by simp [preserve,resources,attachLoss,underlying]) j hj (eq.symm ▸ live)

lemma reductionLower {H : SigHom} {m : List Sig} (needed : necessary m) (nd : m.Nodup)
    (image : ((fullRaw.toFinset.image H.fn).image can) ⊆ insert zero m.toFinset)
    (cert : ∀ j ≤ 9, ¬ BL j m.toFinset) (q : ℕ)
    (canRun : Projection8403.Can q (fullRaw.toFinset.image H.fn)) : 10 ≤ q := by
  obtain ⟨k,t,S,le,run,small⟩ := canRun
  obtain ⟨j,V,lim,signed,sub⟩ := compress run
  have sub2 := (sub.trans (Finset.image_mono _ small)).trans image
  have incl : V ⊆ m.toFinset := by
    intro v hv
    exact (Finset.mem_insert.mp (sub2 hv)).resolve_left (signed.forms v hv).1.2.1
  obtain ⟨u,restored⟩ := signed.expand
  have basis := allNeeded restored incl needed
  by_contra! lt
  exact cert j (by omega) (basis ▸ signed)

lemma initial : preserve reductions 0 fullRaw.toFinset := by
  intro H lost h q ok
  simp only [reductions, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simpa using reductionLower needed0 (by decide +kernel) images0 cert0 q ok
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simpa using reductionLower needed0 (by decide +kernel) images1 cert0 q ok
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simpa using reductionLower needed3 (by decide +kernel) images3 cert3 q ok
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simpa using reductionLower needed0 (by decide +kernel) images5 cert0 q ok
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simpa using reductionLower needed0 (by decide +kernel) images6 cert0 q ok

def FW0 : Sig := (0xffffe0000000,0xe000e000e000e000)
def FW1 : Sig := (0x20c8f57655b520c8,0xfdf5fdf5fdf5fdf5)
def FW2 : Sig := (0x29da1112c49329da,0x2c002c002c002c)
def FW3 : Sig := (0x318085c016003180,0x1700170017001700)
def FW4 : Sig := (0x4e00020008004e00,0x0)
def FW5 : Sig := (0x4e00ffffe8004e00,0xe000e000e000e000)
def FW6 : Sig := (0x6ac8f7765db56ac8,0xfdf5fdf5fdf5fdf5)
def FW7 : Sig := (0x6fda1312cc936fda,0x2c002c002c002c)
def FW8 : Sig := (0x707c443c11e0707c,0x4c004c004c004c0)
def FW9 : Sig := (0x7e7c463c19e07e7c,0x4c004c004c004c0)
def FW10 : Sig := (0x7f8087c01e007f80,0x1700170017001700)
def FW11 : Sig := (0x8000f8001fff8000,0x9800980098009800)
def FW12 : Sig := (0x801c581ce0e3801c,0xa84fa84fa84fa84f)
def FW13 : Sig := (0xb19cdddcf6e3b19c,0xbf4fbf4fbf4fbf4f)
def FW14 : Sig := (0xce00fa001fffce00,0x9800980098009800)
def FW15 : Sig := (0xce1c5a1ce8e3ce1c,0xa84fa84fa84fa84f)
def FW16 : Sig := (0xff9cdfdcfee3ff9c,0xbf4fbf4fbf4fbf4f)
def FT0 : Nat → List Entry := fun _ => []
lemma FV0 : verifiedR true 11 0 FT0 := emptyR _ _
def FG1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT1 : Nat → List Entry := bucketOf FG1
set_option maxRecDepth 160000 in
lemma FV1 : verifiedR true 11 1 FT1 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV0
  apply checkBuckets
  simp only [FG1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT2 : Nat → List Entry := bucketOf FG2
set_option maxRecDepth 160000 in
lemma FV2 : verifiedR true 11 2 FT2 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV1
  apply checkBuckets
  simp only [FG2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT3 : Nat → List Entry := bucketOf FG3
set_option maxRecDepth 160000 in
lemma FV3 : verifiedR true 11 3 FT3 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV2
  apply checkBuckets
  simp only [FG3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT4 : Nat → List Entry := bucketOf FG4
set_option maxRecDepth 160000 in
lemma FV4 : verifiedR true 11 4 FT4 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV3
  apply checkBuckets
  simp only [FG4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG5 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT5 : Nat → List Entry := bucketOf FG5
set_option maxRecDepth 160000 in
lemma FV5 : verifiedR true 11 5 FT5 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV4
  apply checkBuckets
  simp only [FG5, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG6 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT6 : Nat → List Entry := bucketOf FG6
set_option maxRecDepth 160000 in
lemma FV6 : verifiedR true 11 6 FT6 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV5
  apply checkBuckets
  simp only [FG6, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FG7 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT7 : Nat → List Entry := bucketOf FG7
set_option maxRecDepth 160000 in
lemma FV7 : verifiedR true 11 7 FT7 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV6
  apply checkBuckets
  simp only [FG7, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]
def FP8_10_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW15]),
([0, 0, 0, 0, 1],[FW2,FW5,FW6,FW8,FW10,FW11,FW12]),
([0, 0, 0, 0, 1],[FW2,FW5,FW6,FW8,FW10,FW11,FW13]),
([0, 0, 0, 0, 1],[FW2,FW5,FW6,FW8,FW10,FW11,FW16]),
([0, 0, 0, 1, 0],[FW0,FW2,FW3,FW6,FW8,FW13,FW14]),
([0, 0, 0, 1, 0],[FW0,FW2,FW6,FW8,FW10,FW13,FW14])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP8_10_0Ok : FP8_10_0.all (testRow chart true FT7 7) = true := by decide +kernel
def FP8_10_1 : List Entry := [([0, 0, 0, 1, 1],[FW2,FW5,FW6,FW8,FW10,FW13,FW14]),
([0, 0, 1, 0, 1],[FW2,FW5,FW6,FW9,FW10,FW11,FW13]),
([0, 0, 1, 1, 0],[FW0,FW2,FW6,FW9,FW10,FW13,FW14]),
([0, 1, 0, 0, 0],[FW0,FW6,FW7,FW8,FW10,FW11,FW12]),
([0, 1, 0, 0, 0],[FW0,FW6,FW7,FW8,FW10,FW11,FW13]),
([0, 1, 0, 0, 0],[FW0,FW6,FW7,FW8,FW10,FW11,FW16])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP8_10_1Ok : FP8_10_1.all (testRow chart true FT7 7) = true := by decide +kernel
def FP8_10_2 : List Entry := [([0, 1, 0, 0, 1],[FW5,FW6,FW7,FW8,FW10,FW11,FW13]),
([0, 1, 0, 1, 0],[FW0,FW6,FW7,FW8,FW10,FW13,FW14]),
([0, 1, 1, 0, 0],[FW0,FW6,FW7,FW9,FW10,FW11,FW13]),
([1, 0, 0, 0, 0],[FW0,FW1,FW2,FW3,FW8,FW11,FW13]),
([1, 0, 0, 0, 0],[FW0,FW1,FW2,FW8,FW10,FW11,FW13]),
([1, 0, 0, 0, 1],[FW1,FW2,FW5,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP8_10_2Ok : FP8_10_2.all (testRow chart true FT7 7) = true := by decide +kernel
def FP8_10_3 : List Entry := [([1, 0, 0, 1, 0],[FW0,FW1,FW2,FW8,FW10,FW13,FW14]),
([1, 0, 1, 0, 0],[FW0,FW1,FW2,FW9,FW10,FW11,FW13]),
([1, 1, 0, 0, 0],[FW0,FW1,FW7,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP8_10_3Ok : FP8_10_3.all (testRow chart true FT7 7) = true := by decide +kernel
def FB8_10 : List Entry := FP8_10_0 ++ FP8_10_1 ++ FP8_10_2 ++ FP8_10_3
def FP8_21_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW11,FW13,FW15]),
([0, 0, 0, 1, 0],[FW0,FW2,FW6,FW8,FW12,FW13,FW14]),
([1, 0, 0, 0, 0],[FW0,FW1,FW2,FW8,FW11,FW12,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP8_21_0Ok : FP8_21_0.all (testRow chart true FT7 7) = true := by decide +kernel
def FB8_21 : List Entry := FP8_21_0
def FG8 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], FB8_10, [], [], [], [], [], [], [], [], [], [], FB8_21, [], [], [], [], [], [], [], [], [], []]
def FT8 : Nat → List Entry := bucketOf FG8
set_option maxRecDepth 160000 in
lemma FV8 : verifiedR true 11 8 FT8 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV7
  apply checkBuckets
  simp only [FG8, FB8_10, FB8_21, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, FP8_10_0Ok, FP8_10_1Ok, FP8_10_2Ok, FP8_10_3Ok, FP8_21_0Ok]
def FP9_0_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW11,FW12,FW13,FW16])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP9_0_0Ok : FP9_0_0.all (testRow chart true FT8 8) = true := by decide +kernel
def FB9_0 : List Entry := FP9_0_0
def FP9_10_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW4,FW6,FW8,FW11,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW6,FW8,FW10,FW11,FW12]),
([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW6,FW8,FW10,FW11,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW6,FW8,FW10,FW11,FW16]),
([0, 0, 0, 0, 0],[FW0,FW2,FW4,FW6,FW8,FW10,FW11,FW12]),
([0, 0, 0, 0, 0],[FW0,FW2,FW4,FW6,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP9_10_0Ok : FP9_10_0.all (testRow chart true FT8 8) = true := by decide +kernel
def FP9_10_1 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW4,FW6,FW8,FW10,FW11,FW16]),
([0, 0, 0, 0, 1],[FW2,FW4,FW5,FW6,FW8,FW10,FW11,FW13]),
([0, 0, 0, 0, 1],[FW2,FW5,FW6,FW8,FW10,FW11,FW13]),
([0, 0, 0, 1, 0],[FW0,FW2,FW4,FW6,FW8,FW10,FW13,FW14]),
([0, 0, 0, 1, 0],[FW0,FW2,FW6,FW8,FW10,FW13,FW14]),
([0, 0, 1, 0, 0],[FW0,FW2,FW4,FW6,FW9,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP9_10_1Ok : FP9_10_1.all (testRow chart true FT8 8) = true := by decide +kernel
def FP9_10_2 : List Entry := [([0, 0, 1, 0, 0],[FW0,FW2,FW6,FW9,FW10,FW11,FW13]),
([0, 1, 0, 0, 0],[FW0,FW4,FW6,FW7,FW8,FW10,FW11,FW13]),
([0, 1, 0, 0, 0],[FW0,FW6,FW7,FW8,FW10,FW11,FW13]),
([1, 0, 0, 0, 0],[FW0,FW1,FW2,FW4,FW8,FW10,FW11,FW13]),
([1, 0, 0, 0, 0],[FW0,FW1,FW2,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP9_10_2Ok : FP9_10_2.all (testRow chart true FT8 8) = true := by decide +kernel
def FB9_10 : List Entry := FP9_10_0 ++ FP9_10_1 ++ FP9_10_2
def FP9_21_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW6,FW8,FW11,FW13,FW16]),
([0, 0, 0, 0, 0],[FW0,FW2,FW4,FW6,FW8,FW11,FW12,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW12,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW13,FW16])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP9_21_0Ok : FP9_21_0.all (testRow chart true FT8 8) = true := by decide +kernel
def FB9_21 : List Entry := FP9_21_0
def FG9 : List (List Entry) := [FB9_0, [], [], [], [], [], [], [], [], [], FB9_10, [], [], [], [], [], [], [], [], [], [], FB9_21, [], [], [], [], [], [], [], [], [], []]
def FT9 : Nat → List Entry := bucketOf FG9
set_option maxRecDepth 160000 in
lemma FV9 : verifiedR true 11 9 FT9 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV8
  apply checkBuckets
  simp only [FG9, FB9_0, FB9_10, FB9_21, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, FP9_0_0Ok, FP9_10_0Ok, FP9_10_1Ok, FP9_10_2Ok, FP9_21_0Ok]
def FP10_10_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW3,FW6,FW8,FW10,FW11,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW4,FW6,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP10_10_0Ok : FP10_10_0.all (testRow chart true FT9 9) = true := by decide +kernel
def FB10_10 : List Entry := FP10_10_0
def FP10_21_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW12,FW13]),
([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW13,FW16])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP10_21_0Ok : FP10_21_0.all (testRow chart true FT9 9) = true := by decide +kernel
def FB10_21 : List Entry := FP10_21_0
def FG10 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], FB10_10, [], [], [], [], [], [], [], [], [], [], FB10_21, [], [], [], [], [], [], [], [], [], []]
def FT10 : Nat → List Entry := bucketOf FG10
set_option maxRecDepth 160000 in
lemma FV10 : verifiedR true 11 10 FT10 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV9
  apply checkBuckets
  simp only [FG10, FB10_10, FB10_21, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, FP10_10_0Ok, FP10_21_0Ok]
def FP11_10_0 : List Entry := [([0, 0, 0, 0, 0],[FW0,FW2,FW6,FW8,FW10,FW11,FW13])]
set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
lemma FP11_10_0Ok : FP11_10_0.all (testRow chart true FT10 10) = true := by decide +kernel
def FB11_10 : List Entry := FP11_10_0
def FG11 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], FB11_10, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def FT11 : Nat → List Entry := bucketOf FG11
set_option maxRecDepth 160000 in
lemma FV11 : verifiedR true 11 11 FT11 := by
  apply checkedTier chart chart_valid true (by decide) (by decide) FV10
  apply checkBuckets
  simp only [FG11, FB11_10, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, FP11_10_0Ok]
lemma fullDAG {k : Nat} (lim : k ≤ 11) (live : BL k fullRaw.toFinset) : False := by
  have eq := sortFinset fullRaw
  apply FV11 [0,0,0,0,0] (sortSignals fullRaw) (hit_mem (by decide +kernel))
     (by decide +kernel) ?_ k lim (eq.symm ▸ live)
  rw [eq]
  exact initial

lemma binary_lower (C : Circuit) (legal : FanInTwo C)
    (spec : ∀ x, C.eval (List.ofFn x) = edge x) : 12 ≤ C.gates.countP costly := by
  obtain ⟨k,t,S,cap,run,sub⟩ := tagExtract C.gates raw8 vals legal (output8 legal spec)
  obtain ⟨j,V,lim,signed,small⟩ := compress run
  have before : S ⊆ raw8.toFinset := fun a ha => List.mem_toFinset.mpr (sub a ha)
  have incl : V ⊆ fullRaw.toFinset := by
    intro v hv
    obtain ⟨u, hu, eq⟩ := Finset.mem_image.mp (small hv)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, List.mem_toFinset.mp (before hu), eq⟩)
  obtain ⟨u,restored⟩ := signed.expand
  have eq := allNeeded restored incl fullNeeded
  by_contra! lt
  exact fullDAG (by omega) (eq ▸ signed)

end PEqualNP.Outside.L_meta_31225_aux.Seven

namespace PEqualNP.Outside.L_meta_31225_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, Stat.Valid w.length s) :
    Stat.Valid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, Stat.Valid m s → Stat.Valid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, Stat.Valid w.length s →
    Stat.val (w ++ t) s = Stat.val w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show Stat.Valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, Stat.Valid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

end CircuitProof
namespace Restrict

open CircuitProof

theorem elim_snoc (n : ℕ) (A : List Gate) (g : Gate) (acc : List Stat × List Gate) :
    elim n (A ++ [g]) acc = elimStep n (elim n A acc) g := by
  simp [elim, List.foldl_append]

theorem elim_stats_length (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih]
    simp [elimStep]
    omega

theorem inv_start {n n' : ℕ} (s0 : Fin n → Stat) (hv : ∀ i, Stat.Valid n' (s0 i))
    (y : Fin n' → Bool) :
    Inv n' (List.ofFn y) (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)) (List.ofFn s0, []) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hlt : i < n
  · have h1 : (List.ofFn s0).getD i (Sum.inl false) = s0 ⟨i, hlt⟩ :=
      getD_ofFn n s0 _ ⟨i, hlt⟩
    have h2 : (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)).getD i false
        = Stat.val (List.ofFn y) (s0 ⟨i, hlt⟩) :=
      getD_ofFn n (fun i => Stat.val (List.ofFn y) (s0 i)) _ ⟨i, hlt⟩
    show Stat.Valid (n' + ([] : List Gate).length) ((List.ofFn s0).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom [] (List.ofFn y)) ((List.ofFn s0).getD i (Sum.inl false)) = _
    rw [h1, h2]
    exact ⟨by simpa using hv ⟨i, hlt⟩, rfl⟩
  · show Stat.Valid (n' + ([] : List Gate).length) ((List.ofFn s0).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom [] (List.ofFn y)) ((List.ofFn s0).getD i (Sum.inl false)) = _
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem restrict_sem {n n' : ℕ} (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) (s0 : Fin n → Stat)
    (hv : ∀ i, Stat.Valid n' (s0 i)) :
    CleanL n' (elim n' gs (List.ofFn s0, [])).2 ∧
    ∀ (y : Fin n' → Bool) (o : ℕ),
      Stat.val (wiresFrom (elim n' gs (List.ofFn s0, [])).2 (List.ofFn y))
        ((elim n' gs (List.ofFn s0, [])).1.getD o (Sum.inl false)) =
      (wiresFrom gs (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i))).getD o false := by
  constructor
  · exact clean_elim n' (List.ofFn fun _ : Fin n' => false) (by simp) gs _ _ hok
      (inv_start s0 hv _) (by intro p g hp; simp at hp)
  · intro y o
    exact ((inv_elim n' (List.ofFn y) (by simp) gs _ _ hok (inv_start s0 hv y)).2 o).2

theorem clean_fan (n : ℕ) (gs : List Gate) (o : ℕ) (h : CleanL n gs) : FanInTwo ⟨gs, o⟩ := by
  intro g hg
  exact (clean_nok n gs h g hg).1

theorem restrict_core {n n' : ℕ} (C : Circuit) (hfan : FanInTwo C) (s0 : Fin n → Stat)
    (hv : ∀ i, Stat.Valid n' (s0 i)) (f' : (Fin n' → Bool) → Bool)
    (he : ∀ y : Fin n' → Bool,
      C.eval (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)) = f' y)
    (hnc : ∃ y y', f' y ≠ f' y') :
    ∃ C' : Circuit, FanInTwo C' ∧ nonNotCount C'.gates ≤ nonNotCount C.gates ∧
      ∀ y : Fin n' → Bool, C'.eval (List.ofFn y) = f' y := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  obtain ⟨hclean, hsem⟩ := restrict_sem C.gates hok s0 hv
  have hval : ∀ y : Fin n' → Bool,
      Stat.val (wiresFrom (elim n' C.gates (List.ofFn s0, [])).2 (List.ofFn y))
        ((elim n' C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false)) = f' y := by
    intro y
    rw [hsem y C.output, ← he y]
    rfl
  cases hst : (elim n' C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨⟨(elim n' C.gates (List.ofFn s0, [])).2, j⟩, clean_fan n' _ j hclean, ?_, ?_⟩
    · simpa [nonNotCount] using elim_nonNotCount n' C.gates (List.ofFn s0, [])
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem elim_count_marked (n : ℕ) (A B : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hg : isNotGate g.op = false)
    (hnone : (simplify g.op (n + (elim n A acc).2.length)
      (g.inputs.map fun i => (elim n A acc).1.getD i (Sum.inl false))).1 = none) :
    nonNotCount (elim n (A ++ g :: B) acc).2 + 1 ≤ nonNotCount acc.2 + nonNotCount (A ++ g :: B) := by
  have h1 : elim n (A ++ g :: B) acc = elim n B (elimStep n (elim n A acc) g) := by
    simp [elim, List.foldl_append]
  have h2 := elim_nonNotCount n B (elimStep n (elim n A acc) g)
  have h3 := elim_nonNotCount n A acc
  have h4 : nonNotCount (elimStep n (elim n A acc) g).2 = nonNotCount (elim n A acc).2 := by
    show nonNotCount ((elim n A acc).2 ++ (simplify g.op (n + (elim n A acc).2.length)
      (g.inputs.map fun i => (elim n A acc).1.getD i (Sum.inl false))).1.toList) = _
    rw [hnone]
    simp
  have h5 : nonNotCount (A ++ g :: B) = nonNotCount A + nonNotCount B + 1 := by
    simp [nonNotCount, List.countP_append, List.countP_cons, hg]
    omega
  rw [h1, h5]
  omega

theorem simplify_binary_some (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List Stat) (h : (simplify op m ins).1 ≠ none) :
    ∃ a b, ins = [Sum.inr a, Sum.inr b] := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at h ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at h ⊢

theorem simplify_not_inr (m : ℕ) (ins : List Stat) (k : ℕ)
    (h : (simplify GateOp.not m ins).2 = Sum.inr k) : ∃ a rest, ins = Sum.inr a :: rest := by
  rcases ins with _ | ⟨a, l⟩
  · simp [simplify, simpNot] at h
  · cases a with
    | inl c => simp [simplify, simpNot] at h
    | inr a => exact ⟨a, l, rfl⟩

theorem restrict_drop {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (p : Fin n)
    (f : (Fin n → Bool) → Bool) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p true) ≠ f (Function.update x p false))
    (hnc : ∃ x y : Fin n → Bool,
      f (Function.update x p false) ≠ f (Function.update y p false)) :
    ∃ C' : Circuit, FanInTwo C' ∧ nonNotCount C'.gates + 1 ≤ nonNotCount C.gates ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f (Function.update x p false) := by
  classical
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  let s0 : Fin n → Stat := fun i => if i = p then Sum.inl false else Sum.inr i.val
  have s0p : ∀ i : Fin n, i = p → s0 i = Sum.inl false := fun i h => if_pos h
  have s0n : ∀ i : Fin n, i ≠ p → s0 i = Sum.inr i.val := fun i h => if_neg h
  have hv : ∀ i, Stat.Valid n (s0 i) := by
    intro i
    by_cases h : i = p
    · rw [s0p i h]; trivial
    · rw [s0n i h]; exact i.isLt
  have hold : ∀ y : Fin n → Bool,
      (fun i => Stat.val (List.ofFn y) (s0 i)) = Function.update y p false := by
    intro y
    funext i
    by_cases h : i = p
    · rw [s0p i h, h, Function.update_self]; rfl
    · rw [s0n i h, Function.update_of_ne h]
      exact getD_ofFn n y false i
  obtain ⟨hclean, hsem⟩ := restrict_sem C.gates hok s0 hv
  have hval : ∀ y : Fin n → Bool,
      Stat.val (wiresFrom (elim n C.gates (List.ofFn s0, [])).2 (List.ofFn y))
        ((elim n C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false))
        = f (Function.update y p false) := by
    intro y
    rw [hsem y C.output, hold y, ← he]
    rfl
  cases hst : (elim n C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr jo =>
    refine ⟨⟨(elim n C.gates (List.ofFn s0, [])).2, jo⟩, clean_fan n _ jo hclean, ?_, ?_⟩
    swap
    · intro y
      have h := hval y
      rw [hst] at h
      exact h
    · by_cases hstrict : ∃ A g B, C.gates = A ++ g :: B ∧ isNotGate g.op = false ∧
          (simplify g.op (n + (elim n A (List.ofFn s0, [])).2.length)
            (g.inputs.map fun i => (elim n A (List.ofFn s0, [])).1.getD i (Sum.inl false))).1
              = none
      · obtain ⟨A, g, B, hsplit, hg, hnone⟩ := hstrict
        have hc := elim_count_marked n A B g (List.ofFn s0, []) hg hnone
        rw [← hsplit] at hc
        have hz : nonNotCount (([] : List Gate)) = 0 := rfl
        show nonNotCount (elim n C.gates (List.ofFn s0, [])).2 + 1 ≤ nonNotCount C.gates
        have hc' : nonNotCount (elim n C.gates (List.ofFn s0, [])).2 + 1
            ≤ nonNotCount ([] : List Gate) + nonNotCount C.gates := hc
        omega
      · exfalso
        push_neg at hstrict
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have key : ∀ A B, C.gates = A ++ B → ∀ i k,
            (elim n A (List.ofFn s0, [])).1.getD i (Sum.inl false) = Sum.inr k →
            (wiresFrom A (List.ofFn (Function.update x p true))).getD i false
              = (wiresFrom A (List.ofFn (Function.update x p false))).getD i false := by
          intro A
          induction A using List.reverseRecOn with
          | nil =>
            intro B _ i k hik
            have hik0 : (List.ofFn s0).getD i (Sum.inl false) = Sum.inr k := hik
            show (List.ofFn (Function.update x p true)).getD i false
              = (List.ofFn (Function.update x p false)).getD i false
            by_cases hlt : i < n
            · have h1 : (List.ofFn s0).getD i (Sum.inl false) = s0 ⟨i, hlt⟩ :=
                getD_ofFn n s0 _ ⟨i, hlt⟩
              have hne : (⟨i, hlt⟩ : Fin n) ≠ p := by
                intro h
                rw [h1, s0p _ h] at hik0
                cases hik0
              have e1 : (List.ofFn (Function.update x p true)).getD i false
                  = Function.update x p true ⟨i, hlt⟩ := getD_ofFn n _ false ⟨i, hlt⟩
              have e2 : (List.ofFn (Function.update x p false)).getD i false
                  = Function.update x p false ⟨i, hlt⟩ := getD_ofFn n _ false ⟨i, hlt⟩
              rw [e1, e2, Function.update_of_ne hne, Function.update_of_ne hne]
            · exfalso
              rw [List.getD_eq_default _ _ (by simp; omega)] at hik0
              cases hik0
          | append_singleton A g ih =>
            intro B hsplit i k hik
            have hsplit' : C.gates = A ++ g :: B := by rw [hsplit]; simp
            have ihA := ih (g :: B) hsplit'
            have hgok : Ok g := hok g (by rw [hsplit']; simp)
            have hlen : (elim n A (List.ofFn s0, [])).1.length = n + A.length := by
              rw [elim_stats_length]; simp
            have hw : ∀ X : List Bool, wiresFrom (A ++ [g]) X = wiresFrom A X ++
                [g.op.eval (g.inputs.map fun i => (wiresFrom A X).getD i false)] := by
              intro X; rw [wiresFrom_append]; rfl
            have hwl : ∀ X : List Bool, X.length = n →
                (wiresFrom A X).length = n + A.length := by
              intro X hX; rw [length_wiresFrom, hX]
            rw [elim_snoc] at hik
            have hik1 : ((elim n A (List.ofFn s0, [])).1 ++
                [(simplify g.op (n + (elim n A (List.ofFn s0, [])).2.length)
                  (g.inputs.map fun i =>
                    (elim n A (List.ofFn s0, [])).1.getD i (Sum.inl false))).2]).getD i
                  (Sum.inl false) = Sum.inr k := hik
            rw [hw, hw]
            by_cases hi : i = n + A.length
            · have hik2 : (simplify g.op (n + (elim n A (List.ofFn s0, [])).2.length)
                  (g.inputs.map fun i =>
                    (elim n A (List.ofFn s0, [])).1.getD i (Sum.inl false))).2 = Sum.inr k := by
                rw [hi, ← hlen, getD_snoc_eq] at hik1
                exact hik1
              have e1 : ∀ X : List Bool, X.length = n →
                  (wiresFrom A X ++ [g.op.eval (g.inputs.map fun i =>
                    (wiresFrom A X).getD i false)]).getD i false
                  = g.op.eval (g.inputs.map fun i => (wiresFrom A X).getD i false) := by
                intro X hX
                rw [hi, ← hwl X hX, getD_snoc_eq]
              rw [e1 _ (by simp), e1 _ (by simp)]
              have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hgok.1
              have binary : (g.op = GateOp.and ∨ g.op = GateOp.or) →
                  g.op.eval (g.inputs.map fun i =>
                    (wiresFrom A (List.ofFn (Function.update x p true))).getD i false)
                  = g.op.eval (g.inputs.map fun i =>
                    (wiresFrom A (List.ofFn (Function.update x p false))).getD i false) := by
                intro hb
                have hnn : isNotGate g.op = false := by
                  rcases hb with h | h <;> rw [h] <;> rfl
                have hemit := hstrict A g B hsplit' hnn
                obtain ⟨a, b, hins⟩ := simplify_binary_some g.op hb _ _ hemit
                rcases hgi : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨c, l⟩⟩⟩
                · rw [hgi] at hins; simp at hins
                · rw [hgi] at hins; simp at hins
                · rw [hgi] at hins
                  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hins
                  have hu := ihA u a hins.1
                  have hv' := ihA v b hins.2
                  simp only [List.map_cons, List.map_nil, hu, hv']
                · rw [hgi] at hins; simp at hins
              rcases hop with hop | hop | hop
              · exact binary (Or.inl hop)
              · exact binary (Or.inr hop)
              · rw [hop] at hik2
                obtain ⟨a, rest, hins⟩ := simplify_not_inr _ _ _ hik2
                rcases hgi : g.inputs with _ | ⟨u, l⟩
                · rw [hgi] at hins; simp at hins
                · rw [hgi] at hins
                  simp only [List.map_cons, List.cons.injEq] at hins
                  have hu := ihA u a hins.1
                  rw [hop]
                  simp only [GateOp.eval, List.map_cons, List.headD_cons, hu]
            · rw [getD_snoc_ne _ _ _ _ (by rw [hlen]; exact hi)] at hik1
              rw [getD_snoc_ne _ _ _ _ (by rw [hwl _ (by simp)]; exact hi),
                getD_snoc_ne _ _ _ _ (by rw [hwl _ (by simp)]; exact hi)]
              exact ihA i k hik1
        have hfin := key C.gates [] (by simp) C.output jo hst
        rw [← he, ← he]
        exact hfin

end Restrict

open CircuitProof Restrict

def eight (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def pin : Fin 8 → Stat := ![Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4, Sum.inr 0, Sum.inr 5, Sum.inr 6, Sum.inr 1]

theorem binaryFloor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = eight x) :
    13 ≤ nonNotCount C.gates := by
  have dep : ∃ x : Fin 8 → Bool, eight (Function.update x 2 true) ≠ eight (Function.update x 2 false) :=
    ⟨fun i => decide (i = 6),by decide +kernel⟩
  have nc : ∃ x y : Fin 8 → Bool, eight (Function.update x 2 false) ≠ eight (Function.update y 2 false) :=
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  obtain ⟨D,fd,sm,cd⟩ := restrict_drop C fan 2 eight correct dep nc
  have valid : ∀ i : Fin 8, Stat.Valid 7 (pin i) := by
    intro i
    fin_cases i <;> norm_num [pin, Stat.Valid]
  have matchTable : ∀ y : Fin 7 → Bool,
      eight (Function.update (fun i => Stat.val (List.ofFn y) (pin i)) 2 false) = Seven.edge y := by
    decide +kernel
  have eval : ∀ y : Fin 7 → Bool,
      D.eval (List.ofFn fun i => Stat.val (List.ofFn y) (pin i)) = Seven.edge y := by
    intro y
    rw [cd, matchTable]
  obtain ⟨E,fe,se,ce⟩ := restrict_core D fd pin valid Seven.edge eval
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  have low := Seven.binary_lower E fe ce
  have eq : Seven.Check2516.costly = (fun g : Gate => !isNotGate g.op) := by
    funext g
    cases g with
    | mk op ins => cases op <;> rfl
  rw [eq] at low
  change 12 ≤ nonNotCount E.gates at low
  omega

def witness8 : Circuit := ⟨[⟨.and,[0,3]⟩, ⟨.or,[0,1]⟩, ⟨.or,[4,5]⟩, ⟨.and,[9,10]⟩, ⟨.or,[1,2]⟩, ⟨.or,[12,3]⟩, ⟨.or,[6,7]⟩, ⟨.and,[13,14]⟩, ⟨.or,[5,6]⟩, ⟨.or,[4,7]⟩, ⟨.and,[16,17]⟩, ⟨.or,[8,11]⟩, ⟨.or,[19,15]⟩, ⟨.or,[20,18]⟩], 21⟩
theorem witnessCorrect : ∀ x : Fin 8 → Bool, witness8.eval (List.ofFn x) = eight x := by decide +kernel

end PEqualNP.Outside.L_meta_31225_aux

open PEqualNP.Outside.L_meta_31225_aux PEqualNP.Outside.L_meta_31225_aux.CircuitProof PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_31225 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hg,eq⟩ := neg
    have fan : FanInTwo ⟨gs,o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryFloor ⟨gs,o⟩ fan computes
    change 13 ≤ nonNotCount gs at low
    have lt : nonNotCount gs < gs.length := by
      unfold nonNotCount
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g,hg,by simp [eq,isNotGate]⟩
    exact ⟨witness8.gates,witness8.output,by simp [witness8],by change 14 ≤ gs.length; omega,witnessCorrect⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨op,cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g,hg,eq⟩)),cap⟩
