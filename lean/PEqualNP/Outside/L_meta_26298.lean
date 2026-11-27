import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26298_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def R_sz : ℕ := 4
def C_sz : ℕ := 4
def N_bits : ℕ := 16
def FULL : ℕ := 65535
def target : ℕ := 4398
def offMask : ℕ := 61137
def allowAON : Bool := true

def inTTs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def onBits : List ℕ := [1, 2, 3, 5, 8, 12]
def onBitMasks : List ℕ := [2, 4, 8, 32, 256, 4096]

def bit (w p : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight w p) 1) 1

lemma bit_eq_testBit (w p : ℕ) : bit w p = w.testBit p := by
  have h : Nat.land (Nat.shiftRight w p) 1 = (w >>> p) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

lemma testBit_land (a b k : ℕ) : (Nat.land a b).testBit k = (a.testBit k && b.testBit k) :=
  Nat.testBit_and a b k

lemma testBit_lor (a b k : ℕ) : (Nat.lor a b).testBit k = (a.testBit k || b.testBit k) :=
  Nat.testBit_or a b k

lemma testBit_xor' (a b k : ℕ) : (Nat.xor a b).testBit k = (a.testBit k ^^ b.testBit k) :=
  Nat.testBit_xor a b k

lemma land_comm (a b : ℕ) : Nat.land a b = Nat.land b a :=
  Nat.and_comm a b

lemma lor_comm (a b : ℕ) : Nat.lor a b = Nat.lor b a :=
  Nat.or_comm a b

lemma beq_false_iff {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

lemma ble_true_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b :=
  Iff.of_eq Nat.ble_eq

lemma ble_false_iff {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, Nat.ble_eq]; omega

lemma testBit_FULL {p : ℕ} (hp : p < N_bits) : FULL.testBit p = true := by
  have : ∀ q : Fin N_bits, FULL.testBit q.val = true := by decide
  exact this ⟨p, hp⟩

lemma testBit_FULL_ge {p : ℕ} (hp : N_bits ≤ p) : FULL.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (show FULL < 2 ^ N_bits by decide)
    (Nat.pow_le_pow_right (by norm_num) hp))

lemma testBit_not {w p : ℕ} (hp : p < N_bits) :
    (Nat.xor w FULL).testBit p = !w.testBit p := by
  rw [testBit_xor', testBit_FULL hp, Bool.xor_true]

lemma lt_pow_and {a b : ℕ} (ha : a < 2 ^ N_bits) : Nat.land a b < 2 ^ N_bits := by
  change a &&& b < 2 ^ N_bits; rw [Nat.and_comm]; exact Nat.and_lt_two_pow b ha

lemma lt_pow_or {a b : ℕ} (ha : a < 2 ^ N_bits) (hb : b < 2 ^ N_bits) :
    Nat.lor a b < 2 ^ N_bits :=
  Nat.or_lt_two_pow ha hb

lemma lt_pow_not {a : ℕ} (ha : a < 2 ^ N_bits) : Nat.xor a FULL < 2 ^ N_bits :=
  Nat.xor_lt_two_pow ha (by decide)

def isProper (w : ℕ) : Bool := Bool.rec (Bool.rec true false (Nat.beq w FULL)) false (Nat.beq w 0)

lemma isProper_iff {w : ℕ} : isProper w = true ↔ w ≠ 0 ∧ w ≠ FULL := by
  unfold isProper
  cases h0 : Nat.beq w 0 <;> cases h1 : Nat.beq w FULL
  · simp [beq_false_iff.mp h0, beq_false_iff.mp h1]
  · simp [Nat.eq_of_beq_eq_true h1]
  · simp [Nat.eq_of_beq_eq_true h0]
  · simp [Nat.eq_of_beq_eq_true h0]

def gateTT (g : Gate) (ws : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | .and, [] => FULL
  | .and, [a] => ws.getD a 0
  | .and, [a, b] => Nat.land (ws.getD a 0) (ws.getD b 0)
  | .or, [] => 0
  | .or, [a] => ws.getD a 0
  | .or, [a, b] => Nat.lor (ws.getD a 0) (ws.getD b 0)
  | .not, [] => FULL
  | .not, a :: _ => Nat.xor (ws.getD a 0) FULL
  | _, _ => 0

def evalTT (gs : List Gate) (ws : List ℕ) : List ℕ :=
  gs.foldl (fun acc g => acc ++ [gateTT g acc]) ws

lemma inTTs_lt : ∀ w ∈ inTTs, w < 2 ^ N_bits := by decide
lemma inTTs_nodup : inTTs.Nodup := by decide
lemma inTTs_proper : ∀ w ∈ inTTs, isProper w = true := by decide
lemma target_lt : target < 2 ^ N_bits := by decide
lemma target_proper : isProper target = true := by decide

lemma inTTs_bit (u : Fin R_sz) (v : Fin C_sz) (i : ℕ) :
    (inTTs.getD i 0).testBit (C_sz * u.val + v.val) = (oneEach u v).getD i false := by
  by_cases hi : i < 8
  · have : ∀ (k : Fin 8) (u : Fin R_sz) (v : Fin C_sz),
        (inTTs.getD k.val 0).testBit (C_sz * u.val + v.val) = (oneEach u v).getD k.val false := by
      decide
    exact this ⟨i, hi⟩ u v
  · have h1 : inTTs.getD i 0 = 0 := by
      simp [List.getD, List.getElem?_eq_none (show inTTs.length ≤ i by simp [inTTs]; omega)]
    have h2 : (oneEach u v).getD i false = false := by
      have hlen : (oneEach u v).length = 8 := by simp [oneEach, R_sz, C_sz]
      simp [List.getD, List.getElem?_eq_none (show (oneEach u v).length ≤ i by omega)]
    rw [h1, h2]; simp

lemma gateTT_lt (g : Gate) (ws : List ℕ) (hws : ∀ w ∈ ws, w < 2 ^ N_bits) :
    gateTT g ws < 2 ^ N_bits := by
  have hget : ∀ i, ws.getD i 0 < 2 ^ N_bits := by
    intro i
    by_cases h : i < ws.length
    · simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some]
      exact hws _ (List.getElem_mem h)
    · simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]
  cases hop : g.op <;> cases hin : g.inputs with
  | nil => simp only [gateTT, hop, hin]; decide
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [gateTT, hop, hin]
      first | exact hget a | exact lt_pow_not (hget a) | exact (by decide)
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        simp only [gateTT, hop, hin]
        first | exact lt_pow_and (hget a) | exact lt_pow_or (hget a) (hget b) | exact lt_pow_not (hget a) | exact (by decide)
      | cons _ _ =>
        simp only [gateTT, hop, hin]
        first | exact lt_pow_not (hget a) | exact (by decide)

lemma gateTT_bit (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List ℕ) (bs : List Bool) (idx : ℕ) (hidx : idx < N_bits)
    (hmatch : ∀ i, (ws.getD i 0).testBit idx = bs.getD i false) :
    (gateTT g ws).testBit idx = g.op.eval (g.inputs.map fun i => bs.getD i false) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · match hin : g.inputs with
    | [] => simp [gateTT, h, hin, GateOp.eval, testBit_FULL hidx]
    | [a] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, hmatch a]
    | [a, b] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, testBit_land, hmatch a, hmatch b]
    | _ :: _ :: _ :: _ => simp [hin] at hlen
  · match hin : g.inputs with
    | [] => simp [gateTT, h, hin, GateOp.eval]
    | [a] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false, hmatch a]
    | [a, b] => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false, testBit_lor, hmatch a, hmatch b]
    | _ :: _ :: _ :: _ => simp [hin] at hlen
  · match hin : g.inputs with
    | [] => simp [gateTT, h, hin, GateOp.eval, testBit_FULL hidx]
    | a :: _ => simp only [gateTT, h, hin, GateOp.eval, List.map_cons, List.headD_cons, testBit_not hidx, hmatch a]

lemma evalTT_bit (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ws : List ℕ) (bs : List Bool) (hlen : ws.length = bs.length) (idx : ℕ) (hidx : idx < N_bits)
    (hmatch : ∀ i, (ws.getD i 0).testBit idx = bs.getD i false) :
    ∀ i, ((evalTT gs ws).getD i 0).testBit idx =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) bs).getD i false := by
  induction gs generalizing ws bs with
  | nil => exact hmatch
  | cons g rest ih =>
    simp only [evalTT, List.foldl_cons] at *
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen])
    intro i
    have hg := hgs g (List.mem_cons_self ..)
    by_cases hi : i < ws.length
    · have hi' : i < bs.length := hlen ▸ hi
      simp only [List.getD, List.getElem?_append_left hi, List.getElem?_append_left hi']
      simpa [List.getD] using hmatch i
    · by_cases heq : i = ws.length
      · subst heq
        have h1 : (ws ++ [gateTT g ws]).getD ws.length 0 = gateTT g ws := by simp [List.getD]
        have h2 : (bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)]).getD ws.length false =
            g.op.eval (g.inputs.map fun j => bs.getD j false) := by rw [hlen]; simp [List.getD]
        rw [h1, h2]
        exact gateTT_bit g hg ws bs idx hidx hmatch
      · have hgt : ws.length + 1 ≤ i := by omega
        have h1 : (ws ++ [gateTT g ws]).getD i 0 = 0 := by
          simp [List.getD, List.getElem?_eq_none (show (ws ++ [gateTT g ws]).length ≤ i by simp; omega)]
        have h2 : (bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)]).getD i false = false := by
          simp [List.getD, List.getElem?_eq_none (show (bs ++ [_]).length ≤ i by simp; omega)]
        rw [h1, h2]; simp

lemma evalTT_lt (gs : List Gate) (ws : List ℕ) (hws : ∀ w ∈ ws, w < 2 ^ N_bits) :
    ∀ w ∈ evalTT gs ws, w < 2 ^ N_bits := by
  induction gs generalizing ws with
  | nil => exact hws
  | cons g rest ih =>
    simp only [evalTT, List.foldl_cons]
    apply ih
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hws w hw
    · exact gateTT_lt g ws hws

lemma circuit_target_mem (C : Circuit)
    (hfit : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrep : Represents (fun (u : Fin R_sz) (v : Fin C_sz) => target.testBit (C_sz * u.val + v.val)) C) :
    target ∈ evalTT C.gates inTTs := by
  set t := (evalTT C.gates inTTs).getD C.output 0
  have hlt : t < 2 ^ N_bits := by
    by_cases ho : C.output < (evalTT C.gates inTTs).length
    · simp only [t, List.getD, List.getElem?_eq_getElem ho, Option.getD_some]
      exact evalTT_lt C.gates inTTs inTTs_lt _ (List.getElem_mem ho)
    · simp [t, List.getElem?_eq_none (Nat.le_of_not_lt ho)]
  have hteq : t = target := by
    apply Nat.eq_of_testBit_eq
    intro idx
    by_cases hidx : idx < N_bits
    · have hu : idx / C_sz < R_sz := by simp only [R_sz, C_sz, N_bits] at hidx ⊢; omega
      have hv : idx % C_sz < C_sz := by simp only [C_sz]; omega
      have hidx_eq : C_sz * (idx / C_sz) + idx % C_sz = idx := Nat.div_add_mod idx C_sz
      have hb := evalTT_bit C.gates hfit inTTs (oneEach ⟨idx / C_sz, hu⟩ ⟨idx % C_sz, hv⟩)
        (by simp [inTTs, oneEach, R_sz, C_sz]) idx hidx
        (fun i => by have hbit := inTTs_bit ⟨idx / C_sz, hu⟩ ⟨idx % C_sz, hv⟩ i; simpa [hidx_eq] using hbit) C.output
      have hr := hrep ⟨idx / C_sz, hu⟩ ⟨idx % C_sz, hv⟩
      simp only [Circuit.eval, Circuit.wires] at hr
      rw [hb, hr, hidx_eq]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le target_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  have hne0 : t ≠ 0 := by rw [hteq]; exact (isProper_iff.mp target_proper).1
  by_cases ho : C.output < (evalTT C.gates inTTs).length
  · rw [← hteq]
    simp only [t, List.getD, List.getElem?_eq_getElem ho, Option.getD_some]
    exact List.getElem_mem ho
  · exfalso; apply hne0
    simp [t, List.getElem?_eq_none (Nat.le_of_not_lt ho)]

/-! ## Index-free semantic steps & canonical order -/

inductive Step where
  | sNot (a : ℕ) : Step
  | sAnd (a b : ℕ) : Step
  | sOr  (a b : ℕ) : Step
  deriving DecidableEq

def Step.out : Step → ℕ
  | .sNot a => Nat.xor a FULL
  | .sAnd a b => Nat.land a b
  | .sOr  a b => Nat.lor a b

def keyNot (a : ℕ) : ℕ := Nat.add (Nat.mul a 2) 1
def keyBin (a x : ℕ) (isOr : Bool) : ℕ :=
  let b := Nat.ble a x
  Nat.add (Nat.add (Nat.add 17179869184 (Nat.mul (Bool.rec x a b) 131072)) (Nat.mul (Bool.rec a x b) 2)) (Bool.rec 0 1 isOr)

lemma keyNot_eq (a : ℕ) : keyNot a = a * 2 + 1 := rfl

lemma keyBin_eq (a x : ℕ) (isOr : Bool) :
    keyBin a x isOr = 17179869184 + min a x * 131072 + max a x * 2 + if isOr then 1 else 0 := by
  unfold keyBin
  cases h : Nat.ble a x with
  | true =>
    have hle : a ≤ x := ble_true_iff.mp h
    cases isOr <;> simp [min_eq_left hle, max_eq_right hle]
  | false =>
    have hlt : x < a := ble_false_iff.mp h
    cases isOr <;> simp [min_eq_right (Nat.le_of_lt hlt), max_eq_left (Nat.le_of_lt hlt)]

def Step.key : Step → ℕ
  | .sNot a => keyNot a
  | .sAnd a b => keyBin a b false
  | .sOr  a b => keyBin a b true

def Step.uses (w : ℕ) : Step → Prop
  | .sNot a => a = w
  | .sAnd a b => a = w ∨ b = w
  | .sOr  a b => a = w ∨ b = w

def Step.valid (ws : List ℕ) : Step → Prop
  | .sNot a => allowAON = true ∧ a ∈ ws
  | .sAnd a b => a ∈ ws ∧ b ∈ ws
  | .sOr  a b => a ∈ ws ∧ b ∈ ws

lemma Step.valid_mono {ws1 ws2 : List ℕ} (h : ∀ x ∈ ws1, x ∈ ws2) {st : Step}
    (hv : st.valid ws1) : st.valid ws2 := by
  cases st with
  | sNot a => exact ⟨hv.1, h a hv.2⟩
  | sAnd a b => exact ⟨h a hv.1, h b hv.2⟩
  | sOr a b => exact ⟨h a hv.1, h b hv.2⟩

lemma Step.out_eq_of_key {s1 s2 : Step}
    (h1 : match s1 with | .sNot a => a < 2 ^ N_bits | .sAnd a b => a < 2 ^ N_bits ∧ b < 2 ^ N_bits | .sOr a b => a < 2 ^ N_bits ∧ b < 2 ^ N_bits)
    (h2 : match s2 with | .sNot a => a < 2 ^ N_bits | .sAnd a b => a < 2 ^ N_bits ∧ b < 2 ^ N_bits | .sOr a b => a < 2 ^ N_bits ∧ b < 2 ^ N_bits)
    (hk : s1.key = s2.key) : s1.out = s2.out := by
  have hpow : 2 ^ N_bits = 65536 := by decide
  rcases s1 with a1 | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases s2 with a2 | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
    simp only [Step.key, Step.out, keyNot_eq, keyBin_eq, Bool.false_eq_true, ↓reduceIte, add_zero] at hk ⊢
  · congr 1; omega
  · exfalso; rw [hpow] at h1; omega
  · exfalso; rw [hpow] at h1; omega
  · exfalso; rw [hpow] at h2; omega
  · rcases h1 with ⟨ha1, hb1⟩; rcases h2 with ⟨ha2, hb2⟩
    rw [hpow] at ha1 hb1 ha2 hb2
    have hmn1 : min a1 b1 < 65536 := min_lt_iff.mpr (.inl ha1)
    have hmx1 : max a1 b1 < 65536 := max_lt ha1 hb1
    have hmn2 : min a2 b2 < 65536 := min_lt_iff.mpr (.inl ha2)
    have hmx2 : max a2 b2 < 65536 := max_lt ha2 hb2
    have hmin : min a1 b1 = min a2 b2 := by omega
    have hmax : max a1 b1 = max a2 b2 := by omega
    rcases le_total a1 b1 with hle1 | hle1 <;> rcases le_total a2 b2 with hle2 | hle2
    · rw [min_eq_left hle1, min_eq_left hle2] at hmin; rw [max_eq_right hle1, max_eq_right hle2] at hmax; rw [hmin, hmax]
    · rw [min_eq_left hle1, min_eq_right hle2] at hmin; rw [max_eq_right hle1, max_eq_left hle2] at hmax; rw [hmin, hmax, land_comm]
    · rw [min_eq_right hle1, min_eq_left hle2] at hmin; rw [max_eq_left hle1, max_eq_right hle2] at hmax; rw [hmin, hmax, land_comm]
    · rw [min_eq_right hle1, min_eq_right hle2] at hmin; rw [max_eq_left hle1, max_eq_left hle2] at hmax; rw [hmin, hmax]
  · omega
  · exfalso; rw [hpow] at h2; omega
  · omega
  · rcases h1 with ⟨ha1, hb1⟩; rcases h2 with ⟨ha2, hb2⟩
    rw [hpow] at ha1 hb1 ha2 hb2
    have hmn1 : min a1 b1 < 65536 := min_lt_iff.mpr (.inl ha1)
    have hmx1 : max a1 b1 < 65536 := max_lt ha1 hb1
    have hmn2 : min a2 b2 < 65536 := min_lt_iff.mpr (.inl ha2)
    have hmx2 : max a2 b2 < 65536 := max_lt ha2 hb2
    have hmin : min a1 b1 = min a2 b2 := by omega
    have hmax : max a1 b1 = max a2 b2 := by omega
    rcases le_total a1 b1 with hle1 | hle1 <;> rcases le_total a2 b2 with hle2 | hle2
    · rw [min_eq_left hle1, min_eq_left hle2] at hmin; rw [max_eq_right hle1, max_eq_right hle2] at hmax; rw [hmin, hmax]
    · rw [min_eq_left hle1, min_eq_right hle2] at hmin; rw [max_eq_right hle1, max_eq_left hle2] at hmax; rw [hmin, hmax, lor_comm]
    · rw [min_eq_right hle1, min_eq_left hle2] at hmin; rw [max_eq_left hle1, max_eq_right hle2] at hmax; rw [hmin, hmax, lor_comm]
    · rw [min_eq_right hle1, min_eq_right hle2] at hmin; rw [max_eq_left hle1, max_eq_left hle2] at hmax; rw [hmin, hmax]

def ValidSeq : List ℕ → List Step → Prop
  | _, [] => True
  | ws, st :: rest => st.valid ws ∧ ValidSeq (ws ++ [st.out]) rest

lemma ValidSeq_mono {ws1 ws2 : List ℕ} (h : ∀ x ∈ ws1, x ∈ ws2) {ss : List Step}
    (hv : ValidSeq ws1 ss) : ValidSeq ws2 ss := by
  induction ss generalizing ws1 ws2 with
  | nil => trivial
  | cons st rest ih =>
    exact ⟨st.valid_mono h hv.1, ih (fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx ⊢
      exact hx.imp (h x) id) hv.2⟩

lemma ValidSeq_out_lt {ws : List ℕ} (hws : ∀ w ∈ ws, w < 2 ^ N_bits) {ss : List Step}
    (hv : ValidSeq ws ss) : ∀ w ∈ ws ++ ss.map Step.out, w < 2 ^ N_bits := by
  induction ss generalizing ws with
  | nil => simpa using hws
  | cons st rest ih =>
    have hout : st.out < 2 ^ N_bits := by
      cases st with
      | sNot a => exact lt_pow_not (hws a hv.1.2)
      | sAnd a b => exact lt_pow_and (hws a hv.1.1)
      | sOr a b => exact lt_pow_or (hws a hv.1.1) (hws b hv.1.2)
    have hws' : ∀ w ∈ ws ++ [st.out], w < 2 ^ N_bits := by
      intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      exact hw.elim (hws w) (fun e => e ▸ hout)
    intro w hw
    exact ih hws' hv.2 w (by simpa [List.append_assoc] using hw)

def Computes (ws : List ℕ) (ss : List Step) : Prop :=
  ValidSeq ws ss ∧ target ∈ ws ++ ss.map Step.out

lemma circuit_to_steps (gs : List Gate)
    (hgs : ∀ g ∈ gs, (if allowAON then g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
                      else g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ws : List ℕ) (ht : target ∈ evalTT gs ws) :
    ∃ ss : List Step, ss.length ≤ gs.length ∧ Computes (0 :: FULL :: ws) ss := by
  suffices ∀ (ws' : List ℕ), (∀ x ∈ ws, x ∈ ws') → 0 ∈ ws' → FULL ∈ ws' →
      ∃ ss : List Step, ss.length ≤ gs.length ∧ Computes ws' ss by
    exact this (0 :: FULL :: ws) (fun x hx => by simp [hx]) (by simp) (by simp)
  induction gs generalizing ws with
  | nil =>
    intro ws' hsub _ _
    exact ⟨[], by simp, trivial, List.mem_append_left _ (hsub _ (by simpa [evalTT] using ht))⟩
  | cons g rest ih =>
    intro ws' hsub h0 h1
    simp only [evalTT, List.foldl_cons] at ht
    have hg := hgs g (List.mem_cons_self ..)
    have hrest := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hget : ∀ i, ws.getD i 0 ∈ ws' := by
      intro i
      by_cases h : i < ws.length
      · simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some]
        exact hsub _ (List.getElem_mem h)
      · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none]; exact h0
    have hmem_or_step : gateTT g ws ∈ ws' ∨ ∃ st : Step, st.valid ws' ∧ st.out = gateTT g ws := by
      rcases hg with ⟨hop, hlen⟩
      have haon : g.op = .not → allowAON = true := by
        intro hnot
        cases ha : allowAON
        · rw [ha] at hop; simp [hnot] at hop
        · rfl
      have hop3 : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        cases ha : allowAON <;> rw [ha] at hop <;> simp at hop <;> tauto
      rcases hop3 with h | h | h
      · match hin : g.inputs with
        | [] => left; simp [gateTT, h, hin, h1]
        | [a] => left; simp only [gateTT, h, hin]; exact hget a
        | [a, b] => right; exact ⟨.sAnd (ws.getD a 0) (ws.getD b 0), ⟨hget a, hget b⟩, by simp [gateTT, h, hin, Step.out]⟩
        | _ :: _ :: _ :: _ => simp [hin] at hlen
      · match hin : g.inputs with
        | [] => left; simp [gateTT, h, hin, h0]
        | [a] => left; simp only [gateTT, h, hin]; exact hget a
        | [a, b] => right; exact ⟨.sOr (ws.getD a 0) (ws.getD b 0), ⟨hget a, hget b⟩, by simp [gateTT, h, hin, Step.out]⟩
        | _ :: _ :: _ :: _ => simp [hin] at hlen
      · match hin : g.inputs with
        | [] => left; simp [gateTT, h, hin, h1]
        | a :: _ => right; exact ⟨.sNot (ws.getD a 0), ⟨haon h, hget a⟩, by simp [gateTT, h, hin, Step.out]⟩
    rcases hmem_or_step with hmem | ⟨st, hstv, hsto⟩
    · obtain ⟨ss, hslen, hcomp⟩ := ih hrest (ws ++ [gateTT g ws]) ht ws' (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        exact hx.elim (hsub x) (fun e => e ▸ hmem)) h0 h1
      exact ⟨ss, by simp; omega, hcomp⟩
    · obtain ⟨ss, hslen, hsv, hst⟩ := ih hrest (ws ++ [gateTT g ws]) ht (ws' ++ [st.out]) (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        exact hx.imp (hsub x) (fun e => e.trans hsto.symm)) (List.mem_append_left _ h0) (List.mem_append_left _ h1)
      exact ⟨st :: ss, by simp; omega, ⟨hstv, hsv⟩, by simpa [List.append_assoc] using hst⟩

def Fresh : List ℕ → List Step → Prop
  | _, [] => True
  | ws, st :: rest => st.out ∉ ws ∧ Fresh (ws ++ [st.out]) rest

def CanonOrder : Option (ℕ × ℕ) → List Step → Prop
  | _, [] => True
  | none, st :: rest => CanonOrder (some (st.out, st.key)) rest
  | some (lo, lk), st :: rest => (st.uses lo ∨ lk < st.key) ∧ CanonOrder (some (st.out, st.key)) rest

def seqLt : List Step → List Step → Prop
  | [], _ => False
  | _, [] => False
  | s1 :: r1, s2 :: r2 => r1.length = r2.length ∧ (s1.key < s2.key ∨ (s1.key = s2.key ∧ seqLt r1 r2))

lemma seqLt_wf : WellFounded seqLt := by
  have aux : ∀ n : ℕ, ∀ l : List Step, l.length = n → Acc seqLt l := by
    intro n
    induction n with
    | zero =>
      intro l hl
      cases l with
      | nil => exact ⟨_, fun y h => by cases y <;> cases h⟩
      | cons _ _ => simp at hl
    | succ n ihn =>
      have aux2 : ∀ k : ℕ, ∀ x : Step, x.key = k →
          ∀ xs : List Step, xs.length = n → Acc seqLt (x :: xs) := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ihk =>
          intro x hxk xs hxs
          have hacc_xs : Acc seqLt xs := ihn xs hxs
          induction hacc_xs generalizing x with
          | intro xs _ ihxs =>
            refine ⟨_, fun y hy => ?_⟩
            cases y with
            | nil => cases hy
            | cons y0 ys =>
              rcases hy with ⟨hlen_eq, hlt | ⟨heq, hrec⟩⟩
              · exact ihk y0.key (hxk ▸ hlt) y0 rfl ys (hlen_eq.trans hxs)
              · exact ihxs ys hrec y0 (heq.trans hxk) (hlen_eq.trans hxs)
      intro l hl
      cases l with
      | nil => simp at hl
      | cons x xs => exact aux2 x.key x rfl xs (by simp at hl; exact hl)
  exact ⟨fun l => aux l.length l rfl⟩

lemma exists_min_canon (ws : List ℕ) (hws : ∀ w ∈ ws, w < 2 ^ N_bits)
    (ss0 : List Step) (hc0 : Computes ws ss0) :
    ∃ ss : List Step, ss.length ≤ ss0.length ∧ Computes ws ss ∧
      (∀ ss', Computes ws ss' → ss.length ≤ ss'.length) ∧ Fresh ws ss ∧ CanonOrder none ss := by
  obtain ⟨len_min, hlen_le, hex_len⟩ : ∃ m ≤ ss0.length,
      (∃ ss, ss.length = m ∧ Computes ws ss) ∧ (∀ ss', Computes ws ss' → m ≤ ss'.length) := by
    classical
    let P : ℕ → Prop := fun m => ∃ ss, ss.length = m ∧ Computes ws ss
    have hP : ∃ m, P m := ⟨ss0.length, ss0, rfl, hc0⟩
    refine ⟨Nat.find hP, Nat.find_min' hP ⟨ss0, rfl, hc0⟩, Nat.find_spec hP, ?_⟩
    intro ss' hss'; exact Nat.find_min' hP ⟨ss', rfl, hss'⟩
  obtain ⟨ss, ⟨hss_len, hss_c⟩, hss_min⟩ :=
    WellFounded.has_min seqLt_wf {ss | ss.length = len_min ∧ Computes ws ss} hex_len.1
  have hmin_len : ∀ ss', Computes ws ss' → ss.length ≤ ss'.length := fun ss' h => by
    rw [hss_len]; exact hex_len.2 ss' h
  have hsplit : ∀ (p q : List Step) (w : List ℕ),
      ValidSeq w (p ++ q) ↔ ValidSeq w p ∧ ValidSeq (w ++ p.map Step.out) q := by
    intro p
    induction p with
    | nil => intro q w; simp [ValidSeq]
    | cons a as ihp =>
      intro q w
      simp only [List.cons_append, ValidSeq, List.map_cons] at ihp ⊢
      rw [ihp, List.append_assoc, List.singleton_append, and_assoc]
  have hfresh : Fresh ws ss := by
    suffices ∀ pre suf, ss = pre ++ suf → Fresh (ws ++ pre.map Step.out) suf by simpa using this [] ss rfl
    intro pre suf heq
    induction suf generalizing pre with
    | nil => trivial
    | cons st rest ih =>
      constructor
      · intro hmem
        have hv_all := hss_c.1; rw [heq] at hv_all
        have h1 := (hsplit pre (st :: rest) ws).mp hv_all
        have hvr' : ValidSeq (ws ++ pre.map Step.out) rest :=
          ValidSeq_mono (fun x hx => by
            simp only [List.mem_append, List.mem_singleton] at hx ⊢
            rcases hx with (h | h) | rfl
            · exact .inl h
            · exact .inr h
            · exact List.mem_append.mp hmem) h1.2.2
        have hcomp' : Computes ws (pre ++ rest) := by
          refine ⟨(hsplit pre rest ws).mpr ⟨h1.1, hvr'⟩, ?_⟩
          have ht := hss_c.2; rw [heq] at ht
          simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at ht ⊢
          rcases ht with hw | hp | hteq | hr
          · exact .inl hw
          · exact .inr (.inl hp)
          · rw [hteq]; simp only [List.mem_append] at hmem; exact hmem.elim .inl (fun h => .inr (.inl h))
          · exact .inr (.inr hr)
        have hle := hmin_len (pre ++ rest) hcomp'
        rw [heq] at hle; simp at hle
      · have := ih (pre ++ [st]) (by rw [heq]; simp)
        simpa [List.append_assoc] using this
  have hcanon : CanonOrder none ss := by
    have hfresh_split : ∀ (p q : List Step) (w : List ℕ),
        Fresh w (p ++ q) → Fresh (w ++ p.map Step.out) q := by
      intro p
      induction p with
      | nil => intro q w h; simpa using h
      | cons a as ihp =>
        intro q w h; have := ihp q (w ++ [a.out]) h.2; simpa [List.append_assoc] using this
    have hadj : ∀ pre s1 s2 rest, ss = pre ++ s1 :: s2 :: rest → s2.uses s1.out ∨ s1.key < s2.key := by
      intro pre s1 s2 rest heq
      by_contra hbad; push Not at hbad; obtain ⟨hnuse, hkle⟩ := hbad
      set Wp := ws ++ pre.map Step.out
      have h1 := (hsplit pre (s1 :: s2 :: rest) ws).mp (heq ▸ hss_c.1)
      have hvp := h1.1; have hvs1 := h1.2.1; have hvs2 := h1.2.2.1; have hvr := h1.2.2.2
      have hf2 : s2.out ∉ Wp ++ [s1.out] := (hfresh_split pre (s1 :: s2 :: rest) ws (heq ▸ hfresh)).2.1
      have hlt_Wp : ∀ w ∈ Wp, w < 2 ^ N_bits := ValidSeq_out_lt hws hvp
      have hvs2_Wp : s2.valid Wp := by
        cases s2 with
        | sNot a =>
          have hm := hvs2.2; rw [List.mem_append, List.mem_singleton] at hm
          exact ⟨hvs2.1, hm.resolve_right hnuse⟩
        | sAnd a b =>
          have ha := hvs2.1; have hb := hvs2.2
          rw [List.mem_append, List.mem_singleton] at ha hb
          simp only [Step.uses, not_or] at hnuse
          exact ⟨ha.resolve_right hnuse.1, hb.resolve_right hnuse.2⟩
        | sOr a b =>
          have ha := hvs2.1; have hb := hvs2.2
          rw [List.mem_append, List.mem_singleton] at ha hb
          simp only [Step.uses, not_or] at hnuse
          exact ⟨ha.resolve_right hnuse.1, hb.resolve_right hnuse.2⟩
      have hne_key : s2.key ≠ s1.key := by
        intro hkeq
        have hout_eq : s2.out = s1.out := by
          apply Step.out_eq_of_key _ _ hkeq
          · cases s2 with
            | sNot a => exact hlt_Wp a hvs2_Wp.2
            | sAnd a b => exact ⟨hlt_Wp a hvs2_Wp.1, hlt_Wp b hvs2_Wp.2⟩
            | sOr a b => exact ⟨hlt_Wp a hvs2_Wp.1, hlt_Wp b hvs2_Wp.2⟩
          · cases s1 with
            | sNot a => exact hlt_Wp a hvs1.2
            | sAnd a b => exact ⟨hlt_Wp a hvs1.1, hlt_Wp b hvs1.2⟩
            | sOr a b => exact ⟨hlt_Wp a hvs1.1, hlt_Wp b hvs1.2⟩
        exact hf2 (by simp [hout_eq])
      have hlt_key : s2.key < s1.key := Nat.lt_of_le_of_ne hkle hne_key
      let ss' := pre ++ s2 :: s1 :: rest
      have hcomp' : Computes ws ss' := by
        refine ⟨(hsplit pre (s2 :: s1 :: rest) ws).mpr ⟨hvp, hvs2_Wp, ?_, ?_⟩, ?_⟩
        · exact s1.valid_mono (fun x hx => List.mem_append_left _ hx) hvs1
        · exact ValidSeq_mono (fun x hx => by simp only [List.mem_append, List.mem_singleton] at hx ⊢; tauto) hvr
        · have ht := hss_c.2; rw [heq] at ht
          simp only [ss', List.map_append, List.map_cons, List.mem_append, List.mem_cons] at ht ⊢; tauto
      have hseq_lt : seqLt ss' ss := by
        rw [heq]
        have : ∀ p, seqLt (p ++ s2 :: s1 :: rest) (p ++ s1 :: s2 :: rest) := by
          intro p; induction p with
          | nil => exact ⟨by simp, .inl hlt_key⟩
          | cons x xs ihp => exact ⟨by simp, .inr ⟨rfl, ihp⟩⟩
        exact this pre
      exact hss_min ss' ⟨by rw [← hss_len, heq]; simp [ss'], hcomp'⟩ hseq_lt
    cases hss : ss with
    | nil => trivial
    | cons s0 rest0 =>
      change CanonOrder (some (s0.out, s0.key)) rest0
      suffices ∀ pre s r, ss = pre ++ s :: r → CanonOrder (some (s.out, s.key)) r by exact this [] s0 rest0 hss
      intro pre s r heq
      induction r generalizing pre s with
      | nil => trivial
      | cons s2 r2 ih => exact ⟨hadj pre s s2 r2 heq, ih (pre ++ [s]) s2 (by rw [heq]; simp)⟩
  exact ⟨ss, by omega, hss_c, hmin_len, hfresh, hcanon⟩

/-! ## Canonical Reach -/

def drop1 (d : Bool) (a : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if d then S.erase a else S

def drop2 (da db : Bool) (a x : ℕ) (S : Finset ℕ) : Finset ℕ :=
  drop1 db x (drop1 da a S)

inductive Reach : ℕ → ℕ → Finset ℕ → ℕ → ℕ → Prop where
  | done {lo lk} : Reach 0 0 {target} lo lk
  | step_not {b u S lo lk} (a : ℕ) (da : Bool)
      (ha : a ∈ S)
      (hord : a = lo ∨ lk < keyNot a)
      (hpc : isProper (Nat.xor a FULL) = true)
      (hnc : Nat.xor a FULL ∉ S) :
      Reach b u (insert (Nat.xor a FULL) (drop1 da a S)) (Nat.xor a FULL) (keyNot a) →
      Reach b (u + 1) S lo lk
  | step_bin {b u S lo lk} (a x : ℕ) (isOr da db : Bool)
      (ha : a ∈ S) (hx : x ∈ S) (hax : a ≠ x)
      (hord : (a = lo ∨ x = lo) ∨ lk < keyBin a x isOr)
      (hpc : isProper (if isOr then Nat.lor a x else Nat.land a x) = true)
      (hnc : (if isOr then Nat.lor a x else Nat.land a x) ∉ S) :
      Reach b u (insert (if isOr then Nat.lor a x else Nat.land a x) (drop2 da db a x S))
        (if isOr then Nat.lor a x else Nat.land a x) (keyBin a x isOr) →
      Reach (b + 1) u S lo lk

lemma reach_to_steps {b u lo lk : ℕ} {S : Finset ℕ} (hR : Reach b u S lo lk)
    (hu : allowAON = false → u = 0)
    (ws : List ℕ) (hsub : ∀ w ∈ S, w ∈ ws) :
    ∃ ss : List Step, ss.length = b + u ∧ Computes ws ss := by
  induction hR generalizing ws with
  | done => exact ⟨[], rfl, trivial, List.mem_append_left _ (hsub target (by simp))⟩
  | @step_not b u S lo lk a da ha _ _ _ _ ih =>
    have haon : allowAON = true := by
      cases h : allowAON
      · have := hu h; omega
      · rfl
    obtain ⟨ss, hslen, hsv, hst⟩ := ih (fun h => by rw [h] at haon; cases haon) (ws ++ [Nat.xor a FULL]) (fun w hw => by
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (hsub w (by cases da <;> simp [drop1] at hw; exact hw; exact hw.2)))
    exact ⟨.sNot a :: ss, by simp; omega, ⟨⟨haon, hsub a ha⟩, hsv⟩, by simpa [Step.out, List.append_assoc] using hst⟩
  | @step_bin b u S lo lk a x isOr da db ha hx _ _ _ _ _ ih =>
    set c := if isOr then Nat.lor a x else Nat.land a x
    obtain ⟨ss, hslen, hsv, hst⟩ := ih hu (ws ++ [c]) (fun w hw => by
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (hsub w (by cases da <;> cases db <;> simp [drop2, drop1] at hw <;> tauto)))
    cases isOr
    · exact ⟨.sAnd a x :: ss, by simp; omega, ⟨⟨hsub a ha, hsub x hx⟩, hsv⟩, by simpa [c, Step.out, List.append_assoc] using hst⟩
    · exact ⟨.sOr a x :: ss, by simp; omega, ⟨⟨hsub a ha, hsub x hx⟩, hsv⟩, by simpa [c, Step.out, List.append_assoc] using hst⟩

lemma card_le_drop1_succ (d : Bool) (a : ℕ) (T : Finset ℕ) :
    T.card ≤ (drop1 d a T).card + 1 := by
  cases d
  · simp [drop1]
  · simp only [drop1, ↓reduceIte]
    by_cases ha : a ∈ T
    · rw [Finset.card_erase_of_mem ha]; have : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩; omega
    · rw [Finset.erase_eq_of_notMem ha]; omega

lemma reach_card_le {b u lo lk : ℕ} {S : Finset ℕ} (h : Reach b u S lo lk) :
    S.card ≤ b + 1 := by
  induction h with
  | done => simp
  | @step_not b u S lo lk a da _ _ _ hna _ ih =>
    have h1 : (insert (Nat.xor a FULL) (drop1 da a S)).card = (drop1 da a S).card + 1 := by
      apply Finset.card_insert_of_notMem
      intro hm
      cases da
      · exact hna hm
      · exact hna (Finset.mem_erase.mp hm).2
    have h2 := card_le_drop1_succ da a S; omega
  | @step_bin b u S lo lk a x isOr da db _ _ _ _ _ hnc _ ih =>
    set c := if isOr then Nat.lor a x else Nat.land a x
    have h1 : (insert c (drop2 da db a x S)).card = (drop2 da db a x S).card + 1 := by
      apply Finset.card_insert_of_notMem
      intro hm
      have : c ∈ S := by
        cases da <;> cases db <;> simp only [drop2, drop1, ↓reduceIte, Bool.false_eq_true, Finset.mem_erase] at hm
        · exact hm
        · exact hm.2
        · exact hm.2
        · exact hm.2.2
      exact hnc this
    have hd1 := card_le_drop1_succ da a S
    have hd2 := card_le_drop1_succ db x (drop1 da a S)
    dsimp only [drop2] at h1 ih; omega

lemma reach_u0_card2 {b lo lk : ℕ} {a x : ℕ}
    (h : Reach b 0 {a, x} lo lk) :
    target = a ∨ target = x ∨ target = Nat.land a x ∨ target = Nat.lor a x := by
  suffices ∀ (b' u' : ℕ) (S : Finset ℕ) (lo' lk' : ℕ), Reach b' u' S lo' lk' → u' = 0 →
      (∀ w ∈ S, w = a ∨ w = x ∨ w = Nat.land a x ∨ w = Nat.lor a x) →
      target = a ∨ target = x ∨ target = Nat.land a x ∨ target = Nat.lor a x by
    exact this b 0 {a, x} lo lk h rfl (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> tauto)
  intro b' u' S lo' lk' hR hu0 hsub
  induction hR with
  | done => exact hsub target (by simp)
  | step_not => omega
  | @step_bin b u S lo lk u1 u2 isOr da db hu1 hu2 _ _ _ _ _ ih =>
    apply ih hu0
    intro w hw; simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · have h1 := hsub u1 hu1; have h2 := hsub u2 hu2
      have hland_closed : ∀ u v, (u = a ∨ u = x ∨ u = Nat.land a x ∨ u = Nat.lor a x) →
          (v = a ∨ v = x ∨ v = Nat.land a x ∨ v = Nat.lor a x) →
          Nat.land u v = a ∨ Nat.land u v = x ∨ Nat.land u v = Nat.land a x ∨ Nat.land u v = Nat.lor a x := by
        intro u v hu hv
        have eq_of : ∀ lhs rhs : ℕ, (∀ k, lhs.testBit k = rhs.testBit k) → lhs = rhs := fun _ _ h => Nat.eq_of_testBit_eq h
        rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv]
        · left; exact eq_of _ _ (fun k => by simp)
        · right; right; left; rfl
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact land_comm x a
        · right; left; exact eq_of _ _ (fun k => by simp)
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact eq_of _ _ (fun k => by simp)
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp)
      have hlor_closed : ∀ u v, (u = a ∨ u = x ∨ u = Nat.land a x ∨ u = Nat.lor a x) →
          (v = a ∨ v = x ∨ v = Nat.land a x ∨ v = Nat.lor a x) →
          Nat.lor u v = a ∨ Nat.lor u v = x ∨ Nat.lor u v = Nat.land a x ∨ Nat.lor u v = Nat.lor a x := by
        intro u v hu hv
        have eq_of : ∀ lhs rhs : ℕ, (∀ k, lhs.testBit k = rhs.testBit k) → lhs = rhs := fun _ _ h => Nat.eq_of_testBit_eq h
        rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv]
        · left; exact eq_of _ _ (fun k => by simp)
        · right; right; right; rfl
        · left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact lor_comm x a
        · right; left; exact eq_of _ _ (fun k => by simp)
        · right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; left; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; left; exact eq_of _ _ (fun k => by simp)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp only [testBit_land, testBit_lor]; cases a.testBit k <;> cases x.testBit k <;> rfl)
        · right; right; right; exact eq_of _ _ (fun k => by simp)
      cases isOr
      · simpa using hland_closed u1 u2 h1 h2
      · simpa using hlor_closed u1 u2 h1 h2
    · apply hsub w
      cases da <;> cases db <;> simp [drop2, drop1] at hw <;> tauto

lemma reach_u0_card1 {b lo lk a : ℕ} (h : Reach b 0 {a} lo lk) : target = a := by
  have := reach_u0_card2 (a := a) (x := a) (by simpa using h)
  have h1 : Nat.land a a = a := by apply Nat.eq_of_testBit_eq; intro k; simp
  have h2 : Nat.lor a a = a := by apply Nat.eq_of_testBit_eq; intro k; simp
  rw [h1, h2] at this; tauto

lemma reach_b0 {u lo lk : ℕ} {S : Finset ℕ} (hS_lt : ∀ w ∈ S, w < 2 ^ N_bits)
    (h : Reach 0 u S lo lk) :
    ∃ w ∈ S, target = w ∨ (0 < u ∧ target = Nat.xor w FULL) := by
  suffices ∀ (b' u' lo' lk' : ℕ) (S' : Finset ℕ), Reach b' u' S' lo' lk' → b' = 0 →
      (∀ w ∈ S', w < 2 ^ N_bits) → ∃ w ∈ S', target = w ∨ (0 < u' ∧ target = Nat.xor w FULL) by
    exact this 0 u lo lk S h rfl hS_lt
  intro b' u' lo' lk' S' hR hb0 hS_lt
  induction hR with
  | done => exact ⟨target, by simp, .inl rfl⟩
  | step_bin => omega
  | @step_not b u S lo lk a da ha _ _ _ _ ih =>
    have hlt' : ∀ w ∈ insert (Nat.xor a FULL) (drop1 da a S), w < 2 ^ N_bits := by
      intro w hw; simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact lt_pow_not (hS_lt a ha)
      · cases da <;> simp [drop1] at hw; exact hS_lt w hw; exact hS_lt w hw.2
    obtain ⟨w, hw, htw⟩ := ih hb0 hlt'
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · refine ⟨a, ha, ?_⟩
      rcases htw with htw | ⟨_, htw⟩
      · exact .inr ⟨by omega, htw⟩
      · left; rw [htw]
        apply Nat.eq_of_testBit_eq; intro k
        by_cases hk : k < N_bits
        · simp
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_pow_not (lt_pow_not (hS_lt a ha)))
            (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (hS_lt a ha) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · have hwm : w ∈ S := by cases da <;> simp [drop1] at hw; exact hw; exact hw.2
      rcases htw with htw | ⟨_, htw⟩
      · exact ⟨w, hwm, .inl htw⟩
      · exact ⟨w, hwm, .inr ⟨by omega, htw⟩⟩

lemma reach_sep {b u lo lk : ℕ} {S : Finset ℕ} (hR : Reach b u S lo lk)
    (p q : ℕ) (hpN : p < N_bits) (hqN : q < N_bits)
    (hp : target.testBit p = true) (hq : target.testBit q = false) :
    if u = 0 then ∃ w ∈ S, w.testBit p = true ∧ w.testBit q = false
    else ∃ w ∈ S, w.testBit p ≠ w.testBit q := by
  induction hR with
  | done =>
    split_ifs
    · exact ⟨target, by simp, hp, hq⟩
    · exact ⟨target, by simp, by rw [hp, hq]; decide⟩
  | @step_not b u S lo lk a da ha _ _ _ _ ih =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have hsep : ∃ w ∈ insert (Nat.xor a FULL) (drop1 da a S), w.testBit p ≠ w.testBit q := by
      by_cases hu : u = 0
      · simp only [hu, ↓reduceIte] at ih; obtain ⟨w, hw, hwp, hwq⟩ := ih
        exact ⟨w, hw, by rw [hwp, hwq]; decide⟩
      · simp only [hu, ↓reduceIte] at ih; exact ih
    obtain ⟨w, hw, hne⟩ := hsep
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · refine ⟨a, ha, fun heq => hne ?_⟩; rw [testBit_not hpN, testBit_not hqN, heq]
    · have : w ∈ S := by cases da <;> simp [drop1] at hw; exact hw; exact hw.2
      exact ⟨w, this, hne⟩
  | @step_bin b u S lo lk a x isOr da db ha hx _ _ _ _ _ ih =>
    by_cases hu : u = 0
    · simp only [hu, ↓reduceIte] at ih ⊢
      obtain ⟨w, hw, hwp, hwq⟩ := ih
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · cases isOr
        · simp only [Bool.false_eq_true, ↓reduceIte, testBit_land, Bool.and_eq_true, Bool.and_eq_false_iff] at hwp hwq
          rcases hwq with hqa | hqx
          · exact ⟨a, ha, hwp.1, hqa⟩
          · exact ⟨x, hx, hwp.2, hqx⟩
        · simp only [↓reduceIte, testBit_lor, Bool.or_eq_true, Bool.or_eq_false_iff] at hwp hwq
          rcases hwp with hpa | hpx
          · exact ⟨a, ha, hpa, hwq.1⟩
          · exact ⟨x, hx, hpx, hwq.2⟩
      · have : w ∈ S := by cases da <;> cases db <;> simp [drop2, drop1] at hw <;> tauto
        exact ⟨w, this, hwp, hwq⟩
    · simp only [hu, ↓reduceIte] at ih ⊢
      obtain ⟨w, hw, hne⟩ := ih
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · by_cases hae : a.testBit p ≠ a.testBit q
        · exact ⟨a, ha, hae⟩
        · push Not at hae
          refine ⟨x, hx, fun hxe => hne ?_⟩
          cases isOr
          · simp [hae, hxe]
          · simp [hae, hxe]
      · have : w ∈ S := by cases da <;> cases db <;> simp [drop2, drop1] at hw <;> tauto
        exact ⟨w, this, hne⟩

def optLo : Option (ℕ × ℕ) → ℕ | none => 0 | some (lo, _) => lo
def optLk : Option (ℕ × ℕ) → ℕ | none => 0 | some (_, lk) => lk

lemma extract_canon (ws : List ℕ) (hws : ∀ w ∈ ws, w < 2 ^ N_bits)
    (ss : List Step) (hv : ValidSeq ws ss) (hf : Fresh ws ss)
    (hmin : ∀ ss', Computes ws ss' → ss.length ≤ ss'.length)
    (prev : Option (ℕ × ℕ)) (hcan : CanonOrder prev ss)
    (ht : target ∈ ws ++ ss.map Step.out)
    (hprop_in : ∀ w ∈ ws, w = 0 ∨ w = FULL ∨ isProper w = true) :
    ∃ b u S, b + u ≤ ss.length ∧ (allowAON = false → u = 0) ∧
      (∀ w ∈ S, w ∈ ws ∧ isProper w = true) ∧ Reach b u S (optLo prev) (optLk prev) := by
  induction ss generalizing ws prev with
  | nil =>
    have htm : target ∈ ws := by simpa using ht
    refine ⟨0, 0, {target}, by simp, fun _ => rfl, ?_, Reach.done⟩
    intro w hw; simp only [Finset.mem_singleton] at hw; subst hw; exact ⟨htm, target_proper⟩
  | cons st rest ih =>
    have hout_lt : st.out < 2 ^ N_bits := by
      cases st with
      | sNot a => exact lt_pow_not (hws a hv.1.2)
      | sAnd a b => exact lt_pow_and (hws a hv.1.1)
      | sOr a b => exact lt_pow_or (hws a hv.1.1) (hws b hv.1.2)
    have hws' : ∀ w ∈ ws ++ [st.out], w < 2 ^ N_bits := by
      intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      exact hw.elim (hws w) (fun e => e ▸ hout_lt)
    have hprop' : ∀ w ∈ ws ++ [st.out], w = 0 ∨ w = FULL ∨ isProper w = true := by
      intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hprop_in w hw
      · by_cases h0 : st.out = 0
        · exact .inl h0
        · by_cases h1 : st.out = FULL
          · exact .inr (.inl h1)
          · exact .inr (.inr (isProper_iff.mpr ⟨h0, h1⟩))
    have hmin_rest : ∀ ss', Computes (ws ++ [st.out]) ss' → rest.length ≤ ss'.length := by
      intro ss' hcomp'
      have hle := hmin (st :: ss') ⟨⟨hv.1, hcomp'.1⟩, by simpa [List.append_assoc] using hcomp'.2⟩
      simp at hle; omega
    have hcan_rest : CanonOrder (some (st.out, st.key)) rest := by
      cases prev with | none => exact hcan | some _ => exact hcan.2
    have hord_prev : prev = none ∨ (st.uses (optLo prev) ∨ optLk prev < st.key) := by
      cases prev with | none => exact .inl rfl | some _ => exact .inr hcan.1
    obtain ⟨b, u, S', hbu, hu0, hS', hR'⟩ :=
      ih (ws ++ [st.out]) hws' hv.2 hf.2 hmin_rest (some (st.out, st.key)) hcan_rest
        (by simpa [List.append_assoc] using ht) hprop'
    set c := st.out
    have hcS : c ∈ S' := by
      by_contra hnc
      have hsub : ∀ w ∈ S', w ∈ ws := by
        intro w hw
        have hm := (hS' w hw).1
        simp only [List.mem_append, List.mem_singleton] at hm
        exact hm.resolve_right (fun e => hnc (e ▸ hw))
      obtain ⟨ss', hslen, hcomp'⟩ := reach_to_steps hR' hu0 ws hsub
      have hle := hmin ss' hcomp'
      simp at hle; omega
    have hcp : isProper c = true := (hS' c hcS).2
    have hc_not_ws : c ∉ ws := hf.1
    have hsub : ∀ w ∈ S'.erase c, w ∈ ws ∧ isProper w = true := by
      intro w hw
      obtain ⟨hne, hmw⟩ := Finset.mem_erase.mp hw
      obtain ⟨hm, hp⟩ := hS' w hmw
      simp only [List.mem_append, List.mem_singleton] at hm
      exact ⟨hm.resolve_right hne, hp⟩
    have hnot0 : c ≠ 0 := (isProper_iff.mp hcp).1
    have hnot1 : c ≠ FULL := (isProper_iff.mp hcp).2
    cases hst : st with
    | sNot a =>
      subst hst
      have ha_ws : a ∈ ws := hv.1.2
      have haon_t : allowAON = true := hv.1.1
      have hap : isProper a = true := by
        rcases hprop_in a ha_ws with rfl | rfl | hp
        · exfalso; exact hnot1 (by simp [c, Step.out])
        · exfalso; exact hnot0 (by simp [c, Step.out])
        · exact hp
      let S := insert a (S'.erase c)
      have hc_not_S : c ∉ S := by
        intro hm; simp only [S, Finset.mem_insert, Finset.mem_erase] at hm
        rcases hm with hca | ⟨hne, _⟩
        · exact hc_not_ws (hca ▸ ha_ws)
        · exact hne rfl
      let da : Bool := decide (a ∉ S'.erase c)
      have hS'_eq : insert c (drop1 da a S) = S' := by
        ext w; simp only [Finset.mem_insert, drop1, S, da]
        by_cases hwc : w = c
        · subst hwc; simp [hcS]
        · simp only [hwc, false_or]
          by_cases hwa : w = a
          · rw [hwa]
            by_cases ham : a ∈ S'.erase c
            · simp [ham, (Finset.mem_erase.mp ham).2]
            · have hna : a ∉ S' := fun hm => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hm⟩)
              simp [ham, hna]
          · by_cases ham : a ∈ S'.erase c <;> simp [ham, Finset.mem_erase, hwc]
      have hord_not : a = optLo prev ∨ optLk prev < keyNot a := by
        rcases hord_prev with rfl | h
        · right; simp [optLk, keyNot_eq]
        · simpa [Step.uses, Step.key] using h
      refine ⟨b, u + 1, S, by simp; omega, (fun h => by rw [h] at haon_t; cases haon_t), ?_, ?_⟩
      · intro w hw; simp only [S, Finset.mem_insert] at hw
        exact hw.elim (fun e => e ▸ ⟨ha_ws, hap⟩) (hsub w)
      · apply Reach.step_not a da (by simp [S]) hord_not hcp hc_not_S
        change Reach b u (insert c (drop1 da a S)) c (keyNot a); rw [hS'_eq]; exact hR'
    | sAnd a x =>
      subst hst
      have ha_ws : a ∈ ws := hv.1.1; have hx_ws : x ∈ ws := hv.1.2
      have hap : isProper a = true := by
        rcases hprop_in a ha_ws with rfl | rfl | hp
        · exfalso; exact hnot0 (by simp [c, Step.out])
        · exfalso
          have : Nat.land FULL x = x := by
            apply Nat.eq_of_testBit_eq; intro k
            by_cases hk : k < N_bits
            · simp [testBit_FULL hk]
            · rw [testBit_land, testBit_FULL_ge (by omega), Bool.false_and,
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le (hws x hx_ws) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          exact hc_not_ws (by rw [show c = x from this]; exact hx_ws)
        · exact hp
      have hxp : isProper x = true := by
        rcases hprop_in x hx_ws with rfl | rfl | hp
        · exfalso; exact hnot0 (by simp [c, Step.out])
        · exfalso
          have : Nat.land a FULL = a := by
            apply Nat.eq_of_testBit_eq; intro k
            by_cases hk : k < N_bits
            · simp [testBit_FULL hk]
            · rw [testBit_land, testBit_FULL_ge (by omega), Bool.and_false,
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le (hws a ha_ws) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          exact hc_not_ws (by rw [show c = a from this]; exact ha_ws)
        · exact hp
      have hax : a ≠ x := by
        intro h; subst h
        have : Nat.land a a = a := by apply Nat.eq_of_testBit_eq; intro k; simp
        exact hc_not_ws (by rw [show c = a from this]; exact ha_ws)
      let S := insert a (insert x (S'.erase c))
      have hc_not_S : c ∉ S := by
        intro hm; simp only [S, Finset.mem_insert, Finset.mem_erase] at hm
        rcases hm with hca | hcx | ⟨hne, _⟩
        · exact hc_not_ws (hca ▸ ha_ws)
        · exact hc_not_ws (hcx ▸ hx_ws)
        · exact hne rfl
      let da : Bool := decide (a ∉ S'.erase c)
      let db : Bool := decide (x ∉ S'.erase c)
      have hS'_eq : insert c (drop2 da db a x S) = S' := by
        ext w; simp only [Finset.mem_insert, drop2, drop1, S, da, db]
        by_cases hwc : w = c
        · subst hwc; simp [hcS]
        · simp only [hwc, false_or]
          by_cases ham : a ∈ S'.erase c <;> by_cases hxm : x ∈ S'.erase c <;>
            simp only [ham, hxm, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
              Bool.false_eq_true, ↓reduceIte, Finset.mem_erase, Finset.mem_insert]
          · constructor
            · rintro (rfl | rfl | ⟨_, hw⟩)
              · exact (Finset.mem_erase.mp ham).2
              · exact (Finset.mem_erase.mp hxm).2
              · exact hw
            · intro hw; right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwx, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact (Finset.mem_erase.mp ham).2
              · exact absurd rfl hwx
              · exact hw
            · intro hw
              refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwa, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact absurd rfl hwa
              · exact (Finset.mem_erase.mp hxm).2
              · exact hw
            · intro hw
              refine ⟨fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwx, hwa, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact absurd rfl hwa
              · exact absurd rfl hwx
              · exact hw
            · intro hw
              refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩),
                fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
      have hord_bin : (a = optLo prev ∨ x = optLo prev) ∨ optLk prev < keyBin a x false := by
        rcases hord_prev with rfl | h
        · right; simp [optLk, keyBin_eq]
        · simpa [Step.uses, Step.key] using h
      refine ⟨b + 1, u, S, by simp; omega, hu0, ?_, ?_⟩
      · intro w hw; simp only [S, Finset.mem_insert] at hw
        rcases hw with rfl | rfl | hm
        · exact ⟨ha_ws, hap⟩
        · exact ⟨hx_ws, hxp⟩
        · exact hsub w hm
      · apply Reach.step_bin a x false da db (by simp [S]) (by simp [S]) hax hord_bin hcp hc_not_S
        change Reach b u (insert c (drop2 da db a x S)) c (keyBin a x false); rw [hS'_eq]; exact hR'
    | sOr a x =>
      subst hst
      have ha_ws : a ∈ ws := hv.1.1; have hx_ws : x ∈ ws := hv.1.2
      have hap : isProper a = true := by
        rcases hprop_in a ha_ws with rfl | rfl | hp
        · exfalso; exact hc_not_ws (by simpa [c, Step.out] using hx_ws)
        · exfalso
          have : Nat.lor FULL x = FULL := by
            apply Nat.eq_of_testBit_eq; intro k
            by_cases hk : k < N_bits
            · simp [testBit_FULL hk]
            · rw [testBit_lor, testBit_FULL_ge (by omega), Bool.false_or,
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le (hws x hx_ws) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          exact hnot1 (by simpa [c, Step.out] using this)
        · exact hp
      have hxp : isProper x = true := by
        rcases hprop_in x hx_ws with rfl | rfl | hp
        · exfalso; exact hc_not_ws (by simpa [c, Step.out] using ha_ws)
        · exfalso
          have : Nat.lor a FULL = FULL := by
            apply Nat.eq_of_testBit_eq; intro k
            by_cases hk : k < N_bits
            · simp [testBit_FULL hk]
            · rw [testBit_lor, testBit_FULL_ge (by omega), Bool.or_false,
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le (hws a ha_ws) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          exact hnot1 (by simpa [c, Step.out] using this)
        · exact hp
      have hax : a ≠ x := by
        intro h; subst h
        have : Nat.lor a a = a := by apply Nat.eq_of_testBit_eq; intro k; simp
        exact hc_not_ws (by rw [show c = a from this]; exact ha_ws)
      let S := insert a (insert x (S'.erase c))
      have hc_not_S : c ∉ S := by
        intro hm; simp only [S, Finset.mem_insert, Finset.mem_erase] at hm
        rcases hm with hca | hcx | ⟨hne, _⟩
        · exact hc_not_ws (hca ▸ ha_ws)
        · exact hc_not_ws (hcx ▸ hx_ws)
        · exact hne rfl
      let da : Bool := decide (a ∉ S'.erase c)
      let db : Bool := decide (x ∉ S'.erase c)
      have hS'_eq : insert c (drop2 da db a x S) = S' := by
        ext w; simp only [Finset.mem_insert, drop2, drop1, S, da, db]
        by_cases hwc : w = c
        · subst hwc; simp [hcS]
        · simp only [hwc, false_or]
          by_cases ham : a ∈ S'.erase c <;> by_cases hxm : x ∈ S'.erase c <;>
            simp only [ham, hxm, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
              Bool.false_eq_true, ↓reduceIte, Finset.mem_erase, Finset.mem_insert]
          · constructor
            · rintro (rfl | rfl | ⟨_, hw⟩)
              · exact (Finset.mem_erase.mp ham).2
              · exact (Finset.mem_erase.mp hxm).2
              · exact hw
            · intro hw; right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwx, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact (Finset.mem_erase.mp ham).2
              · exact absurd rfl hwx
              · exact hw
            · intro hw
              refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwa, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact absurd rfl hwa
              · exact (Finset.mem_erase.mp hxm).2
              · exact hw
            · intro hw
              refine ⟨fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
          · constructor
            · rintro ⟨hwx, hwa, (rfl | rfl | ⟨_, hw⟩)⟩
              · exact absurd rfl hwa
              · exact absurd rfl hwx
              · exact hw
            · intro hw
              refine ⟨fun hwx => hxm (Finset.mem_erase.mpr ⟨hwx ▸ hwc, hwx ▸ hw⟩),
                fun hwa => ham (Finset.mem_erase.mpr ⟨hwa ▸ hwc, hwa ▸ hw⟩), ?_⟩
              right; right; exact ⟨hwc, hw⟩
      have hord_bin : (a = optLo prev ∨ x = optLo prev) ∨ optLk prev < keyBin a x true := by
        rcases hord_prev with rfl | h
        · right; simp [optLk, keyBin_eq]
        · simpa [Step.uses, Step.key] using h
      refine ⟨b + 1, u, S, by simp; omega, hu0, ?_, ?_⟩
      · intro w hw; simp only [S, Finset.mem_insert] at hw
        rcases hw with rfl | rfl | hm
        · exact ⟨ha_ws, hap⟩
        · exact ⟨hx_ws, hxp⟩
        · exact hsub w hm
      · apply Reach.step_bin a x true da db (by simp [S]) (by simp [S]) hax hord_bin hcp hc_not_S
        change Reach b u (insert c (drop2 da db a x S)) c (keyBin a x true); rw [hS'_eq]; exact hR'

/-! ## Fast Nat bitmask search -/

def monoCovM (m acc : ℕ) : List ℕ → Bool
  | [] => Nat.beq acc 0
  | w :: ws =>
    Bool.rec
      (let acc' := Nat.land w acc
       Bool.rec (monoCovM m acc' ws) true (Nat.beq acc' 0))
      (monoCovM m acc ws)
      (Nat.beq (Nat.land w m) 0)

def eqCovM (m acc : ℕ) : List ℕ → Bool
  | [] => Nat.beq acc 0
  | w :: ws =>
    let acc' := Nat.land (Bool.rec w (Nat.xor w FULL) (Nat.beq (Nat.land w m) 0)) acc
    Bool.rec (eqCovM m acc' ws) true (Nat.beq acc' 0)

def allCovAux (allowNot : Bool) (W : List ℕ) : List ℕ → Bool
  | [] => true
  | m :: ms =>
    Bool.rec false (allCovAux allowNot W ms)
      (Bool.rec (monoCovM m offMask W) (eqCovM m offMask W) allowNot)

def allCov (allowNot : Bool) (W : List ℕ) : Bool :=
  allCovAux allowNot W onBitMasks

lemma testBit_of_land_pow2_eq_zero (p w : ℕ) (h : Nat.land w (2 ^ p) = 0) :
    w.testBit p = false := by
  have hk := congrArg (fun n => n.testBit p) h
  rw [testBit_land, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at hk
  exact hk

lemma testBit_of_land_pow2_ne_zero (p w : ℕ) (h : Nat.land w (2 ^ p) ≠ 0) :
    w.testBit p = true := by
  cases hw : w.testBit p
  · exfalso; apply h
    apply Nat.eq_of_testBit_eq; intro k
    rw [testBit_land, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hpk : p = k
    · subst hpk; simp [hw]
    · simp [hpk]
  · rfl

lemma monoCovM_of_sep (p : ℕ) (W : List ℕ) (acc : ℕ)
    (hacc : ∀ q, acc.testBit q = true → ∃ w ∈ W, w.testBit p = true ∧ w.testBit q = false) :
    monoCovM (2 ^ p) acc W = true := by
  induction W generalizing acc with
  | nil =>
    rw [monoCovM, Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro q
    rw [Nat.zero_testBit]
    cases hq : acc.testBit q
    · rfl
    · obtain ⟨_, hw, _⟩ := hacc q hq; cases hw
  | cons w ws ih =>
    unfold monoCovM
    cases hb : Nat.beq (Nat.land w (2 ^ p)) 0 with
    | true =>
      dsimp only
      apply ih acc; intro q hq
      obtain ⟨w', hw', hwp', hwq'⟩ := hacc q hq
      rcases List.mem_cons.mp hw' with hw_eq | hw'
      · rw [hw_eq, testBit_of_land_pow2_eq_zero p w (Nat.eq_of_beq_eq_true hb)] at hwp'
        exact Bool.noConfusion hwp'
      · exact ⟨w', hw', hwp', hwq'⟩
    | false =>
      dsimp only
      cases hz : Nat.beq (Nat.land w acc) 0 with
      | true => rfl
      | false =>
        dsimp only
        apply ih (Nat.land w acc); intro q hq
        rw [testBit_land, Bool.and_eq_true] at hq
        obtain ⟨w', hw', hwp', hwq'⟩ := hacc q hq.2
        rcases List.mem_cons.mp hw' with rfl | hw'
        · rw [hq.1] at hwq'; exact Bool.noConfusion hwq'
        · exact ⟨w', hw', hwp', hwq'⟩

lemma eqCovM_of_sep (p : ℕ) (W : List ℕ) (acc : ℕ) (hacc_lt : acc < 2 ^ N_bits)
    (hacc : ∀ q, acc.testBit q = true → ∃ w ∈ W, w.testBit p ≠ w.testBit q) :
    eqCovM (2 ^ p) acc W = true := by
  induction W generalizing acc with
  | nil =>
    rw [eqCovM, Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro q
    rw [Nat.zero_testBit]
    cases hq : acc.testBit q
    · rfl
    · obtain ⟨_, hw, _⟩ := hacc q hq; cases hw
  | cons w ws ih =>
    unfold eqCovM
    cases hb : Nat.beq (Nat.land w (2 ^ p)) 0 with
    | true =>
      dsimp only
      have hwp : w.testBit p = false := testBit_of_land_pow2_eq_zero p w (Nat.eq_of_beq_eq_true hb)
      cases hz : Nat.beq (Nat.land (Nat.xor w FULL) acc) 0 with
      | true => rfl
      | false =>
        dsimp only
        have hlt' : Nat.land (Nat.xor w FULL) acc < 2 ^ N_bits := by
          rw [land_comm]; exact lt_pow_and hacc_lt
        apply ih (Nat.land (Nat.xor w FULL) acc) hlt'
        intro q hq
        rw [testBit_land, Bool.and_eq_true] at hq
        have hqN : q < N_bits := by
          by_contra hge
          have h0 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hacc_lt (Nat.pow_le_pow_right (by norm_num) (show N_bits ≤ q by omega)))
          rw [h0] at hq; exact Bool.noConfusion hq.2
        rw [testBit_not hqN, Bool.not_eq_true'] at hq
        obtain ⟨w', hw', hne⟩ := hacc q hq.2
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact (hne (hwp.trans hq.1.symm)).elim
        · exact ⟨w', hw', hne⟩
    | false =>
      dsimp only
      have hwp : w.testBit p = true := testBit_of_land_pow2_ne_zero p w (beq_false_iff.mp hb)
      cases hz : Nat.beq (Nat.land w acc) 0 with
      | true => rfl
      | false =>
        dsimp only
        have hlt' : Nat.land w acc < 2 ^ N_bits := by
          rw [land_comm]; exact lt_pow_and hacc_lt
        apply ih (Nat.land w acc) hlt'
        intro q hq
        rw [testBit_land, Bool.and_eq_true] at hq
        obtain ⟨w', hw', hne⟩ := hacc q hq.2
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact (hne (hwp.trans hq.1.symm)).elim
        · exact ⟨w', hw', hne⟩

lemma allCov_of_sep (allowNot : Bool) (W : List ℕ)
    (hsep : ∀ p < N_bits, ∀ q < N_bits, target.testBit p = true → target.testBit q = false →
      if allowNot then ∃ w ∈ W, w.testBit p ≠ w.testBit q
      else ∃ w ∈ W, w.testBit p = true ∧ w.testBit q = false) :
    allCov allowNot W = true := by
  have hm_spec : ∀ m ∈ onBitMasks, ∃ p : Fin N_bits, m = 2 ^ p.val ∧ target.testBit p.val = true := by decide
  have hoff_lt : offMask < 2 ^ N_bits := by decide
  have hoff_bit : ∀ q, offMask.testBit q = true → q < N_bits ∧ target.testBit q = false := by
    intro q hqo
    have hqN : q < N_bits := by
      by_contra hge
      have h0 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hoff_lt (Nat.pow_le_pow_right (by norm_num) (show N_bits ≤ q by omega)))
      rw [h0] at hqo; exact Bool.noConfusion hqo
    have hqt : target.testBit q = false := by
      have : offMask = Nat.xor target FULL := rfl
      rw [this, testBit_not hqN, Bool.not_eq_true'] at hqo; exact hqo
    exact ⟨hqN, hqt⟩
  unfold allCov
  suffices ∀ ms : List ℕ, (∀ m ∈ ms, ∃ p : Fin N_bits, m = 2 ^ p.val ∧ target.testBit p.val = true) →
      allCovAux allowNot W ms = true from this onBitMasks hm_spec
  intro ms hms
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    unfold allCovAux
    obtain ⟨p, rfl, hpt⟩ := hms m (List.mem_cons_self ..)
    have hcur : Bool.rec (monoCovM (2 ^ p.val) offMask W) (eqCovM (2 ^ p.val) offMask W) allowNot = true := by
      cases allowNot with
      | false =>
        apply monoCovM_of_sep p.val W offMask
        intro q hqo
        obtain ⟨hqN, hqt⟩ := hoff_bit q hqo
        simpa using hsep p.val p.isLt q hqN hpt hqt
      | true =>
        apply eqCovM_of_sep p.val W offMask hoff_lt
        intro q hqo
        obtain ⟨hqN, hqt⟩ := hoff_bit q hqo
        simpa using hsep p.val p.isLt q hqN hpt hqt
    rw [hcur]
    exact ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))

def memNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => Bool.rec (memNat x ys) true (Nat.beq y x)

lemma memNat_iff (x : ℕ) (W : List ℕ) : memNat x W = true ↔ x ∈ W := by
  induction W with
  | nil => simp [memNat]
  | cons y ys ih =>
    unfold memNat; cases hb : Nat.beq y x
    · simp only [List.mem_cons, ih]
      exact ⟨Or.inr, fun h => h.resolve_left (fun e => by rw [e, Nat.beq_refl] at hb; exact Bool.noConfusion hb)⟩
    · simp [Nat.eq_of_beq_eq_true hb]

def eraseNat (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => Bool.rec (y :: eraseNat x ys) ys (Nat.beq y x)

lemma eraseNat_eq (x : ℕ) (W : List ℕ) : eraseNat x W = W.erase x := by
  induction W with
  | nil => rfl
  | cons y ys ih =>
    unfold eraseNat; cases hb : Nat.beq y x
    · have hne : (y == x) = false := hb
      rw [List.erase_cons, hne, ih]; rfl
    · have heq : (y == x) = true := hb
      rw [List.erase_cons, heq]; rfl

def tryNotAux (f : ℕ → Bool) : List ℕ → Bool
  | [] => false
  | a :: rest => Bool.rec (tryNotAux f rest) true (f a)

lemma tryNotAux_of_mem (f : ℕ → Bool) (W : List ℕ) (a : ℕ) (ha : a ∈ W) (hf : f a = true) :
    tryNotAux f W = true := by
  induction W with
  | nil => cases ha
  | cons y ys ih =>
    unfold tryNotAux
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hf]
    · cases f y <;> [exact ih ha; rfl]

def tryPairsAux (f : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => false
  | a :: rest => Bool.rec (tryPairsAux f rest) true (tryNotAux (f a) rest)

lemma tryPairsAux_or (f : ℕ → ℕ → Bool) (W : List ℕ) (a x : ℕ)
    (ha : a ∈ W) (hx : x ∈ W) (hax : a ≠ x) (h1 : f a x = true) (h2 : f x a = true) :
    tryPairsAux f W = true := by
  induction W with
  | nil => cases ha
  | cons y ys ih =>
    unfold tryPairsAux
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hx with hxy | hx'
      · exact absurd hxy.symm hax
      · rw [tryNotAux_of_mem (f a) ys x hx' h1]
    · rcases List.mem_cons.mp hx with rfl | hx'
      · rw [tryNotAux_of_mem (f x) ys a ha' h2]
      · cases tryNotAux (f y) ys <;> [exact ih ha' hx'; rfl]

def tryBinOpCore (go : List ℕ → ℕ → ℕ → ℕ → Bool) (b len : ℕ) (W : List ℕ) (a x k c : ℕ) : Bool :=
  match isProper c with
  | false => false
  | true =>
    match memNat c W with
    | true => false
    | false =>
      match go (c :: eraseNat x (eraseNat a W)) (Nat.pred len) c k with
      | true => true
      | false =>
        match Nat.ble len b with
        | false => false
        | true =>
          match go (c :: eraseNat a W) len c k with
          | true => true
          | false =>
            match go (c :: eraseNat x W) len c k with
            | true => true
            | false =>
              match Nat.ble (Nat.succ len) b with
              | true => go (c :: W) (Nat.succ len) c k
              | false => false

def tryBinOp2 (go : List ℕ → ℕ → ℕ → ℕ → Bool) (b len : ℕ) (W : List ℕ) (lo lk a x : ℕ) (isOr : Bool) (c : ℕ) : Bool :=
  let k := keyBin a x isOr
  match Nat.beq a lo with
  | true => tryBinOpCore go b len W a x k c
  | false =>
    match Nat.beq x lo with
    | true => tryBinOpCore go b len W a x k c
    | false =>
      match Nat.ble k lk with
      | true => false
      | false => tryBinOpCore go b len W a x k c

def searchFuel : ℕ → ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → Bool
  | 0, b, _, W, len, _, _ =>
    match Nat.ble (Nat.add b 2) len with
    | true => false
    | false => memNat target W
  | fuel + 1, b, u, W, len, lo, lk =>
    match Nat.ble (Nat.add b 2) len with
    | true => false
    | false =>
      match memNat target W with
      | true => true
      | false =>
        match b with
        | 0 =>
          match u with
          | 0 => false
          | _ + 1 =>
            match W with
            | [a] => Nat.beq (Nat.xor a FULL) target
            | _ => false
        | b' + 1 =>
          match u with
          | 0 =>
            match len with
            | 2 =>
              match W with
              | [a, x] => Bool.rec (Nat.beq (Nat.lor a x) target) true (Nat.beq (Nat.land a x) target)
              | _ => false
            | 1 => false
            | _ =>
              match allCov false W with
              | false => false
              | true =>
                let go := searchFuel fuel b' 0
                tryPairsAux (fun a x =>
                  Bool.rec
                    (tryBinOp2 go b len W lo lk a x true (Nat.lor a x))
                    true
                    (tryBinOp2 go b len W lo lk a x false (Nat.land a x))) W
          | u' + 1 =>
            match allCov true W with
            | false => false
            | true =>
              let tryNot :=
                tryNotAux (fun a =>
                  let k := keyNot a
                  let runNot :=
                    let c := Nat.xor a FULL
                    match isProper c with
                    | false => false
                    | true =>
                      match memNat c W with
                      | true => false
                      | false =>
                        match searchFuel fuel b u' (c :: eraseNat a W) len c k with
                        | true => true
                        | false =>
                          match Nat.ble len b with
                          | true => searchFuel fuel b u' (c :: W) (Nat.succ len) c k
                          | false => false
                  match Nat.beq a lo with
                  | true => runNot
                  | false =>
                    match Nat.ble k lk with
                    | true => false
                    | false => runNot) W
              match tryNot with
              | true => true
              | false =>
                let go := searchFuel fuel b' (u' + 1)
                tryPairsAux (fun a x =>
                  Bool.rec
                    (tryBinOp2 go b len W lo lk a x true (Nat.lor a x))
                    true
                    (tryBinOp2 go b len W lo lk a x false (Nat.land a x))) W

def search (b u : ℕ) (W : List ℕ) (lo lk : ℕ) : Bool :=
  searchFuel (Nat.add b u) b u W W.length lo lk

lemma toFinset_eraseNat (a : ℕ) (W : List ℕ) (hnd : W.Nodup) :
    (eraseNat a W).toFinset = W.toFinset.erase a := by
  rw [eraseNat_eq]; ext z; simp [hnd.mem_erase_iff]

lemma len_eraseNat_of_mem {a : ℕ} {W : List ℕ} (ha : a ∈ W) :
    (eraseNat a W).length = W.length - 1 := by
  rw [eraseNat_eq, List.length_erase_of_mem ha]

lemma search_complete {b u lo lk : ℕ} {S : Finset ℕ} (hR : Reach b u S lo lk) :
    ∀ W : List ℕ, W.Nodup → W.toFinset = S → (∀ w ∈ W, w < 2 ^ N_bits) → search b u W lo lk = true := by
  induction hR with
  | @done lo lk =>
    intro W hnd hW _
    have hlen : W.length = 1 := by rw [← List.toFinset_card_of_nodup hnd, hW]; simp
    have hmem : memNat target W = true := (memNat_iff target W).mpr (by rw [← List.mem_toFinset, hW]; simp)
    simp [search, searchFuel, hlen, hmem]
  | @step_not b u S lo lk a da ha hord hpc hnc hnext ih =>
    intro W hnd hW hlt
    have haW : a ∈ W := by rwa [← List.mem_toFinset, hW]
    have hcard : W.length ≤ b + 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hW]; exact reach_card_le (Reach.step_not a da ha hord hpc hnc hnext)
    have hble : Nat.ble (Nat.add b 2) W.length = false := ble_false_iff.mpr (show W.length < b + 2 by omega)
    change searchFuel ((b + u) + 1) b (u + 1) W W.length lo lk = true
    unfold searchFuel
    rw [hble]; dsimp only
    cases htg : memNat target W
    swap; · rfl
    have htg_ne : target ∉ S := fun hm => by
      have := (memNat_iff target W).mpr (by rwa [← List.mem_toFinset, hW])
      rw [this] at htg; exact Bool.noConfusion htg
    cases b with
    | zero =>
      dsimp only
      have hlen1 : W.length = 1 := by
        have hpos : 0 < W.length := by rw [← List.toFinset_card_of_nodup hnd, hW]; exact Finset.card_pos.mpr ⟨a, ha⟩
        omega
      match W with
      | [w0] =>
        have hSlt : ∀ w ∈ S, w < 2 ^ N_bits := fun w hw => hlt w (by rwa [← List.mem_toFinset, hW])
        obtain ⟨w, hw, htw⟩ := reach_b0 hSlt (Reach.step_not a da ha hord hpc hnc hnext)
        have hww0 : w = w0 := by
          have : w ∈ [w0] := by rw [← List.mem_toFinset, hW]; exact hw
          simpa using this
        subst hww0
        rcases htw with htw | ⟨_, htw⟩
        · exact (htg_ne (htw ▸ hw)).elim
        · simp [htw, Nat.beq_refl]
      | [] => simp at hlen1
      | _ :: _ :: _ => simp at hlen1
    | succ b' =>
      dsimp only
      have hcov : allCov true W = true := allCov_of_sep true W (fun p hpN q hqN hp hq => by
        have hs := reach_sep (Reach.step_not a da ha hord hpc hnc hnext) p q hpN hqN hp hq
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hs
        obtain ⟨w, hw, hne⟩ := hs
        exact ⟨w, by rwa [← List.mem_toFinset, hW], hne⟩)
      rw [hcov]; dsimp only
      have htryNot : tryNotAux (fun a' =>
          let k := keyNot a'
          let runNot :=
            let c := Nat.xor a' FULL
            match isProper c with
            | false => false
            | true =>
              match memNat c W with
              | true => false
              | false =>
                match searchFuel (b' + 1 + u) (b' + 1) u (c :: eraseNat a' W) W.length c k with
                | true => true
                | false =>
                  match Nat.ble W.length (b' + 1) with
                  | true => searchFuel (b' + 1 + u) (b' + 1) u (c :: W) (Nat.succ W.length) c k
                  | false => false
          match Nat.beq a' lo with
          | true => runNot
          | false =>
            match Nat.ble k lk with
            | true => false
            | false => runNot) W = true := by
        apply tryNotAux_of_mem _ W a haW
        have hncW : memNat (Nat.xor a FULL) W = false := by
          apply Bool.eq_false_iff.mpr; intro hm
          exact hnc (by rw [← hW, List.mem_toFinset]; exact (memNat_iff _ _).mp hm)
        have hrun : (match isProper (Nat.xor a FULL) with
            | false => false
            | true =>
              match memNat (Nat.xor a FULL) W with
              | true => false
              | false =>
                match searchFuel (b' + 1 + u) (b' + 1) u (Nat.xor a FULL :: eraseNat a W) W.length (Nat.xor a FULL) (keyNot a) with
                | true => true
                | false =>
                  match Nat.ble W.length (b' + 1) with
                  | true => searchFuel (b' + 1 + u) (b' + 1) u (Nat.xor a FULL :: W) (Nat.succ W.length) (Nat.xor a FULL) (keyNot a)
                  | false => false) = true := by
          rw [hpc, hncW]; dsimp only
          cases da
          · have hcard' : (insert (Nat.xor a FULL) S).card ≤ (b' + 1) + 1 := by
              simpa [drop1] using reach_card_le hnext
            have hlen_le : W.length ≤ b' + 1 := by
              rw [Finset.card_insert_of_notMem hnc, ← hW, List.toFinset_card_of_nodup hnd] at hcard'; omega
            have hrec : searchFuel (b' + 1 + u) (b' + 1) u (Nat.xor a FULL :: W) (Nat.succ W.length) (Nat.xor a FULL) (keyNot a) = true :=
              ih (Nat.xor a FULL :: W) (List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact hm), hnd⟩)
                (by simp [List.toFinset_cons, hW, drop1]) (fun w hw => by
                  rcases List.mem_cons.mp hw with rfl | hw
                  · exact lt_pow_not (hlt a haW)
                  · exact hlt w hw)
            cases h1 : searchFuel (b' + 1 + u) (b' + 1) u (Nat.xor a FULL :: eraseNat a W) W.length (Nat.xor a FULL) (keyNot a)
            · rw [ble_true_iff.mpr hlen_le]; exact hrec
            · rfl
          · have hnd' : (Nat.xor a FULL :: eraseNat a W).Nodup := by
              rw [eraseNat_eq]
              exact List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact List.mem_of_mem_erase hm), hnd.erase a⟩
            have hW' : (Nat.xor a FULL :: eraseNat a W).toFinset = insert (Nat.xor a FULL) (drop1 true a S) := by
              simp [List.toFinset_cons, toFinset_eraseNat a W hnd, hW, drop1]
            have hlt' : ∀ w ∈ Nat.xor a FULL :: eraseNat a W, w < 2 ^ N_bits := fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact lt_pow_not (hlt a haW)
              · rw [eraseNat_eq] at hw; exact hlt w (List.mem_of_mem_erase hw)
            have hlen_eq : (Nat.xor a FULL :: eraseNat a W).length = W.length := by
              have hpos : 0 < W.length := List.length_pos_of_mem haW
              simp [len_eraseNat_of_mem haW]; omega
            have hrec : searchFuel (b' + 1 + u) (b' + 1) u (Nat.xor a FULL :: eraseNat a W) W.length (Nat.xor a FULL) (keyNot a) = true := by
              rw [← hlen_eq]; exact ih _ hnd' hW' hlt'
            rw [hrec]
        dsimp only
        rcases hord with rfl | hlt_k
        · rw [Nat.beq_refl]; exact hrun
        · cases Nat.beq a lo
          · rw [ble_false_iff.mpr hlt_k]; exact hrun
          · exact hrun
      rw [htryNot]
  | @step_bin b u S lo lk a x isOr da db ha hx hax hord hpc hnc hnext ih =>
    intro W hnd hW hlt
    have haW : a ∈ W := by rwa [← List.mem_toFinset, hW]
    have hxW : x ∈ W := by rwa [← List.mem_toFinset, hW]
    have hcard : W.length ≤ b + 2 := by
      rw [← List.toFinset_card_of_nodup hnd, hW]
      exact reach_card_le (Reach.step_bin a x isOr da db ha hx hax hord hpc hnc hnext)
    have hble : Nat.ble (Nat.add (b + 1) 2) W.length = false := ble_false_iff.mpr (show W.length < b + 1 + 2 by omega)
    have hfuel : Nat.add (b + 1) u = (Nat.add b u) + 1 := show b + 1 + u = (b + u) + 1 by omega
    unfold search; rw [hfuel]
    unfold searchFuel
    rw [hble]; dsimp only
    cases htg : memNat target W
    swap; · rfl
    have htg_ne : target ∉ S := fun hm => by
      have := (memNat_iff target W).mpr (by rwa [← List.mem_toFinset, hW])
      rw [this] at htg; exact Bool.noConfusion htg
    set c := if isOr then Nat.lor a x else Nat.land a x
    have hlt_c : c < 2 ^ N_bits := by
      have ha_lt := hlt a haW
      have hx_lt := hlt x hxW
      cases isOr
      · exact lt_pow_and ha_lt
      · exact lt_pow_or ha_lt hx_lt
    have hpairs : tryPairsAux (fun u1 u2 =>
        Bool.rec
          (tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 true (Nat.lor u1 u2))
          true
          (tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 false (Nat.land u1 u2))) W = true := by
      have mk_branch : ∀ (u1 u2 : ℕ) (d1 d2 : Bool),
          u1 ∈ W → u2 ∈ W → u1 ≠ u2 →
          (if isOr then Nat.lor u1 u2 else Nat.land u1 u2) = c →
          keyBin u1 u2 isOr = keyBin a x isOr →
          (u1 = lo ∨ u2 = lo) ∨ lk < keyBin u1 u2 isOr →
          drop2 d1 d2 u1 u2 S = drop2 da db a x S →
          Bool.rec
            (tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 true (Nat.lor u1 u2))
            true
            (tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 false (Nat.land u1 u2)) = true := by
        intro u1 u2 d1 d2 hu1 hu2 hu12 hce hke hord' hde
        have hncW : memNat c W = false := by
          apply Bool.eq_false_iff.mpr; intro hm
          exact hnc (by rw [← hW, List.mem_toFinset]; exact (memNat_iff _ _).mp hm)
        have hcore : tryBinOpCore (searchFuel (Nat.add b u) b u) (b + 1) W.length W u1 u2 (keyBin u1 u2 isOr) c = true := by
          unfold tryBinOpCore
          rw [hpc, hncW]; dsimp only
          have hcard_next : (insert c (drop2 d1 d2 u1 u2 S)).card ≤ b + 1 := by
            rw [hde]; exact reach_card_le hnext
          cases d1 <;> cases d2
          · have hlen_le : W.length + 1 ≤ b + 1 := by
              simp only [drop2, drop1, Bool.false_eq_true, ↓reduceIte] at hcard_next
              rw [Finset.card_insert_of_notMem hnc, ← hW, List.toFinset_card_of_nodup hnd] at hcard_next; omega
            have hrec : searchFuel (Nat.add b u) b u (c :: W) (Nat.succ W.length) c (keyBin a x isOr) = true :=
              ih (c :: W) (List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact hm), hnd⟩)
                (by rw [← hde]; simp [List.toFinset_cons, hW, drop2, drop1])
                (fun w hw => (List.mem_cons.mp hw).elim (fun e => e ▸ hlt_c) (hlt w))
            rw [hke, ble_true_iff.mpr (show W.length ≤ b + 1 by omega), ble_true_iff.mpr hlen_le, hrec]
            cases searchFuel (Nat.add b u) b u (c :: eraseNat u2 (eraseNat u1 W)) (Nat.pred W.length) c (keyBin a x isOr)
            · cases searchFuel (Nat.add b u) b u (c :: eraseNat u1 W) W.length c (keyBin a x isOr)
              · cases searchFuel (Nat.add b u) b u (c :: eraseNat u2 W) W.length c (keyBin a x isOr) <;> rfl
              · rfl
            · rfl
          · have hnd' : (c :: eraseNat u2 W).Nodup := by
              rw [eraseNat_eq]
              exact List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact List.mem_of_mem_erase hm), hnd.erase u2⟩
            have hW' : (c :: eraseNat u2 W).toFinset = insert c (drop2 false true u1 u2 S) := by
              simp [List.toFinset_cons, toFinset_eraseNat u2 W hnd, hW, drop2, drop1]
            have hlen_le : W.length ≤ b + 1 := by
              have := card_le_drop1_succ true u2 S
              simp only [drop2, drop1, Bool.false_eq_true, ↓reduceIte] at hcard_next
              rw [Finset.card_insert_of_notMem (fun hm => hnc (Finset.mem_erase.mp hm).2)] at hcard_next
              rw [← List.toFinset_card_of_nodup hnd, hW]; simp only [drop1, ↓reduceIte] at this; omega
            have hlen_eq : (c :: eraseNat u2 W).length = W.length := by
              have hpos : 0 < W.length := List.length_pos_of_mem hu2
              simp [len_eraseNat_of_mem hu2]; omega
            have hrec : searchFuel (Nat.add b u) b u (c :: eraseNat u2 W) W.length c (keyBin a x isOr) = true := by
              rw [← hlen_eq]
              exact ih (c :: eraseNat u2 W) hnd' (hde ▸ hW') (fun w hw => by
                rcases List.mem_cons.mp hw with rfl | hw
                · exact hlt_c
                · rw [eraseNat_eq] at hw; exact hlt w (List.mem_of_mem_erase hw))
            rw [hke, ble_true_iff.mpr hlen_le, hrec]
            cases searchFuel (Nat.add b u) b u (c :: eraseNat u2 (eraseNat u1 W)) (Nat.pred W.length) c (keyBin a x isOr)
            · cases searchFuel (Nat.add b u) b u (c :: eraseNat u1 W) W.length c (keyBin a x isOr) <;> rfl
            · rfl
          · have hnd' : (c :: eraseNat u1 W).Nodup := by
              rw [eraseNat_eq]
              exact List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact List.mem_of_mem_erase hm), hnd.erase u1⟩
            have hW' : (c :: eraseNat u1 W).toFinset = insert c (drop2 true false u1 u2 S) := by
              simp [List.toFinset_cons, toFinset_eraseNat u1 W hnd, hW, drop2, drop1]
            have hlen_le : W.length ≤ b + 1 := by
              have := card_le_drop1_succ true u1 S
              simp only [drop2, drop1, Bool.false_eq_true, ↓reduceIte] at hcard_next
              rw [Finset.card_insert_of_notMem (fun hm => hnc (Finset.mem_erase.mp hm).2)] at hcard_next
              rw [← List.toFinset_card_of_nodup hnd, hW]; simp only [drop1, ↓reduceIte] at this; omega
            have hlen_eq : (c :: eraseNat u1 W).length = W.length := by
              have hpos : 0 < W.length := List.length_pos_of_mem hu1
              simp [len_eraseNat_of_mem hu1]; omega
            have hrec : searchFuel (Nat.add b u) b u (c :: eraseNat u1 W) W.length c (keyBin a x isOr) = true := by
              rw [← hlen_eq]
              exact ih (c :: eraseNat u1 W) hnd' (hde ▸ hW') (fun w hw => by
                rcases List.mem_cons.mp hw with rfl | hw
                · exact hlt_c
                · rw [eraseNat_eq] at hw; exact hlt w (List.mem_of_mem_erase hw))
            rw [hke, ble_true_iff.mpr hlen_le, hrec]
            cases searchFuel (Nat.add b u) b u (c :: eraseNat u2 (eraseNat u1 W)) (Nat.pred W.length) c (keyBin a x isOr) <;> rfl
          · have hnd1 : (eraseNat u1 W).Nodup := by rw [eraseNat_eq]; exact hnd.erase u1
            have hu2' : u2 ∈ eraseNat u1 W := by rw [eraseNat_eq]; exact (hnd.mem_erase_iff).mpr ⟨hu12.symm, hu2⟩
            have hnd' : (c :: eraseNat u2 (eraseNat u1 W)).Nodup := by
              rw [eraseNat_eq, eraseNat_eq]
              exact List.nodup_cons.mpr ⟨fun hm => hnc (by rw [← hW, List.mem_toFinset]; exact List.mem_of_mem_erase (List.mem_of_mem_erase hm)), (hnd.erase u1).erase u2⟩
            have hW' : (c :: eraseNat u2 (eraseNat u1 W)).toFinset = insert c (drop2 true true u1 u2 S) := by
              simp [List.toFinset_cons, toFinset_eraseNat u2 _ hnd1, toFinset_eraseNat u1 W hnd, hW, drop2, drop1]
            have hlen_eq : (c :: eraseNat u2 (eraseNat u1 W)).length = Nat.pred W.length := by
              have hge2 : 2 ≤ W.length := by
                have h2c : ({u1, u2} : Finset ℕ).card = 2 := Finset.card_pair hu12
                have hsub2 : {u1, u2} ⊆ W.toFinset := by
                  intro z hz; simp at hz; rcases hz with rfl | rfl <;> simp [hu1, hu2]
                have := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup hnd] at this; omega
              simp [len_eraseNat_of_mem hu2', len_eraseNat_of_mem hu1]; omega
            have hrec : searchFuel (Nat.add b u) b u (c :: eraseNat u2 (eraseNat u1 W)) (Nat.pred W.length) c (keyBin a x isOr) = true := by
              rw [← hlen_eq]
              exact ih (c :: eraseNat u2 (eraseNat u1 W)) hnd' (hde ▸ hW') (fun w hw => by
                rcases List.mem_cons.mp hw with rfl | hw
                · exact hlt_c
                · rw [eraseNat_eq, eraseNat_eq] at hw; exact hlt w (List.mem_of_mem_erase (List.mem_of_mem_erase hw)))
            rw [hke, hrec]
        have htry : tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 isOr c = true := by
          unfold tryBinOp2; dsimp only
          rcases hord' with (h1 | h2) | hlt_k
          · have hb : Nat.beq u1 lo = true := h1 ▸ Nat.beq_refl u1
            rw [hb]; exact hcore
          · have hb : Nat.beq u2 lo = true := h2 ▸ Nat.beq_refl u2
            cases Nat.beq u1 lo
            · rw [hb]; exact hcore
            · exact hcore
          · cases Nat.beq u1 lo
            · cases Nat.beq u2 lo
              · rw [ble_false_iff.mpr hlt_k]; exact hcore
              · exact hcore
            · exact hcore
        cases isOr
        · simp only [Bool.false_eq_true, ↓reduceIte] at hce
          rw [hce, htry]
        · simp only [↓reduceIte] at hce
          rw [hce, htry]
          cases tryBinOp2 (searchFuel (Nat.add b u) b u) (b + 1) W.length W lo lk u1 u2 false (Nat.land u1 u2) <;> rfl
      have hkey_comm : keyBin x a isOr = keyBin a x isOr := by
        simp [keyBin_eq, min_comm, max_comm]
      have hdrop_comm : drop2 db da x a S = drop2 da db a x S := by
        ext z; cases da <;> cases db <;> simp [drop2, drop1, and_left_comm]
      exact tryPairsAux_or _ W a x haW hxW hax
        (mk_branch a x da db haW hxW hax rfl rfl hord rfl)
        (mk_branch x a db da hxW haW hax.symm (by cases isOr <;> [exact land_comm x a; exact lor_comm x a]) hkey_comm
          (by
            rcases hord with (h | h) | h
            · exact .inl (.inr h)
            · exact .inl (.inl h)
            · exact .inr (hkey_comm.symm ▸ h))
          hdrop_comm)
    cases u with
    | zero =>
      dsimp only
      have hcov0 : allCov false W = true := allCov_of_sep false W (fun p hpN q hqN hp hq => by
        have hs := reach_sep (Reach.step_bin a x isOr da db ha hx hax hord hpc hnc hnext) p q hpN hqN hp hq
        simp only [↓reduceIte] at hs
        obtain ⟨w, hw, hwp, hwq⟩ := hs
        exact ⟨w, by rwa [← List.mem_toFinset, hW], hwp, hwq⟩)
      rcases W with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, rest⟩⟩⟩
      · cases haW
      · exfalso
        have hS1 : S = {w0} := by rw [← hW]; ext z; simp
        have := reach_u0_card1 (hS1 ▸ Reach.step_bin a x isOr da db ha hx hax hord hpc hnc hnext)
        exact htg_ne (by rw [hS1, this]; simp)
      · dsimp only
        have hS2 : S = {w0, w1} := by rw [← hW]; ext z; simp
        have hres := reach_u0_card2 (hS2 ▸ Reach.step_bin a x isOr da db ha hx hax hord hpc hnc hnext)
        rcases hres with heq | heq | heq | heq
        · exact (htg_ne (by rw [hS2, heq]; simp)).elim
        · exact (htg_ne (by rw [hS2, heq]; simp)).elim
        · simp [heq, Nat.beq_refl]
        · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, heq, Nat.beq_refl]; cases Nat.beq (Nat.land w0 w1) (Nat.lor w0 w1) <;> rfl
      · dsimp only; rw [hcov0]; exact hpairs
    | succ u' =>
      dsimp only
      have hcov1 : allCov true W = true := allCov_of_sep true W (fun p hpN q hqN hp hq => by
        have hs := reach_sep (Reach.step_bin a x isOr da db ha hx hax hord hpc hnc hnext) p q hpN hqN hp hq
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hs
        obtain ⟨w, hw, hne⟩ := hs
        exact ⟨w, by rwa [← List.mem_toFinset, hW], hne⟩)
      rw [hcov1]; dsimp only
      cases tryNotAux (fun a' =>
          let k := keyNot a'
          let runNot :=
            let c := Nat.xor a' FULL
            match isProper c with
            | false => false
            | true =>
              match memNat c W with
              | true => false
              | false =>
                match searchFuel (Nat.add b (u' + 1)) (b + 1) u' (c :: eraseNat a' W) W.length c k with
                | true => true
                | false =>
                  match Nat.ble W.length (b + 1) with
                  | true => searchFuel (Nat.add b (u' + 1)) (b + 1) u' (c :: W) (Nat.succ W.length) c k
                  | false => false
          match Nat.beq a' lo with
          | true => runNot
          | false =>
            match Nat.ble k lk with
            | true => false
            | false => runNot) W
      · exact hpairs
      · rfl

def validStarts (b u : ℕ) : List (List ℕ) :=
  inTTs.sublists.filter fun W => Nat.ble W.length (b + 1) && allCov (!Nat.beq u 0) W

lemma lb_of_excl
    (hexcl : ∀ b u, b + u ≤ 6 → (allowAON = false → u = 0) →
      (validStarts b u).all (fun W => !search b u W 0 0) = true) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (4398 : ℕ).testBit (4 * u.val + v.val)) C) := by
  rintro ⟨C, hfit, hsz, hrep⟩
  have hfit3 : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg; exact hfit g hg
  have hgs : ∀ g ∈ C.gates, (if allowAON then g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
      else g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg; simpa [allowAON] using hfit g hg
  have hmem := circuit_target_mem C hfit3 hrep
  obtain ⟨ss0, hlen0, hcomp0⟩ := circuit_to_steps C.gates hgs inTTs hmem
  have hws0_lt : ∀ w ∈ (0 :: FULL :: inTTs), w < 2 ^ N_bits := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · decide
    · rcases List.mem_cons.mp hw with rfl | hw
      · decide
      · exact inTTs_lt w hw
  obtain ⟨ss, hss_le, hcomp, hmin, hfresh, hcanon⟩ := exists_min_canon (0 :: FULL :: inTTs) hws0_lt ss0 hcomp0
  have hprop0 : ∀ w ∈ (0 :: FULL :: inTTs), w = 0 ∨ w = FULL ∨ isProper w = true := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact .inl rfl
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact .inr (.inl rfl)
      · exact .inr (.inr (inTTs_proper w hw))
  obtain ⟨b, u, S, hbu, hu0, hS, hR⟩ := extract_canon (0 :: FULL :: inTTs) hws0_lt ss hcomp.1 hfresh hmin none hcanon hcomp.2 hprop0
  have hS_in : ∀ w ∈ S, w ∈ inTTs := by
    intro w hw
    obtain ⟨hm, hp⟩ := hS w hw
    have ⟨h0, h1⟩ := isProper_iff.mp hp
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (h0 rfl).elim
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact (h1 rfl).elim
      · exact hm
  let W := inTTs.filter fun w => decide (w ∈ S)
  have hWnd : W.Nodup := inTTs_nodup.filter _
  have hWfs : W.toFinset = S := by
    ext w; simp only [W, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hS_in w h, h⟩⟩
  have hWlt : ∀ w ∈ W, w < 2 ^ N_bits := fun w hw => inTTs_lt w (List.mem_filter.mp hw).1
  have hlen : W.length ≤ b + 1 := by
    rw [← List.toFinset_card_of_nodup hWnd, hWfs]; exact reach_card_le hR
  have hcov : allCov (!Nat.beq u 0) W = true := allCov_of_sep (!Nat.beq u 0) W (fun p hpN q hqN hp hq => by
    have hs := reach_sep hR p q hpN hqN hp hq
    cases u with
    | zero =>
      simp only [Nat.beq_refl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      obtain ⟨w, hw, hwp, hwq⟩ := hs; exact ⟨w, by rwa [← List.mem_toFinset, hWfs], hwp, hwq⟩
    | succ u' =>
      simp only [show Nat.beq (u' + 1) 0 = false from rfl, Bool.not_false, ↓reduceIte,
        Nat.add_eq_zero_iff, one_ne_zero, and_false] at hs ⊢
      obtain ⟨w, hw, hne⟩ := hs; exact ⟨w, by rwa [← List.mem_toFinset, hWfs], hne⟩)
  have hWmem : W ∈ validStarts b u := by
    simp only [validStarts, List.mem_filter, List.mem_sublists, Bool.and_eq_true, ble_true_iff]
    exact ⟨List.filter_sublist, hlen, hcov⟩
  have hfound := search_complete hR W hWnd hWfs hWlt
  have hsz' : C.gates.length ≤ 6 := hsz
  have hbad := List.all_eq_true.mp (hexcl b u (by omega) hu0) W hWmem
  have hf0 : search b u W 0 0 = true := hfound
  rw [hf0] at hbad; exact Bool.noConfusion hbad

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u0 :
    (List.range 7).all (fun b =>
      (validStarts b 0).all (fun W => !search b 0 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u1 :
    (List.range 6).all (fun b =>
      (validStarts b 1).all (fun W => !search b 1 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u2 :
    (List.range 5).all (fun b =>
      (validStarts b 2).all (fun W => !search b 2 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u3 :
    (List.range 4).all (fun b =>
      (validStarts b 3).all (fun W => !search b 3 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u4 :
    (List.range 3).all (fun b =>
      (validStarts b 4).all (fun W => !search b 4 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u5 :
    (List.range 2).all (fun b =>
      (validStarts b 5).all (fun W => !search b 5 W 0 0)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma excl_u6 :
    (List.range 1).all (fun b =>
      (validStarts b 6).all (fun W => !search b 6 W 0 0)) = true := by
  decide +kernel

theorem main_lb : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (4398 : ℕ).testBit (4 * u.val + v.val)) C) := by
  apply lb_of_excl
  intro b u hbu hu0
  have hu : u ≤ 6 := by omega
  interval_cases u
  · exact List.all_eq_true.mp excl_u0 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u1 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u2 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u3 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u4 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u5 b (List.mem_range.mpr (by omega))
  · exact List.all_eq_true.mp excl_u6 b (List.mem_range.mpr (by omega))


lemma mat_eq :
    (fun (u : Fin 4) (v : Fin 4) => (([14, 2, 1, 1] : List ℕ).getD u.val 0).testBit v.val) = (fun (u : Fin 4) (v : Fin 4) => (4398 : ℕ).testBit (4 * u.val + v.val)) := by
  funext u v
  fin_cases u <;> fin_cases v <;> decide

theorem main_lb_rows : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 2, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  rintro ⟨C, h1, h2, h3⟩
  exact main_lb ⟨C, h1, h2, by rwa [mat_eq] at h3⟩

end PEqualNP.Outside.L_meta_26298_aux

theorem PEqualNP.Outside.L_meta_26298 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 2, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) :=
  PEqualNP.Outside.L_meta_26298_aux.main_lb_rows
