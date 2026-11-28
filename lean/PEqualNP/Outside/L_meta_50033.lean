import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50033

open PEqualNP.CircuitLowerBounds

def mget (M : List ℕ) (i : ℕ) : ℕ := M.getD i 0

def opMask : GateOp → List ℕ → ℕ
  | GateOp.and, l => (l.foldr (· &&& ·) 31) % 32
  | GateOp.or, l => (l.foldr (· ||| ·) 0) % 32
  | GateOp.not, l => (31 ^^^ l.headD 0) % 32
  | _, _ => 0

def masks (gs : List Gate) (M : List ℕ) : List ℕ :=
  gs.foldl (fun M g => M ++ [opMask g.op (g.inputs.map (mget M))]) M

def notCnt (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

def vs (S : ℕ) : List ℕ := (List.range 32).filter fun a => S.testBit a

def isAndOr (S v : ℕ) : Bool :=
  v == 31 || v == 0 || (vs S).any fun a => v == (a &&& 31) % 32 || v == (a ||| 0) % 32 ||
    (vs S).any fun b => v == (a &&& (b &&& 31)) % 32 || v == (a ||| (b ||| 0)) % 32

def isNot (S v : ℕ) : Bool := (vs S).any fun a => v == (31 ^^^ a) % 32

def targ (v : ℕ) : Bool := v == 2 || v == 22 || v == 27

def miss (S : ℕ) : ℕ := (!S.testBit 2).toNat + (!S.testBit 22).toNat + (!S.testBit 27).toNat

def can : ℕ → ℕ → ℕ → Bool
  | 0, _, S => miss S == 0
  | g + 1, n, S => miss S == 0 || (decide (miss S ≤ g + 1) && (can g n S ||
      (List.range 32).any fun u => !S.testBit u && (!(g + 1 == miss S) || targ u) &&
        ((isAndOr S u && can g n (S ||| 2 ^ u)) ||
          (decide (0 < n) && isNot S u && can g (n - 1) (S ||| 2 ^ u)))))

def S0 : ℕ := 2 ^ 30 + 2 ^ 28 + 2 ^ 24 + 2 ^ 16 + 2 ^ 0 + 2 ^ 31

def M0 : List ℕ := [30, 28, 24, 16, 0, 31]

theorem can_S0 : can 5 2 S0 = false := by decide +kernel

theorem can_le (g n S : ℕ) (h : can g n S = true) : miss S ≤ g := by
  cases g with
  | zero => simp [can] at h; omega
  | succ g =>
    simp only [can, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, -⟩ <;> omega

theorem can_of_miss (g n S : ℕ) (h : miss S = 0) : can g n S = true := by
  cases g <;> simp [can, h]

theorem bit_ins (S v u : ℕ) : (S ||| 2 ^ v).testBit u = (S.testBit u || decide (v = u)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem miss_le (S v : ℕ) : miss S ≤ miss (S ||| 2 ^ v) + 1 := by
  unfold miss
  rw [bit_ins, bit_ins, bit_ins]
  cases S.testBit 2 <;> cases S.testBit 22 <;> cases S.testBit 27 <;>
    by_cases h2 : v = 2 <;> by_cases h22 : v = 22 <;> by_cases h27 : v = 27 <;> simp_all <;> omega

theorem miss_same (S v : ℕ) (hv : targ v = false) : miss (S ||| 2 ^ v) = miss S := by
  unfold miss
  simp only [targ, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hv
  rw [bit_ins, bit_ins, bit_ins]
  simp [hv.1.1, hv.1.2, hv.2]

theorem getD_mem (M : List ℕ) (i : ℕ) : M.getD i 0 ∈ M ∨ M.getD i 0 = 0 := by
  by_cases hi : i < M.length
  · left; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · right; rw [List.getD_eq_default _ _ (by omega)]

theorem opMask_lt (op : GateOp) (l : List ℕ) : opMask op l < 32 := by
  cases op <;> simp only [opMask] <;> omega

theorem mem_vs (S a : ℕ) : a ∈ vs S ↔ a < 32 ∧ S.testBit a = true := by
  simp [vs]

theorem sound (gs : List Gate) : ∀ (M : List ℕ) (S g n : ℕ),
    (∀ x ∈ gs, x.op = GateOp.and ∨ x.op = GateOp.or ∨ x.op = GateOp.not) →
    (∀ x ∈ gs, x.inputs.length ≤ 2) → gs.length ≤ g → notCnt gs ≤ n →
    (∀ m ∈ M, m < 32 ∧ S.testBit m = true) → S.testBit 0 = true →
    (2 ∈ masks gs M ∧ 22 ∈ masks gs M ∧ 27 ∈ masks gs M) → can g n S = true := by
  induction gs with
  | nil =>
    intro M S g n _ _ _ _ hM _ ht
    apply can_of_miss
    simp only [masks, List.foldl_nil] at ht
    have h2 := (hM _ ht.1).2
    have h22 := (hM _ ht.2.1).2
    have h27 := (hM _ ht.2.2).2
    simp [miss, h2, h22, h27]
  | cons x rest ih =>
    intro M S g n hop hlen hg hn hM h0 ht
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
    set l := x.inputs.map (mget M) with hl
    set v := opMask x.op l with hv
    have hlv : ∀ u ∈ l, u ∈ vs S := by
      intro u hu
      rw [hl, List.mem_map] at hu
      obtain ⟨i, -, rfl⟩ := hu
      rw [mem_vs]
      rcases getD_mem M i with h | h
      · exact hM _ h
      · simp only [mget, h]; exact ⟨by norm_num, h0⟩
    have hll : l.length ≤ 2 := by rw [hl, List.length_map]; exact hlen x (by simp)
    have hm : masks (x :: rest) M = masks rest (M ++ [v]) := rfl
    rw [hm] at ht
    have hop' := hop x (by simp)
    have hopr : ∀ y ∈ rest, y.op = GateOp.and ∨ y.op = GateOp.or ∨ y.op = GateOp.not :=
      fun y hy => hop y (by simp [hy])
    have hlenr : ∀ y ∈ rest, y.inputs.length ≤ 2 := fun y hy => hlen y (by simp [hy])
    have hgr : rest.length ≤ g := by simp at hg; omega
    have hnr : notCnt rest ≤ n := by
      simp only [notCnt, PEqualNP.NotBracket.notCount] at hn ⊢
      rw [List.filter_cons] at hn
      split at hn <;> (try simp at hn) <;> omega
    by_cases hvS : S.testBit v = true
    ·
      have hM' : ∀ m ∈ M ++ [v], m < 32 ∧ S.testBit m = true := by
        intro m hm'
        rcases List.mem_append.mp hm' with h | h
        · exact hM m h
        · simp at h; subst h; exact ⟨opMask_lt _ _, hvS⟩
      have hc := ih (M ++ [v]) S g n hopr hlenr hgr hnr hM' h0 ht
      have hle := can_le g n S hc
      have hle' : miss S ≤ g + 1 := by omega
      simp [can, hc, hle']
    · have hvS' : S.testBit v = false := by simpa using hvS
      have hM' : ∀ m ∈ M ++ [v], m < 32 ∧ (S ||| 2 ^ v).testBit m = true := by
        intro m hm'
        rw [bit_ins]
        rcases List.mem_append.mp hm' with h | h
        · exact ⟨(hM m h).1, by simp [(hM m h).2]⟩
        · simp at h; subst h; exact ⟨opMask_lt _ _, by simp⟩
      have h0' : (S ||| 2 ^ v).testBit 0 = true := by rw [bit_ins]; simp [h0]
      have hv32 : v < 32 := opMask_lt _ _

      have key : ∀ n', can g n' (S ||| 2 ^ v) = true →
          miss S ≤ g + 1 ∧ (¬ g + 1 = miss S ∨ targ v = true) := by
        intro n' hc
        have hle := can_le g n' _ hc
        have h1 := miss_le S v
        refine ⟨by omega, ?_⟩
        cases htv : targ v
        · rw [miss_same S v htv] at hle
          left; omega
        · right; rfl
      rcases hop' with hx | hx | hx
      ·
        have hnr' : notCnt rest ≤ n := hnr
        have hc := ih (M ++ [v]) (S ||| 2 ^ v) g n hopr hlenr hgr hnr' hM' h0' ht
        obtain ⟨k1, k2⟩ := key n hc
        have hA : isAndOr S v = true := by
          rw [hv, hx]
          match l, hlv, hll with
          | [], _, _ => simp [opMask, isAndOr]
          | [a], hlv, _ =>
            have ha := hlv a (by simp)
            simp only [isAndOr, opMask, List.foldr, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
            exact Or.inr ⟨a, ha, by simp⟩
          | [a, b], hlv, _ =>
            have ha := hlv a (by simp)
            have hb := hlv b (by simp)
            simp only [isAndOr, opMask, List.foldr, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
            exact Or.inr ⟨a, ha, Or.inr ⟨b, hb, by simp⟩⟩
          | _ :: _ :: _ :: _, _, h => simp at h
        simp only [can, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
          List.any_eq_true, List.mem_range]
        right
        refine ⟨k1, Or.inr ⟨v, hv32, ?_⟩⟩
        simp [hvS', hA, hc] <;> exact k2
      ·
        have hc := ih (M ++ [v]) (S ||| 2 ^ v) g n hopr hlenr hgr hnr hM' h0' ht
        obtain ⟨k1, k2⟩ := key n hc
        have hA : isAndOr S v = true := by
          rw [hv, hx]
          match l, hlv, hll with
          | [], _, _ => simp [opMask, isAndOr]
          | [a], hlv, _ =>
            have ha := hlv a (by simp)
            simp only [isAndOr, opMask, List.foldr, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
            exact Or.inr ⟨a, ha, by simp⟩
          | [a, b], hlv, _ =>
            have ha := hlv a (by simp)
            have hb := hlv b (by simp)
            simp only [isAndOr, opMask, List.foldr, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
            exact Or.inr ⟨a, ha, Or.inr ⟨b, hb, by simp⟩⟩
          | _ :: _ :: _ :: _, _, h => simp at h
        simp only [can, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
          List.any_eq_true, List.mem_range]
        right
        refine ⟨k1, Or.inr ⟨v, hv32, ?_⟩⟩
        simp [hvS', hA, hc] <;> exact k2
      ·
        have hn1 : 0 < n ∧ notCnt rest ≤ n - 1 := by
          simp only [notCnt, PEqualNP.NotBracket.notCount] at hn ⊢
          rw [List.filter_cons] at hn
          simp [hx] at hn
          omega
        have hc := ih (M ++ [v]) (S ||| 2 ^ v) g (n - 1) hopr hlenr hgr hn1.2 hM' h0' ht
        obtain ⟨k1, k2⟩ := key (n - 1) hc
        have hN : isNot S v = true := by
          rw [hv, hx]
          simp only [isNot, opMask, List.any_eq_true, beq_iff_eq]
          match l, hlv with
          | [], _ => exact ⟨0, (mem_vs S 0).mpr ⟨by norm_num, h0⟩, rfl⟩
          | a :: _, hlv => exact ⟨a, hlv a (by simp), rfl⟩
        simp only [can, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
          List.any_eq_true, List.mem_range]
        right
        refine ⟨k1, Or.inr ⟨v, hv32, ?_⟩⟩
        simp [hvS', hN, hc, hn1.1] <;> exact k2

theorem op_bits (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (l : List ℕ) (t : ℕ) (ht : t < 5) :
    op.eval (l.map fun m => m.testBit t) = (opMask op l).testBit t := by
  have hmod : ∀ x : ℕ, (x % 32).testBit t = x.testBit t := by
    intro x
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.testBit_mod_two_pow]
    simp [ht]
  rcases hop with rfl | rfl | rfl
  · simp only [GateOp.eval, opMask, hmod]
    induction l with
    | nil => simp; interval_cases t <;> rfl
    | cons a l ih => simp [Nat.testBit_and, ← ih]
  · simp only [GateOp.eval, opMask, hmod]
    induction l with
    | nil => simp
    | cons a l ih => simp [Nat.testBit_or, ← ih]
  · simp only [GateOp.eval, opMask, hmod, Nat.testBit_xor]
    have h31 : (31 : ℕ).testBit t = true := by interval_cases t <;> rfl
    cases l with
    | nil => simp [h31]
    | cons a l => simp [h31]

theorem wires_bits (gs : List Gate)
    (hop : ∀ x ∈ gs, x.op = GateOp.and ∨ x.op = GateOp.or ∨ x.op = GateOp.not)
    (t : ℕ) (ht : t < 5) : ∀ M : List ℕ,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (M.map fun m => m.testBit t) = (masks gs M).map fun m => m.testBit t := by
  induction gs with
  | nil => intro M; rfl
  | cons x rest ih =>
    intro M
    have hg : ∀ i, (M.map fun m => m.testBit t).getD i false = (mget M i).testBit t := by
      intro i
      simp only [mget, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases M[i]? <;> simp
    have hstep : (M.map fun m => m.testBit t) ++
        [x.op.eval (x.inputs.map fun i => (M.map fun m => m.testBit t).getD i false)] =
        (M ++ [opMask x.op (x.inputs.map (mget M))]).map fun m => m.testBit t := by
      rw [List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, hg]
      rw [← op_bits x.op (hop x (by simp)) _ t ht, List.map_map]
      rfl
    simp only [List.foldl_cons]
    rw [hstep]
    exact ih (fun y hy => hop y (by simp [hy])) _

theorem pin (c : ℕ) (hc : c = 2 ∨ c = 22 ∨ c = 27) : ∀ a < 32,
    (∀ t : Fin 5, a.testBit t.val = c.testBit t.val) → a = c := by
  rcases hc with rfl | rfl | rfl <;> decide

theorem inputs_eq : ∀ t : Fin 5,
    (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true] =
      M0.map fun m => m.testBit t.val := by decide

end PEqualNP.Outside.L_meta_50033

open PEqualNP.Outside.L_meta_50033 in
theorem PEqualNP.Outside.L_meta_50033 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (27 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, hw⟩
  have hop : ∀ x ∈ D.gates, x.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      x.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      x.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro x hx
    have := (hfan x hx).1
    simpa using this
  have hlen : ∀ x ∈ D.gates, x.inputs.length ≤ 2 := fun x hx => (hfan x hx).2
  have hbits : ∀ (t : Fin 5) (i : ℕ), (D.wires ((List.ofFn (fun j : Fin 4 => decide (j.val < t.val))) ++ [false, true])).getD i false =
      (mget (masks D.gates M0) i).testBit t.val := by
    intro t i
    rw [inputs_eq t]
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [wires_bits D.gates hop t.val t.isLt M0]
    simp only [mget, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (masks D.gates M0)[i]? <;> simp
  have hlt : ∀ m ∈ masks D.gates M0, m < 32 := by
    have gen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List ℕ),
        (∀ m ∈ M, m < 32) → ∀ m ∈ masks gs M, m < 32 := by
      intro gs
      induction gs with
      | nil => intro M hM; exact hM
      | cons x rest ih =>
        intro M hM
        apply ih
        intro m hm
        rcases List.mem_append.mp hm with h | h
        · exact hM m h
        · simp at h; subst h; exact opMask_lt _ _
    exact gen D.gates M0 (by decide)
  have hin : ∀ (c : ℕ) (i : ℕ), (c = 2 ∨ c = 22 ∨ c = 27) →
      (∀ t : Fin 5, (mget (masks D.gates M0) i).testBit t.val = c.testBit t.val) →
      c ∈ masks D.gates M0 := by
    intro c i hc h
    have hlt' : mget (masks D.gates M0) i < 32 := by
      rcases getD_mem (masks D.gates M0) i with h' | h'
      · exact hlt _ h'
      · simp only [mget, h']; norm_num
    have he := pin c hc _ hlt' h
    rcases getD_mem (masks D.gates M0) i with h' | h'
    · unfold mget at he; rw [he] at h'; exact h'
    · unfold mget at he; rw [he] at h'; rcases hc with rfl | rfl | rfl <;> simp at h'
  have h2 := hin 2 p.val (Or.inl rfl) (fun t => by rw [← hbits]; exact (hw t).1)
  have h22 := hin 22 q.val (Or.inr (Or.inl rfl)) (fun t => by rw [← hbits]; exact (hw t).2.1)
  have h27 := hin 27 r.val (Or.inr (Or.inr rfl)) (fun t => by rw [← hbits]; exact (hw t).2.2)
  have hc := sound D.gates M0 S0 5 2 hop hlen hsize hnot (by decide) (by decide) ⟨h2, h22, h27⟩
  rw [can_S0] at hc
  exact absurd hc (by decide)
