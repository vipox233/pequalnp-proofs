import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20876_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def isAONB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def isAOB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def mask (P : ℕ) : ℕ := 2 ^ P - 1

lemma testBit_mask {P k : ℕ} (hk : k < P) : (mask P).testBit k = true := by
  simp [mask, Nat.testBit_two_pow_sub_one, hk]

def gateCol (P : ℕ) (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => cs.getD a 0).foldr (· &&& ·) (mask P)
  | GateOp.or => (g.inputs.map fun a => cs.getD a 0).foldr (· ||| ·) 0
  | GateOp.not => mask P ^^^ (g.inputs.map fun a => cs.getD a 0).headD 0
  | _ => 0

def aonB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op && decide (g.inputs.length ≤ 2)

def aoB (C : Circuit) : Bool :=
  C.gates.all fun g => isAOB g.op && decide (g.inputs.length ≤ 2)

lemma fanInTwo_of_aonB (C : Circuit) (h : aonB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [isAONB, hop] at h1 ⊢

lemma monotone2_of_aoB (C : Circuit) (h : aoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [isAOB, hop] at h1 ⊢

lemma aonB_of_aoB (C : Circuit) (h : aoB C = true) : aonB C = true := by
  rw [aonB, List.all_eq_true]
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [isAOB, isAONB, hop] at h1 ⊢

def Agree (k : ℕ) (cs : List ℕ) (w : List Bool) : Prop :=
  cs.length = w.length ∧ ∀ j, (cs.getD j 0).testBit k = w.getD j false

lemma agree_snoc {k : ℕ} {cs : List ℕ} {w : List Bool} {c : ℕ} {v : Bool}
    (h : Agree k cs w) (hv : c.testBit k = v) : Agree k (cs ++ [c]) (w ++ [v]) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  rcases lt_trichotomy j cs.length with hj | hj | hj
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (h.1 ▸ hj)]
    exact h.2 j
  · subst hj
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ h.1.symm.le]
    simp [h.1, hv]
  · have hl := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma testBit_foldr_and {P k : ℕ} (hk : k < P) (l : List ℕ) :
    (l.foldr (· &&& ·) (mask P)).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [testBit_mask hk]
  | cons c l ih => simp [ih]

lemma testBit_foldr_or {k : ℕ} (l : List ℕ) :
    (l.foldr (· ||| ·) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

lemma gateCol_spec {P k : ℕ} (hk : k < P) {cs : List ℕ} {w : List Bool}
    (h : Agree k cs w) (g : Gate) (hg : isAONB g.op = true) :
    (gateCol P g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => cs.getD a 0).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_and hk, hmap]
  | or => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_or, hmap]
  | not =>
    simp only [gateCol, hop, GateOp.eval]
    rw [Nat.testBit_xor, testBit_mask hk, ← hmap]
    cases g.inputs <;> simp
  | mod m => rw [hop] at hg; simp [isAONB] at hg
  | maj => rw [hop] at hg; simp [isAONB] at hg

lemma agree_foldl {P k : ℕ} (hk : k < P) :
    ∀ (gs : List Gate) (cs : List ℕ) (w : List Bool), (∀ g ∈ gs, isAONB g.op = true) →
      Agree k cs w →
      Agree k (gs.foldl (fun cs g => cs ++ [gateCol P g cs]) cs)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro cs w _ h; exact h
  | cons g gs ih =>
    intro cs w hg h
    simp only [List.foldl_cons]
    apply ih _ _ (fun x hx => hg x (List.mem_cons_of_mem g hx))
    exact agree_snoc h (gateCol_spec hk h g (hg g (List.mem_cons_self ..)))

def rowCol (m : ℕ) (i : ℕ) : ℕ :=
  (mask m) <<< (i * m)

def colCol (n m : ℕ) (j : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i => acc ||| (1 <<< (i * m + j))) 0

def initCols (n m : ℕ) : List ℕ :=
  (List.range n).map (rowCol m) ++ (List.range m).map (colCol n m)

def pcols (n m : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol (n * m) g cs]) (initCols n m)

lemma testBit_rowCol {m i u v : ℕ} (hv : v < m) :
    (rowCol m i).testBit (u * m + v) = decide (i = u) := by
  simp only [rowCol, Nat.testBit_shiftLeft]
  by_cases h : i * m ≤ u * m + v
  · simp only [h, decide_true, Bool.true_and]
    by_cases hiu : i = u
    · subst hiu
      have hsub : i * m + v - i * m = v := by omega
      rw [hsub, testBit_mask hv]; simp
    · have hlt : i < u := by
        by_contra hge
        have : (u + 1) * m ≤ i * m := Nat.mul_le_mul_right m (by omega)
        have : u * m + m ≤ i * m := by linarith
        omega
      have hmul : (i + 1) * m ≤ u * m := Nat.mul_le_mul_right m (by omega)
      have hge : m ≤ u * m + v - i * m := by
        have : i * m + m ≤ u * m := by linarith
        omega
      have hmask : mask m < 2 ^ m := by
        simp only [mask]; exact Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos
      have : (mask m).testBit (u * m + v - i * m) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hmask (Nat.pow_le_pow_right (by omega) hge))
      rw [this]; simp [hiu]
  · simp only [h, decide_false, Bool.false_and]
    have hne : i ≠ u := by intro heq; subst heq; omega
    simp [hne]

lemma testBit_colCol_aux {m j u v : ℕ} (hj : j < m) (hv : v < m) :
    ∀ (k : ℕ) (acc : ℕ),
      ((List.range k).foldl (fun a i => a ||| (1 <<< (i * m + j))) acc).testBit (u * m + v) =
        (acc.testBit (u * m + v) || decide (u < k ∧ j = v)) := by
  intro k
  induction k with
  | zero => intro acc; simp
  | succ k ih =>
    intro acc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih]
    have hbit : (1 <<< (k * m + j)).testBit (u * m + v) = decide (k = u ∧ j = v) := by
      rw [Nat.testBit_shiftLeft]
      by_cases heq : k * m + j = u * m + v
      · have hku : k = u := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h1 | h2 <;> nlinarith
        have hjv : j = v := by nlinarith
        subst hku; subst hjv
        simp
      · by_cases hle : k * m + j ≤ u * m + v
        · have hpos : u * m + v - (k * m + j) ≠ 0 := by omega
          have h1 : (1 : ℕ).testBit (u * m + v - (k * m + j)) = false := by
            cases hsub : u * m + v - (k * m + j) with
            | zero => omega
            | succ d => simp [Nat.testBit_succ]
          rw [h1]
          have hnot : ¬(k = u ∧ j = v) := by rintro ⟨rfl, rfl⟩; exact heq rfl
          simp [hnot]
        · have hnot : ¬(k = u ∧ j = v) := by rintro ⟨rfl, rfl⟩; exact heq rfl
          simp [hle, hnot]
    rw [hbit]
    by_cases hjv : j = v
    · subst hjv
      by_cases hu : u < k
      · have : u < k + 1 := by omega
        simp [hu, this]
      · by_cases heq : u = k
        · subst heq; simp
        · have : ¬(u < k + 1) := by omega
          have hne : k ≠ u := by omega
          simp [hu, this, hne]
    · simp [hjv]

lemma testBit_colCol {n m j u v : ℕ} (hj : j < m) (hu : u < n) (hv : v < m) :
    (colCol n m j).testBit (u * m + v) = decide (j = v) := by
  unfold colCol
  rw [testBit_colCol_aux hj hv]
  simp [hu]

lemma agree_initCols {n m : ℕ} (u : Fin n) (v : Fin m) :
    Agree (u.val * m + v.val) (initCols n m) (oneEach u v) := by
  refine ⟨by simp [initCols, oneEach], fun j => ?_⟩
  simp only [initCols, oneEach]
  by_cases h1 : j < n
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_map, List.getElem?_range h1, List.getElem?_ofFn, dif_pos h1]
    simp only [Option.map_some, Option.getD_some, testBit_rowCol v.isLt]
    congr 1; exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  · by_cases h2 : j < n + m
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_map, List.length_range, List.length_ofFn]
      have hj2 : j - n < m := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_map, List.getElem?_range hj2, List.getElem?_ofFn, dif_pos hj2]
      simp only [Option.map_some, Option.getD_some, testBit_colCol hj2 u.isLt v.isLt]
      congr 1; exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      simp

def tcolAux (m : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, k => ((r &&& mask m) <<< (k * m)) ||| tcolAux m rs (k + 1)

def tcol (m : ℕ) (tab : List ℕ) : ℕ :=
  tcolAux m tab 0

lemma testBit_tcolAux {m : ℕ} :
    ∀ (rs : List ℕ) (k u v : ℕ), v < m →
      (tcolAux m rs k).testBit (u * m + v) =
        if k ≤ u then (rs.getD (u - k) 0).testBit v else false := by
  intro rs
  induction rs with
  | nil =>
    intro k u v _
    simp [tcolAux]
  | cons r rs ih =>
    intro k u v hv
    simp only [tcolAux, Nat.testBit_or, ih (k + 1) u v hv, Nat.testBit_shiftLeft]
    by_cases hku : k ≤ u
    · by_cases heq : k = u
      · subst heq
        have h1 : k * m ≤ k * m + v := by omega
        have h2 : k * m + v - k * m = v := by omega
        have h3 : ¬(k + 1 ≤ k) := by omega
        simp [h1, h2, h3, testBit_mask hv]
      · have hlt : k < u := by omega
        have hmul : (k + 1) * m ≤ u * m := Nat.mul_le_mul_right m (by omega)
        have hge : k * m ≤ u * m + v := by nlinarith
        have hsub : m ≤ u * m + v - k * m := by
          have : k * m + m ≤ u * m := by linarith
          omega
        have hlt2 : r &&& mask m < 2 ^ m := by
          have hm : mask m < 2 ^ m := by
            simp only [mask]; exact Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos
          exact lt_of_le_of_lt Nat.and_le_right hm
        have hzero : (r &&& mask m).testBit (u * m + v - k * m) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by omega) hsub))
        have hkp : k + 1 ≤ u := by omega
        have hidx : u - k = (u - (k + 1)) + 1 := by omega
        simp [hku, hkp, hge, hzero, hidx]
    · have hlt : u < k := by omega
      have hmul : (u + 1) * m ≤ k * m := Nat.mul_le_mul_right m (by omega)
      have hgt : ¬(k * m ≤ u * m + v) := by
        have : u * m + m ≤ k * m := by linarith
        omega
      have hkp : ¬(k + 1 ≤ u) := by omega
      simp [hku, hkp, hgt]

lemma represents_of_pcols (n m : ℕ) (C : Circuit) (tab : List ℕ)
    (haon : aonB C = true)
    (hcol : ((pcols n m C).getD C.output 0 == tcol m tab) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (tab.getD u.val 0).testBit v.val) C := by
  have heq : (pcols n m C).getD C.output 0 = tcol m tab := beq_iff_eq.mp hcol
  have hg : ∀ g ∈ C.gates, isAONB g.op = true := fun g hm => by
    have := List.all_eq_true.mp haon g hm
    simp only [Bool.and_eq_true] at this
    exact this.1
  intro u v
  have hk : u.val * m + v.val < n * m := by
    have h1 : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    nlinarith [v.isLt]
  have hag := agree_foldl hk C.gates (initCols n m) (oneEach u v) hg (agree_initCols u v)
  have hget := hag.2 C.output
  change ((pcols n m C).getD C.output 0).testBit (u.val * m + v.val) = C.eval (oneEach u v) at hget
  rw [← hget, heq, tcol, testBit_tcolAux tab 0 u.val v.val v.isLt]
  simp

lemma represents_of_pcols_mask (n m M : ℕ) (C : Circuit)
    (haon : aonB C = true)
    (hcol : ((pcols n m C).getD C.output 0 == (M &&& mask (n * m))) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => M.testBit (m * u.val + v.val)) C := by
  have heq : (pcols n m C).getD C.output 0 = M &&& mask (n * m) := beq_iff_eq.mp hcol
  have hg : ∀ g ∈ C.gates, isAONB g.op = true := fun g hm => by
    have := List.all_eq_true.mp haon g hm
    simp only [Bool.and_eq_true] at this
    exact this.1
  intro u v
  have hk : u.val * m + v.val < n * m := by
    have h1 : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    nlinarith [v.isLt]
  have hag := agree_foldl hk C.gates (initCols n m) (oneEach u v) hg (agree_initCols u v)
  have hget := hag.2 C.output
  change ((pcols n m C).getD C.output 0).testBit (u.val * m + v.val) = C.eval (oneEach u v) at hget
  rw [← hget, heq, Nat.testBit_and, testBit_mask hk, Bool.and_true, Nat.mul_comm]

def circ : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], 19⟩
set_option maxRecDepth 200000 in
lemma h_ok : aoB circ = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma h_col : ((pcols 5 5 circ).getD circ.output 0 == (31930401 &&& mask (5 * 5))) = true := by decide +kernel
lemma h_sz : circ.size ≤ 10 := by decide +kernel
end PEqualNP.Outside.L_meta_20876_aux

theorem PEqualNP.Outside.L_meta_20876 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31930401 : ℕ).testBit (5 * u.val + v.val)) 10)  := by
  exact ⟨PEqualNP.Outside.L_meta_20876_aux.circ, PEqualNP.Outside.L_meta_20876_aux.monotone2_of_aoB PEqualNP.Outside.L_meta_20876_aux.circ PEqualNP.Outside.L_meta_20876_aux.h_ok, PEqualNP.Outside.L_meta_20876_aux.h_sz, PEqualNP.Outside.L_meta_20876_aux.represents_of_pcols_mask 5 5 31930401 PEqualNP.Outside.L_meta_20876_aux.circ (PEqualNP.Outside.L_meta_20876_aux.aonB_of_aoB PEqualNP.Outside.L_meta_20876_aux.circ PEqualNP.Outside.L_meta_20876_aux.h_ok) PEqualNP.Outside.L_meta_20876_aux.h_col⟩
