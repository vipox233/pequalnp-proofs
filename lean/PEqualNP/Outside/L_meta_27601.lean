import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_27601_aux
open PEqualNP.CircuitLowerBounds

def comb (k : Bool) (x y : BitVec 16) := if k then x &&& y else x ||| y
lemma commute (k : Bool) (x y : BitVec 16) : comb k x y = comb k y x := by
  cases k <;> simp [comb, BitVec.and_comm, BitVec.or_comm]
def mix (xs ys : List (BitVec 16)) := xs.flatMap fun x => ys.flatMap fun y => [comb true x y, comb false x y]
def s1 : List (BitVec 16) := [0xff00,0xf0f0,0xcccc,0xaaaa]
def s2 := s1 ++ mix s1 s1
def s3 := s2 ++ mix s1 s2
def s4 := s3 ++ mix s1 s3 ++ mix s2 s2
def weight (x : BitVec 16) : ℕ :=
  if x = 0 ∨ x = -1 then 5 else if x ∈ s1 then 4 else if x ∈ s2 then 3 else
  if x ∈ s3 then 2 else if x ∈ s4 then 1 else 0

lemma weight_le (x : BitVec 16) : weight x ≤ 5 := by unfold weight; split_ifs <;> decide
lemma mem_mix {x y : BitVec 16} {a b} (hx : x ∈ a) (hy : y ∈ b) (k : Bool) :
    comb k x y ∈ mix a b := by
  apply List.mem_flatMap.mpr
  refine ⟨x,hx,List.mem_flatMap.mpr ⟨y,hy,?_⟩⟩
  cases k <;> simp

lemma w2 {x} (h : x ∈ s2) : 3 ≤ weight x := by unfold weight; split_ifs <;> omega
lemma w3 {x} (h : x ∈ s3) : 2 ≤ weight x := by unfold weight; split_ifs <;> omega
lemma w4 {x} (h : x ∈ s4) : 1 ≤ weight x := by unfold weight; split_ifs <;> omega
lemma ones_bit : ∀ j : Fin 16, (65535 : BitVec 16).getLsbD j.val = true := by decide

lemma charge (k : Bool) (x y : BitVec 16) :
    weight x + weight y ≤ 5 + weight (comb k x y) := by
  have cons (a b : BitVec 16) (h : a = 0 ∨ a = -1) :
      weight a + weight b ≤ 5 + weight (comb k a b) := by
    have z : comb k a b = a ∨ comb k a b = b := by
      rcases h with rfl | rfl <;> cases k
      · right
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [comb]
      · left
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [comb]
      · left
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [comb,hi]
        exact fun _ => ones_bit ⟨i,hi⟩
      · right
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [comb,hi]
        exact fun _ => ones_bit ⟨i,hi⟩
    have := weight_le a
    have := weight_le b
    rcases z with z | z <;> rw [z] <;> omega
  by_cases hx : x = 0 ∨ x = -1
  · exact cons x y hx
  by_cases hy : y = 0 ∨ y = -1
  · simpa [Nat.add_comm (weight y) (weight x),commute k y x] using cons y x hy
  have m11 (a b) (ha : a ∈ s1) (hb : b ∈ s1) : 3 ≤ weight (comb k a b) :=
    w2 (List.mem_append_right _ (mem_mix ha hb k))
  have m12 (a b) (ha : a ∈ s1) (hb : b ∈ s2) : 2 ≤ weight (comb k a b) :=
    w3 (List.mem_append_right _ (mem_mix ha hb k))
  have m13 (a b) (ha : a ∈ s1) (hb : b ∈ s3) : 1 ≤ weight (comb k a b) :=
    w4 (List.mem_append_left _ (List.mem_append_right _ (mem_mix ha hb k)))
  have m22 (a b) (ha : a ∈ s2) (hb : b ∈ s2) : 1 ≤ weight (comb k a b) :=
    w4 (List.mem_append_right _ (mem_mix ha hb k))
  have classify (a : BitVec 16) (nc : ¬ (a = 0 ∨ a = -1)) :
      (weight a = 4 ∧ a ∈ s1) ∨ (weight a = 3 ∧ a ∈ s2) ∨
      (weight a = 2 ∧ a ∈ s3) ∨ weight a ≤ 1 := by
    unfold weight
    rw [if_neg nc]
    split_ifs <;> simp_all
  have m21 (a b) (ha : a ∈ s2) (hb : b ∈ s1) : 2 ≤ weight (comb k a b) := by
    rw [commute]; exact m12 b a hb ha
  have m31 (a b) (ha : a ∈ s3) (hb : b ∈ s1) : 1 ≤ weight (comb k a b) := by
    rw [commute]; exact m13 b a hb ha
  rcases classify x hx with ⟨ax,ex⟩ | ⟨ax,ex⟩ | ⟨ax,ex⟩ | ax <;>
    rcases classify y hy with ⟨ay,ey⟩ | ⟨ay,ey⟩ | ⟨ay,ey⟩ | ay <;>
    first | omega | (have := m11 x y ex ey; omega) | (have := m12 x y ex ey; omega) |
      (have := m21 x y ex ey; omega) | (have := m13 x y ex ey; omega) |
      (have := m31 x y ex ey; omega) | (have := m22 x y ex ey; omega)

def f (x : Fin 9 → Bool) :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
   (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
def ea (x : Fin 9 → Bool) : Bool := GateOp.or.eval [x 0, x 1]
def eb (x : Fin 9 → Bool) : Bool := GateOp.and.eval [x 3, x 8]
def row (m : ℕ) (i : Fin 9) := m.testBit i.val
def hidVars : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]
def witness : Fin 9 → ℕ := ![162, 97, 80, 132, 68, 66, 20, 12, 17]
set_option maxRecDepth 8192 in
lemma necessary (j : Fin 9) (hj : j ∈ hidVars) : ∃ x y : Fin 9 → Bool,
    (∀ i, i ≠ j → x i = y i) ∧ ea x = ea y ∧ eb x = eb y ∧ f x ≠ f y := by
  refine ⟨row (witness j), row (witness j + 2^j.val), ?_⟩
  revert hj
  fin_cases j <;> decide
lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma budget (m : ℕ) (hm : 0 < m) (L : Finset ℕ) (hL : ∀ i ∈ L, i < 11) (W : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (live : ∀ i ∈ L ∪ Finset.Ico 11 (10+m), ∃ j < m, i ∈ S j)
    (localBound : ∀ j < m, ∑ i ∈ S j, W i ≤ 5 + W (11+j)) :
    ∑ i ∈ L, W i ≤ 5*m + W (10+m) := by
  classical
  have h : ∑ i ∈ L ∪ Finset.Ico 11 (10+m), W i ≤ ∑ j ∈ Finset.range m, (5 + W (11+j)) := by
    calc ∑ i ∈ L ∪ Finset.Ico 11 (10+m), W i
          ≤ ∑ i ∈ L ∪ Finset.Ico 11 (10+m), ∑ j ∈ Finset.range m, if i ∈ S j then W i else 0 := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨j,hj,mem⟩ := live i hi
          simpa [mem] using (Finset.single_le_sum (f := fun j => if i ∈ S j then W i else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))
       _ = _ := Finset.sum_comm
       _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← Finset.sum_filter]
          exact (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).2)
            (fun _ _ _ => Nat.zero_le _)).trans (localBound j (Finset.mem_range.mp hj))
  have dis : Disjoint L (Finset.Ico 11 (10+m)) := Finset.disjoint_left.mpr (fun i hi hI => by
    have := hL i hi
    have := (Finset.mem_Ico.mp hI).1
    omega)
  have e : ∑ j ∈ Finset.range m, W (11+j) = ∑ i ∈ Finset.Ico 11 (10+m), W i + W (10+m) := by
    have h1 : ∑ i ∈ Finset.Ico 11 (11+m), W i = ∑ j ∈ Finset.range m, W (11+j) := by
      rw [Finset.sum_Ico_eq_sum_range, show 11+m-11 = m by omega]
    rw [← h1, show 11+m = (10+m)+1 by omega, Finset.sum_Ico_succ_top (by omega)]
  rw [Finset.sum_union dis, Finset.sum_add_distrib, e] at h
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  omega
def val (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
def gate (C : Circuit) (j : ℕ) := C.gates.getD j ⟨.and,[]⟩
def legal (g : Gate) (n : ℕ) :=
  (g.op = .not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b])

lemma back {g n} (h : legal g n) : ∀ i ∈ g.inputs, i < n := by
  rcases h with ⟨_,a,ha,h⟩ | ⟨_,a,b,hab,hb,h⟩ <;> rw [h] <;> simp_all <;> omega

lemma gate_get (C : Circuit) (j : ℕ) (h : j < C.gates.length) : gate C j = C.gates[j] := by
  simp [gate,List.getD_eq_getElem?_getD,h]

lemma val_input (C : Circuit) (x : Fin 9 → Bool) (j : Fin 9) : val C x j = x j := by
  unfold val Circuit.wires
  rw [foldl_wires_getD_lt _ _ _ (by simp)]
  fin_cases j <;> rfl

lemma val_lt (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : val C x i = x ⟨i,hi⟩ :=
  val_input C x ⟨i,hi⟩

lemma val_gate {C : Circuit} (x : Fin 9 → Bool) {j : ℕ} (hj : j < C.gates.length)
    (hl : legal (gate C j) (9+j)) :
    val C x (9+j) = (gate C j).op.eval ((gate C j).inputs.map (val C x)) := by
  rw [gate_get _ _ hj] at hl ⊢
  unfold val Circuit.wires
  simpa only [List.length_ofFn] using foldl_wires_getD_gate C.gates (List.ofFn x) j hj
    (by simpa only [List.length_ofFn] using back hl)

lemma valA {C : Circuit} (hl : ∀ j < C.size, legal (gate C j) (9+j)) (two : 2 ≤ C.size)
    (ha : gate C 0 = ⟨.or,[0,1]⟩) (x : Fin 9 → Bool) : val C x 9 = ea x := by
  have h := val_gate x (j := 0) (by change 0 < C.size; omega) (hl 0 (by omega))
  rw [ha] at h
  simp only [Nat.add_zero, List.map_cons, List.map_nil, val_lt C x 0 (by omega), val_lt C x 1 (by omega)] at h
  exact h
lemma valB {C : Circuit} (hl : ∀ j < C.size, legal (gate C j) (9+j)) (two : 2 ≤ C.size)
    (ha : gate C 0 = ⟨.or,[0,1]⟩) (hb : gate C 1 = ⟨.and,[3,8]⟩) (x : Fin 9 → Bool) : val C x 10 = eb x := by
  have h := val_gate x (j := 1) (by change 1 < C.size; omega) (hl 1 (by omega))
  rw [hb] at h
  simp only [List.map_cons, List.map_nil, val_lt C x 3 (by omega), val_lt C x 8 (by omega)] at h
  exact h
lemma sensitive_read {C : Circuit} (hl : ∀ j < C.size, legal (gate C j) (9+j))
    (two : 2 ≤ C.size) (ha : gate C 0 = ⟨.or,[0,1]⟩) (hb : gate C 1 = ⟨.and,[3,8]⟩)
    (ho : C.output+1 = 9+C.size) (hf : ∀ x, val C x C.output = f x)
    (v : Fin 9) (hv : v ∈ hidVars) : ∃ j, 2 ≤ j ∧ j < C.size ∧ v.val ∈ (gate C j).inputs := by
  obtain ⟨x,y,agree,pa,pb,neq⟩ := necessary v hv
  by_contra absent
  apply neq
  rw [← hf x, ← hf y]
  have all : ∀ i, i < 9+C.size → i ≠ v.val → val C x i = val C y i := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi ne
      by_cases small : i < 9
      · let q : Fin 9 := ⟨i,small⟩
        exact (val_input C x q).trans ((agree q (fun he => ne (congrArg Fin.val he))).trans
          (val_input C y q).symm)
      by_cases i9 : i = 9
      · rw [i9, valA hl two ha x, valA hl two ha y]
        exact pa
      by_cases i10 : i = 10
      · rw [i10, valB hl two ha hb x, valB hl two ha hb y]
        exact pb
      let k := i-9
      have ix : i = 9+k := by dsimp [k]; omega
      have hk : k < C.size := by omega
      rw [ix, val_gate x hk (hl k hk), val_gate y hk (hl k hk)]
      congr 1
      apply List.map_congr_left
      intro q hq
      have earlier := back (hl k hk) q hq
      apply ih q (by omega) (by omega)
      rintro rfl
      exact absent ⟨k,by omega,hk,hq⟩
  exact all C.output (by omega) (by have := v.isLt; omega)
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def input (r : Fin 16) : Fin 9 → Bool :=
  ![r.val.testBit 3, true, r.val.testBit 2, false, true, r.val.testBit 1, r.val.testBit 0, true, false]
def table (C : Circuit) (i : ℕ) := encodePoint (fun r => val C (input r) i)
def gtab (i : ℕ) : BitVec 16 :=
  if h : i < 9 then encodePoint (fun r => input r ⟨i,h⟩)
  else if i = 9 then encodePoint (fun r => ea (input r)) else encodePoint (fun r => eb (input r))
lemma pinCharge {C : Circuit} {j : ℕ} (hj : j < C.size) (hl : legal (gate C j) (9+j)) :
    ∑ i ∈ (gate C j).inputs.toFinset, weight (table C i) ≤ 5 + weight (table C (9+j)) := by
  have ev (r) := val_gate (input r) hj hl
  rcases hl with ⟨h,a,_,pin⟩ | ⟨h,a,b,ab,_,pin⟩
  · simp [pin]
    have := weight_le (table C a)
    omega
  · have eq (k : Bool) (opEq : (gate C j).op = if k then .and else .or) :
        table C (9+j) = comb k (table C a) (table C b) := by
      unfold table
      cases k
      · change _ = _ ||| _
        rw [← encodeOr]
        congr 1
        funext r
        simpa [opEq,pin,GateOp.eval] using ev r
      · change _ = _ &&& _
        rw [← encodeAnd]
        congr 1
        funext r
        simpa [opEq,pin,GateOp.eval] using ev r
    have ne : a ≠ b := Nat.ne_of_lt ab
    rcases h with h | h
    · simpa [pin,ne,eq true h] using charge true (table C a) (table C b)
    · simpa [pin,ne,eq false h] using charge false (table C a) (table C b)

def Lset : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma table_eq {C : Circuit} (hl : ∀ j < C.size, legal (gate C j) (9+j)) (two : 2 ≤ C.size)
    (ha : gate C 0 = ⟨.or,[0,1]⟩) (hb : gate C 1 = ⟨.and,[3,8]⟩) (i : ℕ) (hi : i ≤ 10) : table C i = gtab i := by
  unfold table gtab
  by_cases h : i < 9
  · rw [dif_pos h]
    congr 1
    funext r
    exact val_lt C (input r) i h
  · rw [dif_neg h]
    by_cases h9 : i = 9
    · rw [if_pos h9]
      congr 1
      funext r
      rw [h9]
      exact valA hl two ha _
    · rw [if_neg h9]
      have h10 : i = 10 := by omega
      congr 1
      funext r
      rw [h10]
      exact valB hl two ha hb _
set_option maxRecDepth 8192 in
lemma sum_start : ∑ i ∈ Lset, weight (gtab i) = 51 := by
  decide +kernel
set_option maxRecDepth 8192 in
lemma endCharge {C : Circuit} (hf : ∀ x, val C x C.output = f x) :
    weight (table C C.output) = 0 := by
  unfold table
  simp_rw [hf]
  decide +kernel
end PEqualNP.Outside.L_meta_27601_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_27601_aux
theorem PEqualNP.Outside.L_meta_27601 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩)) := by
  rintro ⟨C,_,size,correct,output,form,_,used,head,second⟩
  have gateList : ∃ gs, C.gates = ⟨.or,[0,1]⟩ :: ⟨.and,[3,8]⟩ :: gs := by
    cases hg : C.gates with
    | nil => simp [hg] at head
    | cons a as =>
      cases ht : as with
      | nil => simp [hg,ht] at second
      | cons b bs =>
        simp [hg,ht] at head second
        exact ⟨bs,by simp [head,second]⟩
  obtain ⟨gs,hgs⟩ := gateList
  have len : C.size = 2 + gs.length := by simp [Circuit.size,hgs]; omega
  have two : 2 ≤ C.size := by omega
  have ha : gate C 0 = ⟨.or,[0,1]⟩ := by simp [gate,hgs]
  have hb : gate C 1 = ⟨.and,[3,8]⟩ := by simp [gate,hgs]
  have hl (j : ℕ) (hj : j < C.size) : legal (gate C j) (9+j) := by
    rw [gate_get C j hj]
    exact form ⟨j,hj⟩
  have hf : ∀ x, val C x C.output = f x := correct
  let m := gs.length
  let S := fun j => (gate C (j+2)).inputs.toFinset
  have hid : ∀ v : Fin 9, v ∈ hidVars → ∃ k, 2 ≤ k ∧ k < C.size ∧ v.val ∈ (gate C k).inputs :=
    fun v hv => sensitive_read hl two ha hb output hf v hv
  have mpos : 0 < m := by
    obtain ⟨k, lo, hi, _⟩ := hid 0 (by decide)
    dsimp [m]
    omega
  have Lbound : ∀ i ∈ Lset, i ≤ 10 := by decide
  have live : ∀ i ∈ Lset ∪ Finset.Ico 11 (10+m), ∃ j < m, i ∈ S j := by
    intro i hi
    have hit : ∃ k, 2 ≤ k ∧ k < C.size ∧ i ∈ (gate C k).inputs := by
      by_cases small : i < 9
      · have key : ∀ q : Fin 9, q.val ∈ Lset → q ∈ hidVars := by decide
        have inL : i ∈ Lset := by
          rcases Finset.mem_union.mp hi with h | h
          · exact h
          · have := (Finset.mem_Ico.mp h).1; omega
        exact hid ⟨i,small⟩ (key ⟨i,small⟩ inL)
      · let q := i-9
        have idq : 9+q = i := by dsimp [q]; omega
        have plen : C.gates.length = 2 + m := len
        have bnd : i < 10+m := by
          rcases Finset.mem_union.mp hi with h | h
          · have := Lbound i h; omega
          · exact (Finset.mem_Ico.mp h).2
        have hq : q < C.gates.length := by omega
        obtain ⟨k, later, pin⟩ := used ⟨q,hq⟩ (by change q + 1 < C.gates.length; omega)
        have hk : i ∈ (gate C k.val).inputs := by
          rw [gate_get _ _ k.isLt,← idq]
          exact pin
        have kpos : 2 ≤ k.val := by
          by_contra! hh
          have ke : k.val = 1 := by change q < k.val at later; omega
          have i9 : i = 9 := by change q < k.val at later; omega
          rw [ke,hb] at hk
          rw [i9] at hk
          exact absurd hk (by decide)
        exact ⟨k.val,kpos,k.isLt,hk⟩
    obtain ⟨k,low,high,pin⟩ := hit
    refine ⟨k-2,by dsimp [m]; omega,?_⟩
    simpa [S,Nat.sub_add_cancel low] using pin
  have loc (j : ℕ) (hj : j < m) :
      ∑ i ∈ S j, weight (table C i) ≤ 5 + weight (table C (11+j)) := by
    have h : j+2 < C.size := by dsimp [m] at hj; omega
    simpa [S,show 9+(j+2) = 11+j by omega] using pinCharge (C := C) h (hl _ h)
  have h := budget m mpos Lset (by decide) (fun i => weight (table C i)) S live loc
  have e : 10+m = C.output := by dsimp [m]; omega
  have st : ∑ i ∈ Lset, weight (table C i) = 51 := by
    rw [← sum_start]
    exact Finset.sum_congr rfl (fun i hi => by rw [table_eq hl two ha hb i (Lbound i hi)])
  rw [st,e,endCharge hf] at h
  dsimp [m] at h
  omega
