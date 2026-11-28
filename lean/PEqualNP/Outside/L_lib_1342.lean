import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1342_aux

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem circuit_wires_eq_run (C : Circuit) (x : List Bool) :
    C.wires x = run C.gates x := rfl

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

private theorem getD_lt {α : Type*} (l : List α) (b dft : α) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t dft = l.getD t dft := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem getD_eq {α : Type*} (l : List α) (b dft : α) :
    (l ++ [b]).getD l.length dft = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp

private theorem run_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD w false = (run gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt]
    · exact ih
    · rw [run_length, List.length_append]; omega

private theorem run_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  simpa [run] using run_prefix [] gs x w (by simpa using hw)

private theorem run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc] at h1 ⊢
    exact h1
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hp1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by rw [List.length_append, List.length_singleton, hlen]; omega)
  rw [hp1, run_snoc]
  have hrlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, hlen]
  rw [← hrlen, getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hrlen]
  by_cases hi : i < x.length + j
  · rw [if_pos hi]
    have htake : (run gs x).getD i false = (run (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i (by rw [hlen]; exact hi)
    exact htake.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

private def posCount [DecidableEq GateOp] (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (g.op ≠ GateOp.not))).length

private def negCount [DecidableEq GateOp] (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (g.op = GateOp.not))).length

private theorem posCount_nil [DecidableEq GateOp] : posCount ([] : List Gate) = 0 := rfl
private theorem negCount_nil [DecidableEq GateOp] : negCount ([] : List Gate) = 0 := rfl

private theorem posCount_append [DecidableEq GateOp] (gs1 gs2 : List Gate) :
    posCount (gs1 ++ gs2) = posCount gs1 + posCount gs2 := by
  simp only [posCount, List.filter_append, List.length_append]

private theorem negCount_append [DecidableEq GateOp] (gs1 gs2 : List Gate) :
    negCount (gs1 ++ gs2) = negCount gs1 + negCount gs2 := by
  simp only [negCount, List.filter_append, List.length_append]

private theorem posCount_add_negCount [DecidableEq GateOp] (gs : List Gate) :
    posCount gs + negCount gs = gs.length := by
  induction gs with
  | nil => simp [posCount, negCount]
  | cons g gs ih =>
    dsimp only [posCount, negCount] at ih ⊢
    rw [List.filter_cons, List.filter_cons, List.length_cons]
    by_cases h : g.op = GateOp.not
    · have h1 : ¬ (g.op ≠ GateOp.not) := not_not.mpr h
      rw [decide_eq_true h, decide_eq_false h1]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · rw [decide_eq_false h, decide_eq_true h]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

private theorem notCount_eq_negCount [DecidableEq GateOp] (C : Circuit) :
    PEqualNP.NotBracket.notCount C = negCount C.gates := by
  dsimp only [PEqualNP.NotBracket.notCount, negCount]
  congr 1
  apply List.filter_congr
  intro g _
  exact congrArg (@decide (g.op = GateOp.not)) (Subsingleton.elim _ _)

private theorem size_sub_notCount_eq_posCount [DecidableEq GateOp] (C : Circuit) :
    C.size - PEqualNP.NotBracket.notCount C = posCount C.gates := by
  rw [notCount_eq_negCount, Circuit.size, ← posCount_add_negCount C.gates]
  omega

private theorem posCount_snoc_pos [DecidableEq GateOp] (gs : List Gate) (g : Gate)
    (h : g.op ≠ GateOp.not) : posCount (gs ++ [g]) = posCount gs + 1 := by
  rw [posCount_append]; simp [posCount, h]

private theorem negCount_snoc_pos [DecidableEq GateOp] (gs : List Gate) (g : Gate)
    (h : g.op ≠ GateOp.not) : negCount (gs ++ [g]) = negCount gs := by
  rw [negCount_append]; simp [negCount, h]

private structure Good (M₀ : ℕ) (gs : List Gate) : Prop where
  fanInTwo : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  readsBack : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < M₀ + j

private theorem good_nil (M₀ : ℕ) : Good M₀ [] where
  fanInTwo := by simp
  readsBack := by simp

private theorem good_snoc {M₀ : ℕ} {gs : List Gate} (hgs : Good M₀ gs) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < M₀ + gs.length) :
    Good M₀ (gs ++ [g]) where
  fanInTwo := by
    intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hgs.fanInTwo g' hg'
    · exact ⟨hop, hlen⟩
  readsBack := by
    intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_lt _ _ _ _ hlt] at hi
      exact hgs.readsBack j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_eq] at hi
      exact hrb i hi

private def bitAt (r k : ℕ) : Bool := decide ((r / 2 ^ k) % 2 = 1)

private theorem bitAt_two_mul_add_zero (v : ℕ) (b : Bool) :
    bitAt (2 * v + if b then 1 else 0) 0 = b := by
  cases b <;> simp [bitAt]

private theorem bitAt_two_mul_add_succ (v : ℕ) (b : Bool) (k : ℕ) :
    bitAt (2 * v + if b then 1 else 0) (k + 1) = bitAt v k := by
  simp only [bitAt, Nat.pow_succ']
  have hdiv : (2 * v + (if b then 1 else 0)) / (2 * 2 ^ k) = v / 2 ^ k := by
    rw [← Nat.div_div_eq_div_mul]
    have h0 : (2 * v + (if b then 1 else 0)) / 2 = v := by
      cases b <;> simp <;> omega
    rw [h0]
  rw [hdiv]

private def foldBits (bs : List Bool) : ℕ :=
  bs.foldl (fun v b => 2 * v + if b then 1 else 0) 0

private theorem foldBits_snoc (bs : List Bool) (b : Bool) :
    foldBits (bs ++ [b]) = 2 * foldBits bs + if b then 1 else 0 := by
  simp only [foldBits, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldBits_lt (bs : List Bool) : foldBits bs < 2 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [foldBits]
  | append_singleton bs b ih =>
    rw [foldBits_snoc, List.length_append, List.length_singleton, Nat.pow_succ']
    cases b <;> simp <;> omega

private theorem bitAt_foldBits (bs : List Bool) (s : ℕ) (hs : s < bs.length) :
    bitAt (foldBits bs) (bs.length - 1 - s) = bs.getD s false := by
  induction bs using List.reverseRecOn with
  | nil => simp at hs
  | append_singleton bs b ih =>
    rw [List.length_append, List.length_singleton] at hs ⊢
    rw [foldBits_snoc]
    by_cases hlast : s = bs.length
    · subst hlast
      have h0 : bs.length + 1 - 1 - bs.length = 0 := by omega
      rw [h0, bitAt_two_mul_add_zero, getD_eq]
    · have hlt : s < bs.length := by omega
      have hpos : bs.length + 1 - 1 - s = (bs.length - 1 - s) + 1 := by omega
      rw [hpos, bitAt_two_mul_add_succ, ih hlt, getD_lt _ _ _ _ hlt]

private theorem bitAt_mod_two_pow (r k n : ℕ) (hk : k < n) :
    bitAt (r % 2 ^ n) k = bitAt r k := by
  simp only [bitAt]
  have hdvd : 2 ^ (k + 1) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
  have h1 : (r % 2 ^ n) % 2 ^ (k + 1) = r % 2 ^ (k + 1) :=
    Nat.mod_mod_of_dvd r hdvd
  have hmod : ∀ m, (m / 2 ^ k) % 2 = (m % 2 ^ (k + 1)) / 2 ^ k := by
    intro m
    rw [Nat.pow_succ', Nat.mod_mul_left_div_self]
  rw [hmod (r % 2 ^ n), hmod r, h1]

private theorem div_two_pow_eq_bitAt (r n : ℕ) (hr : r < 2 ^ (n + 1)) :
    r / 2 ^ n = if bitAt r n then 1 else 0 := by
  have hlt : r / 2 ^ n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.pow_succ, Nat.mul_comm] at hr
    exact hr
  have hd : r / 2 ^ n = 0 ∨ r / 2 ^ n = 1 := by
    rcases Nat.lt_or_ge (r / 2 ^ n) 1 with hlt1 | hge1
    · exact Or.inl (Nat.lt_one_iff.mp hlt1)
    · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hlt) hge1)
  rcases hd with h0 | h1
  · simp [bitAt, h0]
  · simp [bitAt, h1]

private theorem le_iff_bitAt_eq_or_lt (b r1 r2 : ℕ) (h1 : r1 < 2 ^ b) (h2 : r2 < 2 ^ b) :
    (r1 = r2 ∧ ∀ k < b, bitAt r1 k = bitAt r2 k) ∨
    (∃ k < b, (∀ t, k < t → t < b → bitAt r1 t = bitAt r2 t) ∧
      bitAt r1 k ≠ bitAt r2 k ∧ (r1 < r2 ↔ bitAt r1 k = false ∧ bitAt r2 k = true)) := by
  induction b generalizing r1 r2 with
  | zero =>
    left
    have hr1 : r1 = 0 := by omega
    have hr2 : r2 = 0 := by omega
    exact ⟨hr1.trans hr2.symm, fun k hk => by omega⟩
  | succ b ih =>
    by_cases htop : bitAt r1 b = bitAt r2 b
    · have hm1 : r1 % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
      have hm2 : r2 % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
      have hdiv : r1 / 2 ^ b = r2 / 2 ^ b := by
        rw [div_two_pow_eq_bitAt r1 b h1, div_two_pow_eq_bitAt r2 b h2, htop]
      rcases ih (r1 % 2 ^ b) (r2 % 2 ^ b) hm1 hm2 with ⟨heq, hbits⟩ | ⟨k, hk, hhi, hne, hlt⟩
      · left
        have hr : r1 = r2 := by
          have e1 := Nat.div_add_mod r1 (2 ^ b)
          have e2 := Nat.div_add_mod r2 (2 ^ b)
          rw [hdiv] at e1
          omega
        refine ⟨hr, fun k hk => ?_⟩
        by_cases hk' : k = b
        · subst hk'; exact htop
        · have hklt : k < b := by omega
          rw [← bitAt_mod_two_pow r1 k b hklt, ← bitAt_mod_two_pow r2 k b hklt]
          exact hbits k hklt
      · right
        refine ⟨k, Nat.lt_succ_of_lt hk, fun t hkt htb => ?_, ?_, ?_⟩
        · by_cases htb' : t = b
          · subst htb'; exact htop
          · have htl : t < b := by omega
            rw [← bitAt_mod_two_pow r1 t b htl, ← bitAt_mod_two_pow r2 t b htl]
            exact hhi t hkt htl
        · rw [← bitAt_mod_two_pow r1 k b hk, ← bitAt_mod_two_pow r2 k b hk]
          exact hne
        · rw [← bitAt_mod_two_pow r1 k b hk, ← bitAt_mod_two_pow r2 k b hk]
          have e1 := Nat.div_add_mod r1 (2 ^ b)
          have e2 := Nat.div_add_mod r2 (2 ^ b)
          rw [hdiv] at e1
          have hlt' : r1 < r2 ↔ r1 % 2 ^ b < r2 % 2 ^ b := by omega
          exact hlt'.trans hlt
    · right
      refine ⟨b, Nat.lt_succ_self b, fun t hbt htb => by omega, htop, ?_⟩
      have d1 := div_two_pow_eq_bitAt r1 b h1
      have d2 := div_two_pow_eq_bitAt r2 b h2
      have e1 := Nat.div_add_mod r1 (2 ^ b)
      have e2 := Nat.div_add_mod r2 (2 ^ b)
      have hm1 : r1 % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
      have hm2 : r2 % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
      cases hb1 : bitAt r1 b <;> cases hb2 : bitAt r2 b
      · exact absurd (hb1.trans hb2.symm) htop
      · rw [hb1] at d1; rw [hb2] at d2
        simp only [Bool.false_eq_true, ↓reduceIte] at d1
        simp only [↓reduceIte] at d2
        have hr1 : r1 = r1 % 2 ^ b := by rw [← e1, d1]; simp
        have hr2 : r2 = 2 ^ b + r2 % 2 ^ b := by rw [← e2, d2]; simp
        simp only [true_and, iff_true]
        omega
      · rw [hb1] at d1; rw [hb2] at d2
        simp only [↓reduceIte] at d1
        simp only [Bool.false_eq_true, ↓reduceIte] at d2
        have hr1 : r1 = 2 ^ b + r1 % 2 ^ b := by rw [← e1, d1]; simp
        have hr2 : r2 = r2 % 2 ^ b := by rw [← e2, d2]; simp
        simp only [Bool.true_eq_false, Bool.false_eq_true, and_self, iff_false]
        intro hlt
        rw [hr1, hr2] at hlt
        omega
      · exact absurd (hb1.trans hb2.symm) htop

private theorem take_filter_range (p : ℕ → Bool) (n s : ℕ)
    (hs : s < ((List.range n).filter p).length) :
    ((List.range n).filter p).take s =
      (List.range (((List.range n).filter p).getD s 0)).filter p := by
  induction n generalizing s with
  | zero => simp at hs
  | succ n ih =>
    rw [List.range_succ, List.filter_append] at hs ⊢
    by_cases hpn : p n = true
    · have hfilt : List.filter p [n] = [n] := by simp [hpn]
      rw [hfilt] at hs ⊢
      rw [List.length_append, List.length_singleton] at hs
      by_cases hlast : s = ((List.range n).filter p).length
      · subst hlast
        rw [List.take_left, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp
      · have hlt : s < ((List.range n).filter p).length := by omega
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt),
          List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          ← List.getD_eq_getElem?_getD]
        exact ih s hlt
    · have hpnf : p n = false := Bool.eq_false_iff.mpr hpn
      have hfilt : List.filter p [n] = [] := by simp [hpnf]
      rw [hfilt, List.append_nil] at hs ⊢
      exact ih s hs

private theorem filter_range_getD_props (p : ℕ → Bool) (n s : ℕ)
    (hs : s < ((List.range n).filter p).length) :
    let L := (List.range n).filter p
    L.getD s 0 < n ∧ p (L.getD s 0) = true ∧
    ((List.range (L.getD s 0)).filter p).length = s ∧
    (∀ j < L.getD s 0, p j = true → ∃ s' < s, L.getD s' 0 = j) := by
  intro L
  have hmem : L.getD s 0 ∈ L := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
    exact List.getElem_mem hs
  have hm := List.mem_filter.mp hmem
  have hlt : L.getD s 0 < n := List.mem_range.mp hm.1
  have htake := take_filter_range p n s hs
  have hlen : ((List.range (L.getD s 0)).filter p).length = s := by
    rw [← htake, List.length_take_of_le (Nat.le_of_lt hs)]
  refine ⟨hlt, hm.2, hlen, fun j hj hjp => ?_⟩
  have hjmem : j ∈ (List.range (L.getD s 0)).filter p :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hj, hjp⟩
  rw [← htake] at hjmem
  rcases List.mem_iff_getElem.mp hjmem with ⟨s', hs', hjs'⟩
  have hs'_lt : s' < s := by
    rw [List.length_take_of_le (Nat.le_of_lt hs)] at hs'
    exact hs'
  refine ⟨s', hs'_lt, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lt_trans hs'_lt hs)]
  simpa [List.getElem_take] using hjs'

private def notIdxList [DecidableEq GateOp] (C : Circuit) : List ℕ :=
  (List.range C.size).filter (fun j => decide ((C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not))

private def notPos [DecidableEq GateOp] (C : Circuit) (j : ℕ) : ℕ :=
  ((List.range j).filter (fun u => decide ((C.gates.getD u ⟨GateOp.or, []⟩).op = GateOp.not))).length

private theorem notIdxList_length [DecidableEq GateOp] (C : Circuit) :
    (notIdxList C).length = PEqualNP.NotBracket.notCount C := by
  dsimp only [notIdxList, PEqualNP.NotBracket.notCount, Circuit.size]
  suffices h : ((List.range C.gates.length).filter (fun u =>
      decide ((C.gates.getD u ⟨GateOp.or, []⟩).op = GateOp.not))).length =
      (C.gates.filter (fun g => decide (g.op = GateOp.not))).length by
    rw [h]
    congr 1
    apply List.filter_congr
    intro g _
    exact congrArg (@decide (g.op = GateOp.not)) (Subsingleton.elim _ _)
  induction C.gates using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.filter_append, List.length_append, List.length_append]
    have ha : (List.range gs.length).filter (fun u =>
        decide (((gs ++ [g]).getD u ⟨.or, []⟩).op = .not)) =
        (List.range gs.length).filter (fun u => decide ((gs.getD u ⟨.or, []⟩).op = .not)) := by
      apply List.filter_congr
      intro u hu
      have hlt := List.mem_range.mp hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    have hb : ([gs.length].filter (fun u =>
        decide (((gs ++ [g]).getD u ⟨.or, []⟩).op = .not))).length =
        ([g].filter (fun g' => decide (g'.op = .not))).length := by
      have hgd : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      cases h : g.op <;> simp [h]
    rw [ha, ih, hb]

private theorem rank_eq_foldBits [DecidableEq GateOp] (d : ℕ) (C : Circuit) (x : Finset (Fin d)) :
    let bits := List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]
    let w := C.wires bits
    let rankVal := (notIdxList C).foldl (fun v j => 2 * v + (if w.getD (d + 2 + j) false then 0 else 1)) 0
    rankVal = foldBits ((notIdxList C).map (fun j => !(w.getD (d + 2 + j) false))) := by
  intro bits w rankVal
  dsimp only [foldBits, rankVal]
  rw [List.foldl_map]
  congr 1; funext v j
  cases w.getD (d + 2 + j) false <;> rfl

private def pushOrList (M₀ cF : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, cF)
  | w :: ws => ws.foldl (fun st u => (st.1 ++ [⟨GateOp.or, [st.2, u]⟩], M₀ + st.1.length)) (gs, w)

private theorem pushOrList_foldl_props [DecidableEq GateOp] (M₀ : ℕ) (ws : List ℕ)
    (gs : List Gate) (w : ℕ) (hgs : Good M₀ gs) (hw : w < M₀ + gs.length)
    (hws : ∀ u ∈ ws, u < M₀ + gs.length) :
    let res := ws.foldl (fun st u => (st.1 ++ [⟨GateOp.or, [st.2, u]⟩], M₀ + st.1.length)) (gs, w)
    (∃ tail, res.1 = gs ++ tail ∧ tail.length = ws.length ∧
      negCount tail = 0 ∧ posCount tail = ws.length) ∧
    Good M₀ res.1 ∧ res.2 < M₀ + res.1.length ∧
    ∀ X : List Bool, X.length = M₀ →
      (run res.1 X).getD res.2 false =
        ((run gs X).getD w false || ws.any (fun u => (run gs X).getD u false)) := by
  induction ws generalizing gs w with
  | nil =>
    refine ⟨⟨[], by simp, rfl, negCount_nil, posCount_nil⟩, hgs, hw, fun X _ => by simp⟩
  | cons u us ih =>
    simp only [List.foldl_cons]
    have hu : u < M₀ + gs.length := hws u (by simp)
    have hgs1 : Good M₀ (gs ++ [(⟨GateOp.or, [w, u]⟩ : Gate)]) :=
      good_snoc hgs ⟨GateOp.or, [w, u]⟩ (by simp) (by simp)
        (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption)
    have hw1 : M₀ + gs.length < M₀ + (gs ++ [(⟨GateOp.or, [w, u]⟩ : Gate)]).length := by simp
    have hus : ∀ v ∈ us, v < M₀ + (gs ++ [(⟨GateOp.or, [w, u]⟩ : Gate)]).length := fun v hv => by
      have hv0 := hws v (by simp [hv])
      simp; omega
    rcases ih (gs ++ [⟨GateOp.or, [w, u]⟩]) (M₀ + gs.length) hgs1 hw1 hus with
      ⟨⟨tail, hres, hlen, hneg, hpos⟩, hgood, hout, heval⟩
    refine ⟨⟨⟨GateOp.or, [w, u]⟩ :: tail, by rw [hres]; simp, by simp [hlen], ?_, ?_⟩, hgood, hout, ?_⟩
    · simp only [negCount, List.filter_cons]
      have hne : GateOp.or ≠ GateOp.not := fun h => GateOp.noConfusion h
      rw [decide_eq_false hne]
      exact hneg
    · simp only [posCount, List.filter_cons, List.length_cons]
      have hne : GateOp.or ≠ GateOp.not := fun h => GateOp.noConfusion h
      rw [decide_eq_true hne]
      simpa [posCount] using hpos
    · intro X hX
      rw [heval X hX]
      have hlen1 : (run gs X).length = M₀ + gs.length := by rw [run_length, hX]
      have hstep : (run (gs ++ [⟨GateOp.or, [w, u]⟩]) X).getD (M₀ + gs.length) false =
          ((run gs X).getD w false || (run gs X).getD u false) := by
        rw [run_snoc, ← hlen1, getD_eq]
        simp [GateOp.eval]
      have hany : us.any (fun v => (run (gs ++ [⟨GateOp.or, [w, u]⟩]) X).getD v false) =
          us.any (fun v => (run gs X).getD v false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        exact exists_congr fun v => and_congr_right fun hv => by
          have hv0 := hws v (by simp [hv])
          rw [run_prefix gs [⟨GateOp.or, [w, u]⟩] X v (by rw [hX]; exact hv0)]
      rw [hstep, hany]
      simp [Bool.or_assoc]

private theorem pushOrList_props [DecidableEq GateOp] (M₀ cF : ℕ) (gs : List Gate) (ws : List ℕ)
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length) (hws : ∀ u ∈ ws, u < M₀ + gs.length) :
    let res := pushOrList M₀ cF gs ws
    (∃ tail, res.1 = gs ++ tail ∧ tail.length = ws.length - 1 ∧
      negCount tail = 0 ∧ posCount tail = ws.length - 1) ∧
    Good M₀ res.1 ∧ res.2 < M₀ + res.1.length ∧
    ∀ X : List Bool, X.length = M₀ → (run gs X).getD cF false = false →
      (run res.1 X).getD res.2 false = ws.any (fun u => (run gs X).getD u false) := by
  cases ws with
  | nil =>
    refine ⟨⟨[], by simp [pushOrList], rfl, negCount_nil, posCount_nil⟩, hgs, hcF, fun X _ hcFv => ?_⟩
    simpa [pushOrList] using hcFv
  | cons w ws =>
    simp only [pushOrList, List.length_cons, Nat.add_sub_cancel]
    have hw : w < M₀ + gs.length := hws w (by simp)
    have hws' : ∀ u ∈ ws, u < M₀ + gs.length := fun u hu => hws u (by simp [hu])
    rcases pushOrList_foldl_props M₀ ws gs w hgs hw hws' with ⟨hcount, hgood, hout, heval⟩
    refine ⟨hcount, hgood, hout, fun X hX _ => ?_⟩
    simpa using heval X hX

private def pushAndList (M₀ : ℕ) (gs : List Gate) : List (ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (a, b) :: ps =>
    let w := M₀ + gs.length
    let res := pushAndList M₀ (gs ++ [⟨GateOp.and, [a, b]⟩]) ps
    (res.1, w :: res.2)

private theorem pushAndList_props [DecidableEq GateOp] (M₀ : ℕ) (gs : List Gate)
    (ps : List (ℕ × ℕ)) (hgs : Good M₀ gs)
    (hps : ∀ p ∈ ps, p.1 < M₀ + gs.length ∧ p.2 < M₀ + gs.length) :
    let res := pushAndList M₀ gs ps
    (∃ tail, res.1 = gs ++ tail ∧ tail.length = ps.length ∧
      negCount tail = 0 ∧ posCount tail = ps.length) ∧
    res.2.length = ps.length ∧
    Good M₀ res.1 ∧
    (∀ w ∈ res.2, w < M₀ + res.1.length) ∧
    ∀ X : List Bool, X.length = M₀ → ∀ idx < ps.length,
      (run res.1 X).getD (res.2.getD idx 0) false =
        ((run gs X).getD (ps.getD idx (0, 0)).1 false &&
          (run gs X).getD (ps.getD idx (0, 0)).2 false) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [pushAndList], rfl, negCount_nil, posCount_nil⟩,
      rfl, hgs, by simp [pushAndList], fun _ _ _ h => by simp at h⟩
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    have ha : a < M₀ + gs.length := (hps (a, b) (by simp)).1
    have hb : b < M₀ + gs.length := (hps (a, b) (by simp)).2
    have hgs1 : Good M₀ (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) :=
      good_snoc hgs ⟨GateOp.and, [a, b]⟩ (by simp) (by simp)
        (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption)
    have hps1 : ∀ q ∈ ps, q.1 < M₀ + (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length ∧
        q.2 < M₀ + (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length := by
      intro q hq
      have hq0 := hps q (by simp [hq])
      simp; omega
    rcases ih (gs ++ [⟨GateOp.and, [a, b]⟩]) hgs1 hps1 with
      ⟨⟨tail, hres, hlen, hneg, hpos⟩, hlen2, hgood, hwmem, heval⟩
    refine ⟨⟨⟨GateOp.and, [a, b]⟩ :: tail, by dsimp only [pushAndList]; rw [hres]; simp,
      by simp [hlen], ?_, ?_⟩, ?_, hgood, ?_, ?_⟩
    · simp only [negCount, List.filter_cons]
      have hne : GateOp.and ≠ GateOp.not := fun h => GateOp.noConfusion h
      rw [decide_eq_false hne]
      exact hneg
    · simp only [posCount, List.filter_cons, List.length_cons]
      have hne : GateOp.and ≠ GateOp.not := fun h => GateOp.noConfusion h
      rw [decide_eq_true hne]
      simpa [posCount] using hpos
    · simp [pushAndList, hlen2]
    · intro w hw
      dsimp only [pushAndList] at hw ⊢
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [hres, List.length_append]; simp; omega
      · exact hwmem w hw
    · intro X hX idx hidx
      dsimp only [pushAndList]
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero]
        have hpref : (run (pushAndList M₀ (gs ++ [⟨GateOp.and, [a, b]⟩]) ps).1 X).getD (M₀ + gs.length) false =
            (run (gs ++ [⟨GateOp.and, [a, b]⟩]) X).getD (M₀ + gs.length) false := by
          rw [hres]
          exact run_prefix (gs ++ [⟨GateOp.and, [a, b]⟩]) tail X (M₀ + gs.length) (by rw [hX]; simp)
        rw [hpref, run_snoc]
        have hrlen : (run gs X).length = M₀ + gs.length := by rw [run_length, hX]
        rw [← hrlen, getD_eq]
        simp [GateOp.eval]
      | succ idx =>
        simp only [List.getD_cons_succ]
        rw [heval X hX idx (by simpa using hidx)]
        have ha1 : (ps.getD idx (0, 0)).1 < M₀ + gs.length := by
          have hmem : ps.getD idx (0, 0) ∈ ps := by
            have hlt : idx < ps.length := by simpa using hidx
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            exact List.getElem_mem hlt
          exact (hps _ (List.mem_cons_of_mem _ hmem)).1
        have hb1 : (ps.getD idx (0, 0)).2 < M₀ + gs.length := by
          have hmem : ps.getD idx (0, 0) ∈ ps := by
            have hlt : idx < ps.length := by simpa using hidx
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            exact List.getElem_mem hlt
          exact (hps _ (List.mem_cons_of_mem _ hmem)).2
        rw [run_prefix gs [⟨GateOp.and, [a, b]⟩] X _ (by rw [hX]; exact ha1),
          run_prefix gs [⟨GateOp.and, [a, b]⟩] X _ (by rw [hX]; exact hb1)]

private def remapLoop [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => (gs0, baseIn)
  | j + 1 =>
    let res := remapLoop d M₀ C baseIn notWire gs0 j
    let g := C.gates.getD j ⟨GateOp.or, []⟩
    if g.op = GateOp.not then
      (res.1, fun w => if w = d + 2 + j then notWire j else res.2 w)
    else
      let g' : Gate := ⟨g.op, g.inputs.map res.2⟩
      let out := M₀ + res.1.length
      (res.1 ++ [g'], fun w => if w = d + 2 + j then out else res.2 w)

private theorem remapLoop_prefix [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate) (n : ℕ) :
    ∀ w < d + 2 + n, ∀ m ≥ n, (remapLoop d M₀ C baseIn notWire gs0 m).2 w =
      (remapLoop d M₀ C baseIn notWire gs0 n).2 w := by
  intro w hw m hm
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn; rfl
  | succ m ih =>
    by_cases hmn : m ≥ n
    · have hne : w ≠ d + 2 + m := by omega
      dsimp only [remapLoop]
      split_ifs <;> simp [hne, ih hmn]
    · have hn : n = m + 1 := by omega
      subst hn; rfl

private theorem remapLoop_gs_prefix [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate) (n m : ℕ) (hnm : n ≤ m) :
    ∃ tail, (remapLoop d M₀ C baseIn notWire gs0 m).1 =
      (remapLoop d M₀ C baseIn notWire gs0 n).1 ++ tail := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn; exact ⟨[], by simp⟩
  | succ m ih =>
    by_cases hle : n ≤ m
    · rcases ih hle with ⟨tail, htail⟩
      dsimp only [remapLoop]
      split_ifs
      · exact ⟨tail, htail⟩
      · refine ⟨tail ++ [_], by rw [htail, List.append_assoc]⟩
    · have hn : n = m + 1 := by omega
      subst hn; exact ⟨[], by simp⟩

private theorem remapLoop_tail [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate) (n : ℕ) :
    ∃ tail, (remapLoop d M₀ C baseIn notWire gs0 n).1 = gs0 ++ tail ∧
      negCount tail = 0 ∧
      posCount tail = ((List.range n).filter (fun j =>
        decide ((C.gates.getD j ⟨GateOp.or, []⟩).op ≠ GateOp.not))).length := by
  induction n with
  | zero => exact ⟨[], by simp [remapLoop], negCount_nil, rfl⟩
  | succ n ih =>
    rcases ih with ⟨tail, hgs, hneg, hpos⟩
    dsimp only [remapLoop]
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hnot : (C.gates.getD n ⟨GateOp.or, []⟩).op = GateOp.not
    · simp only [hnot, ↓reduceIte, List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false,
        decide_false]
      exact ⟨tail, hgs, hneg, by simpa using hpos⟩
    · simp only [hnot, ↓reduceIte, List.filter_cons, List.filter_nil, ne_eq, not_false_eq_true,
        decide_true, List.length_singleton]
      set g' : Gate := ⟨(C.gates.getD n ⟨GateOp.or, []⟩).op,
        (C.gates.getD n ⟨GateOp.or, []⟩).inputs.map (remapLoop d M₀ C baseIn notWire gs0 n).2⟩
      refine ⟨tail ++ [g'], by rw [hgs, List.append_assoc], ?_, ?_⟩
      · rw [negCount_snoc_pos tail g' hnot]; exact hneg
      · rw [posCount_snoc_pos tail g' hnot, hpos]

private theorem remapLoop_posCount_full [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate) :
    ∃ tail, (remapLoop d M₀ C baseIn notWire gs0 C.size).1 = gs0 ++ tail ∧
      negCount tail = 0 ∧ posCount tail = C.size - PEqualNP.NotBracket.notCount C := by
  rcases remapLoop_tail d M₀ C baseIn notWire gs0 C.size with ⟨tail, htail, hneg, hpos⟩
  refine ⟨tail, htail, hneg, ?_⟩
  rw [hpos]
  have hsum : ((List.range C.size).filter (fun j =>
      decide ((C.gates.getD j ⟨GateOp.or, []⟩).op ≠ GateOp.not))).length +
      (notIdxList C).length = (List.range C.size).length := by
    dsimp only [notIdxList]
    induction C.size with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append, List.filter_append, List.length_append,
        List.length_append, List.length_append]
      simp only [List.filter_cons, List.filter_nil]
      by_cases h : (C.gates.getD n ⟨GateOp.or, []⟩).op = GateOp.not
      · have h1 : ¬ ((C.gates.getD n ⟨GateOp.or, []⟩).op ≠ GateOp.not) := not_not.mpr h
        rw [decide_eq_true h, decide_eq_false h1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil, List.length_singleton]
        omega
      · rw [decide_eq_false h, decide_eq_true h]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil, List.length_singleton]
        omega
  rw [List.length_range, notIdxList_length] at hsum
  omega

private theorem remapLoop_map_lt [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs0.length)
    (hnot : ∀ j < C.size, notWire j < M₀ + gs0.length) :
    ∀ n ≤ C.size, ∀ w < d + 2 + n,
      (remapLoop d M₀ C baseIn notWire gs0 n).2 w <
        M₀ + (remapLoop d M₀ C baseIn notWire gs0 n).1.length := by
  intro n hn
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rcases remapLoop_tail d M₀ C baseIn notWire gs0 n with ⟨tail, htail, _, _⟩
    have hlen_le : gs0.length ≤ (remapLoop d M₀ C baseIn notWire gs0 n).1.length := by
      rw [htail, List.length_append]; omega
    intro w hw
    dsimp only [remapLoop]
    by_cases hgate : (C.gates.getD n ⟨GateOp.or, []⟩).op = GateOp.not
    · simp only [hgate, ↓reduceIte]
      by_cases heq : w = d + 2 + n
      · rw [if_pos heq]; exact lt_of_lt_of_le (hnot n hn) (by omega)
      · rw [if_neg heq]; exact ih (Nat.le_of_succ_le hn) w (by omega)
    · simp only [hgate, ↓reduceIte, List.length_append, List.length_singleton]
      by_cases heq : w = d + 2 + n
      · rw [if_pos heq]; omega
      · rw [if_neg heq]; exact lt_trans (ih (Nat.le_of_succ_le hn) w (by omega)) (by omega)

private theorem remapLoop_good [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs0 : Good M₀ gs0)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs0.length)
    (hnot : ∀ j < C.size, notWire j < M₀ + gs0.length) :
    ∀ n ≤ C.size, Good M₀ (remapLoop d M₀ C baseIn notWire gs0 n).1 := by
  intro n hn
  induction n with
  | zero => exact hgs0
  | succ n ih =>
    have hgood := ih (Nat.le_of_succ_le hn)
    have hmap := remapLoop_map_lt d M₀ C baseIn notWire gs0 hbase hnot n (Nat.le_of_succ_le hn)
    dsimp only [remapLoop]
    by_cases hgate : (C.gates.getD n ⟨GateOp.or, []⟩).op = GateOp.not
    · simp only [hgate, ↓reduceIte]; exact hgood
    · simp only [hgate, ↓reduceIte]
      have hnC : n < C.gates.length := hn
      have hmem : C.gates.getD n ⟨GateOp.or, []⟩ ∈ C.gates := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnC]
        exact List.getElem_mem hnC
      rcases hfan _ hmem with ⟨hop, hlen⟩
      set g' : Gate := ⟨(C.gates.getD n ⟨GateOp.or, []⟩).op,
        (C.gates.getD n ⟨GateOp.or, []⟩).inputs.map (remapLoop d M₀ C baseIn notWire gs0 n).2⟩
      apply good_snoc hgood g' hop (by simpa [g'] using hlen)
      intro u hu
      simp only [g', List.mem_map] at hu
      rcases hu with ⟨i, hi, rfl⟩
      exact hmap i (hrb n hnC i hi)

private theorem remapLoop_eval [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hbaseB : ∀ w < d + 2, baseIn w < M₀ + gs0.length)
    (hnotB : ∀ j < C.size, notWire j < M₀ + gs0.length)
    (x : List Bool) (hx : x.length = d + 2)
    (X : List Bool) (hX : X.length = M₀)
    (hbaseEq : ∀ w < d + 2, (run gs0 X).getD (baseIn w) false = x.getD w false)
    (k : ℕ) (hk : k ≤ C.size)
    (hnotEq : ∀ j < k, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
      (run gs0 X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false) :
    ∀ n ≤ k, ∀ w < d + 2 + n,
      (run (remapLoop d M₀ C baseIn notWire gs0 n).1 X).getD
        ((remapLoop d M₀ C baseIn notWire gs0 n).2 w) false =
      (C.wires x).getD w false := by
  intro n hn
  induction n with
  | zero =>
    intro w hw
    dsimp only [remapLoop]
    rw [hbaseEq w hw]
    have hci : (C.wires x).getD w false = x.getD w false := by
      rw [circuit_wires_eq_run]
      exact run_input C.gates x w (by rw [hx]; exact hw)
    exact hci.symm
  | succ n ih =>
    intro w hw
    have ih' := ih (Nat.le_of_succ_le hn)
    rcases remapLoop_tail d M₀ C baseIn notWire gs0 n with ⟨tail, htail, _, _⟩
    have hmap := remapLoop_map_lt d M₀ C baseIn notWire gs0 hbaseB hnotB n (by omega)
    dsimp only [remapLoop]
    by_cases hgate : (C.gates.getD n ⟨GateOp.or, []⟩).op = GateOp.not
    · simp only [hgate, ↓reduceIte]
      by_cases heq : w = d + 2 + n
      · subst heq
        rw [if_pos rfl]
        have hpref : (run (remapLoop d M₀ C baseIn notWire gs0 n).1 X).getD (notWire n) false =
            (run gs0 X).getD (notWire n) false := by
          rw [htail]
          exact run_prefix gs0 tail X (notWire n) (by rw [hX]; exact hnotB n (by omega))
        rw [hpref]
        exact hnotEq n hn hgate
      · rw [if_neg heq]
        exact ih' w (by omega)
    · simp only [hgate, ↓reduceIte]
      by_cases heq : w = d + 2 + n
      · subst heq
        rw [if_pos rfl]
        have hrlen : (run (remapLoop d M₀ C baseIn notWire gs0 n).1 X).length =
            M₀ + (remapLoop d M₀ C baseIn notWire gs0 n).1.length := by
          rw [run_length, hX]
        rw [run_snoc, ← hrlen, getD_eq]
        have hnC : n < C.gates.length := Nat.lt_of_lt_of_le hn hk
        have hCgate : (C.wires x).getD (d + 2 + n) false =
            ((C.gates[n]).op.eval ((C.gates[n]).inputs.map fun i =>
              if i < d + 2 + n then (C.wires x).getD i false else false)) := by
          rw [circuit_wires_eq_run]
          have rg := run_gate C.gates x n hnC
          rw [hx] at rg
          exact rg
        have hgd : C.gates.getD n ⟨GateOp.or, []⟩ = C.gates[n] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnC]; rfl
        rw [hCgate, hgd]
        congr 1
        simp only [List.map_map]
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < d + 2 + n := by
          have hu' : u ∈ (C.gates.getD n ⟨GateOp.or, []⟩).inputs := by rwa [hgd]
          exact hrb n hnC u hu'
        rw [if_pos hu_lt]
        exact ih' u hu_lt
      · rw [if_neg heq]
        have hwlt : w < d + 2 + n := by omega
        have hpref : (run ((remapLoop d M₀ C baseIn notWire gs0 n).1 ++
            [⟨(C.gates.getD n ⟨GateOp.or, []⟩).op,
              (C.gates.getD n ⟨GateOp.or, []⟩).inputs.map
                (remapLoop d M₀ C baseIn notWire gs0 n).2⟩]) X).getD
            ((remapLoop d M₀ C baseIn notWire gs0 n).2 w) false =
            (run (remapLoop d M₀ C baseIn notWire gs0 n).1 X).getD
            ((remapLoop d M₀ C baseIn notWire gs0 n).2 w) false :=
          run_prefix _ [_] X _ (by rw [hX]; exact hmap w hwlt)
        rw [hpref]
        exact ih' w hwlt

private theorem remapLoop_eval_final [DecidableEq GateOp] (d M₀ : ℕ) (C : Circuit)
    (baseIn notWire : ℕ → ℕ) (gs0 : List Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hbaseB : ∀ w < d + 2, baseIn w < M₀ + gs0.length)
    (hnotB : ∀ j < C.size, notWire j < M₀ + gs0.length)
    (x : List Bool) (hx : x.length = d + 2)
    (X : List Bool) (hX : X.length = M₀)
    (hbaseEq : ∀ w < d + 2, (run gs0 X).getD (baseIn w) false = x.getD w false)
    (k : ℕ) (hk : k ≤ C.size)
    (hnotEq : ∀ j < k, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
      (run gs0 X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false) :
    ∀ w < d + 2 + k,
      (run (remapLoop d M₀ C baseIn notWire gs0 C.size).1 X).getD
        ((remapLoop d M₀ C baseIn notWire gs0 C.size).2 w) false =
      (C.wires x).getD w false := by
  intro w hw
  rw [remapLoop_prefix d M₀ C baseIn notWire gs0 k w hw C.size hk]
  rcases remapLoop_gs_prefix d M₀ C baseIn notWire gs0 k C.size hk with ⟨tail, htail⟩
  have hmap := remapLoop_map_lt d M₀ C baseIn notWire gs0 hbaseB hnotB k hk w hw
  rw [htail, run_prefix _ tail X _ (by rw [hX]; exact hmap)]
  exact remapLoop_eval d M₀ C baseIn notWire gs0 hrb hbaseB hnotB x hx X hX hbaseEq k hk hnotEq k le_rfl w hw

private def cmpAux [DecidableEq GateOp] (M₀ cT cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (r b : ℕ) (gs : List Gate) : ℕ → List Gate × ℕ
  | 0 => (gs, cT)
  | t + 1 =>
    let res := cmpAux M₀ cT cF C wmap notIdxs r b gs t
    let s := b - (t + 1)
    let j := notIdxs.getD s 0
    let g := C.gates.getD j ⟨GateOp.or, []⟩
    let inW := match g.inputs.head? with | some u => wmap u | none => cF
    let op := if bitAt r t then GateOp.and else GateOp.or
    (res.1 ++ [⟨op, [inW, res.2]⟩], M₀ + res.1.length)

private theorem cmpAux_tail [DecidableEq GateOp] (M₀ cT cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (r b : ℕ) (gs : List Gate) (t : ℕ) :
    ∃ tail, (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 = gs ++ tail ∧
      negCount tail = 0 ∧ posCount tail = t := by
  induction t with
  | zero => exact ⟨[], by simp [cmpAux], negCount_nil, posCount_nil⟩
  | succ t ih =>
    rcases ih with ⟨tail, hgs, hneg, hpos⟩
    dsimp only [cmpAux]
    set op := if bitAt r t then GateOp.and else GateOp.or
    have hop : op ≠ GateOp.not := by
      dsimp [op]
      cases bitAt r t
      · exact fun h => GateOp.noConfusion h
      · exact fun h => GateOp.noConfusion h
    set res := cmpAux M₀ cT cF C wmap notIdxs r b gs t
    set j := notIdxs.getD (b - (t + 1)) 0
    set g := C.gates.getD j ⟨GateOp.or, []⟩
    set inW := match g.inputs.head? with | some u => wmap u | none => cF
    set gNew : Gate := ⟨op, [inW, res.2]⟩
    refine ⟨tail ++ [gNew], by rw [hgs, List.append_assoc], ?_, ?_⟩
    · rw [negCount_snoc_pos tail gNew hop]; exact hneg
    · rw [posCount_snoc_pos tail gNew hop, hpos]

private theorem cmpAux_good [DecidableEq GateOp] (d M₀ cT cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (r b : ℕ) (gs : List Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs) (hcT : cT < M₀ + gs.length) (hcF : cF < M₀ + gs.length)
    (hmap : ∀ w < d + 2 + C.size, wmap w < M₀ + gs.length)
    (hidxs : ∀ s < b, notIdxs.getD s 0 < C.size) :
    ∀ t ≤ b, Good M₀ (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 ∧
      (cmpAux M₀ cT cF C wmap notIdxs r b gs t).2 < M₀ + (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1.length := by
  intro t ht
  induction t with
  | zero => exact ⟨hgs, hcT⟩
  | succ t ih =>
    rcases ih (Nat.le_of_succ_le ht) with ⟨hgood, hout⟩
    rcases cmpAux_tail M₀ cT cF C wmap notIdxs r b gs t with ⟨tail, htail, _, _⟩
    have hlen_le : gs.length ≤ (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1.length := by
      rw [htail, List.length_append]; omega
    dsimp only [cmpAux]
    set res := cmpAux M₀ cT cF C wmap notIdxs r b gs t
    set s := b - (t + 1)
    have hs : s < b := by omega
    have hj : notIdxs.getD s 0 < C.size := hidxs s hs
    set j := notIdxs.getD s 0
    set g := C.gates.getD j ⟨GateOp.or, []⟩
    set inW := match g.inputs.head? with | some u => wmap u | none => cF
    have hinW : inW < M₀ + res.1.length := by
      dsimp only [inW]
      cases hhead : g.inputs.head? with
      | none => exact lt_of_lt_of_le hcF (by omega)
      | some u =>
        have hu_mem : u ∈ g.inputs := List.mem_of_mem_head? hhead
        have hu_lt : u < d + 2 + j := hrb j hj u hu_mem
        exact lt_of_lt_of_le (hmap u (by omega)) (by omega)
    set op := if bitAt r t then GateOp.and else GateOp.or
    have hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
      dsimp [op]; split_ifs <;> simp
    set gNew : Gate := ⟨op, [inW, res.2]⟩
    have hgood' : Good M₀ (res.1 ++ [gNew]) :=
      good_snoc hgood gNew hop (by simp [gNew])
        (fun i hi => by simp [gNew] at hi; rcases hi with rfl | rfl <;> assumption)
    exact ⟨hgood', by simp⟩

private def cmpInWire [DecidableEq GateOp] (cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (b t : ℕ) : ℕ :=
  let j := notIdxs.getD (b - (t + 1)) 0
  let g := C.gates.getD j ⟨GateOp.or, []⟩
  match g.inputs.head? with | some u => wmap u | none => cF

private theorem cmpAux_eval_eq [DecidableEq GateOp] (M₀ cT cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (r b : ℕ) (gs : List Gate)
    (X : List Bool) (hX : X.length = M₀)
    (hcT : (run gs X).getD cT false = true)
    (hinB : ∀ t < b, cmpInWire cF C wmap notIdxs b t < M₀ + gs.length)
    (hinEq : ∀ t < b, (run gs X).getD (cmpInWire cF C wmap notIdxs b t) false = bitAt r t) :
    ∀ t ≤ b, (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
      (cmpAux M₀ cT cF C wmap notIdxs r b gs t).2 false = true := by
  intro t ht
  induction t with
  | zero => exact hcT
  | succ t ih =>
    have ih' := ih (Nat.le_of_succ_le ht)
    rcases cmpAux_tail M₀ cT cF C wmap notIdxs r b gs t with ⟨tail, htail, _, _⟩
    dsimp only [cmpAux]
    have hlen : (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).length =
        M₀ + (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1.length := by
      rw [run_length, hX]
    rw [run_snoc, ← hlen, getD_eq]
    have hin : (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
        (cmpInWire cF C wmap notIdxs b t) false = bitAt r t := by
      rw [htail, run_prefix gs tail X _ (by rw [hX]; exact hinB t ht), hinEq t ht]
    change (if bitAt r t then GateOp.and else GateOp.or).eval
      [(run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD (cmpInWire cF C wmap notIdxs b t) false,
        (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
          (cmpAux M₀ cT cF C wmap notIdxs r b gs t).2 false] = true
    rw [hin, ih']
    cases bitAt r t <;> simp [GateOp.eval]

private theorem cmpAux_eval_mismatch [DecidableEq GateOp] (M₀ cT cF : ℕ) (C : Circuit) (wmap : ℕ → ℕ)
    (notIdxs : List ℕ) (r b : ℕ) (gs : List Gate)
    (X : List Bool) (hX : X.length = M₀)
    (hinB : ∀ t < b, cmpInWire cF C wmap notIdxs b t < M₀ + gs.length)
    (tStar : ℕ) (htStar : tStar < b)
    (hhi : ∀ t, tStar < t → t < b →
      (run gs X).getD (cmpInWire cF C wmap notIdxs b t) false = bitAt r t)
    (hne : (run gs X).getD (cmpInWire cF C wmap notIdxs b tStar) false ≠ bitAt r tStar) :
    ∀ t, tStar + 1 ≤ t → t ≤ b →
      (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
        (cmpAux M₀ cT cF C wmap notIdxs r b gs t).2 false =
      (run gs X).getD (cmpInWire cF C wmap notIdxs b tStar) false := by
  intro t hlo hhi_b
  induction t with
  | zero => omega
  | succ t ih =>
    rcases cmpAux_tail M₀ cT cF C wmap notIdxs r b gs t with ⟨tail, htail, _, _⟩
    dsimp only [cmpAux]
    have hlen : (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).length =
        M₀ + (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1.length := by
      rw [run_length, hX]
    rw [run_snoc, ← hlen, getD_eq]
    have hin : (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
        (cmpInWire cF C wmap notIdxs b t) false =
        (run gs X).getD (cmpInWire cF C wmap notIdxs b t) false := by
      rw [htail, run_prefix gs tail X _ (by rw [hX]; exact hinB t hhi_b)]
    change (if bitAt r t then GateOp.and else GateOp.or).eval
      [(run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD (cmpInWire cF C wmap notIdxs b t) false,
        (run (cmpAux M₀ cT cF C wmap notIdxs r b gs t).1 X).getD
          (cmpAux M₀ cT cF C wmap notIdxs r b gs t).2 false] =
      (run gs X).getD (cmpInWire cF C wmap notIdxs b tStar) false
    rw [hin]
    by_cases heq : t = tStar
    · subst heq
      cases hval : (run gs X).getD (cmpInWire cF C wmap notIdxs b t) false <;>
        cases hr : bitAt r t
      · exfalso; exact hne (hval.trans hr.symm)
      · simp [GateOp.eval]
      · simp [GateOp.eval]
      · exfalso; exact hne (hval.trans hr.symm)
    · have hgt : tStar < t := by omega
      have ih' := ih (by omega) (by omega)
      rw [ih', hhi t hgt hhi_b]
      cases bitAt r t <;> simp [GateOp.eval]

private theorem flatten_ofFn_length {k m : ℕ} (f : Fin k → List Bool)
    (hf : ∀ j, (f j).length = m) :
    (List.ofFn f).flatten.length = k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.flatten_singleton,
      List.length_append, ih (fun j => f j.castSucc) (fun j => hf _), hf (Fin.last k)]
    ring

private theorem getD_flatten_ofFn {k m : ℕ} (f : Fin k → List Bool)
    (hf : ∀ j, (f j).length = m) (j : Fin k) (r : ℕ) (hr : r < m) :
    (List.ofFn f).flatten.getD (j.val * m + r) false = (f j).getD r false := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.flatten_singleton]
    have hlen : (List.ofFn (fun u : Fin k => f u.castSucc)).flatten.length = k * m :=
      flatten_ofFn_length _ (fun u => hf _)
    by_cases hj : j.val < k
    · have hidx : j.val * m + r < (List.ofFn (fun u : Fin k => f u.castSucc)).flatten.length := by
        rw [hlen]
        have : j.val + 1 ≤ k := hj
        calc j.val * m + r < j.val * m + m := by omega
          _ = (j.val + 1) * m := by ring
          _ ≤ k * m := Nat.mul_le_mul_right m this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hidx, ← List.getD_eq_getElem?_getD]
      have heq : j = (⟨j.val, hj⟩ : Fin k).castSucc := Fin.ext rfl
      rw [heq]
      exact ih (fun u => f u.castSucc) (fun u => hf _) ⟨j.val, hj⟩
    · have hj_lt : j.val < k + 1 := j.isLt
      have hj_eq : j = Fin.last k := Fin.ext (by simp [Fin.val_last]; omega)
      subst hj_eq
      simp only [Fin.val_last]
      have hge : (List.ofFn (fun u : Fin k => f u.castSucc)).flatten.length ≤ k * m + r := by
        rw [hlen]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hlen,
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

private def decodeStep (M₀ cF : ℕ) (T : List ℕ) (r : ℕ) (gs : List Gate) (I : List ℕ) :
    List Gate × List ℕ :=
  let queries := (List.range I.length).map (fun c =>
    (I.getD c cF, T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF))
  let res1 := pushAndList M₀ gs queries
  let res2 := pushOrList M₀ cF res1.1 res1.2
  let nbit := M₀ + res2.1.length
  let gs3 := res2.1 ++ [⟨GateOp.not, [res2.2]⟩]
  let expands := I.flatMap (fun Ic => [(Ic, nbit), (Ic, res2.2)])
  pushAndList M₀ gs3 expands

private def decodeTree (M₀ cF cT : ℕ) (T : List ℕ) (B : ℕ) (gs : List Gate) :
    ℕ → List Gate × List ℕ
  | 0 => (gs, [cT])
  | ℓ + 1 =>
    let res := decodeTree M₀ cF cT T B gs ℓ
    decodeStep M₀ cF T (B - (ℓ + 1)) res.1 res.2

private theorem decodeStep_props [DecidableEq GateOp] (M₀ cF : ℕ) (T : List ℕ) (r : ℕ)
    (gs : List Gate) (I : List ℕ)
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hI : ∀ w ∈ I, w < M₀ + gs.length)
    (hT : ∀ w ∈ T, w < M₀ + gs.length) :
    let res := decodeStep M₀ cF T r gs I
    (∃ tail, res.1 = gs ++ tail ∧ negCount tail = 1 ∧
      posCount tail = 3 * I.length + (I.length - 1)) ∧
    res.2.length = 2 * I.length ∧
    Good M₀ res.1 ∧
    (∀ w ∈ res.2, w < M₀ + res.1.length) := by
  dsimp only [decodeStep]
  set queries := (List.range I.length).map (fun c =>
    (I.getD c cF, T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF))
  have hqB : ∀ p ∈ queries, p.1 < M₀ + gs.length ∧ p.2 < M₀ + gs.length := by
    intro p hp
    simp only [queries, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨c, hc, rfl⟩
    constructor
    · exact hI _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; exact List.getElem_mem hc)
    · by_cases hct : c * 2 ^ (r + 1) + 2 ^ r < T.length
      · have hmem : T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF ∈ T := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hct]; exact List.getElem_mem hct
        exact hT _ hmem
      · have hnone : T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hct), Option.getD_none]
        dsimp only
        rw [hnone]
        exact hcF
  rcases pushAndList_props M₀ gs queries hgs hqB with
    ⟨⟨t1, ht1, _, hn1, hp1⟩, hlen1, hg1, hm1, _⟩
  set res1 := pushAndList M₀ gs queries
  have hl1 : gs.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
  rcases pushOrList_props M₀ cF res1.1 res1.2 hg1 (by omega) hm1 with
    ⟨⟨t2, ht2, _, hn2, hp2⟩, hg2, hw2, _⟩
  set res2 := pushOrList M₀ cF res1.1 res1.2
  have hl2 : res1.1.length ≤ res2.1.length := by rw [ht2, List.length_append]; omega
  set nbit := M₀ + res2.1.length
  set gs3 := res2.1 ++ [⟨GateOp.not, [res2.2]⟩]
  have hg3 : Good M₀ gs3 := good_snoc hg2 ⟨GateOp.not, [res2.2]⟩ (by simp) (by simp)
    (fun u hu => by simp at hu; subst hu; exact hw2)
  set expands := I.flatMap (fun Ic => [(Ic, nbit), (Ic, res2.2)])
  have hexB : ∀ p ∈ expands, p.1 < M₀ + gs3.length ∧ p.2 < M₀ + gs3.length := by
    intro p hp
    simp only [expands, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨Ic, hIc, rfl | rfl⟩
    · refine ⟨lt_of_lt_of_le (hI Ic hIc) (by simp [gs3]; omega), ?_⟩
      simp only [gs3, List.length_append, List.length_singleton, nbit]; omega
    · refine ⟨lt_of_lt_of_le (hI Ic hIc) (by simp [gs3]; omega),
        lt_trans hw2 (by simp only [gs3, List.length_append, List.length_singleton]; omega)⟩
  rcases pushAndList_props M₀ gs3 expands hg3 hexB with
    ⟨⟨t4, ht4, _, hn4, hp4⟩, hlen4, hg4, hm4, _⟩
  have hqlen : queries.length = I.length := by simp [queries]
  have helen : expands.length = 2 * I.length := by
    clear hlen4 hg4 hm4 hexB hg3
    induction I with
    | nil => simp [expands]
    | cons a as ih => simp [expands] at ih ⊢; omega
  refine ⟨⟨t1 ++ t2 ++ [⟨GateOp.not, [res2.2]⟩] ++ t4, ?_, ?_, ?_⟩, ?_, hg4, hm4⟩
  · rw [ht4]; simp only [gs3]; rw [ht2, ht1]; simp [List.append_assoc]
  · have hn_not : negCount [⟨GateOp.not, [res2.2]⟩] = 1 := by
      dsimp only [negCount]; rw [List.filter_cons, decide_eq_true rfl]; rfl
    rw [negCount_append, negCount_append, negCount_append, hn1, hn2, hn_not, hn4]
  · have hp_not : posCount [⟨GateOp.not, [res2.2]⟩] = 0 := by
      dsimp only [posCount]; rw [List.filter_cons, decide_eq_false (not_not.mpr rfl)]; rfl
    rw [posCount_append, posCount_append, posCount_append, hp1, hp2, hp_not, hp4, hlen1, hqlen, helen]
    omega
  · rw [hlen4, helen]

private theorem decodeTree_props [DecidableEq GateOp] (M₀ cF cT : ℕ) (T : List ℕ) (B : ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hcT : cT < M₀ + gs.length) (hT : ∀ w ∈ T, w < M₀ + gs.length) :
    ∀ ℓ ≤ B,
      let res := decodeTree M₀ cF cT T B gs ℓ
      (∃ tail, res.1 = gs ++ tail ∧ negCount tail = ℓ ∧ posCount tail ≤ 4 * (2 ^ ℓ - 1)) ∧
      res.2.length = 2 ^ ℓ ∧
      Good M₀ res.1 ∧
      (∀ w ∈ res.2, w < M₀ + res.1.length) := by
  intro ℓ hℓ
  induction ℓ with
  | zero =>
    refine ⟨⟨[], by simp [decodeTree], negCount_nil, by simp [posCount_nil]⟩,
      by simp [decodeTree], hgs, fun w hw => by simp [decodeTree] at hw; subst hw; exact hcT⟩
  | succ ℓ ih =>
    rcases ih (Nat.le_of_succ_le hℓ) with ⟨⟨t1, ht1, hn1, hp1⟩, hlen1, hg1, hm1⟩
    set res := decodeTree M₀ cF cT T B gs ℓ
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    rcases decodeStep_props M₀ cF T (B - (ℓ + 1)) res.1 res.2 hg1 (by omega) hm1
        (fun w hw => lt_of_lt_of_le (hT w hw) (by omega)) with
      ⟨⟨t2, ht2, hn2, hp2⟩, hlen2, hg2, hm2⟩
    refine ⟨⟨t1 ++ t2, by dsimp only [decodeTree]; rw [ht2, ht1, List.append_assoc],
      by rw [negCount_append, hn1, hn2], ?_⟩, ?_, hg2, hm2⟩
    · rw [hlen1] at hp2
      have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_pow ℓ 2 (by positivity)
      have hpow2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [posCount_append]
      calc posCount t1 + posCount t2
          ≤ 4 * (2 ^ ℓ - 1) + (3 * 2 ^ ℓ + (2 ^ ℓ - 1)) := Nat.add_le_add hp1 (le_of_eq hp2)
        _ ≤ 4 * (2 ^ (ℓ + 1) - 1) := by rw [hpow2]; omega
    · dsimp only [decodeTree]
      rw [hlen2, hlen1, Nat.pow_succ']

private theorem decodeStep_eval [DecidableEq GateOp] (M₀ cF : ℕ) (T : List ℕ) (r : ℕ)
    (gs : List Gate) (I : List ℕ)
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hI : ∀ w ∈ I, w < M₀ + gs.length)
    (hT : ∀ w ∈ T, w < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (k : ℕ) (hIlen : I.length = 2 ^ k)
    (uStar : ℕ) (huStar : uStar < 2 ^ (k + r + 1))
    (hTlen : 2 ^ (k + r + 1) ≤ T.length)
    (hTval : ∀ u < 2 ^ (k + r + 1), (run gs X).getD (T.getD u cF) false = decide (u ≤ uStar))
    (hIval : ∀ c < 2 ^ k, (run gs X).getD (I.getD c cF) false = decide (uStar / 2 ^ (r + 1) = c)) :
    let res := decodeStep M₀ cF T r gs I
    ∀ c < 2 ^ (k + 1),
      (run res.1 X).getD (res.2.getD c cF) false = decide (uStar / 2 ^ r = c) := by
  dsimp only [decodeStep]
  set queries := (List.range I.length).map (fun c =>
    (I.getD c cF, T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF))
  have hqB : ∀ p ∈ queries, p.1 < M₀ + gs.length ∧ p.2 < M₀ + gs.length := by
    intro p hp
    simp only [queries, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨c, hc, rfl⟩
    constructor
    · exact hI _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; exact List.getElem_mem hc)
    · by_cases hct : c * 2 ^ (r + 1) + 2 ^ r < T.length
      · have hmem : T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF ∈ T := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hct]; exact List.getElem_mem hct
        exact hT _ hmem
      · have hnone : T.getD (c * 2 ^ (r + 1) + 2 ^ r) cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hct), Option.getD_none]
        dsimp only
        rw [hnone]
        exact hcF
  rcases pushAndList_props M₀ gs queries hgs hqB with
    ⟨⟨t1, ht1, _, _, _⟩, hlen1, hg1, hm1, heval1⟩
  set res1 := pushAndList M₀ gs queries
  have hl1 : gs.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
  rcases pushOrList_props M₀ cF res1.1 res1.2 hg1 (by omega) hm1 with
    ⟨⟨t2, ht2, _, _, _⟩, hg2, hw2, heval2⟩
  set res2 := pushOrList M₀ cF res1.1 res1.2
  have hl2 : res1.1.length ≤ res2.1.length := by rw [ht2, List.length_append]; omega
  set nbit := M₀ + res2.1.length
  set gs3 := res2.1 ++ [⟨GateOp.not, [res2.2]⟩]
  have hg3 : Good M₀ gs3 := good_snoc hg2 ⟨GateOp.not, [res2.2]⟩ (by simp) (by simp)
    (fun u hu => by simp at hu; subst hu; exact hw2)
  set expands := I.flatMap (fun Ic => [(Ic, nbit), (Ic, res2.2)])
  have hexB : ∀ p ∈ expands, p.1 < M₀ + gs3.length ∧ p.2 < M₀ + gs3.length := by
    intro p hp
    simp only [expands, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨Ic, hIc, rfl | rfl⟩
    · refine ⟨lt_of_lt_of_le (hI Ic hIc) (by simp [gs3]; omega), ?_⟩
      simp only [gs3, List.length_append, List.length_singleton, nbit]; omega
    · refine ⟨lt_of_lt_of_le (hI Ic hIc) (by simp [gs3]; omega),
        lt_trans hw2 (by simp only [gs3, List.length_append, List.length_singleton]; omega)⟩
  rcases pushAndList_props M₀ gs3 expands hg3 hexB with
    ⟨⟨t4, ht4, _, _, _⟩, hlen4, hg4, hm4, heval4⟩
  set cStar := uStar / 2 ^ (r + 1)
  have hcStar : cStar < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc uStar < 2 ^ (k + r + 1) := huStar
      _ = 2 ^ k * 2 ^ (r + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
  have hpow_split : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ']
  have hbit_eq : (run res2.1 X).getD res2.2 false = decide ((uStar / 2 ^ r) % 2 = 1) := by
    have hcFv1 : (run res1.1 X).getD cF false = false := by
      rw [ht1, run_prefix gs t1 X cF (by rw [hX]; exact hcF), hcFv]
    rw [heval2 X hX hcFv1]
    have hq_val : ∀ idx < res1.2.length,
        (run res1.1 X).getD (res1.2.getD idx cF) false =
          decide (idx = cStar ∧ (uStar / 2 ^ r) % 2 = 1) := by
      intro idx hidx
      rw [hlen1] at hidx
      have hidx' : idx < queries.length := hidx
      have hc_lt : idx < 2 ^ k := by simpa [queries, hIlen] using hidx'
      have he1 := heval1 X hX idx hidx'
      have hgetd : res1.2.getD idx cF = res1.2.getD idx 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hlen1]; exact hidx')]
        rfl
      rw [hgetd, he1]
      have hqget : queries.getD idx (0, 0) =
          (I.getD idx cF, T.getD (idx * 2 ^ (r + 1) + 2 ^ r) cF) := by
        dsimp only [queries]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by rw [hIlen]; exact hc_lt)]
        rfl
      rw [hqget, hIval idx hc_lt]
      have hu_lt : idx * 2 ^ (r + 1) + 2 ^ r < 2 ^ (k + r + 1) := by
        have h1 : idx + 1 ≤ 2 ^ k := hc_lt
        have hpos_r : 0 < 2 ^ r := by positivity
        calc idx * 2 ^ (r + 1) + 2 ^ r
            < idx * 2 ^ (r + 1) + 2 ^ (r + 1) := by rw [hpow_split]; omega
          _ = (idx + 1) * 2 ^ (r + 1) := by ring
          _ ≤ 2 ^ k * 2 ^ (r + 1) := Nat.mul_le_mul_right _ h1
          _ = 2 ^ (k + r + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
      rw [hTval _ hu_lt]
      by_cases hcs : idx = cStar
      · subst hcs
        have hed := Nat.div_add_mod uStar (2 ^ (r + 1))
        have hmod_lt : uStar % 2 ^ (r + 1) < 2 ^ (r + 1) := Nat.mod_lt _ (by positivity)
        have hpos_r : 0 < 2 ^ r := Nat.pow_pos (by omega)
        have hdiv_r : uStar / 2 ^ r = 2 * cStar + (uStar % 2 ^ (r + 1)) / 2 ^ r := by
          have h1 : uStar = uStar % 2 ^ (r + 1) + 2 ^ r * (2 * cStar) := by
            calc uStar = 2 ^ (r + 1) * cStar + uStar % 2 ^ (r + 1) := hed.symm
              _ = uStar % 2 ^ (r + 1) + 2 ^ r * (2 * cStar) := by rw [hpow_split]; ring
          conv_lhs => rw [h1, Nat.add_mul_div_left _ _ hpos_r]
          omega
        have hmod_le : cStar * 2 ^ (r + 1) + 2 ^ r ≤ uStar ↔ 2 ^ r ≤ uStar % 2 ^ (r + 1) := by
          have hed' : cStar * 2 ^ (r + 1) + uStar % 2 ^ (r + 1) = uStar := by
            rw [Nat.mul_comm]; exact hed
          omega
        have hbit_r : (2 ^ r ≤ uStar % 2 ^ (r + 1)) ↔ (uStar / 2 ^ r) % 2 = 1 := by
          rw [hdiv_r]
          rcases Nat.lt_or_ge (uStar % 2 ^ (r + 1)) (2 ^ r) with hlt | hge
          · have hq0 : (uStar % 2 ^ (r + 1)) / 2 ^ r = 0 := Nat.div_eq_of_lt hlt
            rw [hq0]; omega
          · have hlt2 : uStar % 2 ^ (r + 1) < 2 * 2 ^ r := by rw [← hpow_split]; exact hmod_lt
            have hq1 : (uStar % 2 ^ (r + 1)) / 2 ^ r = 1 := by
              have ha : 1 ≤ (uStar % 2 ^ (r + 1)) / 2 ^ r :=
                (Nat.le_div_iff_mul_le hpos_r).mpr (by simpa using hge)
              have hb : (uStar % 2 ^ (r + 1)) / 2 ^ r < 2 :=
                (Nat.div_lt_iff_lt_mul hpos_r).mpr (by simpa [Nat.mul_comm] using hlt2)
              omega
            rw [hq1]; omega
        simp [hmod_le, hbit_r]
      · have hcs' : ¬ cStar = idx := Ne.symm hcs
        simp [hcs, hcs']
    have hcStar_idx : cStar < res1.2.length := by rw [hlen1]; simpa [queries, hIlen] using hcStar
    cases hbit : decide ((uStar / 2 ^ r) % 2 = 1)
    · apply Bool.eq_false_iff.mpr
      intro htrue
      rw [List.any_eq_true] at htrue
      rcases htrue with ⟨w, hw, hval⟩
      rcases List.mem_iff_getElem.mp hw with ⟨idx, hidx, rfl⟩
      have hidx' : idx < res1.2.length := hidx
      have hgetd : res1.2[idx] = res1.2.getD idx cF := by
        symm; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx']; rfl
      rw [hgetd, hq_val idx hidx'] at hval
      simp at hval
      rw [hval.2] at hbit
      simp at hbit
    · rw [List.any_eq_true]
      refine ⟨res1.2[cStar], List.getElem_mem hcStar_idx, ?_⟩
      have hgetd : res1.2[cStar] = res1.2.getD cStar cF := by
        symm; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcStar_idx]; rfl
      rw [hgetd, hq_val cStar hcStar_idx]
      simp [of_decide_eq_true hbit]
  have hnbit_eq : (run gs3 X).getD nbit false = !decide ((uStar / 2 ^ r) % 2 = 1) := by
    have hrlen2 : (run res2.1 X).length = M₀ + res2.1.length := by rw [run_length, hX]
    dsimp only [gs3, nbit]
    rw [run_snoc, ← hrlen2, getD_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [hbit_eq]
  have hbit_eq3 : (run gs3 X).getD res2.2 false = decide ((uStar / 2 ^ r) % 2 = 1) := by
    dsimp only [gs3]
    rw [run_prefix res2.1 [⟨GateOp.not, [res2.2]⟩] X res2.2 (by rw [hX]; exact hw2), hbit_eq]
  have helen : expands.length = 2 * I.length := by
    clear heval4 hlen4 hm4 hg4 hexB
    induction I with
    | nil => simp [expands]
    | cons a as ih => simp [expands] at ih ⊢; omega
  have hexp_getD : ∀ c < I.length,
      expands.getD (2 * c) (0, 0) = (I.getD c 0, nbit) ∧
      expands.getD (2 * c + 1) (0, 0) = (I.getD c 0, res2.2) := by
    have hgen : ∀ (I' : List ℕ) (c : ℕ), c < I'.length →
        (I'.flatMap (fun w => [(w, nbit), (w, res2.2)])).getD (2 * c) (0, 0) = (I'.getD c 0, nbit) ∧
        (I'.flatMap (fun w => [(w, nbit), (w, res2.2)])).getD (2 * c + 1) (0, 0) = (I'.getD c 0, res2.2) := by
      intro I'
      induction I' with
      | nil => intro c hc; simp at hc
      | cons a as ih =>
        intro c hc
        rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append]
        cases c with
        | zero => simp
        | succ c =>
          have h1 : 2 * (c + 1) = 2 * c + 2 := by omega
          have h2 : 2 * c + 2 + 1 = 2 * c + 1 + 2 := by omega
          rw [h1, h2]
          exact ih c (by simpa using hc)
    exact hgen I
  intro c hc
  have hc' : c < 2 * 2 ^ k := by rw [← Nat.pow_succ']; exact hc
  have hidx_lt : c < expands.length := by rw [helen, hIlen]; exact hc'
  have hgetd : (pushAndList M₀ gs3 expands).2.getD c cF =
      (pushAndList M₀ gs3 expands).2.getD c 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlen4]; exact hidx_lt)]
    rfl
  rw [hgetd, heval4 X hX c hidx_lt]
  have hI_pref : ∀ q < I.length, (run gs3 X).getD (I.getD q 0) false =
      (run gs X).getD (I.getD q cF) false := by
    intro q hq
    have hmem : I.getD q 0 ∈ I := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; exact List.getElem_mem hq
    have hget_eq : I.getD q 0 = I.getD q cF := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
    have hB : I.getD q 0 < M₀ + gs.length := hI _ hmem
    have hgs3_tail : gs3 = gs ++ (t1 ++ t2 ++ [⟨GateOp.not, [res2.2]⟩]) := by
      dsimp only [gs3]; rw [ht2, ht1]; simp [List.append_assoc]
    rw [hgs3_tail, run_prefix gs _ X _ (by rw [hX]; exact hB), hget_eq]
  have hdiv_eq : uStar / 2 ^ (r + 1) = (uStar / 2 ^ r) / 2 := by
    rw [hpow_split, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hdiv2 : uStar / 2 ^ r = 2 * cStar + (uStar / 2 ^ r) % 2 := by
    dsimp only [cStar]; rw [hdiv_eq]; exact (Nat.div_add_mod _ 2).symm
  rcases Nat.even_or_odd' c with ⟨q, rfl | rfl⟩
  · have hq : q < I.length := by rw [hIlen]; omega
    rw [(hexp_getD q hq).1, hI_pref q hq, hIval q (by rw [← hIlen]; exact hq), hnbit_eq]
    have hm2 : (uStar / 2 ^ r) % 2 < 2 := Nat.mod_lt _ (by positivity)
    by_cases hcs : cStar = q <;> by_cases hodd : (uStar / 2 ^ r) % 2 = 1 <;>
      simp [hcs, hodd] <;> omega
  · have hq : q < I.length := by rw [hIlen]; omega
    rw [(hexp_getD q hq).2, hI_pref q hq, hIval q (by rw [← hIlen]; exact hq), hbit_eq3]
    have hm2 : (uStar / 2 ^ r) % 2 < 2 := Nat.mod_lt _ (by positivity)
    by_cases hcs : cStar = q <;> by_cases hodd : (uStar / 2 ^ r) % 2 = 1 <;>
      simp [hcs, hodd] <;> omega

private theorem decodeTree_eval [DecidableEq GateOp] (M₀ cF cT : ℕ) (T : List ℕ) (B : ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hcT : cT < M₀ + gs.length) (hT : ∀ w ∈ T, w < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (hcTv : (run gs X).getD cT false = true)
    (uStar : ℕ) (huStar : uStar < 2 ^ B) (hTlen : 2 ^ B ≤ T.length)
    (hTval : ∀ u < 2 ^ B, (run gs X).getD (T.getD u cF) false = decide (u ≤ uStar)) :
    ∀ ℓ ≤ B,
      let res := decodeTree M₀ cF cT T B gs ℓ
      ∀ c < 2 ^ ℓ, (run res.1 X).getD (res.2.getD c cF) false = decide (uStar / 2 ^ (B - ℓ) = c) := by
  intro ℓ hℓ
  induction ℓ with
  | zero =>
    intro _ c hc
    have hc0 : c = 0 := Nat.lt_one_iff.mp hc
    subst hc0
    change (run (decodeTree M₀ cF cT T B gs 0).1 X).getD ((decodeTree M₀ cF cT T B gs 0).2.getD 0 cF) false =
      decide (uStar / 2 ^ (B - 0) = 0)
    have hdiv0 : uStar / 2 ^ (B - 0) = 0 := Nat.div_eq_of_lt (by simpa using huStar)
    simp only [decodeTree, List.getD_cons_zero, hcTv, hdiv0]
    rfl
  | succ ℓ ih =>
    have ih' := ih (Nat.le_of_succ_le hℓ)
    rcases decodeTree_props M₀ cF cT T B gs hgs hcF hcT hT ℓ (Nat.le_of_succ_le hℓ) with
      ⟨⟨t1, ht1, _, _⟩, hlen1, hg1, hm1⟩
    set res := decodeTree M₀ cF cT T B gs ℓ
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    have hpref : ∀ w < M₀ + gs.length, (run res.1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    have hpow_eq : ℓ + (B - (ℓ + 1)) + 1 = B := by omega
    have hTval1 : ∀ u < 2 ^ (ℓ + (B - (ℓ + 1)) + 1),
        (run res.1 X).getD (T.getD u cF) false = decide (u ≤ uStar) := by
      intro u hu
      rw [hpow_eq] at hu
      have huB := hTval u hu
      have huT : u < T.length := lt_of_lt_of_le hu hTlen
      have hmem : T.getD u cF ∈ T := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem huT]; exact List.getElem_mem huT
      rw [hpref _ (hT _ hmem), huB]
    have hIval1 : ∀ c < 2 ^ ℓ,
        (run res.1 X).getD (res.2.getD c cF) false = decide (uStar / 2 ^ (B - (ℓ + 1) + 1) = c) := by
      intro c hc
      have heq_sub : B - ℓ = B - (ℓ + 1) + 1 := by omega
      rw [← heq_sub]
      exact ih' c hc
    dsimp only [decodeTree]
    exact decodeStep_eval M₀ cF T (B - (ℓ + 1)) res.1 res.2 hg1 (by omega) hm1
      (fun w hw => lt_of_lt_of_le (hT w hw) (by omega)) X hX (by rw [hpref cF hcF, hcFv])
      ℓ hlen1 uStar (by rw [hpow_eq]; exact huStar) (by rw [hpow_eq]; exact hTlen) hTval1 hIval1

private noncomputable def sortedRanks [DecidableEq GateOp] (d : ℕ) (G : Finset (Finset (Fin d)))
    (A : Circuit) : List ℕ :=
  (G.image (fun x =>
    let bits := List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]
    let w := A.wires bits
    (notIdxList A).foldl (fun v j => 2 * v + (if w.getD (d + 2 + j) false then 0 else 1)) 0)).sort (· ≤ ·)

private theorem sortedRanks_props [DecidableEq GateOp] (d : ℕ) (G : Finset (Finset (Fin d)))
    (A : Circuit) (hG : G.Nonempty) :
    let rs := sortedRanks d G A
    0 < rs.length ∧ rs.Pairwise (· < ·) ∧
    (∀ r ∈ rs, r < 2 ^ PEqualNP.NotBracket.notCount A) := by
  dsimp only [sortedRanks]
  set S := G.image (fun x =>
    let bits := List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]
    let w := A.wires bits
    (notIdxList A).foldl (fun v j => 2 * v + (if w.getD (d + 2 + j) false then 0 else 1)) 0)
  have hS : S.Nonempty := hG.image _
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  refine ⟨by rw [hlen]; exact hS.card_pos,
    List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S), ?_⟩
  intro r hr
  rw [Finset.mem_sort] at hr
  rcases Finset.mem_image.mp hr with ⟨x, _, rfl⟩
  rw [rank_eq_foldBits]
  have hlt := foldBits_lt ((notIdxList A).map (fun j =>
    !((A.wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false)))
  simpa [notIdxList_length] using hlt

section Comb
open scoped Classical

theorem card_filter_last {l : ℕ} (p : Fin (l+1) → Prop) :
    (Finset.univ.filter p).card = (Finset.univ.filter (fun j : Fin l => p j.castSucc)).card +
      (if p (Fin.last l) then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

noncomputable def hgt {u k : ℕ} (tag : Fin k → Finset (Fin u)) (w : Fin k → Fin k → ℕ) (j : Fin k) : ℕ :=
  Finset.univ.sup (fun i => if h : tag i ⊂ tag j then hgt tag w i + w i j else 0)
termination_by (tag j).card
decreasing_by exact Finset.card_lt_card h

theorem hgt_eq {u k : ℕ} (tag : Fin k → Finset (Fin u)) (w : Fin k → Fin k → ℕ) (j : Fin k) :
    hgt tag w j = Finset.univ.sup (fun i => if tag i ⊂ tag j then hgt tag w i + w i j else 0) := by
  rw [hgt]
  congr 1

theorem hgt_ge {u k : ℕ} (tag : Fin k → Finset (Fin u)) (w : Fin k → Fin k → ℕ) {i j : Fin k}
    (h : tag i ⊂ tag j) : hgt tag w i + w i j ≤ hgt tag w j := by
  rw [hgt_eq tag w j]
  have := Finset.le_sup (f := fun i => if tag i ⊂ tag j then hgt tag w i + w i j else 0) (Finset.mem_univ i)
  simp only [if_pos h] at this
  exact this

theorem comb {u d k B : ℕ} (tag : Fin k → Finset (Fin u))
    (G : Fin k → Finset (Finset (Fin d))) (m : Fin k → ℕ) (pos : Fin k → Finset (Fin d) → ℕ)
    (fl : Fin k → Finset (Fin d) → Fin k → Finset (Fin d) → Prop)
    (boundary : Fin k → Fin k → Prop)
    (hbd : ∀ i j, boundary i j ↔ ∃ x ∈ G i, ∃ y ∈ G j, pos i x + 1 = m i ∧ pos j y = 0 ∧ fl i x j y)
    (hm : ∀ i, 1 ≤ m i) (hpos : ∀ i, ∀ x ∈ G i, pos i x < m i)
    (htop : ∀ i, ∃ x ∈ G i, pos i x + 1 = m i) (hbot : ∀ i, ∃ x ∈ G i, pos i x = 0) :
    let chains := ∀ (l : Nat) (path : Fin (l+1) → Fin k),
      (∀ a c, a < c → tag (path a) ⊂ tag (path c)) →
      1 + (∑ a, (m (path a)-1)) +
        (Finset.univ.filter (fun j : Fin l => boundary (path j.castSucc) (path j.succ))).card ≤ 2^B
    let place := ∃ base : Fin k → Nat, (∀ i, base i + m i ≤ 2^B) ∧
      ∀ i j, tag i ⊂ tag j → ∀ x ∈ G i, ∀ y ∈ G j,
        base i + pos i x + (if fl i x j y then 1 else 0) ≤ base j + pos j y
    (place ↔ chains) := by
  intro chains place

  have step : ∀ base : Fin k → ℕ, (∀ i j, tag i ⊂ tag j → ∀ x ∈ G i, ∀ y ∈ G j,
        base i + pos i x + (if fl i x j y then 1 else 0) ≤ base j + pos j y) →
      ∀ i j, tag i ⊂ tag j → base i + (m i - 1) + (if boundary i j then 1 else 0) ≤ base j := by
    intro base hb i j hij
    by_cases hbd' : boundary i j
    · obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := (hbd i j).1 hbd'
      have := hb i j hij x hx y hy
      rw [if_pos h3] at this
      rw [if_pos hbd']
      omega
    · obtain ⟨x, hx, h1⟩ := htop i
      obtain ⟨y, hy, h2⟩ := hbot j
      have := hb i j hij x hx y hy
      rw [if_neg hbd']
      have h0 : (if fl i x j y then 1 else 0) ≥ 0 := Nat.zero_le _
      omega
  constructor
  · rintro ⟨base, hb1, hb2⟩
    have hst := step base hb2
    have tele : ∀ (l : ℕ) (path : Fin (l+1) → Fin k), (∀ a c, a < c → tag (path a) ⊂ tag (path c)) →
        (∑ a : Fin l, (m (path a.castSucc) - 1)) +
          (Finset.univ.filter (fun j : Fin l => boundary (path j.castSucc) (path j.succ))).card ≤
          base (path (Fin.last l)) := by
      intro l
      induction l with
      | zero => intro path _; simp
      | succ l ih =>
        intro path hpath
        have ih' := ih (fun a => path a.castSucc) (fun a c h => hpath _ _ (Fin.castSucc_lt_castSucc_iff.2 h))
        have hlast := hst (path (Fin.last l).castSucc) (path (Fin.last (l+1)))
          (hpath _ _ (Fin.castSucc_lt_last _))
        rw [Fin.sum_univ_castSucc, card_filter_last]
        have e1 : (Finset.univ.filter (fun j : Fin l =>
            boundary (path j.castSucc.castSucc) (path j.castSucc.succ))).card =
            (Finset.univ.filter (fun j : Fin l =>
            boundary (path j.castSucc.castSucc) (path j.succ.castSucc))).card := by
          rfl
        rw [e1]
        have e2 : (Fin.last l).succ = Fin.last (l+1) := Fin.succ_last l
        rw [e2]
        have e3 : (Fin.last l).castSucc = (Fin.last l).castSucc := rfl
        have hle : (∑ a : Fin l, (m (path a.castSucc.castSucc) - 1)) +
            (Finset.univ.filter (fun j : Fin l =>
              boundary (path j.castSucc.castSucc) (path j.succ.castSucc))).card ≤
            base (path (Fin.last l).castSucc) := ih'
        omega
    intro l path hpath
    have h1 := tele l path hpath
    have h2 := hb1 (path (Fin.last l))
    have h3 := hm (path (Fin.last l))
    rw [Fin.sum_univ_castSucc]
    omega
  · intro hch
    let w : Fin k → Fin k → ℕ := fun i j => m i - 1 + (if boundary i j then 1 else 0)
    have hchain : ∀ (n : ℕ) (j : Fin k), (tag j).card ≤ n → ∃ (l : ℕ) (path : Fin (l+1) → Fin k),
        (∀ a c, a < c → tag (path a) ⊂ tag (path c)) ∧ path (Fin.last l) = j ∧
        hgt tag w j = (∑ a : Fin l, (m (path a.castSucc) - 1)) +
          (Finset.univ.filter (fun a : Fin l => boundary (path a.castSucc) (path a.succ))).card := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro j hj
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k)) ⟨j, Finset.mem_univ j⟩
        (fun i => if tag i ⊂ tag j then hgt tag w i + w i j else 0)
      rw [← hgt_eq] at hi
      by_cases hij : tag i ⊂ tag j
      · rw [if_pos hij] at hi
        have hlt : (tag i).card < (tag j).card := Finset.card_lt_card hij
        obtain ⟨l, path, hp1, hp2, hp3⟩ := ih (tag i).card (by omega) i le_rfl
        refine ⟨l + 1, Fin.snoc path j, ?_, by simp, ?_⟩
        · intro a c hac
          have hsub : ∀ a : Fin (l+1), tag (path a) ⊆ tag i := by
            intro a
            rcases eq_or_lt_of_le (Fin.le_last a) with h | h
            · rw [h, hp2]
            · rw [← hp2]; exact (hp1 _ _ h).subset
          by_cases hc : c = Fin.last (l+1)
          · subst hc
            have ha : a ≠ Fin.last (l+1) := ne_of_lt hac
            obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
            rw [Fin.snoc_castSucc, Fin.snoc_last]
            exact lt_of_le_of_lt (hsub a') hij
          · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hc
            have ha : a ≠ Fin.last (l+1) := fun h => by
              rw [h] at hac; exact absurd hac (not_lt.2 (Fin.le_last _))
            obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hp1 _ _ (Fin.castSucc_lt_castSucc_iff.1 hac)
        · rw [hi, Fin.sum_univ_castSucc, card_filter_last]
          simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
          rw [hp3, hp2]
          dsimp only [w]
          omega
      · rw [if_neg hij] at hi
        refine ⟨0, fun _ => j, fun a c h => absurd h (by omega), rfl, ?_⟩
        rw [hi]
        simp
    refine ⟨hgt tag w, fun i => ?_, fun i j hij x hx y hy => ?_⟩
    · obtain ⟨l, path, hp1, hp2, hp3⟩ := hchain _ i le_rfl
      have := hch l path hp1
      rw [Fin.sum_univ_castSucc, hp2] at this
      have := hm i
      omega
    · have hge : hgt tag w i + (m i - 1 + (if boundary i j then 1 else 0)) ≤ hgt tag w j :=
        hgt_ge tag w hij
      have hpx := hpos i x hx
      by_cases hf : fl i x j y
      · rw [if_pos hf]
        by_cases hb : pos i x + 1 = m i ∧ pos j y = 0
        · have hbd' : boundary i j := (hbd i j).2 ⟨x, hx, y, hy, hb.1, hb.2, hf⟩
          rw [if_pos hbd'] at hge
          omega
        · have h0 : (if boundary i j then 1 else 0) ≥ 0 := Nat.zero_le _
          omega
      · rw [if_neg hf]
        have h0 : (if boundary i j then 1 else 0) ≥ 0 := Nat.zero_le _
        omega

end Comb

private def chain (op : GateOp) (M₀ : ℕ) : List Gate × ℕ → List ℕ → List Gate × ℕ
  | st, [] => st
  | st, v :: vs => chain op M₀ (st.1 ++ [⟨op, [st.2, v]⟩], M₀ + st.1.length) vs

private theorem chain_props [DecidableEq GateOp] (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (M₀ : ℕ) : ∀ (vs : List ℕ) (gs : List Gate) (w : ℕ), Good M₀ gs → w < M₀ + gs.length →
      (∀ v ∈ vs, v < M₀ + gs.length) →
      (∃ tail, (chain op M₀ (gs, w) vs).1 = gs ++ tail ∧ negCount tail = 0 ∧ posCount tail = vs.length) ∧
      Good M₀ (chain op M₀ (gs, w) vs).1 ∧
      (chain op M₀ (gs, w) vs).2 < M₀ + (chain op M₀ (gs, w) vs).1.length := by
  have hopn : op ≠ GateOp.not := by
    rcases hop with rfl | rfl <;> exact fun h => GateOp.noConfusion h
  have hopm : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
    rcases hop with rfl | rfl <;> simp
  intro vs
  induction vs with
  | nil =>
    intro gs w hgs hw _
    exact ⟨⟨[], by simp [chain], negCount_nil, posCount_nil⟩, hgs, hw⟩
  | cons v vs ih =>
    intro gs w hgs hw hvs
    have hv : v < M₀ + gs.length := hvs v (by simp)
    set g : Gate := ⟨op, [w, v]⟩
    have hg : Good M₀ (gs ++ [g]) :=
      good_snoc hgs g hopm (by simp [g]) (fun i hi => by
        simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption)
    have e : chain op M₀ (gs, w) (v :: vs) = chain op M₀ (gs ++ [g], M₀ + gs.length) vs := rfl
    rw [e]
    obtain ⟨⟨tail, ht, hn, hp⟩, hgood, hout⟩ := ih (gs ++ [g]) (M₀ + gs.length) hg (by simp)
      (fun v' hv' => by have := hvs v' (by simp [hv']); simp; omega)
    have hgn : g.op ≠ GateOp.not := hopn
    have hn1 : negCount [g] = 0 := by simp [negCount, hgn]
    have hp1 : posCount [g] = 1 := by simp [posCount, hgn]
    refine ⟨⟨[g] ++ tail, by rw [ht, List.append_assoc], ?_, ?_⟩, hgood, hout⟩
    · rw [negCount_append, hn, hn1]
    · rw [posCount_append, hp, hp1, List.length_cons]; omega

private theorem chain_eval (op : GateOp) (M₀ : ℕ) : ∀ (vs : List ℕ) (gs : List Gate) (w : ℕ),
      (∀ v ∈ vs, v < M₀ + gs.length) → ∀ X : List Bool, X.length = M₀ →
      (run (chain op M₀ (gs, w) vs).1 X).getD (chain op M₀ (gs, w) vs).2 false =
        vs.foldl (fun acc v => op.eval [acc, (run gs X).getD v false]) ((run gs X).getD w false) := by
  intro vs
  induction vs with
  | nil => intro gs w _ X _; rfl
  | cons v vs ih =>
    intro gs w hvs X hX
    have hv : v < M₀ + gs.length := hvs v (by simp)
    have e : chain op M₀ (gs, w) (v :: vs) = chain op M₀ (gs ++ [Gate.mk op [w, v]], M₀ + gs.length) vs := rfl
    rw [e, ih (gs ++ [Gate.mk op [w, v]]) (M₀ + gs.length)
      (fun v' hv' => by have := hvs v' (by simp [hv']); simp; omega) X hX]
    rw [List.foldl_cons]
    have hlen : (run gs X).length = M₀ + gs.length := by rw [run_length, hX]
    have h1 : (run (gs ++ [Gate.mk op [w, v]]) X).getD (M₀ + gs.length) false =
        op.eval [(run gs X).getD w false, (run gs X).getD v false] := by
      rw [run_snoc, ← hlen, getD_eq]; rfl
    rw [h1]
    apply List.foldl_ext
    intro acc v' hv'
    have := hvs v' (by simp [hv'])
    rw [run_prefix gs _ X v' (by rw [hX]; exact this)]

private theorem all_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ v ∈ l, f v = g v) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]

private theorem any_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ v ∈ l, f v = g v) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]

private theorem foldl_and (f : ℕ → Bool) : ∀ (vs : List ℕ) (a : Bool),
    vs.foldl (fun acc v => GateOp.and.eval [acc, f v]) a = (a && vs.all f) := by
  intro vs
  induction vs with
  | nil => intro a; simp
  | cons v vs ih =>
    intro a
    rw [List.foldl_cons, ih]
    simp [GateOp.eval, Bool.and_assoc]

private theorem foldl_or (f : ℕ → Bool) : ∀ (vs : List ℕ) (a : Bool),
    vs.foldl (fun acc v => GateOp.or.eval [acc, f v]) a = (a || vs.any f) := by
  intro vs
  induction vs with
  | nil => intro a; simp
  | cons v vs ih =>
    intro a
    rw [List.foldl_cons, ih]
    simp [GateOp.eval, Bool.or_assoc]

private def buildSel (M₀ cT : ℕ) (tv : ℕ → List ℕ) : ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, fun _ => cT)
  | n + 1, gs =>
    let res := buildSel M₀ cT tv n gs
    let r := chain GateOp.and M₀ (res.1, cT) (tv n)
    (r.1, fun i => if i = n then r.2 else res.2 i)

private theorem buildSel_props [DecidableEq GateOp] (M₀ cT : ℕ) (tv : ℕ → List ℕ) (gs : List Gate)
    (hgs : Good M₀ gs) (hcT : cT < M₀ + gs.length) (htv : ∀ i, ∀ v ∈ tv i, v < M₀ + gs.length) :
    ∀ n, (∃ tail, (buildSel M₀ cT tv n gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
        posCount tail = ∑ i ∈ Finset.range n, (tv i).length) ∧
      Good M₀ (buildSel M₀ cT tv n gs).1 ∧
      ∀ i < n, (buildSel M₀ cT tv n gs).2 i < M₀ + (buildSel M₀ cT tv n gs).1.length := by
  intro n
  induction n with
  | zero => exact ⟨⟨[], by simp [buildSel], negCount_nil, by simp [posCount_nil]⟩, hgs, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hb1⟩ := ih
    have hl1 : gs.length ≤ (buildSel M₀ cT tv n gs).1.length := by rw [ht1, List.length_append]; omega
    obtain ⟨⟨t2, ht2, hn2, hp2⟩, hg2, hb2⟩ := chain_props GateOp.and (Or.inl rfl) M₀ (tv n)
      (buildSel M₀ cT tv n gs).1 cT hg1 (by omega) (fun v hv => by have := htv n v hv; omega)
    have hl2 : (buildSel M₀ cT tv n gs).1.length ≤
        (chain GateOp.and M₀ ((buildSel M₀ cT tv n gs).1, cT) (tv n)).1.length := by
      rw [ht2, List.length_append]; omega
    refine ⟨⟨t1 ++ t2, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show (chain GateOp.and M₀ ((buildSel M₀ cT tv n gs).1, cT) (tv n)).1 = _
      rw [ht2, ht1, List.append_assoc]
    · rw [negCount_append, hn1, hn2]
    · rw [posCount_append, hp1, hp2, Finset.sum_range_succ]
    · exact hg2
    · intro i hi
      show (if i = n then _ else _) < M₀ + (chain GateOp.and M₀ ((buildSel M₀ cT tv n gs).1, cT) (tv n)).1.length
      by_cases h : i = n
      · rw [if_pos h]; exact hb2
      · rw [if_neg h]; exact lt_of_lt_of_le (hb1 i (by omega)) (by omega)

private theorem buildSel_eval [DecidableEq GateOp] (M₀ cT : ℕ) (tv : ℕ → List ℕ) (gs : List Gate)
    (hgs : Good M₀ gs) (hcT : cT < M₀ + gs.length) (htv : ∀ i, ∀ v ∈ tv i, v < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀) (hcTv : (run gs X).getD cT false = true) :
    ∀ n, ∀ i < n, (run (buildSel M₀ cT tv n gs).1 X).getD ((buildSel M₀ cT tv n gs).2 i) false =
      (tv i).all (fun v => (run gs X).getD v false) := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    obtain ⟨⟨t1, ht1, _, _⟩, hg1, hb1⟩ := buildSel_props M₀ cT tv gs hgs hcT htv n
    have hl1 : gs.length ≤ (buildSel M₀ cT tv n gs).1.length := by rw [ht1, List.length_append]; omega
    obtain ⟨⟨t2, ht2, _, _⟩, _, _⟩ := chain_props GateOp.and (Or.inl rfl) M₀ (tv n)
      (buildSel M₀ cT tv n gs).1 cT hg1 (by omega) (fun v hv => by have := htv n v hv; omega)
    have hpre : ∀ w < M₀ + gs.length, (run (buildSel M₀ cT tv n gs).1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    show (run (chain GateOp.and M₀ ((buildSel M₀ cT tv n gs).1, cT) (tv n)).1 X).getD
      (if i = n then _ else _) false = _
    by_cases h : i = n
    · subst h
      rw [if_pos rfl, chain_eval GateOp.and M₀ (tv i) _ cT (fun v hv => by have := htv i v hv; omega) X hX,
        foldl_and, hpre cT hcT, hcTv, Bool.true_and]
      exact all_congr' (fun v hv => hpre v (htv i v hv))
    · rw [if_neg h, ht2, run_prefix _ t2 X _ (by rw [hX]; exact hb1 i (by omega))]
      exact ih i (by omega)

private def stCut [DecidableEq GateOp] (d M₀ cF cT : ℕ) (C : Circuit) (baseIn : ℕ → ℕ) (r selW : ℕ)
    (gs : List Gate) : List Gate × ℕ × (ℕ → ℕ) :=
  let b := PEqualNP.NotBracket.notCount C
  let notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
  let res1 := remapLoop d M₀ C baseIn notWire gs C.size
  let res2 := cmpAux M₀ cT cF C res1.2 (notIdxList C) r b res1.1 b
  (res2.1 ++ [⟨GateOp.and, [selW, res2.2]⟩], M₀ + res2.1.length, res1.2)

private theorem stCut_props [DecidableEq GateOp] (d M₀ cF cT : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r selW : ℕ) (gs : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length) (hsel : selW < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length) :
    (∃ tail, (stCut d M₀ cF cT C baseIn r selW gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
      posCount tail = (C.size - PEqualNP.NotBracket.notCount C) + PEqualNP.NotBracket.notCount C + 1) ∧
    Good M₀ (stCut d M₀ cF cT C baseIn r selW gs).1 ∧
    (stCut d M₀ cF cT C baseIn r selW gs).2.1 < M₀ + (stCut d M₀ cF cT C baseIn r selW gs).1.length ∧
    ∀ w < d + 2 + C.size, (stCut d M₀ cF cT C baseIn r selW gs).2.2 w <
      M₀ + (stCut d M₀ cF cT C baseIn r selW gs).1.length := by
  dsimp only [stCut]
  set b := PEqualNP.NotBracket.notCount C
  set notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
  have hnotB : ∀ j < C.size, notWire j < M₀ + gs.length := fun j _ => by
    dsimp [notWire]; split_ifs <;> assumption
  rcases remapLoop_posCount_full d M₀ C baseIn notWire gs with ⟨t1, ht1, hn1, hp1⟩
  have hg1 : Good M₀ (remapLoop d M₀ C baseIn notWire gs C.size).1 :=
    remapLoop_good d M₀ C baseIn notWire gs hfan hrb hgs hbase hnotB C.size le_rfl
  have hm1 : ∀ w < d + 2 + C.size, (remapLoop d M₀ C baseIn notWire gs C.size).2 w <
      M₀ + (remapLoop d M₀ C baseIn notWire gs C.size).1.length :=
    remapLoop_map_lt d M₀ C baseIn notWire gs hbase hnotB C.size le_rfl
  have hlen1 : gs.length ≤ (remapLoop d M₀ C baseIn notWire gs C.size).1.length := by
    rw [ht1, List.length_append]; omega
  have hcT1 : cT < M₀ + (remapLoop d M₀ C baseIn notWire gs C.size).1.length := by omega
  have hcF1 : cF < M₀ + (remapLoop d M₀ C baseIn notWire gs C.size).1.length := by omega
  have hidxs : ∀ s < b, (notIdxList C).getD s 0 < C.size := by
    intro s hs
    have hs' : s < (notIdxList C).length := by rw [notIdxList_length]; exact hs
    exact (filter_range_getD_props _ C.size s hs').1
  rcases cmpAux_good d M₀ cT cF C (remapLoop d M₀ C baseIn notWire gs C.size).2 (notIdxList C) r b
      (remapLoop d M₀ C baseIn notWire gs C.size).1 hrb hg1 hcT1 hcF1 hm1 hidxs b le_rfl with
    ⟨hg2, hw2⟩
  rcases cmpAux_tail M₀ cT cF C (remapLoop d M₀ C baseIn notWire gs C.size).2 (notIdxList C) r b
      (remapLoop d M₀ C baseIn notWire gs C.size).1 b with ⟨t2, ht2, hn2, hp2⟩
  set res2 := cmpAux M₀ cT cF C (remapLoop d M₀ C baseIn notWire gs C.size).2
      (notIdxList C) r b (remapLoop d M₀ C baseIn notWire gs C.size).1 b
  have hlen2 : (remapLoop d M₀ C baseIn notWire gs C.size).1.length ≤ res2.1.length := by
    rw [ht2, List.length_append]; omega
  set gAnd : Gate := ⟨GateOp.and, [selW, res2.2]⟩
  have hg3 : Good M₀ (res2.1 ++ [gAnd]) := by
    apply good_snoc hg2 gAnd (by simp [gAnd]) (by simp [gAnd])
    intro u hu; simp [gAnd] at hu
    rcases hu with rfl | rfl
    · omega
    · exact hw2
  have hAndNot : gAnd.op ≠ GateOp.not := fun h => GateOp.noConfusion h
  refine ⟨⟨t1 ++ t2 ++ [gAnd], ?_, ?_, ?_⟩, hg3, by simp, fun w hw => ?_⟩
  · rw [ht2, ht1]; simp [List.append_assoc]
  · rw [negCount_append, negCount_append, hn1, hn2]; simp [negCount, hAndNot]
  · have hp3 : posCount [gAnd] = 1 := by simp [posCount, hAndNot]
    rw [posCount_append, posCount_append, hp1, hp2, hp3]
  · have := hm1 w hw
    simp only [List.length_append, List.length_singleton]
    omega

private theorem cmp_core [DecidableEq GateOp] (d M₀ cF cT : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r : ℕ) (gs : List Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length)
    (hr : r < 2 ^ PEqualNP.NotBracket.notCount C)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (hcTv : (run gs X).getD cT false = true)
    (x : List Bool) (hx : x.length = d + 2)
    (hbase' : ∀ w < d + 2, (run gs X).getD (baseIn w) false = x.getD w false) :
    let b := PEqualNP.NotBracket.notCount C
    let notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
    let res1 := remapLoop d M₀ C baseIn notWire gs C.size
    let res2 := cmpAux M₀ cT cF C res1.2 (notIdxList C) r b res1.1 b
    let r_real := (notIdxList C).foldl (fun v j =>
      2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0
    (run res2.1 X).getD res2.2 false = decide (r ≤ r_real) ∧
    (r = r_real → ∀ w < d + 2 + C.size, (run res1.1 X).getD (res1.2 w) false = (C.wires x).getD w false) := by
  intro b notWire res1 res2 r_real
  have hnotB : ∀ j < C.size, notWire j < M₀ + gs.length := fun j _ => by
    dsimp [notWire]; split_ifs <;> assumption
  rcases remapLoop_tail d M₀ C baseIn notWire gs C.size with ⟨t1, ht1, _, _⟩
  have hm1 : ∀ w < d + 2 + C.size, res1.2 w < M₀ + res1.1.length :=
    remapLoop_map_lt d M₀ C baseIn notWire gs hbase hnotB C.size le_rfl
  have hlen1 : gs.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
  let bs := (notIdxList C).map (fun j => !((C.wires x).getD (d + 2 + j) false))
  have hbs_len : bs.length = b := by simp [bs, notIdxList_length, b]
  have hr_real_eq : r_real = foldBits bs := by
    show (notIdxList C).foldl (fun v j =>
      2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0 = foldBits bs
    dsimp only [foldBits, bs]
    rw [List.foldl_map]
    congr 1; funext v j
    cases (C.wires x).getD (d + 2 + j) false <;> rfl
  have hr_real_lt : r_real < 2 ^ b := by
    rw [hr_real_eq, ← hbs_len]
    exact foldBits_lt bs
  have hbit_real : ∀ s < b, bitAt r_real (b - 1 - s) =
      !((C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false) := by
    intro s hs
    rw [hr_real_eq]
    have hs' : s < bs.length := by rw [hbs_len]; exact hs
    have hfb := bitAt_foldBits bs s hs'
    rw [hbs_len] at hfb
    rw [hfb]
    have hs_idx : s < (notIdxList C).length := by rw [notIdxList_length]; exact hs
    dsimp only [bs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs_idx]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs_idx]
  have hidx_props : ∀ s < b,
      (notIdxList C).getD s 0 < C.size ∧
      (C.gates.getD ((notIdxList C).getD s 0) ⟨GateOp.or, []⟩).op = GateOp.not ∧
      notPos C ((notIdxList C).getD s 0) = s ∧
      (∀ j < (notIdxList C).getD s 0, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
        ∃ s' < s, (notIdxList C).getD s' 0 = j) := by
    intro s hs
    have hs_idx : s < (notIdxList C).length := by rw [notIdxList_length]; exact hs
    rcases filter_range_getD_props (fun j => decide ((C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not))
      C.size s hs_idx with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, of_decide_eq_true h2, h3, fun j hj hjn => h4 j hj (decide_eq_true hjn)⟩
  have hcT1 : (run res1.1 X).getD cT false = true := by
    rw [ht1, run_prefix gs t1 X cT (by rw [hX]; exact hcT), hcTv]
  have hinB : ∀ t < b, cmpInWire cF C res1.2 (notIdxList C) b t < M₀ + res1.1.length := by
    intro t ht
    dsimp only [cmpInWire]
    set s := b - (t + 1)
    have hs : s < b := by omega
    have hj := (hidx_props s hs).1
    cases hhead : (C.gates.getD ((notIdxList C).getD s 0) ⟨GateOp.or, []⟩).inputs.head? with
    | none => exact lt_of_lt_of_le hcF (by omega)
    | some u =>
      have hu_lt := hrb _ hj u (List.mem_of_mem_head? hhead)
      exact hm1 u (by omega)
  have eval_cmp_at : ∀ k_gate ≤ C.size,
      (∀ j < k_gate, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
        (run gs X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false) →
      ∀ s < b, (notIdxList C).getD s 0 ≤ k_gate →
        (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b (b - 1 - s)) false =
          bitAt r_real (b - 1 - s) := by
    intro k_gate hk_gate hnotEq s hs hj_le
    have heval := remapLoop_eval_final d M₀ C baseIn notWire gs hrb hbase hnotB
      x hx X hX hbase' k_gate hk_gate hnotEq
    have hbsub : b - (b - 1 - s + 1) = s := by omega
    dsimp only [cmpInWire]
    rw [hbsub]
    set j := (notIdxList C).getD s 0
    have hjC : j < C.gates.length := (hidx_props s hs).1
    have hjop : (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not := (hidx_props s hs).2.1
    have hCgate : (C.wires x).getD (d + 2 + j) false =
        ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun u =>
          if u < d + 2 + j then (C.wires x).getD u false else false)) := by
      rw [circuit_wires_eq_run]
      have rg := run_gate C.gates x j hjC
      rw [hx] at rg
      exact rg
    have hgd : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjC]; rfl
    rw [hbit_real s hs, hCgate, ← hgd, hjop]
    cases hhead : (C.gates.getD j ⟨GateOp.or, []⟩).inputs.head? with
    | none =>
      have hn1 : (C.gates.getD j ⟨GateOp.or, []⟩).inputs = [] :=
        List.head?_eq_none_iff.mp hhead
      rw [ht1, run_prefix gs t1 X cF (by rw [hX]; exact hcF), hcFv, hn1]
      simp [GateOp.eval]
    | some u =>
      have hu_lt : u < d + 2 + j := hrb j hjC u (List.mem_of_mem_head? hhead)
      rw [heval u (by omega)]
      have hcons : ∃ us, (C.gates.getD j ⟨GateOp.or, []⟩).inputs = u :: us := by
        cases hl : (C.gates.getD j ⟨GateOp.or, []⟩).inputs with
        | nil => rw [hl] at hhead; simp at hhead
        | cons a as => rw [hl] at hhead; simp at hhead; exact ⟨as, by rw [hhead]⟩
      rcases hcons with ⟨us, hus⟩
      rw [hus]
      simp [GateOp.eval, hu_lt]
  have hnotEqAll : r = r_real → ∀ j < C.size, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
      (run gs X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false := by
    intro hrr j hj hjn
    have hmem : j ∈ notIdxList C := List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hjn⟩
    rcases List.mem_iff_getElem.mp hmem with ⟨s, hs, hjs⟩
    have hs_b : s < b := by dsimp only [b]; rw [← notIdxList_length C]; exact hs
    have hj_eq : (notIdxList C).getD s 0 = j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; simpa using hjs
    rw [← hj_eq]
    dsimp only [notWire]
    rw [hrr]
    rw [(hidx_props s hs_b).2.2.1]
    have hb := hbit_real s hs_b
    cases hbit : bitAt r_real (b - 1 - s)
    · rw [if_neg Bool.false_ne_true, hcTv]
      rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
    · rw [if_pos rfl, hcFv]
      rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
  refine ⟨?_, fun hrr => remapLoop_eval_final d M₀ C baseIn notWire gs hrb hbase hnotB
    x hx X hX hbase' C.size le_rfl (hnotEqAll hrr)⟩
  rcases le_iff_bitAt_eq_or_lt b r r_real hr hr_real_lt with ⟨hrr, _⟩ | ⟨tStar, htStar, hhi, hne, hlt_r⟩
  · have hinEq : ∀ t < b, (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b t) false =
        bitAt r t := by
      intro t ht
      set s := b - 1 - t
      have hs : s < b := by omega
      have hsub : b - 1 - s = t := by omega
      rw [← hsub, hrr]
      exact eval_cmp_at C.size le_rfl (hnotEqAll hrr) s hs (Nat.le_of_lt (hidx_props s hs).1)
    rw [cmpAux_eval_eq M₀ cT cF C res1.2 (notIdxList C) r b res1.1 X hX hcT1 hinB hinEq b le_rfl]
    simp [hrr]
  · set sStar := b - 1 - tStar
    have hsStar : sStar < b := by omega
    set jStar := (notIdxList C).getD sStar 0
    have hjStarC : jStar < C.size := (hidx_props sStar hsStar).1
    have hnotEq : ∀ j < jStar, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
        (run gs X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false := by
      intro j hj hjn
      rcases (hidx_props sStar hsStar).2.2.2 j hj hjn with ⟨s, hs_lt, rfl⟩
      have hs_b : s < b := lt_trans hs_lt hsStar
      dsimp only [notWire]
      rw [(hidx_props s hs_b).2.2.1]
      have ht_gt : tStar < b - 1 - s := by omega
      have ht_lt : b - 1 - s < b := by omega
      have hsame := hhi (b - 1 - s) ht_gt ht_lt
      have hb := hbit_real s hs_b
      rw [hsame]
      cases hbit : bitAt r_real (b - 1 - s)
      · rw [if_neg Bool.false_ne_true, hcTv]
        rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
      · rw [if_pos rfl, hcFv]
        rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
    have hhi_in : ∀ t, tStar < t → t < b →
        (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b t) false = bitAt r t := by
      intro t hgt htb
      set s := b - 1 - t
      have hs_lt : s < sStar := by omega
      have hs_b : s < b := lt_trans hs_lt hsStar
      have hj_lt : (notIdxList C).getD s 0 < jStar := by
        have hpw : (notIdxList C).Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
        have hs_idx : s < (notIdxList C).length := by dsimp only [b] at hs_b; rw [notIdxList_length]; exact hs_b
        have hsStar_idx : sStar < (notIdxList C).length := by dsimp only [b] at hsStar; rw [notIdxList_length]; exact hsStar
        have hlt_pw := (List.pairwise_iff_getElem.mp hpw) s sStar hs_idx hsStar_idx hs_lt
        simp only [jStar, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs_idx,
          List.getElem?_eq_getElem hsStar_idx, Option.getD_some]
        exact hlt_pw
      have hsub : b - 1 - s = t := by omega
      rw [← hsub, eval_cmp_at jStar (Nat.le_of_lt hjStarC) hnotEq s hs_b (Nat.le_of_lt hj_lt), hsub, hhi t hgt htb]
    have htStar_in : (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b tStar) false =
        bitAt r_real tStar := by
      have hsub : b - 1 - sStar = tStar := by omega
      rw [← hsub]
      exact eval_cmp_at jStar (Nat.le_of_lt hjStarC) hnotEq sStar hsStar le_rfl
    have hne_in : (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b tStar) false ≠
        bitAt r tStar := by
      rw [htStar_in]; exact hne.symm
    rw [cmpAux_eval_mismatch M₀ cT cF C res1.2 (notIdxList C) r b res1.1 X hX hinB
      tStar htStar hhi_in hne_in b htStar le_rfl, htStar_in]
    cases hb1 : bitAt r tStar <;> cases hb2 : bitAt r_real tStar
    · exact absurd (hb1.trans hb2.symm) hne
    · have hlt' : r < r_real := hlt_r.mpr ⟨hb1, hb2⟩
      simp [Nat.le_of_lt hlt']
    · have hnotlt : ¬ (r < r_real) := by rw [hlt_r]; simp [hb1, hb2]
      have hner : r ≠ r_real := fun h => by subst h; rw [hb1] at hb2; exact Bool.noConfusion hb2
      have hnotle : ¬ (r ≤ r_real) := by omega
      simp [hnotle]
    · exact absurd (hb1.trans hb2.symm) hne

private theorem stCut_eval [DecidableEq GateOp] (d M₀ cF cT : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r selW : ℕ) (gs : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length) (hsel : selW < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length)
    (hr : r < 2 ^ PEqualNP.NotBracket.notCount C)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (hcTv : (run gs X).getD cT false = true)
    (x : List Bool) (hx : x.length = d + 2)
    (hbase' : ∀ w < d + 2, (run gs X).getD (baseIn w) false = x.getD w false) :
    (run (stCut d M₀ cF cT C baseIn r selW gs).1 X).getD (stCut d M₀ cF cT C baseIn r selW gs).2.1 false =
      ((run gs X).getD selW false && decide (r ≤ (notIdxList C).foldl (fun v j =>
        2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0)) ∧
    (r = (notIdxList C).foldl (fun v j => 2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0 →
      ∀ w < d + 2 + C.size, (run (stCut d M₀ cF cT C baseIn r selW gs).1 X).getD
        ((stCut d M₀ cF cT C baseIn r selW gs).2.2 w) false = (C.wires x).getD w false) := by
  have hc := cmp_core d M₀ cF cT C baseIn r gs hrb hcF hcT hbase hr X hX hcFv hcTv x hx hbase'
  dsimp only at hc
  dsimp only [stCut]
  set b := PEqualNP.NotBracket.notCount C
  set notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
  have hnotB : ∀ j < C.size, notWire j < M₀ + gs.length := fun j _ => by
    dsimp [notWire]; split_ifs <;> assumption
  rcases remapLoop_tail d M₀ C baseIn notWire gs C.size with ⟨t1, ht1, _, _⟩
  have hm1 : ∀ w < d + 2 + C.size, (remapLoop d M₀ C baseIn notWire gs C.size).2 w <
      M₀ + (remapLoop d M₀ C baseIn notWire gs C.size).1.length :=
    remapLoop_map_lt d M₀ C baseIn notWire gs hbase hnotB C.size le_rfl
  have hlen1 : gs.length ≤ (remapLoop d M₀ C baseIn notWire gs C.size).1.length := by
    rw [ht1, List.length_append]; omega
  rcases cmpAux_tail M₀ cT cF C (remapLoop d M₀ C baseIn notWire gs C.size).2 (notIdxList C) r b
      (remapLoop d M₀ C baseIn notWire gs C.size).1 b with ⟨t2, ht2, _, _⟩
  set res2 := cmpAux M₀ cT cF C (remapLoop d M₀ C baseIn notWire gs C.size).2
      (notIdxList C) r b (remapLoop d M₀ C baseIn notWire gs C.size).1 b
  have hlen2 : (remapLoop d M₀ C baseIn notWire gs C.size).1.length ≤ res2.1.length := by
    rw [ht2, List.length_append]; omega
  constructor
  · have hrlen : (run res2.1 X).length = M₀ + res2.1.length := by rw [run_length, hX]
    rw [run_snoc, ← hrlen, getD_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [hc.1, ht2, ht1, List.append_assoc, run_prefix gs (t1 ++ t2) X selW (by rw [hX]; exact hsel)]
  · intro hrr w hw
    rw [ht2, List.append_assoc,
      run_prefix _ (t2 ++ [Gate.mk GateOp.and [selW, res2.2]]) X _ (by rw [hX]; exact hm1 w hw)]
    exact hc.2 hrr w hw

private def buildStates [DecidableEq GateOp] (d M₀ cF cT : ℕ) {k : ℕ} (A : Fin k → Circuit)
    (bIn : Fin k → ℕ → ℕ) (rr : Fin k → ℕ → ℕ) (sel : Fin k → ℕ) (pq : ℕ → Fin k × ℕ) :
    ℕ → List Gate → List Gate × (ℕ → ℕ) × (ℕ → ℕ → ℕ)
  | 0, gs => (gs, fun _ => cF, fun _ _ => cF)
  | n + 1, gs =>
    let res := buildStates d M₀ cF cT A bIn rr sel pq n gs
    let c := stCut d M₀ cF cT (A (pq n).1) (bIn (pq n).1) (rr (pq n).1 (pq n).2) (sel (pq n).1) res.1
    (c.1, fun q => if q = n then c.2.1 else res.2.1 q, fun q => if q = n then c.2.2 else res.2.2 q)

private theorem buildStates_props [DecidableEq GateOp] (d M₀ cF cT : ℕ) {k : ℕ} (A : Fin k → Circuit)
    (bIn : Fin k → ℕ → ℕ) (rr : Fin k → ℕ → ℕ) (sel : Fin k → ℕ) (pq : ℕ → Fin k × ℕ) (gs : List Gate)
    (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsel : ∀ i, sel i < M₀ + gs.length) (hbIn : ∀ i, ∀ w < d + 2, bIn i w < M₀ + gs.length) :
    ∀ n, (∃ tail, (buildStates d M₀ cF cT A bIn rr sel pq n gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
        posCount tail = ∑ q ∈ Finset.range n, (((A (pq q).1).size - PEqualNP.NotBracket.notCount (A (pq q).1)) +
          PEqualNP.NotBracket.notCount (A (pq q).1) + 1)) ∧
      Good M₀ (buildStates d M₀ cF cT A bIn rr sel pq n gs).1 ∧
      (∀ q < n, (buildStates d M₀ cF cT A bIn rr sel pq n gs).2.1 q <
        M₀ + (buildStates d M₀ cF cT A bIn rr sel pq n gs).1.length) ∧
      (∀ q < n, ∀ w < d + 2 + (A (pq q).1).size, (buildStates d M₀ cF cT A bIn rr sel pq n gs).2.2 q w <
        M₀ + (buildStates d M₀ cF cT A bIn rr sel pq n gs).1.length) := by
  intro n
  induction n with
  | zero =>
    exact ⟨⟨[], by simp [buildStates], negCount_nil, by simp [posCount_nil]⟩, hgs,
      fun q hq => absurd hq (by omega), fun q hq => absurd hq (by omega)⟩
  | succ n ih =>
    obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hc1, hm1⟩ := ih
    set res := buildStates d M₀ cF cT A bIn rr sel pq n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    obtain ⟨⟨t2, ht2, hn2, hp2⟩, hg2, hc2, hm2⟩ := stCut_props d M₀ cF cT (A (pq n).1) (bIn (pq n).1)
      (rr (pq n).1 (pq n).2) (sel (pq n).1) res.1 (hA _).1 (hA _).2 hg1 (by omega) (by omega)
      (by have := hsel (pq n).1; omega) (fun w hw => by have := hbIn (pq n).1 w hw; omega)
    set c := stCut d M₀ cF cT (A (pq n).1) (bIn (pq n).1) (rr (pq n).1 (pq n).2) (sel (pq n).1) res.1
    have hl2 : res.1.length ≤ c.1.length := by rw [ht2, List.length_append]; omega
    refine ⟨⟨t1 ++ t2, ?_, ?_, ?_⟩, hg2, ?_, ?_⟩
    · show c.1 = _
      rw [ht2, ht1, List.append_assoc]
    · rw [negCount_append, hn1, hn2]
    · rw [posCount_append, hp1, hp2, Finset.sum_range_succ]
    · intro q hq
      show (if q = n then c.2.1 else res.2.1 q) < M₀ + c.1.length
      by_cases h : q = n
      · rw [if_pos h]; exact hc2
      · rw [if_neg h]; exact lt_of_lt_of_le (hc1 q (by omega)) (by omega)
    · intro q hq w hw
      show (if q = n then c.2.2 else res.2.2 q) w < M₀ + c.1.length
      by_cases h : q = n
      · subst h; rw [if_pos rfl]; exact hm2 w hw
      · rw [if_neg h]; exact lt_of_lt_of_le (hm1 q (by omega) w hw) (by omega)

private theorem buildStates_eval [DecidableEq GateOp] (d M₀ cF cT : ℕ) {k : ℕ} (A : Fin k → Circuit)
    (bIn : Fin k → ℕ → ℕ) (rr : Fin k → ℕ → ℕ) (sel : Fin k → ℕ) (pq : ℕ → Fin k × ℕ) (gs : List Gate)
    (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsel : ∀ i, sel i < M₀ + gs.length) (hbIn : ∀ i, ∀ w < d + 2, bIn i w < M₀ + gs.length)
    (hrr : ∀ i s, rr i s < 2 ^ PEqualNP.NotBracket.notCount (A i))
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false) (hcTv : (run gs X).getD cT false = true)
    (xs : Fin k → List Bool) (hxs : ∀ i, (xs i).length = d + 2)
    (hbv : ∀ i, ∀ w < d + 2, (run gs X).getD (bIn i w) false = (xs i).getD w false) :
    ∀ n, ∀ q < n,
      (run (buildStates d M₀ cF cT A bIn rr sel pq n gs).1 X).getD
        ((buildStates d M₀ cF cT A bIn rr sel pq n gs).2.1 q) false =
        ((run gs X).getD (sel (pq q).1) false && decide (rr (pq q).1 (pq q).2 ≤
          (notIdxList (A (pq q).1)).foldl (fun v j =>
            2 * v + (if ((A (pq q).1).wires (xs (pq q).1)).getD (d + 2 + j) false then 0 else 1)) 0)) ∧
      (rr (pq q).1 (pq q).2 = (notIdxList (A (pq q).1)).foldl (fun v j =>
            2 * v + (if ((A (pq q).1).wires (xs (pq q).1)).getD (d + 2 + j) false then 0 else 1)) 0 →
        ∀ w < d + 2 + (A (pq q).1).size,
          (run (buildStates d M₀ cF cT A bIn rr sel pq n gs).1 X).getD
            ((buildStates d M₀ cF cT A bIn rr sel pq n gs).2.2 q w) false =
          ((A (pq q).1).wires (xs (pq q).1)).getD w false) := by
  intro n
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    obtain ⟨⟨t1, ht1, _, _⟩, hg1, hc1, hm1⟩ :=
      buildStates_props d M₀ cF cT A bIn rr sel pq gs hA hgs hcF hcT hsel hbIn n
    set res := buildStates d M₀ cF cT A bIn rr sel pq n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    have hpre : ∀ w < M₀ + gs.length, (run res.1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    obtain ⟨⟨t2, ht2, _, _⟩, _, _, _⟩ := stCut_props d M₀ cF cT (A (pq n).1) (bIn (pq n).1)
      (rr (pq n).1 (pq n).2) (sel (pq n).1) res.1 (hA _).1 (hA _).2 hg1 (by omega) (by omega)
      (by have := hsel (pq n).1; omega) (fun w hw => by have := hbIn (pq n).1 w hw; omega)
    set c := stCut d M₀ cF cT (A (pq n).1) (bIn (pq n).1) (rr (pq n).1 (pq n).2) (sel (pq n).1) res.1 with hcdef
    show (run c.1 X).getD (if q = n then c.2.1 else res.2.1 q) false = _ ∧
      (_ → ∀ w < _, (run c.1 X).getD ((if q = n then c.2.2 else res.2.2 q) w) false = _)
    by_cases h : q = n
    · subst h
      rw [if_pos rfl, if_pos rfl]
      have hev := stCut_eval d M₀ cF cT (A (pq q).1) (bIn (pq q).1) (rr (pq q).1 (pq q).2) (sel (pq q).1) res.1
        (hA _).1 (hA _).2 hg1 (by omega) (by omega) (by have := hsel (pq q).1; omega)
        (fun w hw => by have := hbIn (pq q).1 w hw; omega) (hrr _ _) X hX
        (by rw [hpre cF hcF, hcFv]) (by rw [hpre cT hcT, hcTv]) (xs (pq q).1) (hxs _)
        (fun w hw => by rw [hpre _ (hbIn _ w hw), hbv _ w hw])
      rw [← hcdef] at hev
      refine ⟨?_, hev.2⟩
      rw [hev.1, hpre _ (hsel _)]
    · rw [if_neg h, if_neg h]
      obtain ⟨ih1, ih2⟩ := ih q (by omega)
      refine ⟨?_, fun hr w hw => ?_⟩
      · rw [ht2, run_prefix _ t2 X _ (by rw [hX]; exact hc1 q (by omega))]
        exact ih1
      · rw [ht2, run_prefix _ t2 X _ (by rw [hX]; exact hm1 q (by omega) w hw)]
        exact ih2 hr w hw

private def buildT (M₀ cF top P : ℕ) (slot : ℕ → ℕ) (cw : ℕ → ℕ) :
    ℕ → List Gate → List Gate × ℕ × (ℕ → ℕ)
  | 0, gs => (gs, cF, fun _ => cF)
  | n + 1, gs =>
    let res := buildT M₀ cF top P slot cw n gs
    let c := chain GateOp.or M₀ (res.1, res.2.1) (((List.range P).filter (fun q => slot q = top - n)).map cw)
    (c.1, c.2, fun v => if v = top - n then c.2 else res.2.2 v)

private theorem buildT_props [DecidableEq GateOp] (M₀ cF top P : ℕ) (slot : ℕ → ℕ) (cw : ℕ → ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hcw : ∀ q < P, cw q < M₀ + gs.length) :
    ∀ n, (∃ tail, (buildT M₀ cF top P slot cw n gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
        posCount tail = ∑ j ∈ Finset.range n, ((List.range P).filter (fun q => slot q = top - j)).length) ∧
      Good M₀ (buildT M₀ cF top P slot cw n gs).1 ∧
      (buildT M₀ cF top P slot cw n gs).2.1 < M₀ + (buildT M₀ cF top P slot cw n gs).1.length ∧
      (∀ v, (buildT M₀ cF top P slot cw n gs).2.2 v < M₀ + (buildT M₀ cF top P slot cw n gs).1.length) := by
  intro n
  induction n with
  | zero => exact ⟨⟨[], by simp [buildT], negCount_nil, by simp [posCount_nil]⟩, hgs, hcF, fun _ => hcF⟩
  | succ n ih =>
    obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hc1, hv1⟩ := ih
    set res := buildT M₀ cF top P slot cw n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    set L := ((List.range P).filter (fun q => slot q = top - n)).map cw
    have hL : ∀ v ∈ L, v < M₀ + res.1.length := by
      intro v hv
      simp only [L, List.mem_map, List.mem_filter, List.mem_range] at hv
      obtain ⟨q, ⟨hq, _⟩, rfl⟩ := hv
      have := hcw q hq; omega
    obtain ⟨⟨t2, ht2, hn2, hp2⟩, hg2, hc2⟩ := chain_props GateOp.or (Or.inr rfl) M₀ L res.1 res.2.1 hg1 hc1 hL
    set c := chain GateOp.or M₀ (res.1, res.2.1) L
    have hl2 : res.1.length ≤ c.1.length := by rw [ht2, List.length_append]; omega
    refine ⟨⟨t1 ++ t2, ?_, ?_, ?_⟩, hg2, hc2, fun v => ?_⟩
    · show c.1 = _
      rw [ht2, ht1, List.append_assoc]
    · rw [negCount_append, hn1, hn2]
    · rw [posCount_append, hp1, hp2, Finset.sum_range_succ]
      simp [L]
    · show (if v = top - n then c.2 else res.2.2 v) < M₀ + c.1.length
      by_cases h : v = top - n
      · rw [if_pos h]; exact hc2
      · rw [if_neg h]; exact lt_of_lt_of_le (hv1 v) (by omega)

private theorem buildT_eval [DecidableEq GateOp] (M₀ cF top P : ℕ) (slot : ℕ → ℕ) (cw : ℕ → ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length)
    (hcw : ∀ q < P, cw q < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀) (hcFv : (run gs X).getD cF false = false) :
    ∀ n ≤ top,
      ((run (buildT M₀ cF top P slot cw n gs).1 X).getD (buildT M₀ cF top P slot cw n gs).2.1 false = true ↔
        ∃ q < P, top - n < slot q ∧ slot q ≤ top ∧ (run gs X).getD (cw q) false = true) ∧
      ∀ v, top - n < v → v ≤ top →
        ((run (buildT M₀ cF top P slot cw n gs).1 X).getD ((buildT M₀ cF top P slot cw n gs).2.2 v) false = true ↔
          ∃ q < P, v ≤ slot q ∧ slot q ≤ top ∧ (run gs X).getD (cw q) false = true) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, fun v h1 h2 => by omega⟩
    show (run gs X).getD cF false = true ↔ _
    rw [hcFv]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro q _ h1 h2
    omega
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨⟨t1, ht1, _, _⟩, hg1, hc1, hv1⟩ := buildT_props M₀ cF top P slot cw gs hgs hcF hcw n
    set res := buildT M₀ cF top P slot cw n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    have hpre : ∀ w < M₀ + gs.length, (run res.1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    set L := ((List.range P).filter (fun q => slot q = top - n)).map cw
    have hL : ∀ v ∈ L, v < M₀ + res.1.length := by
      intro v hv
      simp only [L, List.mem_map, List.mem_filter, List.mem_range] at hv
      obtain ⟨q, ⟨hq, _⟩, rfl⟩ := hv
      have := hcw q hq; omega
    obtain ⟨⟨t2, ht2, _, _⟩, _, hc2⟩ := chain_props GateOp.or (Or.inr rfl) M₀ L res.1 res.2.1 hg1 hc1 hL
    set c := chain GateOp.or M₀ (res.1, res.2.1) L
    have hcv : (run c.1 X).getD c.2 false = true ↔
        ∃ q < P, top - (n + 1) < slot q ∧ slot q ≤ top ∧ (run gs X).getD (cw q) false = true := by
      rw [chain_eval GateOp.or M₀ L res.1 res.2.1 hL X hX, foldl_or, Bool.or_eq_true, ih1, List.any_eq_true]
      constructor
      · rintro (⟨q, hq, h1, h2, h3⟩ | ⟨v, hv, hval⟩)
        · exact ⟨q, hq, by omega, h2, h3⟩
        · simp only [L, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hv
          obtain ⟨q, ⟨hq, hsq⟩, rfl⟩ := hv
          refine ⟨q, hq, by omega, by omega, ?_⟩
          rw [← hpre _ (hcw q hq)]; exact hval
      · rintro ⟨q, hq, h1, h2, h3⟩
        by_cases hs : slot q = top - n
        · right
          refine ⟨cw q, ?_, ?_⟩
          · simp only [L, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
            exact ⟨q, ⟨hq, hs⟩, rfl⟩
          · rw [hpre _ (hcw q hq)]; exact h3
        · left; exact ⟨q, hq, by omega, h2, h3⟩
    refine ⟨hcv, fun v h1 h2 => ?_⟩
    show (run c.1 X).getD (if v = top - n then c.2 else res.2.2 v) false = true ↔ _
    by_cases h : v = top - n
    · rw [if_pos h, hcv]
      constructor
      · rintro ⟨q, hq, h3, h4, h5⟩; exact ⟨q, hq, by omega, h4, h5⟩
      · rintro ⟨q, hq, h3, h4, h5⟩; exact ⟨q, hq, by omega, h4, h5⟩
    · rw [if_neg h, ht2, run_prefix _ t2 X _ (by rw [hX]; exact hv1 v)]
      exact ih2 v (by omega) h2

private theorem filter_range_succ_length (p : ℕ → Bool) (P : ℕ) :
    ((List.range (P + 1)).filter p).length = ((List.range P).filter p).length + (if p P then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : p P <;> simp [h]

private theorem buildT_count (slot : ℕ → ℕ) (top : ℕ) : ∀ n ≤ top + 1, ∀ P,
    ∑ j ∈ Finset.range n, ((List.range P).filter (fun q => slot q = top - j)).length ≤ P := by
  intro n hn P
  induction P with
  | zero => simp
  | succ P ih =>
    have e : ∀ j, ((List.range (P + 1)).filter (fun q => slot q = top - j)).length =
        ((List.range P).filter (fun q => slot q = top - j)).length + (if slot P = top - j then 1 else 0) := by
      intro j
      rw [filter_range_succ_length]
      simp
    simp only [e, Finset.sum_add_distrib]
    have h1 : ∑ j ∈ Finset.range n, (if slot P = top - j then 1 else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_range] at ha hb
      omega
    omega

private def buildOut (M₀ t : ℕ) (Iw sw : ℕ → ℕ) (fw : ℕ → ℕ → ℕ) :
    ℕ → List Gate → List Gate × (ℕ → ℕ → ℕ)
  | 0, gs => (gs, fun _ _ => 0)
  | n + 1, gs =>
    let res := buildOut M₀ t Iw sw fw n gs
    let gs1 := res.1 ++ [⟨GateOp.and, [Iw n, sw n]⟩]
    let r2 := pushAndList M₀ gs1 ((List.range t).map (fun a => (M₀ + res.1.length, fw n a)))
    (r2.1, fun q a => if q = n then r2.2.getD a 0 else res.2 q a)

private theorem buildOut_props [DecidableEq GateOp] (M₀ t : ℕ) (Iw sw : ℕ → ℕ) (fw : ℕ → ℕ → ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hIw : ∀ q, Iw q < M₀ + gs.length) (hsw : ∀ q, sw q < M₀ + gs.length)
    (hfw : ∀ q, ∀ a < t, fw q a < M₀ + gs.length) :
    ∀ n, (∃ tail, (buildOut M₀ t Iw sw fw n gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
        posCount tail = n * (1 + t)) ∧
      Good M₀ (buildOut M₀ t Iw sw fw n gs).1 ∧
      (∀ q < n, ∀ a < t, (buildOut M₀ t Iw sw fw n gs).2 q a < M₀ + (buildOut M₀ t Iw sw fw n gs).1.length) := by
  intro n
  induction n with
  | zero => exact ⟨⟨[], by simp [buildOut], negCount_nil, by simp [posCount_nil]⟩, hgs, fun q hq => absurd hq (by omega)⟩
  | succ n ih =>
    obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hc1⟩ := ih
    set res := buildOut M₀ t Iw sw fw n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    set g : Gate := ⟨GateOp.and, [Iw n, sw n]⟩
    have hgn : g.op ≠ GateOp.not := fun h => GateOp.noConfusion h
    have hg1' : Good M₀ (res.1 ++ [g]) := by
      apply good_snoc hg1 g (by simp [g]) (by simp [g])
      intro u hu; simp [g] at hu
      rcases hu with rfl | rfl
      · have := hIw n; omega
      · have := hsw n; omega
    set ps := (List.range t).map (fun a => (M₀ + res.1.length, fw n a))
    have hps : ∀ p ∈ ps, p.1 < M₀ + (res.1 ++ [g]).length ∧ p.2 < M₀ + (res.1 ++ [g]).length := by
      intro p hp
      simp only [ps, List.mem_map, List.mem_range] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      simp only [List.length_append, List.length_singleton]
      have := hfw n a ha
      constructor <;> omega
    obtain ⟨⟨t2, ht2, _, hn2, hp2⟩, hlen2, hg2, hm2, _⟩ := pushAndList_props M₀ (res.1 ++ [g]) ps hg1' hps
    set r2 := pushAndList M₀ (res.1 ++ [g]) ps
    refine ⟨⟨t1 ++ [g] ++ t2, ?_, ?_, ?_⟩, hg2, fun q hq a ha => ?_⟩
    · show r2.1 = _
      rw [ht2, ht1]; simp [List.append_assoc]
    · rw [negCount_append, negCount_append, hn1, hn2]; simp [negCount, hgn]
    · have hpg : posCount [g] = 1 := by simp [posCount, hgn]
      rw [posCount_append, posCount_append, hp1, hp2, hpg]
      simp [ps]; ring
    · show (if q = n then r2.2.getD a 0 else res.2 q a) < M₀ + r2.1.length
      have hl2 : res.1.length + 1 ≤ r2.1.length := by
        rw [ht2]; simp only [List.length_append, List.length_singleton]; omega
      by_cases h : q = n
      · rw [if_pos h]
        apply hm2
        have : a < r2.2.length := by rw [hlen2]; simp [ps, ha]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
        exact List.getElem_mem this
      · rw [if_neg h]; exact lt_of_lt_of_le (hc1 q (by omega) a ha) (by omega)

private theorem buildOut_eval [DecidableEq GateOp] (M₀ t : ℕ) (Iw sw : ℕ → ℕ) (fw : ℕ → ℕ → ℕ)
    (gs : List Gate) (hgs : Good M₀ gs) (hIw : ∀ q, Iw q < M₀ + gs.length) (hsw : ∀ q, sw q < M₀ + gs.length)
    (hfw : ∀ q, ∀ a < t, fw q a < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀) :
    ∀ n, ∀ q < n, ∀ a < t, (run (buildOut M₀ t Iw sw fw n gs).1 X).getD ((buildOut M₀ t Iw sw fw n gs).2 q a) false =
      (((run gs X).getD (Iw q) false && (run gs X).getD (sw q) false) && (run gs X).getD (fw q a) false) := by
  intro n
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq a ha
    obtain ⟨⟨t1, ht1, _, _⟩, hg1, hc1⟩ := buildOut_props M₀ t Iw sw fw gs hgs hIw hsw hfw n
    set res := buildOut M₀ t Iw sw fw n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    have hpre : ∀ w < M₀ + gs.length, (run res.1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    set g : Gate := ⟨GateOp.and, [Iw n, sw n]⟩
    have hg1' : Good M₀ (res.1 ++ [g]) := by
      apply good_snoc hg1 g (by simp [g]) (by simp [g])
      intro u hu; simp [g] at hu
      rcases hu with rfl | rfl
      · have := hIw n; omega
      · have := hsw n; omega
    set ps := (List.range t).map (fun a => (M₀ + res.1.length, fw n a))
    have hps : ∀ p ∈ ps, p.1 < M₀ + (res.1 ++ [g]).length ∧ p.2 < M₀ + (res.1 ++ [g]).length := by
      intro p hp
      simp only [ps, List.mem_map, List.mem_range] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      simp only [List.length_append, List.length_singleton]
      have := hfw n a ha
      constructor <;> omega
    obtain ⟨⟨t2, ht2, _, _⟩, hlen2, hg2, hm2, hev2⟩ := pushAndList_props M₀ (res.1 ++ [g]) ps hg1' hps
    set r2 := pushAndList M₀ (res.1 ++ [g]) ps
    have hpre1 : ∀ w < M₀ + res.1.length, (run (res.1 ++ [g]) X).getD w false = (run res.1 X).getD w false := by
      intro w hw; rw [run_prefix res.1 [g] X w (by rw [hX]; exact hw)]
    show (run r2.1 X).getD (if q = n then r2.2.getD a 0 else res.2 q a) false = _
    by_cases h : q = n
    · subst h
      rw [if_pos rfl]
      have hlt : a < ps.length := by simp [ps, ha]
      rw [hev2 X hX a hlt]
      have hpa : ps.getD a (0, 0) = (M₀ + res.1.length, fw q a) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        simp [ps]
      rw [hpa]
      dsimp only
      have hrlen : (run res.1 X).length = M₀ + res.1.length := by rw [run_length, hX]
      have hd : (run (res.1 ++ [g]) X).getD (M₀ + res.1.length) false =
          ((run gs X).getD (Iw q) false && (run gs X).getD (sw q) false) := by
        rw [run_snoc, ← hrlen, getD_eq]
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [hpre _ (hIw q), hpre _ (hsw q)]
      rw [hd, hpre1 _ (by have := hfw q a ha; omega), hpre _ (hfw q a ha)]
    · rw [if_neg h, ht2, List.append_assoc, run_prefix _ ([g] ++ t2) X _ (by rw [hX]; exact hc1 q (by omega) a ha)]
      exact ih q (by omega) a ha

private def mkTaps (M₀ cF : ℕ) (lst : ℕ → List ℕ) : ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, fun _ => cF)
  | n + 1, gs =>
    let res := mkTaps M₀ cF lst n gs
    let r := pushOrList M₀ cF res.1 (lst n)
    (r.1, fun a => if a = n then r.2 else res.2 a)

private theorem mkTaps_props [DecidableEq GateOp] (M₀ cF : ℕ) (lst : ℕ → List ℕ) (gs : List Gate)
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length) (hl : ∀ a, ∀ w ∈ lst a, w < M₀ + gs.length) :
    ∀ n, (∃ tail, (mkTaps M₀ cF lst n gs).1 = gs ++ tail ∧ negCount tail = 0 ∧
        posCount tail = ∑ a ∈ Finset.range n, ((lst a).length - 1)) ∧
      Good M₀ (mkTaps M₀ cF lst n gs).1 ∧
      (∀ a < n, (mkTaps M₀ cF lst n gs).2 a < M₀ + (mkTaps M₀ cF lst n gs).1.length) := by
  intro n
  induction n with
  | zero => exact ⟨⟨[], by simp [mkTaps], negCount_nil, by simp [posCount_nil]⟩, hgs, fun a ha => absurd ha (by omega)⟩
  | succ n ih =>
    obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hc1⟩ := ih
    set res := mkTaps M₀ cF lst n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    obtain ⟨⟨t2, ht2, _, hn2, hp2⟩, hg2, hc2, _⟩ := pushOrList_props M₀ cF res.1 (lst n) hg1 (by omega)
      (fun w hw => by have := hl n w hw; omega)
    set r := pushOrList M₀ cF res.1 (lst n)
    have hl2 : res.1.length ≤ r.1.length := by rw [ht2, List.length_append]; omega
    refine ⟨⟨t1 ++ t2, ?_, ?_, ?_⟩, hg2, fun a ha => ?_⟩
    · show r.1 = _
      rw [ht2, ht1, List.append_assoc]
    · rw [negCount_append, hn1, hn2]
    · rw [posCount_append, hp1, hp2, Finset.sum_range_succ]
    · show (if a = n then r.2 else res.2 a) < M₀ + r.1.length
      by_cases h : a = n
      · rw [if_pos h]; exact hc2
      · rw [if_neg h]; exact lt_of_lt_of_le (hc1 a (by omega)) (by omega)

private theorem mkTaps_eval [DecidableEq GateOp] (M₀ cF : ℕ) (lst : ℕ → List ℕ) (gs : List Gate)
    (hgs : Good M₀ gs) (hcF : cF < M₀ + gs.length) (hl : ∀ a, ∀ w ∈ lst a, w < M₀ + gs.length)
    (X : List Bool) (hX : X.length = M₀) (hcFv : (run gs X).getD cF false = false) :
    ∀ n, ∀ a < n, (run (mkTaps M₀ cF lst n gs).1 X).getD ((mkTaps M₀ cF lst n gs).2 a) false =
      (lst a).any (fun w => (run gs X).getD w false) := by
  intro n
  induction n with
  | zero => intro a ha; omega
  | succ n ih =>
    intro a ha
    obtain ⟨⟨t1, ht1, _, _⟩, hg1, hc1⟩ := mkTaps_props M₀ cF lst gs hgs hcF hl n
    set res := mkTaps M₀ cF lst n gs
    have hl1 : gs.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    have hpre : ∀ w < M₀ + gs.length, (run res.1 X).getD w false = (run gs X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs t1 X w (by rw [hX]; exact hw)]
    obtain ⟨⟨t2, ht2, _, _, _⟩, _, _, hev⟩ := pushOrList_props M₀ cF res.1 (lst n) hg1 (by omega)
      (fun w hw => by have := hl n w hw; omega)
    set r := pushOrList M₀ cF res.1 (lst n)
    show (run r.1 X).getD (if a = n then r.2 else res.2 a) false = _
    by_cases h : a = n
    · subst h
      rw [if_pos rfl, hev X hX (by rw [hpre cF hcF, hcFv])]
      exact any_congr' (fun w hw => hpre w (hl a w hw))
    · rw [if_neg h, ht2, run_prefix _ t2 X _ (by rw [hX]; exact hc1 a (by omega))]
      exact ih a (by omega)

section Facts
open scoped Classical

noncomputable def bitsL {d : ℕ} (x : Finset (Fin d)) : List Bool :=
  List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]

noncomputable def rk [DecidableEq GateOp] {d : ℕ} (C : Circuit) (x : Finset (Fin d)) : ℕ :=
  (notIdxList C).foldl (fun v j => 2 * v + (if (C.wires (bitsL x)).getD (d + 2 + j) false then 0 else 1)) 0

noncomputable def sts [DecidableEq GateOp] {d : ℕ} (G : Finset (Finset (Fin d))) (C : Circuit) : Finset ℕ :=
  G.image (rk C)

noncomputable def srt [DecidableEq GateOp] {d : ℕ} (G : Finset (Finset (Fin d))) (C : Circuit) : List ℕ :=
  (sts G C).sort (· ≤ ·)

noncomputable def ps [DecidableEq GateOp] {d : ℕ} (G : Finset (Finset (Fin d))) (C : Circuit)
    (x : Finset (Fin d)) : ℕ :=
  ((sts G C).filter (fun v => v < rk C x)).card

noncomputable def wd {d t : ℕ} (C : Circuit) (o : Fin t → ℕ) (x : Finset (Fin d)) (a : Fin t) : Bool :=
  (C.wires (bitsL x)).getD (o a) false

theorem bitsL_length {d : ℕ} (x : Finset (Fin d)) : (bitsL x).length = d + 2 := by
  simp [bitsL]

theorem rk_lt [DecidableEq GateOp] {d : ℕ} (C : Circuit) (x : Finset (Fin d)) :
    rk C x < 2 ^ PEqualNP.NotBracket.notCount C := by
  have h := rank_eq_foldBits d C x
  dsimp only at h
  have h2 : rk C x = foldBits ((notIdxList C).map (fun j =>
      !((C.wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false))) := h
  rw [h2]
  have hlt := foldBits_lt ((notIdxList C).map (fun j =>
    !((C.wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false)))
  simpa [notIdxList_length] using hlt

theorem filter_lt_sorted : ∀ (L : List ℕ), L.Pairwise (· < ·) → ∀ s (hs : s < L.length),
    (L.filter (fun v => decide (v < L[s]))).length = s := by
  intro L
  induction L with
  | nil => intro _ s hs; simp at hs
  | cons a L ih =>
    intro hp s hs
    rw [List.pairwise_cons] at hp
    cases s with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [List.filter_cons, if_neg (by simp)]
      rw [List.filter_eq_nil_iff.2]
      · rfl
      · intro v hv; have := hp.1 v hv; simp; omega
    | succ s =>
      simp only [List.getElem_cons_succ]
      have hs' : s < L.length := by simpa using hs
      have hlt : a < L[s] := hp.1 _ (List.getElem_mem hs')
      rw [List.filter_cons, if_pos (by simpa using hlt), List.length_cons, ih hp.2 s hs']

theorem pos_facts [DecidableEq GateOp] {d : ℕ} (G : Finset (Finset (Fin d))) (C : Circuit)
    (hG : G.Nonempty) :
    1 ≤ (sts G C).card ∧
    (∀ x ∈ G, ps G C x < (sts G C).card) ∧
    (∀ x ∈ G, (srt G C).getD (ps G C x) 0 = rk C x) ∧
    (∀ x ∈ G, ∀ s < (sts G C).card, (srt G C).getD s 0 ≤ rk C x → s ≤ ps G C x) ∧
    (∀ s, (srt G C).getD s 0 < 2 ^ PEqualNP.NotBracket.notCount C) ∧
    (∃ x ∈ G, ps G C x + 1 = (sts G C).card) ∧ (∃ x ∈ G, ps G C x = 0) := by
  set S := sts G C
  set L := srt G C
  have hLS : L.toFinset = S := Finset.sort_toFinset _ _
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  have hLp : L.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S)
  have hLlen : L.length = S.card := Finset.length_sort _
  have hmemL : ∀ v, v ∈ L ↔ v ∈ S := fun v => Finset.mem_sort _
  have hcard : ∀ v, (S.filter (fun w => w < v)).card = (L.filter (fun w => decide (w < v))).length := by
    intro v
    have e : L.toFinset.filter (fun w => w < v) = (L.filter (fun w => decide (w < v))).toFinset := by
      ext w; simp
    rw [← hLS, e, List.toFinset_card_of_nodup (hLnd.filter _)]
  have hidx : ∀ x ∈ G, ∃ s0, ∃ h : s0 < L.length, L[s0] = rk C x ∧ ps G C x = s0 := by
    intro x hx
    have hm : rk C x ∈ L := (hmemL _).2 (Finset.mem_image_of_mem _ hx)
    obtain ⟨s0, hs0, he⟩ := List.mem_iff_getElem.1 hm
    refine ⟨s0, hs0, he, ?_⟩
    show (S.filter (fun w => w < rk C x)).card = s0
    rw [hcard, ← he, filter_lt_sorted L hLp s0 hs0]
  have hne : S.Nonempty := hG.image _
  refine ⟨hne.card_pos, fun x hx => ?_, fun x hx => ?_, fun x hx s hs hle => ?_, fun s => ?_, ?_, ?_⟩
  · obtain ⟨s0, hs0, _, hp⟩ := hidx x hx
    rw [hp, ← hLlen]; exact hs0
  · obtain ⟨s0, hs0, he, hp⟩ := hidx x hx
    rw [hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs0]
    simpa using he
  · obtain ⟨s0, hs0, he, hp⟩ := hidx x hx
    rw [hp]
    by_contra hlt
    have hs' : s < L.length := by rw [hLlen]; exact hs
    have := (List.pairwise_iff_getElem.mp hLp) s0 s hs0 hs' (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs'] at hle
    simp at hle
    omega
  · by_cases hs : s < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
      have hm : L[s] ∈ S := (hmemL _).1 (List.getElem_mem hs)
      obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hm
      simp only [Option.getD_some]
      rw [← hx]; exact rk_lt C x
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]
      positivity
  · have hpos : 0 < L.length := by rw [hLlen]; exact hne.card_pos
    have hm : L[L.length - 1] ∈ S := (hmemL _).1 (List.getElem_mem (by omega))
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hm
    obtain ⟨s0, hs0, he, hp⟩ := hidx x hx
    refine ⟨x, hx, ?_⟩
    rw [hp, ← hLlen]
    have : s0 = L.length - 1 := by
      by_contra hne'
      have h1 : s0 < L.length - 1 := by omega
      have := (List.pairwise_iff_getElem.mp hLp) s0 (L.length - 1) hs0 (by omega) h1
      rw [he, ← hxe] at this
      exact lt_irrefl _ this
    omega
  · have hpos : 0 < L.length := by rw [hLlen]; exact hne.card_pos
    have hm : L[0] ∈ S := (hmemL _).1 (List.getElem_mem hpos)
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hm
    obtain ⟨s0, hs0, he, hp⟩ := hidx x hx
    refine ⟨x, hx, ?_⟩
    rw [hp]
    by_contra hne'
    have := (List.pairwise_iff_getElem.mp hLp) 0 s0 hpos hs0 (by omega)
    rw [he, ← hxe] at this
    exact lt_irrefl _ this

noncomputable def rawL {u d k : ℕ} (tag : Fin k → Finset (Fin u)) (i : Fin k) (X : Fin k → Finset (Fin d)) :
    List Bool :=
  List.ofFn (fun v : Fin u => decide (v ∈ tag i)) ++
    (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten ++ [false, true]

theorem rawL_facts {u d k : ℕ} (tag : Fin k → Finset (Fin u)) (i : Fin k) (X : Fin k → Finset (Fin d)) :
    (rawL tag i X).length = u + k * d + 2 ∧
    (∀ v : Fin u, (rawL tag i X).getD v.val false = decide (v ∈ tag i)) ∧
    (∀ (j : Fin k) (z : Fin d), (rawL tag i X).getD (u + j.val * d + z.val) false = decide (z ∈ X j)) ∧
    (rawL tag i X).getD (u + k * d) false = false ∧ (rawL tag i X).getD (u + k * d + 1) false = true := by
  have hfl : (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten.length = k * d :=
    flatten_ofFn_length _ (fun j => by simp)
  have hA : (List.ofFn (fun v : Fin u => decide (v ∈ tag i))).length = u := by simp
  refine ⟨?_, fun v => ?_, fun j z => ?_, ?_, ?_⟩
  · simp only [rawL, List.length_append, hA, hfl, List.length_cons, List.length_nil]
  · unfold rawL
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hA]; exact v.isLt)]
    simp
  · unfold rawL
    have h1 : u + j.val * d + z.val < u + (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten.length := by
      rw [hfl]
      have : (j.val + 1) * d ≤ k * d := Nat.mul_le_mul_right d j.isLt
      have : (j.val + 1) * d = j.val * d + d := by ring
      have := z.isLt
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_append, hA]; omega),
      List.getElem?_append_right (by rw [hA]; omega), hA, ← List.getD_eq_getElem?_getD]
    rw [show u + j.val * d + z.val - u = j.val * d + z.val by omega]
    rw [getD_flatten_ofFn _ (fun j => by simp) j z.val z.isLt]
    simp [List.getD_eq_getElem?_getD]
  · unfold rawL
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_append, hA, hfl]; omega)]
    simp [hA, hfl]
  · unfold rawL
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_append, hA, hfl]; omega)]
    simp [hA, hfl]

noncomputable def prs {k : ℕ} (m : Fin k → ℕ) : List (Fin k × ℕ) :=
  (List.finRange k).flatMap (fun i => (List.range (m i)).map (fun s => (i, s)))

theorem mem_prs {k : ℕ} (m : Fin k → ℕ) (i : Fin k) (s : ℕ) : (i, s) ∈ prs m ↔ s < m i := by
  simp [prs]

theorem prs_getD_mem {k : ℕ} (m : Fin k → ℕ) (dflt : Fin k × ℕ) (q : ℕ) (hq : q < (prs m).length) :
    (prs m).getD q dflt ∈ prs m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  exact List.getElem_mem hq

theorem prs_exists {k : ℕ} (m : Fin k → ℕ) (dflt : Fin k × ℕ) (i : Fin k) (s : ℕ) (hs : s < m i) :
    ∃ q < (prs m).length, (prs m).getD q dflt = (i, s) := by
  obtain ⟨q, hq, he⟩ := List.mem_iff_getElem.1 ((mem_prs m i s).2 hs)
  refine ⟨q, hq, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  simpa using he

theorem sum_range_getD {α : Type*} (F : α → ℕ) (dflt : α) : ∀ l : List α,
    ∑ q ∈ Finset.range l.length, F (l.getD q dflt) = (l.map F).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem prs_sum_aux {k : ℕ} (m : Fin k → ℕ) (f : Fin k → ℕ) : ∀ l : List (Fin k),
    ((l.flatMap (fun i => (List.range (m i)).map (fun s => (i, s)))).map (fun p => f p.1)).sum =
      (l.map (fun i => m i * f i)).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, prs_sum_aux m f l, List.map_cons, List.sum_cons]
    simp [List.map_map, Function.comp_def]

theorem prs_len_aux {k : ℕ} (m : Fin k → ℕ) : ∀ l : List (Fin k),
    (l.flatMap (fun i => (List.range (m i)).map (fun s => (i, s)))).length = (l.map m).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, prs_len_aux m l, List.map_cons, List.sum_cons]
    simp

theorem prs_sum {k : ℕ} (m : Fin k → ℕ) (f : Fin k → ℕ) (dflt : Fin k × ℕ) :
    ∑ q ∈ Finset.range (prs m).length, f ((prs m).getD q dflt).1 = ∑ i, m i * f i := by
  rw [sum_range_getD (fun p => f p.1) dflt (prs m)]
  unfold prs
  rw [prs_sum_aux, Fin.sum_univ_def]

theorem prs_length {k : ℕ} (m : Fin k → ℕ) : (prs m).length = ∑ i, m i := by
  unfold prs
  rw [prs_len_aux, Fin.sum_univ_def]

end Facts

section Core
open scoped Classical

theorem bitsL_lt {d : ℕ} (x : Finset (Fin d)) (w : ℕ) (hw : w < d) :
    (bitsL x).getD w false = decide ((⟨w, hw⟩ : Fin d) ∈ x) := by
  unfold bitsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
  simp [hw]

theorem bitsL_d {d : ℕ} (x : Finset (Fin d)) : (bitsL x).getD d false = false := by
  unfold bitsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem bitsL_d1 {d : ℕ} (x : Finset (Fin d)) : (bitsL x).getD (d + 1) false = true := by
  unfold bitsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem core [DecidableEq GateOp] (u d k t B : ℕ) (hk : 0 < k) (tag : Fin k → Finset (Fin u))
    (htag : Function.Injective tag) (G : Fin k → Finset (Finset (Fin d))) (A : Fin k → Circuit)
    (out : Fin k → Fin t → ℕ) (hG : ∀ i, (G i).Nonempty)
    (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (hout : ∀ i a, out i a < d + 2 + (A i).size)
    (base : Fin k → ℕ) (hb1 : ∀ i, base i + (sts (G i) (A i)).card ≤ 2 ^ B)
    (hb2 : ∀ i j, tag i ⊂ tag j → ∀ x ∈ G i, ∀ y ∈ G j,
      base i + ps (G i) (A i) x ≤ base j + ps (G j) (A j) y ∧
      ((∃ a, wd (A i) (out i) x a = true ∧ wd (A j) (out j) y a = false) →
        base i + ps (G i) (A i) x + 1 ≤ base j + ps (G j) (A j) y)) :
    ∃ (C : Circuit) (tap : Fin t → ℕ),
      (PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (u + k * d + 2) C ∧
        C.output < u + k * d + 2 + C.size) ∧
      (∀ a, tap a < u + k * d + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ B ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ k * u + 5 * 2 ^ B +
        ∑ i, (sts (G i) (A i)).card * (((A i).size - PEqualNP.NotBracket.notCount (A i)) +
          2 * PEqualNP.NotBracket.notCount (A i) + 2 * t + 4) ∧
      ∀ i (X : Fin k → Finset (Fin d)), X i ∈ G i → ∀ a,
        (C.wires (rawL tag i X)).getD (tap a) false = wd (A i) (out i) (X i) a := by
  have PF := fun i => pos_facts (G i) (A i) (hG i)
  let N := u + k * d
  let M₀ := N + 2
  let m : Fin k → ℕ := fun i => (sts (G i) (A i)).card
  let rr : Fin k → ℕ → ℕ := fun i s => (srt (G i) (A i)).getD s 0
  let dflt : Fin k × ℕ := (⟨0, hk⟩, 0)
  let P := (prs m).length
  let pq : ℕ → Fin k × ℕ := fun q => (prs m).getD q dflt
  let slot : ℕ → ℕ := fun q => base (pq q).1 + (pq q).2
  let top := 2 ^ B - 1
  have hB1 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  let tv : ℕ → List ℕ := fun i => if h : i < k then
    ((List.finRange u).filter (fun v => decide (v ∈ tag ⟨i, h⟩))).map Fin.val else []
  have htv_len : ∀ i, (tv i).length ≤ u := by
    intro i
    simp only [tv]
    split_ifs
    · rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    · simp
  have htv : ∀ i, ∀ v ∈ tv i, v < M₀ + ([] : List Gate).length := by
    intro i v hv
    simp only [tv] at hv
    split_ifs at hv
    · simp only [List.mem_map] at hv
      obtain ⟨z, _, rfl⟩ := hv
      have := z.isLt
      simp only [List.length_nil, M₀, N]; omega
    · simp at hv

  obtain ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hs1⟩ := buildSel_props M₀ (N + 1) tv [] (good_nil M₀)
    (by simp [M₀]) htv k
  set st1 := buildSel M₀ (N + 1) tv k [] with hst1
  have hl1 : M₀ ≤ M₀ + st1.1.length := by omega
  let sel : Fin k → ℕ := fun i => st1.2 i.val
  have hsel : ∀ i, sel i < M₀ + st1.1.length := fun i => hs1 i.val i.isLt
  let bIn : Fin k → ℕ → ℕ := fun i w => if w < d then u + i.val * d + w else if w = d then N else N + 1
  have hbIn_lt : ∀ i, ∀ w < d + 2, bIn i w < M₀ := by
    intro i w hw
    simp only [bIn]
    split_ifs
    · have h1 : (i.val + 1) * d ≤ k * d := Nat.mul_le_mul_right d i.isLt
      have h2 : (i.val + 1) * d = i.val * d + d := by ring
      simp only [M₀, N]; omega
    · simp only [M₀, N]; omega
    · simp only [M₀, N]; omega
  have hrr : ∀ i s, rr i s < 2 ^ PEqualNP.NotBracket.notCount (A i) := fun i s => (PF i).2.2.2.2.1 s

  obtain ⟨⟨t2, ht2, hn2, hp2⟩, hg2, hc2, hm2⟩ := buildStates_props d M₀ N (N + 1) A bIn rr sel pq st1.1 hA hg1
    (by omega) (by omega) hsel (fun i w hw => by have := hbIn_lt i w hw; omega) P
  set st2 := buildStates d M₀ N (N + 1) A bIn rr sel pq P st1.1 with hst2
  have hl2 : st1.1.length ≤ st2.1.length := by rw [ht2, List.length_append]; omega

  obtain ⟨⟨t3, ht3, hn3, hp3⟩, hg3, hc3, hv3⟩ := buildT_props M₀ N top P slot st2.2.1 st2.1 hg2 (by omega) hc2 top
  set st3 := buildT M₀ N top P slot st2.2.1 top st2.1 with hst3
  have hl3 : st2.1.length ≤ st3.1.length := by rw [ht3, List.length_append]; omega

  let T : List ℕ := (N + 1) :: (List.range top).map (fun j => st3.2.2 (j + 1))
  have hT : ∀ w ∈ T, w < M₀ + st3.1.length := by
    intro w hw
    simp only [T, List.mem_cons, List.mem_map, List.mem_range] at hw
    rcases hw with rfl | ⟨j, _, rfl⟩
    · omega
    · exact hv3 _
  have hTlen : T.length = 2 ^ B := by simp only [T, List.length_cons, List.length_map, List.length_range, top]; omega
  obtain ⟨⟨t4, ht4, hn4, hp4⟩, hlen4, hg4, hm4⟩ := decodeTree_props M₀ N (N + 1) T B st3.1 hg3 (by omega) (by omega) hT B le_rfl
  set st4 := decodeTree M₀ N (N + 1) T B st3.1 B with hst4
  have hl4 : st3.1.length ≤ st4.1.length := by rw [ht4, List.length_append]; omega

  let Iw : ℕ → ℕ := fun q => st4.2.getD (slot q) N
  let sw : ℕ → ℕ := fun q => sel (pq q).1
  let fw : ℕ → ℕ → ℕ := fun q a => if h : q < P ∧ a < t then st2.2.2 q (out (pq q).1 ⟨a, h.2⟩) else N
  have hIw : ∀ q, Iw q < M₀ + st4.1.length := by
    intro q
    simp only [Iw]
    by_cases h : slot q < st4.2.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact hm4 _ (List.getElem_mem h)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]; omega
  have hsw : ∀ q, sw q < M₀ + st4.1.length := fun q => by
    show sel (pq q).1 < M₀ + st4.1.length
    have := hsel (pq q).1; omega
  have hfw : ∀ q, ∀ a < t, fw q a < M₀ + st4.1.length := by
    intro q a ha
    simp only [fw]
    split_ifs with h
    · have := hm2 q h.1 _ (hout (pq q).1 ⟨a, h.2⟩); omega
    · omega
  obtain ⟨⟨t5, ht5, hn5, hp5⟩, hg5, hc5⟩ := buildOut_props M₀ t Iw sw fw st4.1 hg4 hIw hsw hfw P
  set st5 := buildOut M₀ t Iw sw fw P st4.1 with hst5
  have hl5 : st4.1.length ≤ st5.1.length := by rw [ht5, List.length_append]; omega

  let al : ℕ → ℕ → Prop := fun q a => ∃ h : a < t, ∃ x ∈ G (pq q).1,
    ps (G (pq q).1) (A (pq q).1) x = (pq q).2 ∧ wd (A (pq q).1) (out (pq q).1) x ⟨a, h⟩ = true
  let lst : ℕ → List ℕ := fun a => ((List.range P).filter (fun q => decide (al q a))).map (fun q => st5.2 q a)
  have hlst : ∀ a, ∀ w ∈ lst a, w < M₀ + st5.1.length := by
    intro a w hw
    simp only [lst, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hw
    obtain ⟨q, ⟨hq, ⟨hat, _⟩⟩, rfl⟩ := hw
    exact hc5 q hq a hat
  obtain ⟨⟨t6, ht6, hn6, hp6⟩, hg6, hc6⟩ := mkTaps_props M₀ N lst st5.1 hg5 (by omega) hlst t
  set st6 := mkTaps M₀ N lst t st5.1 with hst6
  have hl6 : st5.1.length ≤ st6.1.length := by rw [ht6, List.length_append]; omega
  refine ⟨⟨st6.1, 0⟩, fun a => st6.2 a.val, ⟨hg6.fanInTwo, hg6.readsBack, ?_⟩, fun a => hc6 a.val a.isLt, ?_, ?_, ?_⟩
  · show 0 < M₀ + st6.1.length; omega
  · rw [notCount_eq_negCount]
    show negCount st6.1 ≤ B
    rw [ht6, negCount_append, hn6, ht5, negCount_append, hn5, ht4, negCount_append, hn4, ht3, negCount_append, hn3,
      ht2, negCount_append, hn2, ht1, negCount_append, hn1]
    simp [negCount_nil]
  · rw [size_sub_notCount_eq_posCount]
    show posCount st6.1 ≤ _
    rw [ht6, posCount_append, hp6, ht5, posCount_append, hp5, ht4, posCount_append, ht3, posCount_append, hp3,
      ht2, posCount_append, hp2, ht1, posCount_append, hp1, posCount_nil]
    have e1 : ∑ i ∈ Finset.range k, (tv i).length ≤ k * u := by
      calc ∑ i ∈ Finset.range k, (tv i).length ≤ ∑ i ∈ Finset.range k, u := Finset.sum_le_sum (fun i _ => htv_len i)
        _ = k * u := by simp
    have e3 : ∑ j ∈ Finset.range top, ((List.range P).filter (fun q => slot q = top - j)).length ≤ P :=
      buildT_count slot top top (by omega) P
    have e6 : ∑ a ∈ Finset.range t, ((lst a).length - 1) ≤ t * P := by
      calc ∑ a ∈ Finset.range t, ((lst a).length - 1) ≤ ∑ a ∈ Finset.range t, P := by
            apply Finset.sum_le_sum
            intro a _
            simp only [lst, List.length_map]
            have := List.length_filter_le (fun q => decide (al q a)) (List.range P)
            rw [List.length_range] at this
            omega
        _ = t * P := by simp
    let f : Fin k → ℕ := fun i => ((A i).size - PEqualNP.NotBracket.notCount (A i)) +
      2 * PEqualNP.NotBracket.notCount (A i) + 2 * t + 4
    have hfs := prs_sum m f dflt
    have e2 : ∑ q ∈ Finset.range P, (((A (pq q).1).size - PEqualNP.NotBracket.notCount (A (pq q).1)) +
        PEqualNP.NotBracket.notCount (A (pq q).1) + 1) + P * (2 * t + 3) ≤
        ∑ q ∈ Finset.range P, f (pq q).1 := by
      have : P * (2 * t + 3) = ∑ q ∈ Finset.range P, (2 * t + 3) := by simp
      rw [this, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q _
      simp only [f]
      omega
    have hfs' : ∑ q ∈ Finset.range P, f (pq q).1 = ∑ i, m i * f i := hfs
    rw [hfs'] at e2
    have e4 := hp4
    show _ ≤ k * u + 5 * 2 ^ B + ∑ i, m i * f i
    have hP2 : P * (1 + t) + P + t * P + P = P * (2 * t + 3) := by ring
    omega
  · intro j0 X hX a
    set Xl := rawL tag j0 X with hXldef
    obtain ⟨hXlen, hXtag, hXblk, hXF, hXT⟩ := rawL_facts tag j0 X
    have hXl : Xl.length = M₀ := hXlen
    have v0 : ∀ gs : List Gate, ∀ w < M₀, (run gs Xl).getD w false = Xl.getD w false :=
      fun gs w hw => run_input gs Xl w (by omega)
    have vF : ∀ gs : List Gate, (run gs Xl).getD N false = false := fun gs => by rw [v0 gs N (by omega)]; exact hXF
    have vT : ∀ gs : List Gate, (run gs Xl).getD (N + 1) false = true := fun gs => by rw [v0 gs (N + 1) (by omega)]; exact hXT

    have ev1 := buildSel_eval M₀ (N + 1) tv [] (good_nil M₀) (by simp [M₀]) htv Xl hXl (vT []) k
    have sel_val : ∀ i : Fin k, (run st1.1 Xl).getD (sel i) false = decide (tag i ⊆ tag j0) := by
      intro i
      rw [ev1 i.val i.isLt]
      simp only [tv, dif_pos i.isLt]
      apply Bool.eq_iff_iff.2
      rw [List.all_eq_true, decide_eq_true_iff]
      constructor
      · intro h z hz
        have := h z.val (List.mem_map.2 ⟨z, List.mem_filter.2 ⟨List.mem_finRange z, by simpa using hz⟩, rfl⟩)
        rw [v0 [] z.val (by have := z.isLt; simp only [M₀, N]; omega), hXtag z] at this
        exact of_decide_eq_true this
      · intro hsub v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
        have hz' : z ∈ tag i := by simpa using (List.mem_filter.1 hz).2
        rw [v0 [] z.val (by have := z.isLt; simp only [M₀, N]; omega), hXtag z]
        exact decide_eq_true (hsub hz')

    have hbv : ∀ i, ∀ w < d + 2, (run st1.1 Xl).getD (bIn i w) false = (bitsL (X i)).getD w false := by
      intro i w hw
      rw [v0 st1.1 _ (hbIn_lt i w hw)]
      simp only [bIn]
      split_ifs with h1 h2
      · rw [hXblk i ⟨w, h1⟩, bitsL_lt (X i) w h1]
      · subst h2; rw [bitsL_d]; exact hXF
      · have : w = d + 1 := by omega
        subst this; rw [bitsL_d1]; exact hXT
    have ev2 := buildStates_eval d M₀ N (N + 1) A bIn rr sel pq st1.1 hA hg1 (by omega) (by omega) hsel
      (fun i w hw => by have := hbIn_lt i w hw; omega) hrr Xl hXl (vF _) (vT _) (fun i => bitsL (X i))
      (fun i => bitsL_length _) hbv P
    have cut_val : ∀ q < P, (run st2.1 Xl).getD (st2.2.1 q) false =
        (decide (tag (pq q).1 ⊆ tag j0) && decide (rr (pq q).1 (pq q).2 ≤ rk (A (pq q).1) (X (pq q).1))) := by
      intro q hq
      rw [← sel_val]
      exact (ev2 q hq).1
    have map_val : ∀ q < P, rr (pq q).1 (pq q).2 = rk (A (pq q).1) (X (pq q).1) →
        ∀ w < d + 2 + (A (pq q).1).size, (run st2.1 Xl).getD (st2.2.2 q w) false =
          ((A (pq q).1).wires (bitsL (X (pq q).1))).getD w false :=
      fun q hq hr => (ev2 q hq).2 hr

    have pq_mem : ∀ q < P, (pq q).2 < m (pq q).1 := by
      intro q hq
      have h := prs_getD_mem m dflt q hq
      rw [← Prod.mk.eta (p := (prs m).getD q dflt)] at h
      exact (mem_prs m _ _).1 h
    have slot_lt : ∀ q < P, slot q < 2 ^ B := by
      intro q hq; have := pq_mem q hq; have := hb1 (pq q).1; simp only [slot]; simp only [m] at *; omega
    have sub_cases : ∀ i, tag i ⊆ tag j0 → i = j0 ∨ tag i ⊂ tag j0 := by
      intro i hsub
      by_cases h : tag i = tag j0
      · exact Or.inl (htag h)
      · exact Or.inr (HasSubset.Subset.ssubset_of_ne hsub h)
    have tie : ∀ i, tag i ⊂ tag j0 → base i + (m i - 1) ≤ base j0 := by
      intro i hi
      obtain ⟨x, hx, hxt⟩ := (PF i).2.2.2.2.2.1
      obtain ⟨y, hy, hyb⟩ := (PF j0).2.2.2.2.2.2
      have := (hb2 i j0 hi x hx y hy).1
      simp only [m]; omega
    set σ := base j0 + ps (G j0) (A j0) (X j0) with hσ
    have hps0 : ps (G j0) (A j0) (X j0) < m j0 := (PF j0).2.1 _ hX
    have hσlt : σ < 2 ^ B := by have := hb1 j0; simp only [m] at hps0; omega
    obtain ⟨q0, hq0, hpq0⟩ := prs_exists m dflt j0 _ hps0
    have hq0a : (pq q0).1 = j0 := by simp only [pq]; rw [hpq0]
    have hq0b : (pq q0).2 = ps (G j0) (A j0) (X j0) := by simp only [pq]; rw [hpq0]
    have rr0 : rr j0 (ps (G j0) (A j0) (X j0)) = rk (A j0) (X j0) := (PF j0).2.2.1 _ hX
    have cut_le : ∀ q < P, (run st2.1 Xl).getD (st2.2.1 q) false = true → slot q ≤ σ := by
      intro q hq hcut
      rw [cut_val q hq, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hcut
      obtain ⟨hsub, hle⟩ := hcut
      rcases sub_cases _ hsub with h | h
      · have hs := pq_mem q hq
        rw [h] at hle hs
        have := (PF j0).2.2.2.1 _ hX _ hs hle
        simp only [slot, σ]; rw [h]; omega
      · have := tie _ h
        have := pq_mem q hq
        simp only [slot, σ]; omega
    have cut_q0 : (run st2.1 Xl).getD (st2.2.1 q0) false = true := by
      rw [cut_val q0 hq0, hq0a, hq0b, rr0]
      simp
    have slot_q0 : slot q0 = σ := by simp only [slot, σ]; rw [hq0a, hq0b]

    have ev3 := (buildT_eval M₀ N top P slot st2.2.1 st2.1 hg2 (by omega) hc2 Xl hXl (vF _) top le_rfl).2
    have hTval : ∀ w < 2 ^ B, (run st3.1 Xl).getD (T.getD w N) false = decide (w ≤ σ) := by
      intro w hw
      cases w with
      | zero => simp only [T, List.getD_cons_zero]; rw [vT]; simp
      | succ v =>
        have hv : v < top := by simp only [top]; omega
        have hget : T.getD (v + 1) N = st3.2.2 (v + 1) := by
          simp only [T, List.getD_cons_succ]
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
          rfl
        rw [hget]
        apply Bool.eq_iff_iff.2
        rw [ev3 (v + 1) (by omega) (by omega), decide_eq_true_iff]
        constructor
        · rintro ⟨q, hq, h1, _, h3⟩; exact le_trans h1 (cut_le q hq h3)
        · intro h
          exact ⟨q0, hq0, by rw [slot_q0]; exact h, by have := slot_lt q0 hq0; simp only [top]; omega, cut_q0⟩

    have ev4 := decodeTree_eval M₀ N (N + 1) T B st3.1 hg3 (by omega) (by omega) hT Xl hXl (vF _) (vT _)
      σ hσlt (by rw [hTlen]) hTval B le_rfl
    have ind_val : ∀ c < 2 ^ B, (run st4.1 Xl).getD (st4.2.getD c N) false = decide (σ = c) := by
      intro c hc
      have := ev4 c (by simpa using hc)
      simpa using this

    have ev5 := buildOut_eval M₀ t Iw sw fw st4.1 hg4 hIw hsw hfw Xl hXl P
    have pre41 : ∀ w < M₀ + st1.1.length, (run st4.1 Xl).getD w false = (run st1.1 Xl).getD w false := by
      intro w hw
      rw [ht4, ht3, ht2, List.append_assoc, List.append_assoc,
        run_prefix st1.1 (t2 ++ (t3 ++ t4)) Xl w (by rw [hXl]; exact hw)]
    have pre42 : ∀ w < M₀ + st2.1.length, (run st4.1 Xl).getD w false = (run st2.1 Xl).getD w false := by
      intro w hw
      rw [ht4, ht3, List.append_assoc, run_prefix st2.1 (t3 ++ t4) Xl w (by rw [hXl]; exact hw)]
    have con_val : ∀ q < P, ∀ (a : Fin t), (run st5.1 Xl).getD (st5.2 q a.val) false =
        ((decide (σ = slot q) && decide (tag (pq q).1 ⊆ tag j0)) &&
          (run st2.1 Xl).getD (st2.2.2 q (out (pq q).1 a)) false) := by
      intro q hq a
      rw [ev5 q hq a.val a.isLt]
      simp only [Iw, sw, fw, dif_pos (And.intro hq a.isLt)]
      rw [ind_val _ (slot_lt q hq), pre41 _ (hsel _), sel_val, pre42 _ (hm2 q hq _ (hout _ _))]

    have ev6 := mkTaps_eval M₀ N lst st5.1 hg5 (by omega) hlst Xl hXl (vF _) t a.val a.isLt
    show (run st6.1 Xl).getD (st6.2 a.val) false = _
    rw [ev6]
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨w, hw, hval⟩
      simp only [lst, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hw
      obtain ⟨q, ⟨hq, hal⟩, rfl⟩ := hw
      have hc := con_val q hq a
      rw [hc] at hval
      simp only [Bool.and_eq_true, decide_eq_true_iff] at hval
      obtain ⟨⟨hσs, hsub⟩, hF⟩ := hval
      obtain ⟨hat, x, hx, hpx, hwx⟩ := hal
      rcases sub_cases _ hsub with h | h
      · have hs : (pq q).2 = ps (G j0) (A j0) (X j0) := by
          simp only [slot, σ] at hσs; rw [h] at hσs; omega
        have hr : rr (pq q).1 (pq q).2 = rk (A (pq q).1) (X (pq q).1) := by rw [h, hs]; exact rr0
        rw [map_val q hq hr _ (hout _ _)] at hF
        rw [h] at hF
        exact hF
      · by_contra hwf
        have hwf' : wd (A j0) (out j0) (X j0) a = false := by simpa using hwf
        have ht := tie _ h
        have hs := pq_mem q hq
        have := (hb2 _ j0 h x hx (X j0) hX).2 ⟨a, by simpa using hwx, hwf'⟩
        simp only [slot, σ] at hσs
        simp only [m] at ht hs
        omega
    · intro hw
      refine ⟨st5.2 q0 a.val, ?_, ?_⟩
      · simp only [lst, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
        refine ⟨q0, ⟨hq0, a.isLt, X (pq q0).1, by rw [hq0a]; exact hX, by rw [hq0a, hq0b], ?_⟩, rfl⟩
        rw [hq0a]; simpa using hw
      · rw [con_val q0 hq0 a, slot_q0, hq0a]
        have hr : rr (pq q0).1 (pq q0).2 = rk (A (pq q0).1) (X (pq q0).1) := by rw [hq0a, hq0b]; exact rr0
        have hmv := map_val q0 hq0 hr (out (pq q0).1 a) (hout _ _)
        rw [hq0a] at hmv
        rw [hmv]
        have e1 : decide (σ = σ) = true := decide_eq_true rfl
        have e2 : decide (tag j0 ⊆ tag j0) = true := decide_eq_true (Finset.Subset.refl _)
        rw [e1, e2, Bool.true_and, Bool.true_and]
        exact hw

end Core

end PEqualNP.Outside.L_lib_1342_aux

theorem PEqualNP.Outside.L_lib_1342 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
  C.output < d+2+C.size
let bits := fun (d : Nat) (x : Finset (Fin d)) =>
  List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false,true]
let rank := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)) =>
  let w := C.wires (bits d x)
  let gates := (List.range C.size).filter (fun j => decide
    ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
  gates.foldl (fun v j => 2*v+(if w.getD (d+2+j) false then 0 else 1)) 0
∀ (u d k t B : Nat) (tag : Fin k → Finset (Fin u)),
  0 < k → Function.Injective tag →
  let N := u+k*d
  let raw := fun (i : Fin k) (X : Fin k → Finset (Fin d)) =>
    List.ofFn (fun v : Fin u => decide (v ∈ tag i)) ++
    (List.ofFn (fun j : Fin k => List.ofFn (fun v : Fin d => decide (v ∈ X j)))).flatten ++ [false,true]
  let falls := fun (w z : Fin t → Bool) => ∃ a, w a = true ∧ z a = false
  ∀ (G : Fin k → Finset (Finset (Fin d))) (A : Fin k → PEqualNP.CircuitLowerBounds.Circuit)
      (out : Fin k → Fin t → Nat),
    (∀ i, (G i).Nonempty) → (∀ i, valid d (A i)) →
    (∀ i a, out i a < d+2+(A i).size) →
    let states := fun i => (G i).image (rank d (A i))
    let m := fun i => (states i).card
    let b := fun i => PEqualNP.NotBracket.notCount (A i)
    let p := fun i => (A i).size - b i
    let pos := fun i x => ((states i).filter (fun v => v < rank d (A i) x)).card
    let word := fun i x (a : Fin t) => ((A i).wires (bits d x)).getD (out i a) false
    let boundary := fun i j => ∃ x ∈ G i, ∃ y ∈ G j,
      pos i x + 1 = m i ∧ pos j y = 0 ∧ falls (word i x) (word j y)
    let chains := ∀ (l : Nat) (path : Fin (l+1) → Fin k),
      (∀ a c, a < c → tag (path a) ⊂ tag (path c)) →
      1 + (∑ a, (m (path a)-1)) +
        (Finset.univ.filter (fun j : Fin l => boundary (path j.castSucc) (path j.succ))).card ≤ 2^B
    let place := ∃ base : Fin k → Nat, (∀ i, base i + m i ≤ 2^B) ∧
      ∀ i j, tag i ⊂ tag j → ∀ x ∈ G i, ∀ y ∈ G j,
        base i + pos i x + (if falls (word i x) (word j y) then 1 else 0) ≤ base j + pos j y
    (place ↔ chains) ∧ (chains →
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat), valid N C ∧
      (∀ a, tap a < N+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ B ∧
      C.size - PEqualNP.NotBracket.notCount C ≤
        k*u + 5*(2^B) + ∑ i, m i*(p i+2*b i+2*t+4) ∧
      ∀ i X, X i ∈ G i → ∀ a,
        (C.wires (raw i X)).getD (tap a) false = word i (X i) a)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
    PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro valid bits rank u d k t B tag hk htag N raw falls G A out hG hA hout states m b p pos word boundary
    chains place
  have hbits_eq : ∀ x : Finset (Fin d), bits d x = PEqualNP.Outside.L_lib_1342_aux.bitsL x := fun x => by
    dsimp only [bits, PEqualNP.Outside.L_lib_1342_aux.bitsL]
    congr 1; congr 1; funext a
    exact congrArg (@decide (a ∈ x)) (Subsingleton.elim _ _)
  have hrank_eq : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)),
      rank d C x =
        ((List.range C.size).filter (fun j => decide
          ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))).foldl
          (fun v j => 2 * v + (if (C.wires (PEqualNP.Outside.L_lib_1342_aux.bitsL x)).getD (d + 2 + j) false
            then 0 else 1)) 0 := by
    intro C x
    dsimp only [rank]
    rw [hbits_eq x]
    have hfilt : (List.range C.size).filter (fun j => @decide
        ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not) (Classical.propDecidable _)) =
        (List.range C.size).filter (fun j => decide
          ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)) := by
      apply List.filter_congr
      intro j _
      exact congrArg (@decide ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
        (Subsingleton.elim _ _)
    rw [hfilt]
    congr 1; funext v j
    congr 1
    exact ite_congr (by rfl) (fun _ => rfl) (fun _ => rfl)
  have hrk : ∀ i x, rank d (A i) x = PEqualNP.Outside.L_lib_1342_aux.rk (A i) x := fun i x =>
    (hrank_eq (A i) x).trans rfl
  have hstates : ∀ i, states i = PEqualNP.Outside.L_lib_1342_aux.sts (G i) (A i) := by
    intro i
    dsimp only [states, PEqualNP.Outside.L_lib_1342_aux.sts]
    ext r
    simp only [Finset.mem_image, hrk]
  have hm : ∀ i, m i = (PEqualNP.Outside.L_lib_1342_aux.sts (G i) (A i)).card := fun i => by
    show (states i).card = _
    rw [hstates i]
  have hpos : ∀ i x, pos i x = PEqualNP.Outside.L_lib_1342_aux.ps (G i) (A i) x := by
    intro i x
    dsimp only [pos]
    rw [hstates i, hrk i x]
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  have hword : ∀ i x a, word i x a = PEqualNP.Outside.L_lib_1342_aux.wd (A i) (out i) x a := by
    intro i x a
    show ((A i).wires (bits d x)).getD (out i a) false = _
    rw [hbits_eq x]
    rfl
  have hraw : ∀ i X, raw i X = PEqualNP.Outside.L_lib_1342_aux.rawL tag i X := by
    intro i X
    dsimp only [raw, PEqualNP.Outside.L_lib_1342_aux.rawL]
    congr 1; congr 1
    · congr 1; funext v
      exact congrArg (@decide (v ∈ tag i)) (Subsingleton.elim _ _)
    · congr 2; funext j; congr 1; funext v
      exact congrArg (@decide (v ∈ X j)) (Subsingleton.elim _ _)
  have PF := fun i => PEqualNP.Outside.L_lib_1342_aux.pos_facts (G i) (A i) (hG i)
  have part1 : place ↔ chains :=
    PEqualNP.Outside.L_lib_1342_aux.comb tag G m pos (fun i x j y => falls (word i x) (word j y)) boundary
      (fun i j => Iff.rfl) (fun i => by rw [hm]; exact (PF i).1)
      (fun i x hx => by rw [hm, hpos]; exact (PF i).2.1 x hx)
      (fun i => by
        obtain ⟨x, hx, h⟩ := (PF i).2.2.2.2.2.1
        exact ⟨x, hx, by rw [hm, hpos]; exact h⟩)
      (fun i => by
        obtain ⟨x, hx, h⟩ := (PF i).2.2.2.2.2.2
        exact ⟨x, hx, by rw [hpos]; exact h⟩)
  refine ⟨part1, fun hch => ?_⟩
  obtain ⟨base, hb1, hb2⟩ := part1.2 hch
  have hb1' : ∀ i, base i + (PEqualNP.Outside.L_lib_1342_aux.sts (G i) (A i)).card ≤ 2 ^ B := fun i => by
    rw [← hm]; exact hb1 i
  have hb2' : ∀ i j, tag i ⊂ tag j → ∀ x ∈ G i, ∀ y ∈ G j,
      base i + PEqualNP.Outside.L_lib_1342_aux.ps (G i) (A i) x ≤
        base j + PEqualNP.Outside.L_lib_1342_aux.ps (G j) (A j) y ∧
      ((∃ a, PEqualNP.Outside.L_lib_1342_aux.wd (A i) (out i) x a = true ∧
          PEqualNP.Outside.L_lib_1342_aux.wd (A j) (out j) y a = false) →
        base i + PEqualNP.Outside.L_lib_1342_aux.ps (G i) (A i) x + 1 ≤
          base j + PEqualNP.Outside.L_lib_1342_aux.ps (G j) (A j) y) := by
    intro i j hij x hx y hy
    have h := hb2 i j hij x hx y hy
    rw [hpos, hpos] at h
    constructor
    · split_ifs at h <;> omega
    · intro hf
      have hf' : falls (word i x) (word j y) := by
        obtain ⟨a, h1, h2⟩ := hf
        exact ⟨a, by rw [hword]; exact h1, by rw [hword]; exact h2⟩
      rw [if_pos hf'] at h
      exact h
  obtain ⟨C, tap, hv, htap, hnc, hsz, hev⟩ := PEqualNP.Outside.L_lib_1342_aux.core u d k t B hk tag htag G A out hG
    (fun i => ⟨(hA i).1, (hA i).2.1⟩) hout base hb1' hb2'
  refine ⟨C, tap, hv, htap, hnc, le_of_le_of_eq hsz ?_, ?_⟩
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hm i]
  · intro i X hX a
    rw [hraw, hword]
    exact hev i X hX a
