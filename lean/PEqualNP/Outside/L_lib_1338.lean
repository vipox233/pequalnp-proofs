import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1338_aux

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

private def threshCut [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r : ℕ) (i : Fin k) (gs : List Gate) : List Gate × ℕ :=
  let b := PEqualNP.NotBracket.notCount C
  let notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
  let res1 := remapLoop d M₀ C baseIn notWire gs C.size
  let res2 := cmpAux M₀ cT cF C res1.2 (notIdxList C) r b res1.1 b
  let w1 := M₀ + res2.1.length
  let gs3 := res2.1 ++ [⟨GateOp.and, [i.val * (d + 1), res2.2]⟩]
  if i.val + 1 < k then
    let w2 := M₀ + gs3.length
    (gs3 ++ [⟨GateOp.or, [(i.val + 1) * (d + 1), w1]⟩], w2)
  else
    (gs3, w1)

private theorem threshCut_props [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r : ℕ) (i : Fin k) (gs : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsi : i.val * (d + 1) < M₀ + gs.length)
    (hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length) :
    let res := threshCut d M₀ cF cT k C baseIn r i gs
    (∃ tail, res.1 = gs ++ tail ∧ negCount tail = 0 ∧
      posCount tail ≤ (C.size - PEqualNP.NotBracket.notCount C) + PEqualNP.NotBracket.notCount C + 2) ∧
    Good M₀ res.1 ∧ res.2 < M₀ + res.1.length := by
  dsimp only [threshCut]
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
  have hlen2 : gs.length ≤ res2.1.length := by
    rw [ht2, ht1, List.length_append, List.length_append]; omega
  set gAnd : Gate := ⟨GateOp.and, [i.val * (d + 1), res2.2]⟩
  have hg3 : Good M₀ (res2.1 ++ [gAnd]) := by
    apply good_snoc hg2 gAnd (by simp [gAnd]) (by simp [gAnd])
    intro u hu; simp [gAnd] at hu
    rcases hu with rfl | rfl
    · exact lt_of_lt_of_le hsi (by omega)
    · exact hw2
  have hAndNot : gAnd.op ≠ GateOp.not := fun h => GateOp.noConfusion h
  by_cases hnext : i.val + 1 < k
  · simp only [hnext, ↓reduceIte]
    set gOr : Gate := ⟨GateOp.or, [(i.val + 1) * (d + 1), M₀ + res2.1.length]⟩
    have hg4 : Good M₀ ((res2.1 ++ [gAnd]) ++ [gOr]) := by
      apply good_snoc hg3 gOr (by simp [gOr]) (by simp [gOr])
      intro u hu; simp [gOr] at hu
      rcases hu with rfl | rfl
      · exact lt_of_lt_of_le (hsnext hnext) (by simp; omega)
      · simp
    have hOrNot : gOr.op ≠ GateOp.not := fun h => GateOp.noConfusion h
    refine ⟨⟨t1 ++ t2 ++ [gAnd, gOr], ?_, ?_, ?_⟩, hg4, ?_⟩
    · rw [ht2, ht1]; simp [List.append_assoc]
    · have hn_tail : negCount [gAnd, gOr] = 0 := by
        dsimp only [negCount]
        rw [List.filter_cons, decide_eq_false hAndNot, if_neg Bool.false_ne_true,
          List.filter_cons, decide_eq_false hOrNot, if_neg Bool.false_ne_true]
        rfl
      rw [negCount_append, negCount_append, hn1, hn2, hn_tail]
    · have hp_tail : posCount [gAnd, gOr] = 2 := by
        dsimp only [posCount]
        rw [List.filter_cons, decide_eq_true hAndNot, if_pos rfl,
          List.filter_cons, decide_eq_true hOrNot, if_pos rfl]
        rfl
      rw [posCount_append, posCount_append, hp1, hp2, hp_tail]
    · simp
  · simp only [hnext, ↓reduceIte]
    refine ⟨⟨t1 ++ t2 ++ [gAnd], ?_, ?_, ?_⟩, hg3, by simp⟩
    · rw [ht2, ht1]; simp [List.append_assoc]
    · have hn_tail : negCount [gAnd] = 0 := by
        dsimp only [negCount]
        rw [List.filter_cons, decide_eq_false hAndNot, if_neg Bool.false_ne_true]
        rfl
      rw [negCount_append, negCount_append, hn1, hn2, hn_tail]
    · have hp_tail : posCount [gAnd] = 1 := by
        dsimp only [posCount]
        rw [List.filter_cons, decide_eq_true hAndNot, if_pos rfl]
        rfl
      rw [posCount_append, posCount_append, hp1, hp2, hp_tail]
      omega

private theorem threshCut_eval [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (r : ℕ) (i : Fin k) (gs : List Gate)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsi : i.val * (d + 1) < M₀ + gs.length)
    (hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length)
    (hr : r < 2 ^ PEqualNP.NotBracket.notCount C)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (hcTv : (run gs X).getD cT false = true)
    (i' : Fin k)
    (hsi_val : (run gs X).getD (i.val * (d + 1)) false = decide (i ≤ i'))
    (hsnext_val : ∀ hnext : i.val + 1 < k,
      (run gs X).getD ((i.val + 1) * (d + 1)) false = decide (i.val + 1 ≤ i'.val))
    (x : List Bool) (hx : x.length = d + 2)
    (hbaseEq : i' = i → ∀ w < d + 2, (run gs X).getD (baseIn w) false = x.getD w false) :
    let res := threshCut d M₀ cF cT k C baseIn r i gs
    let r_real := (notIdxList C).foldl (fun v j =>
      2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0
    (run res.1 X).getD res.2 false =
      if i' < i then false else if i < i' then true else decide (r ≤ r_real) := by
  dsimp only [threshCut]
  set b := PEqualNP.NotBracket.notCount C
  set notWire := fun j => if bitAt r (b - 1 - notPos C j) then cF else cT
  set res1 := remapLoop d M₀ C baseIn notWire gs C.size
  set res2 := cmpAux M₀ cT cF C res1.2 (notIdxList C) r b res1.1 b
  have hnotB : ∀ j < C.size, notWire j < M₀ + gs.length := fun j _ => by
    dsimp [notWire]; split_ifs <;> assumption
  rcases remapLoop_tail d M₀ C baseIn notWire gs C.size with ⟨t1, ht1, _, _⟩
  rcases cmpAux_tail M₀ cT cF C res1.2 (notIdxList C) r b res1.1 b with ⟨t2, ht2, _, _⟩
  have hm1 : ∀ w < d + 2 + C.size, res1.2 w < M₀ + res1.1.length :=
    remapLoop_map_lt d M₀ C baseIn notWire gs hbase hnotB C.size le_rfl
  have hlen1 : gs.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
  have hlen2 : gs.length ≤ res2.1.length := by rw [ht2, List.length_append]; omega
  have hsi_2 : (run res2.1 X).getD (i.val * (d + 1)) false = decide (i ≤ i') := by
    rw [ht2, ht1, List.append_assoc, run_prefix gs (t1 ++ t2) X _ (by rw [hX]; exact hsi), hsi_val]
  set gAnd : Gate := ⟨GateOp.and, [i.val * (d + 1), res2.2]⟩
  have hstep1 : (run (res2.1 ++ [gAnd]) X).getD (M₀ + res2.1.length) false =
      (decide (i ≤ i') && (run res2.1 X).getD res2.2 false) := by
    have hrlen : (run res2.1 X).length = M₀ + res2.1.length := by rw [run_length, hX]
    rw [run_snoc, ← hrlen, getD_eq]
    simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true]
    rw [hsi_2]
  have hmain : (run (if i.val + 1 < k then
        (res2.1 ++ [gAnd] ++ [⟨GateOp.or, [(i.val + 1) * (d + 1), M₀ + res2.1.length]⟩],
          M₀ + (res2.1 ++ [gAnd]).length)
        else (res2.1 ++ [gAnd], M₀ + res2.1.length)).1 X).getD
      (if i.val + 1 < k then
        (res2.1 ++ [gAnd] ++ [⟨GateOp.or, [(i.val + 1) * (d + 1), M₀ + res2.1.length]⟩],
          M₀ + (res2.1 ++ [gAnd]).length)
        else (res2.1 ++ [gAnd], M₀ + res2.1.length)).2 false =
      if i' < i then false else if i < i' then true else (run res2.1 X).getD res2.2 false := by
    by_cases hnext : i.val + 1 < k
    · simp only [hnext, ↓reduceIte]
      have hsnext_3 : (run (res2.1 ++ [gAnd]) X).getD ((i.val + 1) * (d + 1)) false =
          decide (i.val + 1 ≤ i'.val) := by
        rw [ht2, ht1, List.append_assoc, List.append_assoc,
          run_prefix gs _ X _ (by rw [hX]; exact hsnext hnext), hsnext_val hnext]
      have hrlen3 : (run (res2.1 ++ [gAnd]) X).length = M₀ + (res2.1 ++ [gAnd]).length := by
        rw [run_length, hX]
      rw [run_snoc, ← hrlen3, getD_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
      rw [hsnext_3, hstep1]
      by_cases hlt : i' < i
      · have h1 : ¬ (i.val + 1 ≤ i'.val) := by omega
        have h2 : ¬ (i ≤ i') := by omega
        simp [hlt, h1, h2]
      · by_cases hgt : i < i'
        · have h1 : i.val + 1 ≤ i'.val := by omega
          simp [hlt, hgt, h1]
        · have h1 : ¬ (i.val + 1 ≤ i'.val) := by omega
          have h2 : i ≤ i' := by omega
          simp [hlt, hgt, h1, h2]
    · simp only [hnext, ↓reduceIte, hstep1]
      by_cases hlt : i' < i
      · have h2 : ¬ (i ≤ i') := by omega
        simp [hlt, h2]
      · by_cases hgt : i < i'
        · exfalso; have := i'.isLt; omega
        · have h2 : i ≤ i' := by omega
          simp [hlt, hgt, h2]
  rw [hmain]
  by_cases hlt : i' < i
  · simp [hlt]
  · by_cases hgt : i < i'
    · simp [hlt, hgt]
    · have heq : i' = i := Fin.ext (by omega)
      simp only [hlt, hgt, ↓reduceIte]
      have hbase' := hbaseEq heq
      let bs := (notIdxList C).map (fun j => !((C.wires x).getD (d + 2 + j) false))
      have hbs_len : bs.length = b := by simp [bs, notIdxList_length, b]
      have hr_real_eq : (notIdxList C).foldl (fun v j =>
          2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0 = foldBits bs := by
        dsimp only [foldBits, bs]
        rw [List.foldl_map]
        congr 1; funext v j
        cases (C.wires x).getD (d + 2 + j) false <;> rfl
      set r_real := (notIdxList C).foldl (fun v j =>
          2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0
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
      rcases le_iff_bitAt_eq_or_lt b r r_real hr hr_real_lt with ⟨rfl, _⟩ | ⟨tStar, htStar, hhi, hne, hlt_r⟩
      · have hnotEq : ∀ j < C.size, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
            (run gs X).getD (notWire j) false = (C.wires x).getD (d + 2 + j) false := by
          intro j hj hjn
          have hmem : j ∈ notIdxList C := List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hjn⟩
          rcases List.mem_iff_getElem.mp hmem with ⟨s, hs, hjs⟩
          have hs_b : s < b := by dsimp only [b]; rw [← notIdxList_length C]; exact hs
          have hj_eq : (notIdxList C).getD s 0 = j := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; simpa using hjs
          rw [← hj_eq]
          dsimp only [notWire]
          rw [(hidx_props s hs_b).2.2.1]
          have hb := hbit_real s hs_b
          cases hbit : bitAt r_real (b - 1 - s)
          · rw [if_neg Bool.false_ne_true, hcTv]
            rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
          · rw [if_pos rfl, hcFv]
            rw [hbit] at hb; cases hcw : (C.wires x).getD (d + 2 + (notIdxList C).getD s 0) false <;> rw [hcw] at hb <;> simp at hb ⊢
        have hinEq : ∀ t < b, (run res1.1 X).getD (cmpInWire cF C res1.2 (notIdxList C) b t) false =
            bitAt r_real t := by
          intro t ht
          set s := b - 1 - t
          have hs : s < b := by omega
          have hsub : b - 1 - s = t := by omega
          rw [← hsub]
          exact eval_cmp_at C.size le_rfl hnotEq s hs (Nat.le_of_lt (hidx_props s hs).1)
        rw [cmpAux_eval_eq M₀ cT cF C res1.2 (notIdxList C) r_real b res1.1 X hX hcT1 hinB hinEq b le_rfl]
        simp
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

private def buildGroupThresh [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (i : Fin k) : List ℕ → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | _ :: rsTail, gs =>
    rsTail.foldl (fun (st : List Gate × List ℕ) r =>
      let cut := threshCut d M₀ cF cT k C baseIn r i st.1
      (cut.1, st.2 ++ [cut.2])) (gs, [i.val * (d + 1)])

private theorem buildGroupThresh_props [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (i : Fin k) (r0 : ℕ) (rsTail : List ℕ) (gs : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsi : i.val * (d + 1) < M₀ + gs.length)
    (hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length) :
    let res := buildGroupThresh d M₀ cF cT k C baseIn i (r0 :: rsTail) gs
    (∃ tail, res.1 = gs ++ tail ∧ negCount tail = 0 ∧
      posCount tail ≤ rsTail.length * (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2)) ∧
    res.2.length = rsTail.length + 1 ∧
    Good M₀ res.1 ∧
    (∀ w ∈ res.2, w < M₀ + res.1.length) := by
  dsimp only [buildGroupThresh]
  suffices h : ∀ (acc : List ℕ) (gs0 : List Gate),
      Good M₀ gs0 → cF < M₀ + gs0.length → cT < M₀ + gs0.length →
      i.val * (d + 1) < M₀ + gs0.length →
      (i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs0.length) →
      (∀ w < d + 2, baseIn w < M₀ + gs0.length) →
      (∀ w ∈ acc, w < M₀ + gs0.length) →
      let res := rsTail.foldl (fun (st : List Gate × List ℕ) r =>
        let cut := threshCut d M₀ cF cT k C baseIn r i st.1
        (cut.1, st.2 ++ [cut.2])) (gs0, acc)
      (∃ tail, res.1 = gs0 ++ tail ∧ negCount tail = 0 ∧
        posCount tail ≤ rsTail.length * (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2)) ∧
      res.2.length = acc.length + rsTail.length ∧
      Good M₀ res.1 ∧
      (∀ w ∈ res.2, w < M₀ + res.1.length) by
    have hres := h [i.val * (d + 1)] gs hgs hcF hcT hsi hsnext hbase (by simp [hsi])
    simpa [Nat.add_comm] using hres
  intro acc gs0 hgs0 hcF0 hcT0 hsi0 hsnext0 hbase0 hacc0
  induction rsTail generalizing acc gs0 with
  | nil =>
    refine ⟨⟨[], by simp, negCount_nil, by simp [posCount_nil]⟩, rfl, hgs0, hacc0⟩
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rcases threshCut_props d M₀ cF cT k C baseIn r i gs0 hfan hrb hgs0 hcF0 hcT0 hsi0 hsnext0 hbase0 with
      ⟨⟨t1, ht1, hn1, hp1⟩, hgood1, hw1⟩
    have hlen_le : gs0.length ≤ (threshCut d M₀ cF cT k C baseIn r i gs0).1.length := by
      rw [ht1, List.length_append]; omega
    have hacc1 : ∀ w ∈ acc ++ [(threshCut d M₀ cF cT k C baseIn r i gs0).2],
        w < M₀ + (threshCut d M₀ cF cT k C baseIn r i gs0).1.length := by
      intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact lt_of_lt_of_le (hacc0 w hw) (by omega)
      · exact hw1
    rcases ih (acc ++ [(threshCut d M₀ cF cT k C baseIn r i gs0).2])
        (threshCut d M₀ cF cT k C baseIn r i gs0).1 hgood1 (by omega) (by omega) (by omega)
        (fun hn => lt_of_lt_of_le (hsnext0 hn) (by omega))
        (fun w hw => lt_of_lt_of_le (hbase0 w hw) (by omega)) hacc1 with
      ⟨⟨t2, ht2, hn2, hp2⟩, hlen2, hgood2, hmem2⟩
    refine ⟨⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc], by rw [negCount_append, hn1, hn2], ?_⟩,
      ?_, hgood2, hmem2⟩
    · rw [posCount_append, List.length_cons, Nat.succ_mul]
      calc posCount t1 + posCount t2
          ≤ (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2) +
              rs.length * (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2) :=
            Nat.add_le_add hp1 hp2
        _ = rs.length * (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2) +
              (C.size - PEqualNP.NotBracket.notCount C + PEqualNP.NotBracket.notCount C + 2) := Nat.add_comm _ _
    · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hlen2 ⊢
      omega

private theorem buildGroupThresh_eval [DecidableEq GateOp] (d M₀ cF cT k : ℕ) (C : Circuit)
    (baseIn : ℕ → ℕ) (i : Fin k) (r0 : ℕ) (rsTail : List ℕ) (gs : List Gate)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C)
    (hgs : Good M₀ gs)
    (hcF : cF < M₀ + gs.length) (hcT : cT < M₀ + gs.length)
    (hsi : i.val * (d + 1) < M₀ + gs.length)
    (hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs.length)
    (hbase : ∀ w < d + 2, baseIn w < M₀ + gs.length)
    (hrs_lt : ∀ r ∈ (r0 :: rsTail), r < 2 ^ PEqualNP.NotBracket.notCount C)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs X).getD cF false = false)
    (hcTv : (run gs X).getD cT false = true)
    (i' : Fin k)
    (hsi_val : (run gs X).getD (i.val * (d + 1)) false = decide (i ≤ i'))
    (hsnext_val : ∀ hnext : i.val + 1 < k,
      (run gs X).getD ((i.val + 1) * (d + 1)) false = decide (i.val + 1 ≤ i'.val))
    (x : List Bool) (hx : x.length = d + 2)
    (hbaseEq : i' = i → ∀ w < d + 2, (run gs X).getD (baseIn w) false = x.getD w false) :
    let res := buildGroupThresh d M₀ cF cT k C baseIn i (r0 :: rsTail) gs
    let r_real := (notIdxList C).foldl (fun v j =>
      2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0
    (i' = i → r0 ≤ r_real) →
    ∀ q < (r0 :: rsTail).length,
      (run res.1 X).getD (res.2.getD q cF) false =
        if i' < i then false else if i < i' then true else decide ((r0 :: rsTail).getD q 0 ≤ r_real) := by
  dsimp only [buildGroupThresh]
  suffices h : ∀ (acc : List ℕ) (rsRest : List ℕ) (gs0 : List Gate),
      Good M₀ gs0 → cF < M₀ + gs0.length → cT < M₀ + gs0.length →
      i.val * (d + 1) < M₀ + gs0.length →
      (i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + gs0.length) →
      (∀ w < d + 2, baseIn w < M₀ + gs0.length) →
      (∀ w ∈ acc, w < M₀ + gs0.length) →
      (∀ r ∈ rsRest, r < 2 ^ PEqualNP.NotBracket.notCount C) →
      (run gs0 X).getD cF false = false →
      (run gs0 X).getD cT false = true →
      (run gs0 X).getD (i.val * (d + 1)) false = decide (i ≤ i') →
      (∀ hnext : i.val + 1 < k,
        (run gs0 X).getD ((i.val + 1) * (d + 1)) false = decide (i.val + 1 ≤ i'.val)) →
      (i' = i → ∀ w < d + 2, (run gs0 X).getD (baseIn w) false = x.getD w false) →
      let res := rsRest.foldl (fun (st : List Gate × List ℕ) r =>
        let cut := threshCut d M₀ cF cT k C baseIn r i st.1
        (cut.1, st.2 ++ [cut.2])) (gs0, acc)
      ∀ q, acc.length ≤ q → q < acc.length + rsRest.length →
        (run res.1 X).getD (res.2.getD q cF) false =
          if i' < i then false else if i < i' then true
          else decide (rsRest.getD (q - acc.length) 0 ≤
            (notIdxList C).foldl (fun v j => 2 * v + (if (C.wires x).getD (d + 2 + j) false then 0 else 1)) 0) by
    intro hr0 q hq
    have hh := h [i.val * (d + 1)] rsTail gs hgs hcF hcT hsi hsnext hbase (by simp [hsi])
      (fun r hr => hrs_lt r (by simp [hr])) hcFv hcTv hsi_val hsnext_val hbaseEq
    set res := rsTail.foldl (fun (st : List Gate × List ℕ) r =>
      let cut := threshCut d M₀ cF cT k C baseIn r i st.1
      (cut.1, st.2 ++ [cut.2])) (gs, [i.val * (d + 1)])
    have hprops := buildGroupThresh_props d M₀ cF cT k C baseIn i r0 rsTail gs hfan hrb hgs hcF hcT hsi hsnext hbase
    dsimp only [buildGroupThresh] at hprops
    rcases hprops.1 with ⟨tail, htail, _, _⟩
    cases q with
    | zero =>
      have hfst : res.2.getD 0 cF = i.val * (d + 1) := by
        clear hh hprops
        suffices hp : ∀ (acc : List ℕ) (rs : List ℕ) (gs0 : List Gate),
            acc ≠ [] → (rs.foldl (fun (st : List Gate × List ℕ) r =>
              let cut := threshCut d M₀ cF cT k C baseIn r i st.1
              (cut.1, st.2 ++ [cut.2])) (gs0, acc)).2.getD 0 cF = acc.getD 0 cF by
          exact hp [i.val * (d + 1)] rsTail gs (by simp)
        intro acc rs gs0 hne
        induction rs generalizing acc gs0 with
        | nil => rfl
        | cons r rs ih' =>
          simp only [List.foldl_cons]
          rw [ih' _ _ (by simp)]
          cases acc with
          | nil => exact absurd rfl hne
          | cons a as => rfl
      rw [hfst, htail, run_prefix gs tail X _ (by rw [hX]; exact hsi), hsi_val]
      simp only [List.getD_cons_zero]
      by_cases hlt : i' < i
      · have : ¬ (i ≤ i') := by omega
        simp [hlt, this]
      · by_cases hgt : i < i'
        · have : i ≤ i' := by omega
          simp [hlt, hgt, this]
        · have heq : i' = i := Fin.ext (by omega)
          have h1 : i ≤ i' := by omega
          simp only [hlt, hgt, h1, ↓reduceIte, decide_true]
          exact (decide_eq_true (hr0 heq)).symm
    | succ q =>
      simp only [List.length_cons] at hq
      have hq' : q + 1 < [i.val * (d + 1)].length + rsTail.length := by
        simp only [List.length_singleton]; omega
      have hres := hh (q + 1) (by simp) hq'
      simpa using hres
  intro acc rsRest gs0 hgs0 hcF0 hcT0 hsi0 hsnext0 hbase0 hacc0 hrs0 hcFv0 hcTv0 hsi_v0 hsnext_v0 hbase_v0
  induction rsRest generalizing acc gs0 with
  | nil => intro _ q h1 h2; rw [List.length_nil, Nat.add_zero] at h2; omega
  | cons r rs ih =>
    simp only [List.foldl_cons]
    have hr : r < 2 ^ PEqualNP.NotBracket.notCount C := hrs0 r (by simp)
    rcases threshCut_props d M₀ cF cT k C baseIn r i gs0 hfan hrb hgs0 hcF0 hcT0 hsi0 hsnext0 hbase0 with
      ⟨⟨t1, ht1, _, _⟩, hgood1, hw1⟩
    set cut := threshCut d M₀ cF cT k C baseIn r i gs0
    have hlen_le : gs0.length ≤ cut.1.length := by rw [ht1, List.length_append]; omega
    have hcut_eval := threshCut_eval d M₀ cF cT k C baseIn r i gs0 hrb hcF0 hcT0 hsi0 hsnext0 hbase0
      hr X hX hcFv0 hcTv0 i' hsi_v0 hsnext_v0 x hx hbase_v0
    have hpref : ∀ w < M₀ + gs0.length, (run cut.1 X).getD w false = (run gs0 X).getD w false := by
      intro w hw; rw [ht1, run_prefix gs0 t1 X w (by rw [hX]; exact hw)]
    have hacc1 : ∀ w ∈ acc ++ [cut.2], w < M₀ + cut.1.length := by
      intro w hw; simp at hw
      rcases hw with hw | rfl
      · exact lt_of_lt_of_le (hacc0 w hw) (by omega)
      · exact hw1
    have ih' := ih (acc ++ [cut.2]) cut.1 hgood1 (by omega) (by omega) (by omega)
      (fun hn => lt_of_lt_of_le (hsnext0 hn) (by omega))
      (fun w hw => lt_of_lt_of_le (hbase0 w hw) (by omega))
      hacc1 (fun r' hr' => hrs0 r' (by simp [hr']))
      (by rw [hpref cF hcF0, hcFv0])
      (by rw [hpref cT hcT0, hcTv0])
      (by rw [hpref _ hsi0, hsi_v0])
      (fun hn => by rw [hpref _ (hsnext0 hn), hsnext_v0 hn])
      (fun heq w hw => by rw [hpref _ (hbase0 w hw)]; exact hbase_v0 heq w hw)
    intro q hlo hhi
    by_cases hq : q = acc.length
    · subst hq
      have hfold_tail : ∃ tail2, (rs.foldl (fun (st : List Gate × List ℕ) r' =>
          let cut' := threshCut d M₀ cF cT k C baseIn r' i st.1
          (cut'.1, st.2 ++ [cut'.2])) (cut.1, acc ++ [cut.2])).1 = cut.1 ++ tail2 := by
        clear ih'
        suffices ht : ∀ (a : List ℕ) (rs' : List ℕ) (g : List Gate),
            Good M₀ g → cF < M₀ + g.length → cT < M₀ + g.length →
            i.val * (d + 1) < M₀ + g.length →
            (i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + g.length) →
            (∀ w < d + 2, baseIn w < M₀ + g.length) →
            ∃ t, (rs'.foldl (fun (st : List Gate × List ℕ) r' =>
              let cut' := threshCut d M₀ cF cT k C baseIn r' i st.1
              (cut'.1, st.2 ++ [cut'.2])) (g, a)).1 = g ++ t by
          exact ht (acc ++ [cut.2]) rs cut.1 hgood1 (by omega) (by omega) (by omega)
            (fun hn => lt_of_lt_of_le (hsnext0 hn) (by omega))
            (fun w hw => lt_of_lt_of_le (hbase0 w hw) (by omega))
        intro a rs' g hg hcFg hcTg hsig hsnextg hbaseg
        induction rs' generalizing a g with
        | nil => exact ⟨[], by simp⟩
        | cons r' rs'' ih'' =>
          simp only [List.foldl_cons]
          rcases threshCut_props d M₀ cF cT k C baseIn r' i g hfan hrb hg hcFg hcTg hsig hsnextg hbaseg with
            ⟨⟨t', ht', _, _⟩, hg', _⟩
          have hlg : g.length ≤ (threshCut d M₀ cF cT k C baseIn r' i g).1.length := by
            rw [ht', List.length_append]; omega
          rcases ih'' _ _ hg' (by omega) (by omega) (by omega)
            (fun hn => lt_of_lt_of_le (hsnextg hn) (by omega))
            (fun w hw => lt_of_lt_of_le (hbaseg w hw) (by omega)) with ⟨t'', ht''⟩
          exact ⟨t' ++ t'', by rw [ht'', ht', List.append_assoc]⟩
      have hfold_elem : (rs.foldl (fun (st : List Gate × List ℕ) r' =>
          let cut' := threshCut d M₀ cF cT k C baseIn r' i st.1
          (cut'.1, st.2 ++ [cut'.2])) (cut.1, acc ++ [cut.2])).2.getD acc.length cF = cut.2 := by
        clear ih'
        suffices he : ∀ (a : List ℕ) (rs' : List ℕ) (g : List Gate) (idx : ℕ),
            idx < a.length →
            (rs'.foldl (fun (st : List Gate × List ℕ) r' =>
              let cut' := threshCut d M₀ cF cT k C baseIn r' i st.1
              (cut'.1, st.2 ++ [cut'.2])) (g, a)).2.getD idx cF = a.getD idx cF by
          have := he (acc ++ [cut.2]) rs cut.1 acc.length (by simp)
          simpa using this
        intro a rs' g idx hidx
        induction rs' generalizing a g with
        | nil => rfl
        | cons r' rs'' ih'' =>
          simp only [List.foldl_cons]
          rw [ih'' _ _ (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hidx, ← List.getD_eq_getElem?_getD]
      rcases hfold_tail with ⟨t2, ht2⟩
      rw [hfold_elem, ht2, run_prefix cut.1 t2 X cut.2 (by rw [hX]; exact hw1), hcut_eval]
      simp
    · have hlo' : (acc ++ [cut.2]).length ≤ q := by simp only [List.length_append, List.length_singleton]; omega
      have hhi' : q < (acc ++ [cut.2]).length + rs.length := by
        simp only [List.length_append, List.length_singleton, List.length_cons] at hhi ⊢; omega
      have ih_res := ih' q hlo' hhi'
      have hsub : q - (acc ++ [cut.2]).length + 1 = q - acc.length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hget : (r :: rs).getD (q - acc.length) 0 = rs.getD (q - (acc ++ [cut.2]).length) 0 := by
        rw [← hsub]; rfl
      rw [hget]
      exact ih_res

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

private def buildRecNotMap [DecidableEq GateOp] (M₀ cF : ℕ) (E : List ℕ) (uStart : ℕ)
    (rs notIdxs : List ℕ) (m b : ℕ) : ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, fun _ => cF)
  | s + 1, gs =>
    let res := buildRecNotMap M₀ cF E uStart rs notIdxs m b s gs
    let j := notIdxs.getD s 0
    let wires := (List.range m).filterMap (fun q =>
      if !(bitAt (rs.getD q 0) (b - 1 - s)) then some (E.getD (uStart + q) cF) else none)
    let orRes := pushOrList M₀ cF res.1 wires
    (orRes.1, fun u => if u = j then orRes.2 else res.2 u)

private theorem buildRecNotMap_props [DecidableEq GateOp] (M₀ cF : ℕ) (E : List ℕ) (uStart : ℕ)
    (rs notIdxs : List ℕ) (m b : ℕ) (hm : 1 ≤ m)
    (gs0 : List Gate) (hgs0 : Good M₀ gs0) (hcF : cF < M₀ + gs0.length)
    (hE : ∀ w ∈ E, w < M₀ + gs0.length) :
    ∀ s ≤ b,
      let res := buildRecNotMap M₀ cF E uStart rs notIdxs m b s gs0
      (∃ tail, res.1 = gs0 ++ tail ∧ negCount tail = 0 ∧ posCount tail ≤ s * (m - 1)) ∧
      Good M₀ res.1 ∧
      (∀ j, res.2 j < M₀ + res.1.length) := by
  intro s hs
  induction s with
  | zero =>
    exact ⟨⟨[], by simp [buildRecNotMap], negCount_nil, by simp [posCount_nil]⟩, hgs0, fun _ => hcF⟩
  | succ s ih =>
    rcases ih (Nat.le_of_succ_le hs) with ⟨⟨t1, ht1, hn1, hp1⟩, hg1, hmap1⟩
    dsimp only [buildRecNotMap]
    set res := buildRecNotMap M₀ cF E uStart rs notIdxs m b s gs0
    have hl1 : gs0.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    set wires := (List.range m).filterMap (fun q =>
      if !(bitAt (rs.getD q 0) (b - 1 - s)) then some (E.getD (uStart + q) cF) else none)
    have hwB : ∀ u ∈ wires, u < M₀ + res.1.length := by
      intro u hu
      simp only [wires, List.mem_filterMap] at hu
      rcases hu with ⟨q, _, hsome⟩
      split_ifs at hsome with hbit
      · simp only [Option.some.injEq] at hsome
        subst hsome
        by_cases hlt : uStart + q < E.length
        · have hmem : E.getD (uStart + q) cF ∈ E := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
          exact lt_of_lt_of_le (hE _ hmem) (by omega)
        · have hnone : E.getD (uStart + q) cF = cF := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
          rw [hnone]
          exact lt_of_lt_of_le hcF (by omega)
    rcases pushOrList_props M₀ cF res.1 wires hg1 (by omega) hwB with
      ⟨⟨t2, ht2, _, hn2, hp2⟩, hg2, hw_or, _⟩
    have hl2 : res.1.length ≤ (pushOrList M₀ cF res.1 wires).1.length := by
      rw [ht2, List.length_append]; omega
    have hwlen : wires.length ≤ m := by
      simpa using List.length_filterMap_le _ (List.range m)
    refine ⟨⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc], by rw [negCount_append, hn1, hn2], ?_⟩,
      hg2, fun j => ?_⟩
    · rw [posCount_append, hp2, Nat.succ_mul]
      omega
    · by_cases heq : j = notIdxs.getD s 0
      · rw [if_pos heq]; exact hw_or
      · rw [if_neg heq]; exact lt_of_lt_of_le (hmap1 j) (by omega)

private theorem buildRecNotMap_eval_at [DecidableEq GateOp] (M₀ cF : ℕ) (E : List ℕ) (uStart : ℕ)
    (rs notIdxs : List ℕ) (m b : ℕ) (hm : 1 ≤ m)
    (gs0 : List Gate) (hgs0 : Good M₀ gs0) (hcF : cF < M₀ + gs0.length)
    (hE : ∀ w ∈ E, w < M₀ + gs0.length)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs0 X).getD cF false = false)
    (qStar : ℕ) (hqStar : qStar < m)
    (hE_eval : ∀ q < m, (run gs0 X).getD (E.getD (uStart + q) cF) false = decide (q = qStar))
    (hb_le : b ≤ notIdxs.length)
    (hpw : notIdxs.Pairwise (· < ·)) :
    ∀ s ≤ b, ∀ s' < s,
      let res := buildRecNotMap M₀ cF E uStart rs notIdxs m b s gs0
      (run res.1 X).getD (res.2 (notIdxs.getD s' 0)) false =
        !(bitAt (rs.getD qStar 0) (b - 1 - s')) := by
  intro s hs
  induction s with
  | zero => intro s' hs'; omega
  | succ s ih =>
    intro s' hs'
    rcases buildRecNotMap_props M₀ cF E uStart rs notIdxs m b hm gs0 hgs0 hcF hE s
        (Nat.le_of_succ_le hs) with ⟨⟨t1, ht1, _, _⟩, hg1, hmap1⟩
    set res := buildRecNotMap M₀ cF E uStart rs notIdxs m b s gs0
    have hl1 : gs0.length ≤ res.1.length := by rw [ht1, List.length_append]; omega
    set wires := (List.range m).filterMap (fun q =>
      if !(bitAt (rs.getD q 0) (b - 1 - s)) then some (E.getD (uStart + q) cF) else none)
    have hwB : ∀ u ∈ wires, u < M₀ + res.1.length := by
      intro u hu
      simp only [wires, List.mem_filterMap] at hu
      rcases hu with ⟨q, _, hsome⟩
      split_ifs at hsome with hbit
      · simp only [Option.some.injEq] at hsome; subst hsome
        by_cases hlt : uStart + q < E.length
        · have hmem : E.getD (uStart + q) cF ∈ E := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
          exact lt_of_lt_of_le (hE _ hmem) (by omega)
        · have hnone : E.getD (uStart + q) cF = cF := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
          rw [hnone]
          exact lt_of_lt_of_le hcF (by omega)
    rcases pushOrList_props M₀ cF res.1 wires hg1 (by omega) hwB with
      ⟨⟨t2, ht2, _, _, _⟩, hg2, hw_or, heval_or⟩
    dsimp only [buildRecNotMap]
    by_cases heq : s' = s
    · subst heq
      rw [if_pos rfl]
      have hcFv1 : (run res.1 X).getD cF false = false := by
        rw [ht1, run_prefix gs0 t1 X cF (by rw [hX]; exact hcF), hcFv]
      rw [heval_or X hX hcFv1]
      have hres_pref : ∀ q < m, (run res.1 X).getD (E.getD (uStart + q) cF) false = decide (q = qStar) := by
        intro q hq
        by_cases hlt : uStart + q < E.length
        · have hmem : E.getD (uStart + q) cF ∈ E := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
          rw [ht1, run_prefix gs0 t1 X _ (by rw [hX]; exact hE _ hmem), hE_eval q hq]
        · have hnone : E.getD (uStart + q) cF = cF := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
          rw [hnone, hcFv1, ← hE_eval q hq, hnone, hcFv]
      cases hbit : !(bitAt (rs.getD qStar 0) (b - 1 - s'))
      · apply Bool.eq_false_iff.mpr
        intro htrue
        rw [List.any_eq_true] at htrue
        rcases htrue with ⟨w, hw, hval⟩
        simp only [wires, List.mem_filterMap, List.mem_range] at hw
        rcases hw with ⟨q, hq, hsome⟩
        split_ifs at hsome with hb
        · simp only [Option.some.injEq] at hsome
          rw [← hsome, hres_pref q hq] at hval
          have hqq : q = qStar := of_decide_eq_true hval
          subst hqq
          rw [hbit] at hb
          exact Bool.false_ne_true hb
      · have hqmem : E.getD (uStart + qStar) cF ∈ wires := by
          simp only [wires, List.mem_filterMap, List.mem_range]
          refine ⟨qStar, hqStar, ?_⟩
          rw [if_pos hbit]
        rw [List.any_eq_true]
        refine ⟨E.getD (uStart + qStar) cF, hqmem, ?_⟩
        rw [hres_pref qStar hqStar]
        simp
    · have hlt : s' < s := by omega
      have hs'_idx : s' < notIdxs.length := by omega
      have hs_idx : s < notIdxs.length := by omega
      have hne_j : notIdxs.getD s' 0 ≠ notIdxs.getD s 0 := by
        have hlt_pw := (List.pairwise_iff_getElem.mp hpw) s' s hs'_idx hs_idx hlt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs'_idx,
          List.getElem?_eq_getElem hs_idx, Option.getD_some]
        exact Nat.ne_of_lt hlt_pw
      rw [if_neg hne_j, ht2, run_prefix res.1 t2 X _ (by rw [hX]; exact hmap1 _)]
      exact ih (Nat.le_of_succ_le hs) s' hlt

private noncomputable def sortedRanks [DecidableEq GateOp] (d : ℕ) (G : Finset (Finset (Fin d)))
    (A : Circuit) : List ℕ :=
  (G.image (fun x =>
    let bits := List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true]
    let w := A.wires bits
    (notIdxList A).foldl (fun v j => 2 * v + (if w.getD (d + 2 + j) false then 0 else 1)) 0)).sort (· ≤ ·)

private def baseInFn (d N : ℕ) (i_val : ℕ) (w : ℕ) : ℕ :=
  if w < d then i_val * (d + 1) + 1 + w else if w = d then N else N + 1

private theorem baseInFn_lt (d k : ℕ) (i : Fin k) (gsLen : ℕ) :
    ∀ w < d + 2, baseInFn d (k * (d + 1)) i.val w < k * (d + 1) + 2 + gsLen := by
  intro w hw
  dsimp only [baseInFn]
  split_ifs with h1 h2
  · have hi : i.val + 1 ≤ k := i.isLt
    calc i.val * (d + 1) + 1 + w
        < i.val * (d + 1) + 1 + d := by omega
      _ = (i.val + 1) * (d + 1) := by ring
      _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ hi
      _ < k * (d + 1) + 2 + gsLen := by omega
  · omega
  · omega

private noncomputable def buildThreshAll [DecidableEq GateOp] (d k : ℕ)
    (G : Fin k → Finset (Finset (Fin d))) (A : Fin k → Circuit) :
    ℕ → List Gate × List ℕ × (Fin k → ℕ)
  | 0 => ([], [], fun _ => 0)
  | n + 1 =>
    let st := buildThreshAll d k G A n
    if h : n < k then
      let i : Fin k := ⟨n, h⟩
      let M₀ := k * (d + 1) + 2
      let rs := sortedRanks d (G i) (A i)
      let res := buildGroupThresh d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
        (baseInFn d (k * (d + 1)) i.val) i rs st.1
      (res.1, st.2.1 ++ res.2, fun j => if j = i then st.2.1.length else st.2.2 j)
    else st

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

private theorem buildThreshAll_props [DecidableEq GateOp] (d k : ℕ) (hk : 0 < k)
    (G : Fin k → Finset (Finset (Fin d))) (hG : ∀ i, (G i).Nonempty)
    (A : Fin k → Circuit) (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i)) :
    ∀ n ≤ k,
      let M₀ := k * (d + 1) + 2
      let st := buildThreshAll d k G A n
      Good M₀ st.1 ∧ negCount st.1 = 0 ∧
      posCount st.1 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < n),
        ((sortedRanks d (G j) (A j)).length - 1) *
          ((A j).size - PEqualNP.NotBracket.notCount (A j) + PEqualNP.NotBracket.notCount (A j) + 2) ∧
      st.2.1.length = ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < n),
        (sortedRanks d (G j) (A j)).length ∧
      (∀ w ∈ st.2.1, w < M₀ + st.1.length) ∧
      (∀ j : Fin k, j.val < n → st.2.2 j + (sortedRanks d (G j) (A j)).length ≤ st.2.1.length) ∧
      (∀ j1 j2 : Fin k, j1.val < j2.val → j2.val < n →
        st.2.2 j1 + (sortedRanks d (G j1) (A j1)).length ≤ st.2.2 j2) ∧
      (∀ u < st.2.1.length, ∃ j : Fin k, ∃ q < (sortedRanks d (G j) (A j)).length,
        j.val < n ∧ u = st.2.2 j + q) := by
  intro n hn
  induction n with
  | zero =>
    dsimp only [buildThreshAll]
    refine ⟨good_nil _, negCount_nil, by simp [posCount_nil], by simp,
      by simp, fun j hj => by omega, fun _ _ _ h => by omega, fun _ hu => by simp at hu⟩
  | succ n ih =>
    rcases ih (Nat.le_of_succ_le hn) with
      ⟨hgood, hneg, hpos, hlen, hmem, hbound, horder, hcov⟩
    dsimp only [buildThreshAll]
    have hnk : n < k := hn
    simp only [hnk, ↓reduceDIte]
    set M₀ := k * (d + 1) + 2
    set i : Fin k := ⟨n, hnk⟩
    set st := buildThreshAll d k G A n
    set rs := sortedRanks d (G i) (A i)
    rcases sortedRanks_props d (G i) (A i) (hG i) with ⟨hrs_pos, _, _⟩
    rcases List.exists_cons_of_length_pos hrs_pos with ⟨r0, rsTail, hrs_eq⟩
    have hcF : k * (d + 1) < M₀ + st.1.length := by omega
    have hcT : k * (d + 1) + 1 < M₀ + st.1.length := by omega
    have hsi : i.val * (d + 1) < M₀ + st.1.length := by
      have hmul : i.val * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt i.isLt)
      omega
    have hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + st.1.length := fun hlt => by
      have hmul : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      omega
    have hbase : ∀ w < d + 2, baseInFn d (k * (d + 1)) i.val w < M₀ + st.1.length :=
      baseInFn_lt d k i st.1.length
    have hgp := buildGroupThresh_props d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
      (baseInFn d (k * (d + 1)) i.val) i r0 rsTail st.1 (hA i).1 (hA i).2 hgood hcF hcT
      hsi hsnext hbase
    rw [← hrs_eq] at hgp
    rcases hgp with ⟨⟨tail, htail, hn_tail, hp_tail⟩, hres_len, hgood', hres_mem⟩
    set res := buildGroupThresh d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
      (baseInFn d (k * (d + 1)) i.val) i rs st.1
    have hlen_le : st.1.length ≤ res.1.length := by rw [htail, List.length_append]; omega
    have hrsTail_len : rsTail.length = (sortedRanks d (G i) (A i)).length - 1 := by
      have h1 : (sortedRanks d (G i) (A i)).length = rsTail.length + 1 := by rw [hrs_eq]; simp
      omega
    have hres_len' : res.2.length = (sortedRanks d (G i) (A i)).length := by rw [hres_len, hrs_eq]; simp
    have hfilt : Finset.univ.filter (fun j : Fin k => j.val < n + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < n)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, i]
      omega
    have hni : i ∉ Finset.univ.filter (fun j : Fin k => j.val < n) := by
      simp [i]
    refine ⟨hgood', by rw [htail, negCount_append, hneg, hn_tail], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htail, posCount_append, hfilt, Finset.sum_insert hni]
      rw [hrsTail_len] at hp_tail
      omega
    · rw [List.length_append, hres_len', hlen, hfilt, Finset.sum_insert hni]
      omega
    · intro w hw
      simp only [List.mem_append] at hw
      rcases hw with hw | hw
      · exact lt_of_lt_of_le (hmem w hw) (by omega)
      · exact hres_mem w hw
    · intro j hj
      by_cases hji : j = i
      · subst hji; rw [if_pos rfl, List.length_append, hres_len']
      · rw [if_neg hji, List.length_append]
        have hjlt : j.val < n := by
          have : j.val ≠ n := fun h => hji (Fin.ext h)
          omega
        exact le_trans (hbound j hjlt) (by omega)
    · intro j1 j2 h12 hj2
      by_cases hj2i : j2 = i
      · subst hj2i
        have hj1lt : j1.val < n := h12
        have hj1ne : j1 ≠ i := fun h => by subst h; simp [i] at hj1lt
        rw [if_pos rfl, if_neg hj1ne]
        exact hbound j1 hj1lt
      · have hj2lt : j2.val < n := by
          have : j2.val ≠ n := fun h => hj2i (Fin.ext h)
          omega
        have hj1lt : j1.val < n := lt_trans h12 hj2lt
        have hj1ne : j1 ≠ i := fun h => by subst h; simp [i] at hj1lt
        rw [if_neg hj1ne, if_neg hj2i]
        exact horder j1 j2 h12 hj2lt
    · intro u hu
      rw [List.length_append, hres_len'] at hu
      by_cases hlt : u < st.2.1.length
      · rcases hcov u hlt with ⟨j, q, hq, hjn, rfl⟩
        have hjne : j ≠ i := fun h => by subst h; simp [i] at hjn
        refine ⟨j, q, hq, by omega, ?_⟩
        rw [if_neg hjne]
      · refine ⟨i, u - st.2.1.length, by omega, by simp [i], ?_⟩
        rw [if_pos rfl]
        omega

private theorem buildThreshAll_eval [DecidableEq GateOp] (d k : ℕ) (hk : 0 < k)
    (G : Fin k → Finset (Finset (Fin d))) (hG : ∀ i, (G i).Nonempty)
    (A : Fin k → Circuit) (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (i' : Fin k) (x' : Finset (Fin d)) (hx' : x' ∈ G i') :
    let M₀ := k * (d + 1) + 2
    let st := buildThreshAll d k G A k
    let X := (List.ofFn (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x'))))).flatten ++ [false, true]
    ∀ n ≤ k, ∀ j : Fin k, j.val < n →
      let st_n := buildThreshAll d k G A n
      ∀ q < (sortedRanks d (G j) (A j)).length,
        (run st_n.1 X).getD (st_n.2.1.getD (st_n.2.2 j + q) (k * (d + 1))) false =
          if i' < j then false else if j < i' then true
          else decide ((sortedRanks d (G j) (A j)).getD q 0 ≤
            (notIdxList (A j)).foldl (fun v u =>
              2 * v + (if ((A j).wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (d + 2 + u) false then 0 else 1)) 0) := by
  intro M₀ _ X n hn
  have hXlen : X.length = M₀ := by
    dsimp only [X, M₀]
    rw [List.length_append]
    have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
    simp [hfl]
  have hX_cF : X.getD (k * (d + 1)) false = false := by
    dsimp only [X]
    have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]
    simp
  have hX_cT : X.getD (k * (d + 1) + 1) false = true := by
    dsimp only [X]
    have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hfl]; omega), hfl]
    have hsub : k * (d + 1) + 1 - k * (d + 1) = 1 := by omega
    rw [hsub]; simp
  have hX_sel : ∀ j : Fin k, X.getD (j.val * (d + 1)) false = decide (j ≤ i') := by
    intro j
    dsimp only [X]
    have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
    have hlt : j.val * (d + 1) < k * (d + 1) := by
      calc j.val * (d + 1) < j.val * (d + 1) + (d + 1) := by omega
        _ = (j.val + 1) * (d + 1) := by ring
        _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ j.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hfl]; exact hlt),
      ← List.getD_eq_getElem?_getD]
    have hgf := getD_flatten_ofFn (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
      decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp) j 0 (by omega)
    simpa using hgf
  have hX_base : ∀ j : Fin k, i' = j → ∀ w < d + 2,
      X.getD (baseInFn d (k * (d + 1)) j.val w) false =
        (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]).getD w false := by
    intro j hji w hw
    subst hji
    dsimp only [baseInFn]
    by_cases h1 : w < d
    · rw [if_pos h1]
      dsimp only [X]
      have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
        decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
      have hlt : i'.val * (d + 1) + (1 + w) < k * (d + 1) := by
        calc i'.val * (d + 1) + (1 + w) < i'.val * (d + 1) + (d + 1) := by omega
          _ = (i'.val + 1) * (d + 1) := by ring
          _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ i'.isLt
      have hadd : i'.val * (d + 1) + 1 + w = i'.val * (d + 1) + (1 + w) := by omega
      rw [hadd, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hfl]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      have hgf := getD_flatten_ofFn (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
        decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp) i' (1 + w) (by omega)
      rw [hgf, Nat.add_comm 1 w, List.getD_cons_succ]
      have hrhs : ((List.ofFn (fun a : Fin d => decide (a ∈ x'))) ++ [false, true]).getD w false =
          (List.ofFn (fun a : Fin d => decide (a ∈ x'))).getD w false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact h1),
          ← List.getD_eq_getElem?_getD]
      rw [hrhs]
      simp [h1]
    · rw [if_neg h1]
      by_cases h2 : w = d
      · subst h2
        rw [if_pos rfl, hX_cF]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      · have hw_eq : w = d + 1 := by omega
        subst hw_eq
        rw [if_neg h2, hX_cT]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    have ih' := ih (Nat.le_of_succ_le hn)
    rcases buildThreshAll_props d k hk G hG A hA n (Nat.le_of_succ_le hn) with
      ⟨hgood, hneg, hpos, hlen, hmem, hbound, horder, hcov⟩
    dsimp only [buildThreshAll]
    have hnk : n < k := hn
    simp only [hnk, ↓reduceDIte]
    set M₀ := k * (d + 1) + 2
    set i : Fin k := ⟨n, hnk⟩
    set st := buildThreshAll d k G A n
    set rs := sortedRanks d (G i) (A i)
    rcases sortedRanks_props d (G i) (A i) (hG i) with ⟨hrs_pos, _, hrs_lt⟩
    rcases List.exists_cons_of_length_pos hrs_pos with ⟨r0, rsTail, hrs_eq⟩
    have hcF : k * (d + 1) < M₀ + st.1.length := by omega
    have hcT : k * (d + 1) + 1 < M₀ + st.1.length := by omega
    have hsi : i.val * (d + 1) < M₀ + st.1.length := by
      have : i.val * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt i.isLt)
      omega
    have hsnext : i.val + 1 < k → (i.val + 1) * (d + 1) < M₀ + st.1.length := fun hlt => by
      have : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      omega
    have hbase : ∀ w < d + 2, baseInFn d (k * (d + 1)) i.val w < M₀ + st.1.length :=
      baseInFn_lt d k i st.1.length
    have hgp := buildGroupThresh_props d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
      (baseInFn d (k * (d + 1)) i.val) i r0 rsTail st.1 (hA i).1 (hA i).2 hgood hcF hcT
      hsi hsnext hbase
    rw [← hrs_eq] at hgp
    rcases hgp with ⟨⟨tail, htail, _, _⟩, hres_len, _, _⟩
    set res := buildGroupThresh d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
      (baseInFn d (k * (d + 1)) i.val) i rs st.1
    have hlen_le : st.1.length ≤ res.1.length := by rw [htail, List.length_append]; omega
    have hcFv : (run st.1 X).getD (k * (d + 1)) false = false := by
      rw [run_input st.1 X _ (by rw [hXlen]; omega), hX_cF]
    have hcTv : (run st.1 X).getD (k * (d + 1) + 1) false = true := by
      rw [run_input st.1 X _ (by rw [hXlen]; omega), hX_cT]
    have hsi0 : i.val * (d + 1) < M₀ := by
      have : i.val * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt i.isLt)
      omega
    have hsi_val : (run st.1 X).getD (i.val * (d + 1)) false = decide (i ≤ i') := by
      rw [run_input st.1 X _ (by rw [hXlen]; exact hsi0), hX_sel i]
    have hsnext_val : ∀ hnext : i.val + 1 < k,
        (run st.1 X).getD ((i.val + 1) * (d + 1)) false = decide (i.val + 1 ≤ i'.val) := fun hnext => by
      have hsn0 : (i.val + 1) * (d + 1) < M₀ := by
        have : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt hnext)
        omega
      rw [run_input st.1 X _ (by rw [hXlen]; exact hsn0),
        hX_sel ⟨i.val + 1, hnext⟩]
      simp [Fin.le_def]
    have hbaseEq : i' = i → ∀ w < d + 2, (run st.1 X).getD (baseInFn d (k * (d + 1)) i.val w) false =
        (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]).getD w false := fun heq w hw => by
      rw [run_input st.1 X _ (by rw [hXlen]; exact baseInFn_lt d k i 0 w hw),
        hX_base i heq w hw]
    have heval := buildGroupThresh_eval d M₀ (k * (d + 1)) (k * (d + 1) + 1) k (A i)
      (baseInFn d (k * (d + 1)) i.val) i r0 rsTail st.1 (hA i).1 (hA i).2 hgood hcF hcT
      hsi hsnext hbase (by rw [← hrs_eq]; exact hrs_lt) X hXlen hcFv hcTv i' hsi_val hsnext_val
      (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]) (by simp) hbaseEq
    rw [← hrs_eq] at heval
    have hr0_le : i' = i → r0 ≤ (notIdxList (A i)).foldl (fun v u =>
        2 * v + (if ((A i).wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (d + 2 + u) false then 0 else 1)) 0 := by
      intro heq
      set r_real := (notIdxList (A i)).foldl (fun v u =>
        2 * v + (if ((A i).wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (d + 2 + u) false then 0 else 1)) 0
      have hmem_rs : r_real ∈ sortedRanks d (G i) (A i) := by
        dsimp only [sortedRanks]
        rw [Finset.mem_sort]
        refine Finset.mem_image.mpr ⟨x', by rw [← heq]; exact hx', rfl⟩
      rw [hrs_eq] at hmem_rs
      simp only [List.mem_cons] at hmem_rs
      rcases hmem_rs with rfl | hmem_tail
      · exact le_rfl
      · have hpw : (r0 :: rsTail).Pairwise (· < ·) := by
          rw [← hrs_eq]; exact (sortedRanks_props d (G i) (A i) (hG i)).2.1
        have hlt := (List.pairwise_cons.mp hpw).1 r_real hmem_tail
        exact Nat.le_of_lt hlt
    have heval' := heval hr0_le
    intro j hj q hq
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl]
      have hget_r : (st.2.1 ++ res.2).getD (st.2.1.length + q) (k * (d + 1)) =
          res.2.getD q (k * (d + 1)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      rw [hget_r]
      exact heval' q hq
    · have hjlt : j.val < n := by
        have : j.val ≠ n := fun h => hji (Fin.ext h)
        omega
      rw [if_neg hji]
      have hidx_lt : st.2.2 j + q < st.2.1.length := lt_of_lt_of_le (Nat.add_lt_add_left hq _) (hbound j hjlt)
      have hget_l : (st.2.1 ++ res.2).getD (st.2.2 j + q) (k * (d + 1)) =
          st.2.1.getD (st.2.2 j + q) (k * (d + 1)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hidx_lt, ← List.getD_eq_getElem?_getD]
      rw [hget_l]
      have hmem_w : st.2.1.getD (st.2.2 j + q) (k * (d + 1)) ∈ st.2.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt]
        exact List.getElem_mem hidx_lt
      rw [htail, run_prefix st.1 tail X _ (by rw [hXlen]; exact hmem _ hmem_w)]
      exact ih' j hjlt q hq

private noncomputable def buildRecoveryAll [DecidableEq GateOp] (d k t : ℕ)
    (G : Fin k → Finset (Finset (Fin d))) (A : Fin k → Circuit)
    (out : Fin k → Fin t → ℕ) (E : List ℕ) (uStart : Fin k → ℕ) (gs0 : List Gate) :
    ℕ → List Gate × (Fin k → ℕ) × (Fin k → Fin t → ℕ)
  | 0 => (gs0, fun _ => k * (d + 1), fun _ _ => k * (d + 1))
  | n + 1 =>
    let st := buildRecoveryAll d k t G A out E uStart gs0 n
    if h : n < k then
      let i : Fin k := ⟨n, h⟩
      let M₀ := k * (d + 1) + 2
      let cF := k * (d + 1)
      let rs := sortedRanks d (G i) (A i)
      let recRes := buildRecNotMap M₀ cF E (uStart i) rs (notIdxList (A i))
        rs.length (PEqualNP.NotBracket.notCount (A i))
        (PEqualNP.NotBracket.notCount (A i)) st.1
      let mapRes := remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size
      let actWires := (List.range rs.length).map (fun q => E.getD (uStart i + q) cF)
      let actRes := pushOrList M₀ cF mapRes.1 actWires
      (actRes.1,
        fun j => if j = i then actRes.2 else st.2.1 j,
        fun j a => if j = i then mapRes.2 (out i a) else st.2.2 j a)
    else st

private theorem buildRecoveryAll_props [DecidableEq GateOp] (d k t : ℕ)
    (G : Fin k → Finset (Finset (Fin d))) (hG : ∀ i, (G i).Nonempty)
    (A : Fin k → Circuit) (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (out : Fin k → Fin t → ℕ) (hout : ∀ i a, out i a < d + 2 + (A i).size)
    (E : List ℕ) (uStart : Fin k → ℕ) (gs0 : List Gate)
    (hgs0 : Good (k * (d + 1) + 2) gs0)
    (hE : ∀ w ∈ E, w < (k * (d + 1) + 2) + gs0.length) :
    ∀ n ≤ k,
      let M₀ := k * (d + 1) + 2
      let st := buildRecoveryAll d k t G A out E uStart gs0 n
      (∃ tail, st.1 = gs0 ++ tail ∧ negCount tail = 0 ∧
        posCount tail ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < n),
          (PEqualNP.NotBracket.notCount (A j) * ((sortedRanks d (G j) (A j)).length - 1) +
            ((A j).size - PEqualNP.NotBracket.notCount (A j)) +
            ((sortedRanks d (G j) (A j)).length - 1))) ∧
      Good M₀ st.1 ∧
      (∀ j : Fin k, j.val < n → st.2.1 j < M₀ + st.1.length) ∧
      (∀ j : Fin k, j.val < n → ∀ a : Fin t, st.2.2 j a < M₀ + st.1.length) := by
  intro n hn
  induction n with
  | zero =>
    dsimp only [buildRecoveryAll]
    refine ⟨⟨[], by simp, negCount_nil, by simp [posCount_nil]⟩,
      hgs0, fun j hj => by omega, fun j hj => by omega⟩
  | succ n ih =>
    rcases ih (Nat.le_of_succ_le hn) with ⟨⟨t0, ht0, hn0, hp0⟩, hgood0, hact0, htap0⟩
    dsimp only [buildRecoveryAll]
    have hnk : n < k := hn
    simp only [hnk, ↓reduceDIte]
    set M₀ := k * (d + 1) + 2
    set cF := k * (d + 1)
    set i : Fin k := ⟨n, hnk⟩
    set st := buildRecoveryAll d k t G A out E uStart gs0 n
    set rs := sortedRanks d (G i) (A i)
    set b_i := PEqualNP.NotBracket.notCount (A i)
    have hl0 : gs0.length ≤ st.1.length := by rw [ht0, List.length_append]; omega
    have hcF0 : cF < M₀ + st.1.length := by omega
    have hE0 : ∀ w ∈ E, w < M₀ + st.1.length := fun w hw => lt_of_lt_of_le (hE w hw) (by omega)
    have hm_pos : 1 ≤ rs.length := (sortedRanks_props d (G i) (A i) (hG i)).1
    rcases buildRecNotMap_props M₀ cF E (uStart i) rs (notIdxList (A i)) rs.length b_i hm_pos
        st.1 hgood0 hcF0 hE0 b_i le_rfl with
      ⟨⟨t1, ht1, hn1, hp1⟩, hgood1, hmap1⟩
    set recRes := buildRecNotMap M₀ cF E (uStart i) rs (notIdxList (A i)) rs.length b_i b_i st.1
    have hl1 : st.1.length ≤ recRes.1.length := by rw [ht1, List.length_append]; omega
    have hbase1 : ∀ w < d + 2, baseInFn d cF i.val w < M₀ + recRes.1.length :=
      baseInFn_lt d k i recRes.1.length
    have hnot1 : ∀ j < (A i).size, recRes.2 j < M₀ + recRes.1.length := fun j _ => hmap1 j
    rcases remapLoop_posCount_full d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 with
      ⟨t2, ht2, hn2, hp2⟩
    have hgood2 : Good M₀ (remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size).1 :=
      remapLoop_good d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (hA i).1 (hA i).2
        hgood1 hbase1 hnot1 (A i).size le_rfl
    have hmap2 : ∀ w < d + 2 + (A i).size,
        (remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size).2 w <
          M₀ + (remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size).1.length :=
      remapLoop_map_lt d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 hbase1 hnot1 (A i).size le_rfl
    set mapRes := remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size
    have hl2 : recRes.1.length ≤ mapRes.1.length := by rw [ht2, List.length_append]; omega
    set actWires := (List.range rs.length).map (fun q => E.getD (uStart i + q) cF)
    have hactB : ∀ w ∈ actWires, w < M₀ + mapRes.1.length := by
      intro w hw
      simp only [actWires, List.mem_map, List.mem_range] at hw
      rcases hw with ⟨q, _, rfl⟩
      by_cases hlt : uStart i + q < E.length
      · have hmem : E.getD (uStart i + q) cF ∈ E := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
        exact lt_of_lt_of_le (hE0 _ hmem) (by omega)
      · have hnone : E.getD (uStart i + q) cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
        rw [hnone]
        omega
    rcases pushOrList_props M₀ cF mapRes.1 actWires hgood2 (by omega) hactB with
      ⟨⟨t3, ht3, _, hn3, hp3⟩, hgood3, hw3, _⟩
    set actRes := pushOrList M₀ cF mapRes.1 actWires
    have hl3 : mapRes.1.length ≤ actRes.1.length := by rw [ht3, List.length_append]; omega
    have hfilt : Finset.univ.filter (fun j : Fin k => j.val < n + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < n)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, i]
      omega
    have hni : i ∉ Finset.univ.filter (fun j : Fin k => j.val < n) := by simp [i]
    have hact_len : actWires.length = rs.length := by simp [actWires]
    refine ⟨⟨t0 ++ t1 ++ t2 ++ t3, ?_, ?_, ?_⟩, hgood3, ?_, ?_⟩
    · rw [ht3, ht2, ht1, ht0]; simp [List.append_assoc]
    · simp only [negCount_append, hn0, hn1, hn2, hn3]
    · rw [hfilt, Finset.sum_insert hni]
      simp only [posCount_append]
      rw [hact_len] at hp3
      dsimp only [b_i, rs] at hp1 hp3
      omega
    · intro j hj
      by_cases hji : j = i
      · subst hji; rw [if_pos rfl]; exact hw3
      · rw [if_neg hji]
        have hjlt : j.val < n := by
          have : j.val ≠ n := fun h => hji (Fin.ext h)
          omega
        exact lt_of_lt_of_le (hact0 j hjlt) (by omega)
    · intro j hj a
      by_cases hji : j = i
      · subst hji; rw [if_pos rfl]
        exact lt_of_lt_of_le (hmap2 (out i a) (hout i a)) (by omega)
      · rw [if_neg hji]
        have hjlt : j.val < n := by
          have : j.val ≠ n := fun h => hji (Fin.ext h)
          omega
        exact lt_of_lt_of_le (htap0 j hjlt a) (by omega)

private theorem buildRecoveryAll_eval [DecidableEq GateOp] (d k t : ℕ)
    (G : Fin k → Finset (Finset (Fin d))) (hG : ∀ i, (G i).Nonempty)
    (A : Fin k → Circuit) (hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i))
    (out : Fin k → Fin t → ℕ) (hout : ∀ i a, out i a < d + 2 + (A i).size)
    (E : List ℕ) (uStart : Fin k → ℕ) (gs0 : List Gate)
    (hgs0 : Good (k * (d + 1) + 2) gs0)
    (hE : ∀ w ∈ E, w < (k * (d + 1) + 2) + gs0.length)
    (X : List Bool) (hX : X.length = k * (d + 1) + 2)
    (hcFv : (run gs0 X).getD (k * (d + 1)) false = false)
    (i' : Fin k) (x' : Finset (Fin d)) (hx' : x' ∈ G i')
    (qStar : ℕ) (hqStar : qStar < (sortedRanks d (G i') (A i')).length)
    (hX_base : ∀ w < d + 2, X.getD (baseInFn d (k * (d + 1)) i'.val w) false =
      (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]).getD w false)
    (hrStar : (sortedRanks d (G i') (A i')).getD qStar 0 =
      (notIdxList (A i')).foldl (fun v u =>
        2 * v + (if ((A i').wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (d + 2 + u) false then 0 else 1)) 0)
    (hE_eval : ∀ j : Fin k, ∀ q < (sortedRanks d (G j) (A j)).length,
      (run gs0 X).getD (E.getD (uStart j + q) (k * (d + 1))) false = decide (j = i' ∧ q = qStar)) :
    ∀ n ≤ k, ∀ j : Fin k, j.val < n →
      let st := buildRecoveryAll d k t G A out E uStart gs0 n
      (run st.1 X).getD (st.2.1 j) false = decide (j = i') ∧
      (j = i' → ∀ a : Fin t, (run st.1 X).getD (st.2.2 j a) false =
        ((A i').wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (out i' a) false) := by
  intro n hn
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    have ih' := ih (Nat.le_of_succ_le hn)
    rcases buildRecoveryAll_props d k t G hG A hA out hout E uStart gs0 hgs0 hE n (Nat.le_of_succ_le hn) with
      ⟨⟨t0, ht0, _, _⟩, hgood0, hact0, htap0⟩
    dsimp only [buildRecoveryAll]
    have hnk : n < k := hn
    simp only [hnk, ↓reduceDIte]
    set M₀ := k * (d + 1) + 2
    set cF := k * (d + 1)
    set i : Fin k := ⟨n, hnk⟩
    set st := buildRecoveryAll d k t G A out E uStart gs0 n
    set rs := sortedRanks d (G i) (A i)
    set b_i := PEqualNP.NotBracket.notCount (A i)
    have hl0 : gs0.length ≤ st.1.length := by rw [ht0, List.length_append]; omega
    have hcF0 : cF < M₀ + st.1.length := by omega
    have hE0 : ∀ w ∈ E, w < M₀ + st.1.length := fun w hw => lt_of_lt_of_le (hE w hw) (by omega)
    have hm_pos : 1 ≤ rs.length := (sortedRanks_props d (G i) (A i) (hG i)).1
    rcases buildRecNotMap_props M₀ cF E (uStart i) rs (notIdxList (A i)) rs.length b_i hm_pos
        st.1 hgood0 hcF0 hE0 b_i le_rfl with
      ⟨⟨t1, ht1, _, _⟩, hgood1, hmap1⟩
    set recRes := buildRecNotMap M₀ cF E (uStart i) rs (notIdxList (A i)) rs.length b_i b_i st.1
    have hl1 : st.1.length ≤ recRes.1.length := by rw [ht1, List.length_append]; omega
    have hbase1 : ∀ w < d + 2, baseInFn d cF i.val w < M₀ + recRes.1.length :=
      baseInFn_lt d k i recRes.1.length
    have hnot1 : ∀ j < (A i).size, recRes.2 j < M₀ + recRes.1.length := fun j _ => hmap1 j
    rcases remapLoop_posCount_full d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 with
      ⟨t2, ht2, _, _⟩
    have hgood2 : Good M₀ (remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size).1 :=
      remapLoop_good d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (hA i).1 (hA i).2
        hgood1 hbase1 hnot1 (A i).size le_rfl
    set mapRes := remapLoop d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1 (A i).size
    have hl2 : recRes.1.length ≤ mapRes.1.length := by rw [ht2, List.length_append]; omega
    set actWires := (List.range rs.length).map (fun q => E.getD (uStart i + q) cF)
    have hactB : ∀ w ∈ actWires, w < M₀ + mapRes.1.length := by
      intro w hw
      simp only [actWires, List.mem_map, List.mem_range] at hw
      rcases hw with ⟨q, _, rfl⟩
      by_cases hlt : uStart i + q < E.length
      · have hmem : E.getD (uStart i + q) cF ∈ E := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
        exact lt_of_lt_of_le (hE0 _ hmem) (by omega)
      · have hnone : E.getD (uStart i + q) cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
        rw [hnone]; omega
    rcases pushOrList_props M₀ cF mapRes.1 actWires hgood2 (by omega) hactB with
      ⟨⟨t3, ht3, _, _, _⟩, _, _, heval3⟩
    set actRes := pushOrList M₀ cF mapRes.1 actWires
    have hst_to_act : actRes.1 = st.1 ++ (t1 ++ t2 ++ t3) := by
      rw [ht3, ht2, ht1]; simp [List.append_assoc]
    have hE_st : ∀ j : Fin k, ∀ q < (sortedRanks d (G j) (A j)).length,
        (run st.1 X).getD (E.getD (uStart j + q) cF) false = decide (j = i' ∧ q = qStar) := by
      intro j q hq
      by_cases hlt : uStart j + q < E.length
      · have hmem : E.getD (uStart j + q) cF ∈ E := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
        rw [ht0, run_prefix gs0 t0 X _ (by rw [hX]; exact hE _ hmem), hE_eval j q hq]
      · have hnone : E.getD (uStart j + q) cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
        have hst_cF : (run st.1 X).getD cF false = false := by
          rw [ht0, run_prefix gs0 t0 X cF (by rw [hX]; omega), hcFv]
        rw [hnone, hst_cF, ← hE_eval j q hq, hnone, hcFv]
    have hact_i_eval : (run actRes.1 X).getD actRes.2 false = decide (i = i') := by
      have hcFm : (run mapRes.1 X).getD cF false = false := by
        rw [ht2, ht1, ht0, List.append_assoc, List.append_assoc,
          run_prefix gs0 _ X cF (by rw [hX]; omega), hcFv]
      rw [heval3 X hX hcFm]
      have hmap_pref : ∀ q < rs.length, (run mapRes.1 X).getD (E.getD (uStart i + q) cF) false =
          decide (i = i' ∧ q = qStar) := by
        intro q hq
        by_cases hlt : uStart i + q < E.length
        · have hmem : E.getD (uStart i + q) cF ∈ E := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
          rw [ht2, ht1, List.append_assoc, run_prefix st.1 (t1 ++ t2) X _ (by rw [hX]; exact hE0 _ hmem),
            hE_st i q hq]
        · have hnone : E.getD (uStart i + q) cF = cF := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
          rw [hnone, hcFm, ← hE_st i q hq, hnone, ht0, run_prefix gs0 t0 X cF (by rw [hX]; omega), hcFv]
      by_cases hii' : i = i'
      · subst hii'
        simp only [decide_true]
        rw [List.any_eq_true]
        refine ⟨E.getD (uStart i + qStar) cF, ?_, ?_⟩
        · simp only [actWires, List.mem_map, List.mem_range]
          exact ⟨qStar, hqStar, rfl⟩
        · rw [hmap_pref qStar hqStar]
          simp
      · simp only [decide_eq_false hii']
        apply Bool.eq_false_iff.mpr
        intro htrue
        rw [List.any_eq_true] at htrue
        rcases htrue with ⟨w, hw, hval⟩
        simp only [actWires, List.mem_map, List.mem_range] at hw
        rcases hw with ⟨q, hq, rfl⟩
        rw [hmap_pref q hq] at hval
        simp [hii'] at hval
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl]
      refine ⟨hact_i_eval, fun hii' a => ?_⟩
      subst hii'
      rw [if_pos rfl]
      have hmap_lt := remapLoop_map_lt d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1
        hbase1 hnot1 (A i).size le_rfl (out i a) (hout i a)
      rw [ht3, run_prefix mapRes.1 t3 X _ (by rw [hX]; exact hmap_lt)]
      have hst_cF : (run st.1 X).getD cF false = false := by
        rw [ht0, run_prefix gs0 t0 X cF (by rw [hX]; omega), hcFv]
      have hpw : (notIdxList (A i)).Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
      have hnot_len : (notIdxList (A i)).length = b_i := notIdxList_length (A i)
      have hrec := buildRecNotMap_eval_at M₀ cF E (uStart i) rs (notIdxList (A i)) rs.length b_i
        hm_pos st.1 hgood0 hcF0 hE0 X hX hst_cF qStar hqStar (fun q hq => by simpa using hE_st i q hq) (by rw [hnot_len]) hpw b_i le_rfl
      have hnotEq : ∀ u < (A i).size, ((A i).gates.getD u ⟨GateOp.or, []⟩).op = GateOp.not →
          (run recRes.1 X).getD (recRes.2 u) false =
            ((A i).wires (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true])).getD (d + 2 + u) false := by
        intro u hu huop
        have humem : u ∈ notIdxList (A i) := List.mem_filter.mpr ⟨List.mem_range.mpr hu, decide_eq_true huop⟩
        rcases List.mem_iff_getElem.mp humem with ⟨s, hs, hus⟩
        have hs_b : s < b_i := by rw [← hnot_len]; exact hs
        have hus' : (notIdxList (A i)).getD s 0 = u := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; simpa using hus
        rw [← hus', hrec s hs_b]
        set xBits := List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]
        have hr_fb : rs.getD qStar 0 = foldBits ((notIdxList (A i)).map (fun v =>
            !((A i).wires xBits).getD (d + 2 + v) false)) := by
          rw [hrStar]
          dsimp only [foldBits]
          rw [List.foldl_map]
          congr 1; funext v g
          cases ((A i).wires xBits).getD (d + 2 + g) false <;> rfl
        rw [hr_fb]
        have hfb := bitAt_foldBits ((notIdxList (A i)).map (fun v =>
          !((A i).wires xBits).getD (d + 2 + v) false)) s (by simp; exact hs)
        simp only [List.length_map, hnot_len] at hfb
        rw [hfb]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs]
        simp only [Option.map_some, Option.getD_some, Bool.not_not, hus]
        rw [hus']
      have hbase_rec : ∀ w < d + 2, (run recRes.1 X).getD (baseInFn d cF i.val w) false =
          (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]).getD w false := by
        intro w hw
        rw [ht1, run_prefix st.1 t1 X _ (by rw [hX]; exact baseInFn_lt d k i st.1.length w hw)]
        rw [run_input st.1 X _ (by rw [hX]; exact baseInFn_lt d k i 0 w hw)]
        exact hX_base w hw
      exact remapLoop_eval_final d M₀ (A i) (baseInFn d cF i.val) recRes.2 recRes.1
        (hA i).2 hbase1 hnot1 (List.ofFn (fun a : Fin d => decide (a ∈ x')) ++ [false, true]) (by simp)
        X hX hbase_rec (A i).size le_rfl hnotEq (out i a) (hout i a)
    · rw [if_neg hji]
      have hjlt : j.val < n := by
        have : j.val ≠ n := fun h => hji (Fin.ext h)
        omega
      have ih_j := ih' j hjlt
      refine ⟨?_, fun hii' a => ?_⟩
      · rw [hst_to_act, run_prefix st.1 (t1 ++ t2 ++ t3) X _ (by rw [hX]; exact hact0 j hjlt)]
        exact ih_j.1
      · rw [if_neg hji]
        rw [hst_to_act, run_prefix st.1 (t1 ++ t2 ++ t3) X _ (by rw [hX]; exact htap0 j hjlt a)]
        exact ih_j.2 hii' a

private def buildTaps (k t M₀ cF : ℕ) (act : Fin k → ℕ) (tapW : Fin k → Fin t → ℕ)
    (gs0 : List Gate) : ℕ → List Gate × (Fin t → ℕ)
  | 0 => (gs0, fun _ => cF)
  | n + 1 =>
    let st := buildTaps k t M₀ cF act tapW gs0 n
    if h : n < t then
      let a : Fin t := ⟨n, h⟩
      let pairs := (List.finRange k).map (fun i => (act i, tapW i a))
      let res1 := pushAndList M₀ st.1 pairs
      let res2 := pushOrList M₀ cF res1.1 res1.2
      (res2.1, fun a' => if a' = a then res2.2 else st.2 a')
    else st

private theorem buildTaps_props [DecidableEq GateOp] (k t M₀ cF : ℕ) (hk : 0 < k)
    (act : Fin k → ℕ) (tapW : Fin k → Fin t → ℕ) (gs0 : List Gate)
    (hgs0 : Good M₀ gs0) (hcF : cF < M₀ + gs0.length)
    (hact : ∀ i, act i < M₀ + gs0.length)
    (htapW : ∀ i a, tapW i a < M₀ + gs0.length) :
    ∀ n ≤ t,
      let st := buildTaps k t M₀ cF act tapW gs0 n
      (∃ tail, st.1 = gs0 ++ tail ∧ negCount tail = 0 ∧ posCount tail ≤ 2 * k * n) ∧
      Good M₀ st.1 ∧
      (∀ a : Fin t, a.val < n → st.2 a < M₀ + st.1.length) := by
  intro n hn
  induction n with
  | zero =>
    dsimp only [buildTaps]
    refine ⟨⟨[], by simp, negCount_nil, by simp [posCount_nil]⟩,
      hgs0, fun a ha => by omega⟩
  | succ n ih =>
    rcases ih (Nat.le_of_succ_le hn) with ⟨⟨t0, ht0, hn0, hp0⟩, hgood0, htap0⟩
    dsimp only [buildTaps]
    have hnt : n < t := hn
    simp only [hnt, ↓reduceDIte]
    set a : Fin t := ⟨n, hnt⟩
    set st := buildTaps k t M₀ cF act tapW gs0 n
    have hl0 : gs0.length ≤ st.1.length := by rw [ht0, List.length_append]; omega
    set pairs := (List.finRange k).map (fun i => (act i, tapW i a))
    have hpB : ∀ p ∈ pairs, p.1 < M₀ + st.1.length ∧ p.2 < M₀ + st.1.length := by
      intro p hp
      simp only [pairs, List.mem_map, List.mem_finRange, true_and] at hp
      rcases hp with ⟨i, rfl⟩
      exact ⟨lt_of_lt_of_le (hact i) (by omega), lt_of_lt_of_le (htapW i a) (by omega)⟩
    rcases pushAndList_props M₀ st.1 pairs hgood0 hpB with
      ⟨⟨t1, ht1, _, hn1, hp1⟩, hlen1, hgood1, hm1, _⟩
    set res1 := pushAndList M₀ st.1 pairs
    have hl1 : st.1.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
    rcases pushOrList_props M₀ cF res1.1 res1.2 hgood1 (by omega) hm1 with
      ⟨⟨t2, ht2, _, hn2, hp2⟩, hgood2, hw2, _⟩
    have hl2 : res1.1.length ≤ (pushOrList M₀ cF res1.1 res1.2).1.length := by
      rw [ht2, List.length_append]; omega
    have hplen : pairs.length = k := by simp [pairs]
    refine ⟨⟨t0 ++ t1 ++ t2, ?_, ?_, ?_⟩, hgood2, fun a' ha' => ?_⟩
    · rw [ht2, ht1, ht0]; simp [List.append_assoc]
    · simp only [negCount_append, hn0, hn1, hn2]
    · simp only [posCount_append]
      rw [hlen1, hplen] at hp2
      rw [hplen] at hp1
      calc posCount t0 + posCount t1 + posCount t2
          ≤ 2 * k * n + k + (k - 1) := by omega
        _ ≤ 2 * k * (n + 1) := by rw [Nat.mul_succ]; omega
    · by_cases haa : a' = a
      · subst haa; rw [if_pos rfl]; exact hw2
      · rw [if_neg haa]
        have halt : a'.val < n := by
          have : a'.val ≠ n := fun h => haa (Fin.ext h)
          omega
        exact lt_of_lt_of_le (htap0 a' halt) (by omega)

private theorem buildTaps_eval [DecidableEq GateOp] (k t M₀ cF : ℕ) (hk : 0 < k)
    (act : Fin k → ℕ) (tapW : Fin k → Fin t → ℕ) (gs0 : List Gate)
    (hgs0 : Good M₀ gs0) (hcF : cF < M₀ + gs0.length)
    (hact : ∀ i, act i < M₀ + gs0.length)
    (htapW : ∀ i a, tapW i a < M₀ + gs0.length)
    (X : List Bool) (hX : X.length = M₀)
    (hcFv : (run gs0 X).getD cF false = false)
    (i' : Fin k) (val : Fin t → Bool)
    (hact_eval : ∀ i, (run gs0 X).getD (act i) false = decide (i = i'))
    (htapW_eval : ∀ a, (run gs0 X).getD (tapW i' a) false = val a) :
    ∀ n ≤ t, ∀ a : Fin t, a.val < n →
      let st := buildTaps k t M₀ cF act tapW gs0 n
      (run st.1 X).getD (st.2 a) false = val a := by
  intro n hn
  induction n with
  | zero => intro a ha; omega
  | succ n ih =>
    have ih' := ih (Nat.le_of_succ_le hn)
    rcases buildTaps_props k t M₀ cF hk act tapW gs0 hgs0 hcF hact htapW n (Nat.le_of_succ_le hn) with
      ⟨⟨t0, ht0, _, _⟩, hgood0, htap0⟩
    dsimp only [buildTaps]
    have hnt : n < t := hn
    simp only [hnt, ↓reduceDIte]
    set a0 : Fin t := ⟨n, hnt⟩
    set st := buildTaps k t M₀ cF act tapW gs0 n
    have hl0 : gs0.length ≤ st.1.length := by rw [ht0, List.length_append]; omega
    set pairs := (List.finRange k).map (fun i => (act i, tapW i a0))
    have hpB : ∀ p ∈ pairs, p.1 < M₀ + st.1.length ∧ p.2 < M₀ + st.1.length := by
      intro p hp
      simp only [pairs, List.mem_map, List.mem_finRange, true_and] at hp
      rcases hp with ⟨i, rfl⟩
      exact ⟨lt_of_lt_of_le (hact i) (by omega), lt_of_lt_of_le (htapW i a0) (by omega)⟩
    rcases pushAndList_props M₀ st.1 pairs hgood0 hpB with
      ⟨⟨t1, ht1, _, _, _⟩, hlen1, hgood1, hm1, heval1⟩
    set res1 := pushAndList M₀ st.1 pairs
    have hl1 : st.1.length ≤ res1.1.length := by rw [ht1, List.length_append]; omega
    rcases pushOrList_props M₀ cF res1.1 res1.2 hgood1 (by omega) hm1 with
      ⟨⟨t2, ht2, _, _, _⟩, _, _, heval2⟩
    intro a ha
    by_cases haa : a = a0
    · subst haa
      rw [if_pos rfl]
      have hcF1 : (run res1.1 X).getD cF false = false := by
        rw [ht1, ht0, List.append_assoc, run_prefix gs0 _ X cF (by rw [hX]; exact hcF), hcFv]
      rw [heval2 X hX hcF1]
      have hplen : pairs.length = k := by simp [pairs]
      have hp_get : ∀ idx (hidx : idx < k),
          pairs.getD idx (0, 0) = (act ⟨idx, hidx⟩, tapW ⟨idx, hidx⟩ a0) := by
        intro idx hidx
        dsimp only [pairs]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simp; exact hidx)]
        simp
      have hres1_eval : ∀ idx (hidx : idx < k),
          (run res1.1 X).getD (res1.2.getD idx 0) false =
            (decide ((⟨idx, hidx⟩ : Fin k) = i') && (run gs0 X).getD (tapW ⟨idx, hidx⟩ a0) false) := by
        intro idx hidx
        have hidxp : idx < pairs.length := by rw [hplen]; exact hidx
        rw [heval1 X hX idx hidxp, hp_get idx hidx]
        rw [ht0, run_prefix gs0 t0 X _ (by rw [hX]; exact hact _),
          run_prefix gs0 t0 X _ (by rw [hX]; exact htapW _ _), hact_eval]
      have hi'_idx : i'.val < res1.2.length := by rw [hlen1, hplen]; exact i'.isLt
      cases hval : val a0
      · apply Bool.eq_false_iff.mpr
        intro htrue
        rw [List.any_eq_true] at htrue
        rcases htrue with ⟨w, hw, hwt⟩
        rcases List.mem_iff_getElem.mp hw with ⟨idx, hidx, rfl⟩
        have hidxk : idx < k := by rw [hlen1, hplen] at hidx; exact hidx
        have hgetd : res1.2[idx] = res1.2.getD idx 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; rfl
        rw [hgetd, hres1_eval idx hidxk] at hwt
        by_cases heqi : (⟨idx, hidxk⟩ : Fin k) = i'
        · rw [heqi, htapW_eval a0, hval] at hwt; simp at hwt
        · simp [heqi] at hwt
      · rw [List.any_eq_true]
        refine ⟨res1.2[i'.val], List.getElem_mem hi'_idx, ?_⟩
        have hgetd : res1.2[i'.val] = res1.2.getD i'.val 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'_idx]; rfl
        rw [hgetd, hres1_eval i'.val i'.isLt]
        have heqi : (⟨i'.val, i'.isLt⟩ : Fin k) = i' := Fin.ext rfl
        rw [heqi, decide_eq_true rfl, Bool.true_and, htapW_eval a0, hval]
    · rw [if_neg haa]
      have halt : a.val < n := by
        have : a.val ≠ n := fun h => haa (Fin.ext h)
        omega
      rw [ht2, ht1, List.append_assoc, run_prefix st.1 (t1 ++ t2) X _ (by rw [hX]; exact htap0 a halt)]
      exact ih' a halt

private theorem L_lib_1338_core [DecidableEq GateOp] :
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
    ∀ (d k t B : Nat) (G : Fin k → Finset (Finset (Fin d)))
        (A : Fin k → PEqualNP.CircuitLowerBounds.Circuit) (out : Fin k → Fin t → Nat),
      0 < k → (∀ i, (G i).Nonempty) → (∀ i, valid d (A i)) →
      (∀ i a, out i a < d+2+(A i).size) →
      let b := fun i => PEqualNP.NotBracket.notCount (A i)
      let p := fun i => (A i).size - b i
      let m := fun i => ((G i).image (rank d (A i))).card
      (∑ i, m i) ≤ 2^B →
        let N := k*(d+1)
        let raw := fun (i : Fin k) (x : Finset (Fin d)) =>
          (List.ofFn (fun j : Fin k => decide (j ≤ i) :: List.ofFn (fun z : Fin d =>
            decide (j < i) || (decide (i=j) && decide (z ∈ x))))).flatten ++ [false,true]
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat), valid N C ∧
          (∀ a, tap a < N+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ B ∧
          C.size-PEqualNP.NotBracket.notCount C ≤
            4*(2^B-1) + 2*k*t + ∑ i, m i*(p i+2*b i+3) ∧
          ∀ i x, x ∈ G i → ∀ a, (C.wires (raw i x)).getD (tap a) false =
            ((A i).wires (bits d x)).getD (out i a) false := by
  intro valid bits rank d k t B G A out hk hG hAvalid hout b p m hM N raw
  have hA : ∀ i, PEqualNP.MetaComplexity.FanInTwo (A i) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) (A i) :=
    fun i => ⟨(hAvalid i).1, (hAvalid i).2.1⟩
  have hm_eq : ∀ i : Fin k, (sortedRanks d (G i) (A i)).length = m i := fun i => by
    dsimp only [sortedRanks, m, rank, bits]
    exact Finset.length_sort _
  set M₀ := N + 2
  set cF := N
  set cT := N + 1

  set st1 := buildThreshAll d k G A k
  rcases buildThreshAll_props d k hk G hG A hA k le_rfl with
    ⟨hgood1, hneg1, hpos1, hlen1, hmem1, hbound1, horder1, hcov1⟩
  have hfilt_univ : Finset.univ.filter (fun j : Fin k => j.val < k) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [hfilt_univ] at hpos1 hlen1
  set T_pad := st1.2.1 ++ List.replicate (2 ^ B - st1.2.1.length) cF
  have hT_len : T_pad.length = 2 ^ B := by
    rw [List.length_append, List.length_replicate, hlen1]
    have hM' : ∑ j : Fin k, (sortedRanks d (G j) (A j)).length ≤ 2 ^ B := by
      simpa only [hm_eq] using hM
    omega
  have hT_mem : ∀ w ∈ T_pad, w < M₀ + st1.1.length := by
    intro w hw
    simp only [T_pad, List.mem_append, List.mem_replicate] at hw
    rcases hw with hw | ⟨_, rfl⟩
    · exact hmem1 w hw
    · omega

  set st2 := decodeTree M₀ cF cT T_pad B st1.1 B
  rcases decodeTree_props M₀ cF cT T_pad B st1.1 hgood1 (by omega) (by omega) hT_mem B le_rfl with
    ⟨⟨t2, ht2, hneg2, hpos2⟩, hlen2, hgood2, hmem2⟩
  have hlen12 : st1.1.length ≤ st2.1.length := by rw [ht2, List.length_append]; omega

  set st3 := buildRecoveryAll d k t G A out st2.2 st1.2.2 st2.1 k
  rcases buildRecoveryAll_props d k t G hG A hA out hout st2.2 st1.2.2 st2.1 hgood2 hmem2 k le_rfl with
    ⟨⟨t3, ht3, hneg3, hpos3⟩, hgood3, hact3, htap3⟩
  rw [hfilt_univ] at hpos3
  have hlen23 : st2.1.length ≤ st3.1.length := by rw [ht3, List.length_append]; omega

  set st4 := buildTaps k t M₀ cF st3.2.1 st3.2.2 st3.1 t
  rcases buildTaps_props k t M₀ cF hk st3.2.1 st3.2.2 st3.1 hgood3 (by omega)
      (fun i => hact3 i i.isLt) (fun i a => htap3 i i.isLt a) t le_rfl with
    ⟨⟨t4, ht4, hneg4, hpos4⟩, hgood4, htap4⟩
  refine ⟨⟨st4.1, 0⟩, st4.2, ⟨hgood4.fanInTwo, hgood4.readsBack, by simp [Circuit.size]⟩,
    fun a => htap4 a a.isLt, ?_, ?_, ?_⟩
  · rw [notCount_eq_negCount]
    dsimp only
    rw [ht4, negCount_append, hneg4, ht3, negCount_append, hneg3, ht2, negCount_append, hneg1, hneg2]
    omega
  · rw [size_sub_notCount_eq_posCount]
    dsimp only
    rw [ht4, posCount_append, ht3, posCount_append, ht2, posCount_append]
    have hsum_groups : (∑ j : Fin k, ((sortedRanks d (G j) (A j)).length - 1) *
          ((A j).size - PEqualNP.NotBracket.notCount (A j) + PEqualNP.NotBracket.notCount (A j) + 2)) +
        ∑ j : Fin k, (PEqualNP.NotBracket.notCount (A j) * ((sortedRanks d (G j) (A j)).length - 1) +
          ((A j).size - PEqualNP.NotBracket.notCount (A j)) + ((sortedRanks d (G j) (A j)).length - 1)) ≤
        ∑ i : Fin k, m i * (p i + 2 * b i + 3) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      have hm_pos : 1 ≤ m j := by rw [← hm_eq j]; exact (sortedRanks_props d (G j) (A j) (hG j)).1
      rw [hm_eq j]
      dsimp only [p, b]
      have hm_split : m j = (m j - 1) + 1 := by omega
      have hLHS : (m j - 1) * ((A j).size - PEqualNP.NotBracket.notCount (A j) +
            PEqualNP.NotBracket.notCount (A j) + 2) +
          (PEqualNP.NotBracket.notCount (A j) * (m j - 1) +
            ((A j).size - PEqualNP.NotBracket.notCount (A j)) + (m j - 1)) =
          (m j - 1) * (((A j).size - PEqualNP.NotBracket.notCount (A j)) +
            2 * PEqualNP.NotBracket.notCount (A j) + 3) +
            ((A j).size - PEqualNP.NotBracket.notCount (A j)) := by ring
      have hRHS : m j * (((A j).size - PEqualNP.NotBracket.notCount (A j)) +
            2 * PEqualNP.NotBracket.notCount (A j) + 3) =
          (m j - 1) * (((A j).size - PEqualNP.NotBracket.notCount (A j)) +
            2 * PEqualNP.NotBracket.notCount (A j) + 3) +
            (((A j).size - PEqualNP.NotBracket.notCount (A j)) +
            2 * PEqualNP.NotBracket.notCount (A j) + 3) := by
        conv_lhs => rw [hm_split, Nat.add_mul, Nat.one_mul]
      omega
    have hsum_all : posCount st1.1 + posCount t3 ≤ ∑ i : Fin k, m i * (p i + 2 * b i + 3) :=
      le_trans (Nat.add_le_add hpos1 hpos3) hsum_groups
    omega
  · intro i' x' hx' a
    set X := raw i' x'
    have hXlen : X.length = M₀ := by
      dsimp only [X, raw, M₀, N]
      rw [List.length_append]
      have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
        decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
      simp [hfl]
    have hX_cF : X.getD cF false = false := by
      dsimp only [X, raw, cF, N]
      have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
        decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]; simp
    have hX_cT : X.getD cT false = true := by
      dsimp only [X, raw, cT, N]
      have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
        decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hfl]; omega), hfl]
      have hsub : k * (d + 1) + 1 - k * (d + 1) = 1 := by omega
      rw [hsub]; simp
    have hX_base : ∀ w < d + 2, X.getD (baseInFn d cF i'.val w) false = (bits d x').getD w false := by
      intro w hw
      dsimp only [baseInFn]
      by_cases h1 : w < d
      · rw [if_pos h1]
        dsimp only [X, raw]
        have hfl := flatten_ofFn_length (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
          decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp)
        have hlt : i'.val * (d + 1) + (1 + w) < k * (d + 1) := by
          calc i'.val * (d + 1) + (1 + w) < i'.val * (d + 1) + (d + 1) := by omega
            _ = (i'.val + 1) * (d + 1) := by ring
            _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ i'.isLt
        have hadd : i'.val * (d + 1) + 1 + w = i'.val * (d + 1) + (1 + w) := by omega
        rw [hadd, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hfl]; exact hlt),
          ← List.getD_eq_getElem?_getD]
        have hgf := getD_flatten_ofFn (k := k) (m := d + 1) (fun j : Fin k => decide (j ≤ i') :: List.ofFn (fun z : Fin d =>
          decide (j < i') || (decide (i' = j) && decide (z ∈ x')))) (fun _ => by simp) i' (1 + w) (by omega)
        rw [hgf, Nat.add_comm 1 w, List.getD_cons_succ]
        have hrhs : (bits d x').getD w false =
            (List.ofFn (fun a : Fin d => decide (a ∈ x'))).getD w false := by
          dsimp only [bits]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact h1),
            ← List.getD_eq_getElem?_getD]
        rw [hrhs]
        simp [h1]
      · rw [if_neg h1]
        by_cases h2 : w = d
        · subst h2
          rw [if_pos rfl, hX_cF]
          dsimp only [bits]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        · have hw_eq : w = d + 1 := by omega
          subst hw_eq
          rw [if_neg h2, hX_cT]
          dsimp only [bits]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
    set r_real := rank d (A i') x'
    have hr_mem : r_real ∈ sortedRanks d (G i') (A i') := by
      dsimp only [sortedRanks]
      rw [Finset.mem_sort]
      exact Finset.mem_image.mpr ⟨x', hx', rfl⟩
    rcases List.mem_iff_getElem.mp hr_mem with ⟨qStar, hqStar, hqStar_eq⟩
    have hrStar : (sortedRanks d (G i') (A i')).getD qStar 0 = r_real := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqStar]; simpa using hqStar_eq
    set uStar := st1.2.2 i' + qStar
    have huStar_lt_len : uStar < st1.2.1.length :=
      lt_of_lt_of_le (Nat.add_lt_add_left hqStar _) (hbound1 i' i'.isLt)
    have huStar_lt : uStar < 2 ^ B := by
      have hM' : st1.2.1.length ≤ 2 ^ B := by
        rw [hlen1]; simpa only [hm_eq] using hM
      exact lt_of_lt_of_le huStar_lt_len hM'
    have hT_eval : ∀ u < 2 ^ B, (run st1.1 X).getD (T_pad.getD u cF) false = decide (u ≤ uStar) := by
      intro u hu
      by_cases hu_len : u < st1.2.1.length
      · have hget_t : T_pad.getD u cF = st1.2.1.getD u cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hu_len, ← List.getD_eq_getElem?_getD]
        rw [hget_t]
        rcases hcov1 u hu_len with ⟨j, q, hq, hjn, rfl⟩
        have he1 := buildThreshAll_eval d k hk G hG A hA i' x' hx' k le_rfl j j.isLt q hq
        rw [he1]
        by_cases hlt : i' < j
        · simp only [hlt, ↓reduceIte]
          have hord := horder1 i' j hlt j.isLt
          have hnotle : ¬ ((buildThreshAll d k G A k).2.2 j + q ≤ uStar) := by dsimp only [st1, uStar]; omega
          simp [hnotle]
        · by_cases hgt : j < i'
          · simp only [hlt, hgt, ↓reduceIte]
            have hord := horder1 j i' hgt i'.isLt
            have hle : (buildThreshAll d k G A k).2.2 j + q ≤ uStar := by dsimp only [st1, uStar]; omega
            simp [hle]
          · have heq : j = i' := Fin.ext (by omega)
            subst heq
            simp only [hlt, hgt, ↓reduceIte]
            rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
            have hrStar' : (sortedRanks d (G j) (A j)).getD qStar 0 =
                List.foldl (fun v u => 2 * v + if ((A j).wires ((List.ofFn (fun a : Fin d => decide (a ∈ x'))) ++ [false, true])).getD (d + 2 + u) false = true then 0 else 1)
                  0 (notIdxList (A j)) := by
              dsimp only [r_real, rank, bits] at hrStar
              exact hrStar
            rw [← hrStar']
            have hpw := (sortedRanks_props d (G j) (A j) (hG j)).2.1
            have hle_iff : (sortedRanks d (G j) (A j)).getD q 0 ≤
                (sortedRanks d (G j) (A j)).getD qStar 0 ↔ q ≤ qStar := by
              constructor
              · intro hle
                by_contra hgtq
                have hltq : qStar < q := by omega
                have hlt_pw := (List.pairwise_iff_getElem.mp hpw) qStar q hqStar hq hltq
                simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqStar,
                  List.getElem?_eq_getElem hq, Option.getD_some] at hle
                omega
              · intro hleq
                by_cases heqq : q = qStar
                · subst heqq; exact le_rfl
                · have hltq : q < qStar := by omega
                  have hlt_pw := (List.pairwise_iff_getElem.mp hpw) q qStar hq hqStar hltq
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqStar,
                    List.getElem?_eq_getElem hq, Option.getD_some]
                  exact Nat.le_of_lt hlt_pw
            have hu_iff : (buildThreshAll d k G A k).2.2 j + q ≤ uStar ↔ q ≤ qStar := by dsimp only [st1, uStar]; omega
            rw [hle_iff, hu_iff]
      · have hsub_lt : u - st1.2.1.length < 2 ^ B - st1.2.1.length := by omega
        have hget_t : T_pad.getD u cF = cF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt hu_len),
            List.getElem?_replicate, if_pos hsub_lt, Option.getD_some]
        rw [hget_t, run_input st1.1 X cF (by rw [hXlen]; omega), hX_cF]
        have hnotle : ¬ (u ≤ uStar) := by omega
        simp [hnotle]
    have hst1_cF : (run st1.1 X).getD cF false = false := by
      rw [run_input st1.1 X cF (by rw [hXlen]; omega), hX_cF]
    have hst1_cT : (run st1.1 X).getD cT false = true := by
      rw [run_input st1.1 X cT (by rw [hXlen]; omega), hX_cT]
    have hE_eval_all := decodeTree_eval M₀ cF cT T_pad B st1.1 hgood1 (by omega) (by omega)
      hT_mem X hXlen hst1_cF hst1_cT uStar huStar_lt (by rw [hT_len]) hT_eval B le_rfl
    have hE_eval : ∀ j : Fin k, ∀ q < (sortedRanks d (G j) (A j)).length,
        (run st2.1 X).getD (st2.2.getD (st1.2.2 j + q) cF) false = decide (j = i' ∧ q = qStar) := by
      intro j q hq
      have huj_lt : st1.2.2 j + q < st1.2.1.length :=
        lt_of_lt_of_le (Nat.add_lt_add_left hq _) (hbound1 j j.isLt)
      have hM' : st1.2.1.length ≤ 2 ^ B := by
        rw [hlen1]; simpa only [hm_eq] using hM
      have huj_B : st1.2.2 j + q < 2 ^ B := lt_of_lt_of_le huj_lt hM'
      rw [hE_eval_all _ huj_B]
      have hsub0 : B - B = 0 := Nat.sub_self B
      rw [hsub0, Nat.pow_zero, Nat.div_one]
      by_cases hji : j = i'
      · subst hji; simp [uStar, eq_comm]
      · have hne : st1.2.2 j + q ≠ uStar := by
          dsimp only [st1, uStar]
          rcases Nat.lt_trichotomy j.val i'.val with hlt | heqv | hgt
          · have hord := horder1 j i' hlt i'.isLt; omega
          · exact absurd (Fin.ext heqv) hji
          · have hord := horder1 i' j hgt j.isLt; omega
        have hne' : uStar ≠ st1.2.2 j + q := Ne.symm hne
        simp [hji, hne']
    have hst2_cF : (run st2.1 X).getD cF false = false := by
      rw [run_input st2.1 X cF (by rw [hXlen]; omega), hX_cF]
    have hrec_eval := buildRecoveryAll_eval d k t G hG A hA out hout st2.2 st1.2.2 st2.1 hgood2 hmem2
      X hXlen hst2_cF i' x' hx' qStar hqStar hX_base hrStar hE_eval k le_rfl
    have hst3_cF : (run st3.1 X).getD cF false = false := by
      rw [run_input st3.1 X cF (by rw [hXlen]; omega), hX_cF]
    have hact_eval : ∀ j, (run st3.1 X).getD (st3.2.1 j) false = decide (j = i') := fun j =>
      (hrec_eval j j.isLt).1
    have htapW_eval : ∀ a0, (run st3.1 X).getD (st3.2.2 i' a0) false =
        ((A i').wires (bits d x')).getD (out i' a0) false :=
      (hrec_eval i' i'.isLt).2 rfl
    have htaps_eval := buildTaps_eval k t M₀ cF hk st3.2.1 st3.2.2 st3.1 hgood3 (by omega)
      (fun i => hact3 i i.isLt) (fun i a => htap3 i i.isLt a) X hXlen hst3_cF i'
      (fun a0 => ((A i').wires (bits d x')).getD (out i' a0) false) hact_eval htapW_eval t le_rfl
    rw [circuit_wires_eq_run]
    exact htaps_eval a a.isLt

end PEqualNP.Outside.L_lib_1338_aux

theorem PEqualNP.Outside.L_lib_1338 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
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
∀ (d k t B : Nat) (G : Fin k → Finset (Finset (Fin d)))
    (A : Fin k → PEqualNP.CircuitLowerBounds.Circuit) (out : Fin k → Fin t → Nat),
  0 < k → (∀ i, (G i).Nonempty) → (∀ i, valid d (A i)) →
  (∀ i a, out i a < d+2+(A i).size) →
  let b := fun i => PEqualNP.NotBracket.notCount (A i)
  let p := fun i => (A i).size - b i
  let m := fun i => ((G i).image (rank d (A i))).card
  (∑ i, m i) ≤ 2^B →
    let N := k*(d+1)
    let raw := fun (i : Fin k) (x : Finset (Fin d)) =>
      (List.ofFn (fun j : Fin k => decide (j ≤ i) :: List.ofFn (fun z : Fin d =>
        decide (j < i) || (decide (i=j) && decide (z ∈ x))))).flatten ++ [false,true]
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat), valid N C ∧
      (∀ a, tap a < N+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ B ∧
      C.size-PEqualNP.NotBracket.notCount C ≤
        4*(2^B-1) + 2*k*t + ∑ i, m i*(p i+2*b i+3) ∧
      ∀ i x, x ∈ G i → ∀ a, (C.wires (raw i x)).getD (tap a) false =
        ((A i).wires (bits d x)).getD (out i a) false) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
    PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro valid bits rank d k t B G A out hk hG hA hout b p m hM N raw
  have hbits_eq : ∀ x : Finset (Fin d),
      bits d x = List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true] := fun x => by
    dsimp only [bits]
    congr 1; congr 1; funext a
    exact congrArg (@decide (a ∈ x)) (Subsingleton.elim _ _)
  have hrank_eq : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin d)),
      rank d C x =
        ((List.range C.size).filter (fun j => decide
          ((C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))).foldl
          (fun v j => 2 * v + (if (C.wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false then 0 else 1)) 0 := by
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
  have hraw_eq : ∀ (i : Fin k) (x : Finset (Fin d)),
      raw i x = (List.ofFn (fun j : Fin k => decide (j ≤ i) :: List.ofFn (fun z : Fin d =>
        decide (j < i) || (decide (i = j) && decide (z ∈ x))))).flatten ++ [false, true] := by
    intro i x
    dsimp only [raw]
    congr 1; congr 1; congr 1; funext j
    congr 1
    · exact congrArg (@decide (j ≤ i)) (Subsingleton.elim _ _)
    · congr 1; funext z
      rw [congrArg (@decide (j < i)) (Subsingleton.elim _ _),
        congrArg (@decide (i = j)) (Subsingleton.elim _ _),
        congrArg (@decide (z ∈ x)) (Subsingleton.elim _ _)]
  have hm_eq : ∀ i : Fin k, m i = ((G i).image (fun x =>
      ((List.range (A i).size).filter (fun j => decide
        (((A i).gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))).foldl
        (fun v j => 2 * v + (if ((A i).wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false then 0 else 1)) 0)).card := by
    intro i; dsimp only [m]
    congr 1; ext r; simp only [Finset.mem_image, hrank_eq]
  have hM' : (∑ i, ((G i).image (fun x =>
      ((List.range (A i).size).filter (fun j => decide
        (((A i).gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))).foldl
        (fun v j => 2 * v + (if ((A i).wires (List.ofFn (fun a : Fin d => decide (a ∈ x)) ++ [false, true])).getD (d + 2 + j) false then 0 else 1)) 0)).card) ≤ 2 ^ B := by
    convert hM using 1
    apply Finset.sum_congr rfl
    intro i _
    exact (hm_eq i).symm
  rcases PEqualNP.Outside.L_lib_1338_aux.L_lib_1338_core d k t B G A out hk hG hA hout hM' with
    ⟨C, tap, hCvalid, htap, hnot, hpos, heval⟩
  refine ⟨C, tap, hCvalid, htap, hnot, ?_, ?_⟩
  · convert hpos using 2
    apply Finset.sum_congr rfl
    intro i _
    rw [hm_eq i]
  · intro i x hx a
    rw [hraw_eq i x, hbits_eq x]
    exact heval i x hx a
