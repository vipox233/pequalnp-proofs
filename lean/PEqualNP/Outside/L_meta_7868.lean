import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]

private lemma foldl_step_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepWire init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    simp [ih]
    omega

private lemma foldl_step_getD_lt (gs : List Gate) (init : List Bool) (w : ℕ) (hw : w < init.length) :
    (gs.foldl stepWire init).getD w Bool.false = init.getD w Bool.false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    have hlen : w < (gs.foldl stepWire init).length := by rw [foldl_step_len]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepWire inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length :=
  foldl_step_len C.gates inp

private lemma wires_getD_input (C : Circuit) (inp : List Bool) (w : ℕ) (hw : w < inp.length) :
    (C.wires inp).getD w Bool.false = inp.getD w Bool.false :=
  foldl_step_getD_lt C.gates inp w hw

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires inp).getD (inp.length + j) Bool.false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((C.gates.take j).foldl stepWire inp).getD i Bool.false) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    calc C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      _ = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
      _ = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by simp
  rw [wires_eq_foldl]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set pref := (C.gates.take j).foldl stepWire inp
  have hplen : pref.length = inp.length + j := by
    simp only [pref, foldl_step_len, List.length_take]
    omega
  have hlt : inp.length + j < (stepWire pref C.gates[j]).length := by
    simp only [stepWire, List.length_append, List.length_singleton, hplen]; omega
  rw [foldl_step_getD_lt _ _ _ hlt]
  simp only [stepWire, List.getD_eq_getElem?_getD]
  rw [← hplen, List.getElem?_append_right (le_refl _)]
  simp

private lemma wires_getD_take_eq (C : Circuit) (inp : List Bool) (j i : ℕ)
    (hj : j ≤ C.gates.length) (hi : i < inp.length + j) :
    ((C.gates.take j).foldl stepWire inp).getD i Bool.false =
      (C.wires inp).getD i Bool.false := by
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  rw [wires_eq_foldl]
  conv_rhs => rw [hsplit]
  rw [List.foldl_append]
  have hplen : ((C.gates.take j).foldl stepWire inp).length = inp.length + j := by
    rw [foldl_step_len, List.length_take]; omega
  exact (foldl_step_getD_lt (C.gates.drop j) ((C.gates.take j).foldl stepWire inp) i (by omega)).symm

private lemma wires_getD_gate_full (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (C.gates[j]).inputs, i < inp.length + j) :
    (C.wires inp).getD (inp.length + j) Bool.false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires inp).getD i Bool.false) := by
  rw [wires_getD_gate C inp j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact wires_getD_take_eq C inp j i (le_of_lt hj) (hrb i hi)

private lemma wires_getD_ge (C : Circuit) (inp : List Bool) (w : ℕ)
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w Bool.false = Bool.false := by
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires inp).length ≤ w := by rw [wires_len]; exact hw
  rw [List.getElem?_eq_none hlen]
  rfl

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

abbrev V := Fin 26
abbrev E := Fin 52
abbrev X := V → Bool
abbrev pidx (e : E) : Fin 13 := Fin.ofNat 13 (e.val % 13 + ([0,1,3,9] : List ℕ).getD (e.val / 13) 0)
abbrev lidx (e : E) : Fin 13 := Fin.ofNat 13 e.val
abbrev lv (e : E) : V := Fin.castAdd 13 (pidx e)
abbrev rv (e : E) : V := Fin.natAdd 13 (lidx e)
def ep (e : E) : X := fun v => decide (v = lv e ∨ v = rv e)
def one (v : V) : X := fun u => decide (u = v)
def zero : X := fun _ => false
def dm (m : E) : X := fun v => ([42074634,17056265,1147395,6815755,17048596,34112530,2294790,13631510,34097192,1124388,4589580,27263020,1093712,2248776,9179160,54526040,2179233,4489361,18350129,41951408,4358466,8978722,36700258,16802144,8716932,17957444,6299844,33604288,17433864,35914888,12599688,107904,34867728,4729104,25199376,215808,2634784,9458208,50398752,431616,5261377,18908225,33696832,855041,10522754,37816450,292992,1710082,21037317,8532228,577793,3411973] : List ℕ).getD m.val 0 |>.testBit v.val
def flipped (x : X) (v : V) : X := fun j => x j || decide (j = v)
def pts (m : E) : Finset (Fin 13) := Finset.univ.filter fun p => dm m (Fin.castAdd 13 p)
theorem deg4 : ∀ v : V, (Finset.univ.filter fun e : E => ep e v).card = 4 := by decide +kernel
theorem twoHit : ∀ u v : V, u ≠ v → (Finset.univ.filter fun e : E => ep e u && ep e v).card ≤ 1 := by decide +kernel
theorem nz20 : ∀ m : E, (Finset.univ.filter fun v : V => dm m v = false).card = 20 := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem commonMask : ∀ u v : V, (u.val < 13 ↔ v.val < 13) → ∃ m : E, dm m u = true ∧ dm m v = true := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem boundary : ∀ m : E, ∀ v : V, dm m v = false → ∃ e : E,
    flipped (dm m) v (lv e) = true ∧ flipped (dm m) v (rv e) = true := by decide +kernel


def inp (x : X) := List.ofFn x ++ [true,false]
def wire (C : Circuit) (i : ℕ) (x : X) := (C.wires (inp x)).getD i false
def ors (C : Circuit) : Finset ℕ := ((Finset.range C.size).filter fun j =>
  (gateAt C j).op.eval [false,true]).image (28 + ·)
def Shape (W : ℕ → X → Bool) (O : Finset ℕ) := ∀ w,
  (∃ b : Bool, ∀ x, W w x = b) ∨ (∃ i : V, ∀ x, W w x = x i) ∨
  ∃ a < w, ∃ b < w, (∀ x, W w x = (W a x && W b x)) ∨
    w ∈ O ∧ ∀ x, W w x = (W a x || W b x)

private theorem inplen (x : X) : (inp x).length = 28 := by simp [inp]
private theorem base (C : Circuit) (w : ℕ) (hw : w < 28) (x : X) :
    wire C w x = (inp x).getD w false := wires_getD_input _ _ _ (by rw [inplen]; exact hw)
private theorem at26 (C : Circuit) (x : X) : wire C 26 x = true := by
  rw [base C 26 (by decide)]
  simp [inp, List.getD_eq_getElem?_getD]
private theorem at27 (C : Circuit) (x : X) : wire C 27 x = false := by
  rw [base C 27 (by decide)]
  simp [inp, List.getD_eq_getElem?_getD]
theorem shape (C : Circuit) (hm : Monotone2 C) : Shape (wire C) (ors C) := by
  intro w
  by_cases hw : w < 26
  · refine Or.inr (Or.inl ⟨⟨w,hw⟩, fun x => ?_⟩)
    rw [base C w (by omega)]
    unfold inp
    rw [List.getD_append _ _ _ _ (by simpa using hw),
      List.getD_eq_getElem _ _ (by simpa using hw)]
    simp only [List.getElem_ofFn]
  by_cases hbase : w < 28
  · rcases (show w = 26 ∨ w = 27 by omega) with rfl | rfl
    · exact Or.inl ⟨_, at26 C⟩
    · exact Or.inl ⟨_, at27 C⟩
  by_cases htop : w < 28 + C.gates.length
  · right; right
    let j := w - 28
    have hj : j < C.gates.length := by dsimp [j]; omega
    have eqw : w = 28 + j := by dsimp [j]; omega
    let g := C.gates[j]
    obtain ⟨hg,hlen⟩ := hm g (List.getElem_mem hj)
    change g.op = GateOp.and ∨ g.op = GateOp.or at hg
    let idx := fun k : ℕ => if k < w then k else 27
    have idxlt (k : ℕ) : idx k < w := by dsimp [idx]; split <;> omega
    have get (x : X) (k : ℕ) :
        ((C.gates.take j).foldl stepWire (inp x)).getD k false = wire C (idx k) x := by
      by_cases h : k < w
      · simp only [idx, ite_eq_left h, wire]
        exact wires_getD_take_eq C (inp x) j k (by omega) (by rw [inplen]; omega)
      · simp only [idx, ite_eq_right h, at27]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · rw [foldl_step_len, inplen, List.length_take, Nat.min_eq_left (by omega)]
          omega
    have eval (x : X) : wire C w x = g.op.eval (g.inputs.map fun k => wire C (idx k) x) := by
      have hh := wires_getD_gate C (inp x) j hj
      rw [inplen, ← eqw] at hh
      rw [wire, hh]
      congr 1
      exact List.map_congr_left fun k _ => get x k
    have memO (op : g.op = GateOp.or) : w ∈ ors C := by
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_⟩,eqw.symm⟩
      have hgat : gateAt C j = g := by simp [gateAt,g,List.getD_eq_getElem?_getD,hj]
      simp [hgat,op,GateOp.eval]
    match hin : g.inputs with
    | [] =>
      rcases hg with op | op
      · exact ⟨26,by omega,26,by omega, Or.inl (fun x => by simp [eval x, hin, op, GateOp.eval, at26])⟩
      · exact ⟨27,by omega,27,by omega, Or.inr ⟨memO op,fun x => by simp [eval x, hin, op, GateOp.eval, at27]⟩⟩
    | [a] =>
      refine ⟨idx a, idxlt _, idx a, idxlt _, ?_⟩
      rcases hg with op | op
      · exact Or.inl fun x => by simp [eval x, hin,op,GateOp.eval]
      · exact Or.inr ⟨memO op, fun x => by simp [eval x,hin,op,GateOp.eval]⟩
    | [a,b] =>
      refine ⟨idx a, idxlt _, idx b, idxlt _, ?_⟩
      rcases hg with op | op
      · exact Or.inl fun x => by simp [eval x,hin,op,GateOp.eval]
      · exact Or.inr ⟨memO op,fun x => by simp [eval x,hin,op,GateOp.eval]⟩
    | _ :: _ :: _ :: _ => simp [hin] at hlen
  · exact Or.inl ⟨false, fun x => wires_getD_ge C (inp x) w (by rw [inplen]; omega)⟩


section Model
variable {W : ℕ → X → Bool} {O : Finset ℕ}

def Tests (W : ℕ → X → Bool) := ∀ m : E, ∃ a b : ℕ,
  W a (dm m) = false ∧ W b (dm m) = false ∧
  ∀ e : E, W a (ep e) = true ∨ W b (ep e) = true

theorem monoW (sh : Shape W O) {x y : X} (xy : ∀ i, x i = true → y i = true)
    (w : ℕ) : W w x = true → W w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases sh w with ⟨c,h⟩ | ⟨i,h⟩ | ⟨a,ha,b,hb,h | ⟨_,h⟩⟩
    · simp only [h]; exact id
    · simpa only [h] using xy i
    · simp only [h, Bool.and_eq_true]
      exact fun p => ⟨ih a ha p.1,ih b hb p.2⟩
    · simp only [h, Bool.or_eq_true]
      exact Or.imp (ih a ha) (ih b hb)

theorem falseBudget (sh : Shape W O) (tests : Tests W) (m : E) :
    18 ≤ (O.filter fun w => W w (dm m) = false).card := by
  classical
  let M := dm m
  let f := fun w => Finset.univ.filter fun v : V =>
    M v = false ∧ W w M = false ∧ W w (flipped M v) = true
  let B := O.filter fun w => W w M = false
  obtain ⟨a,b,fa,fb,pos⟩ := tests m
  have count := dag_union_bound f {a,b} B
  have step : ∀ w, 1 < (f w).card →
      (∃ a < w, f w ⊆ f a) ∨ (w ∈ B ∧ ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b) := by
    intro w big
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (f w).card)
    have fw := (Finset.mem_filter.mp hv).2.2.1
    rcases sh w with ⟨c,op⟩ | ⟨i,op⟩ | ⟨i,hi,j,hj,op | ⟨hw,op⟩⟩
    · have ht := (Finset.mem_filter.mp hv).2.2.2
      simp only [op] at fw ht
      exact Bool.false_ne_true (fw.symm.trans ht) |>.elim
    · have hs : f w ⊆ {i} := by
        intro k hk
        obtain ⟨_,h1,h2⟩ := (Finset.mem_filter.mp hk).2
        rw [op] at h1
        simp only [op,flipped,h1,Bool.false_or,decide_eq_true_eq] at h2
        exact Finset.mem_singleton.mpr h2.symm
      have := Finset.card_le_card hs
      simp at this
      omega
    · rw [op, Bool.and_eq_false_iff] at fw
      rcases fw with h | h
      · left; refine ⟨i,hi,fun k hk => ?_⟩
        obtain ⟨hz,_,h2⟩ := (Finset.mem_filter.mp hk).2
        rw [op, Bool.and_eq_true] at h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,h,h2.1⟩
      · left; refine ⟨j,hj,fun k hk => ?_⟩
        obtain ⟨hz,_,h2⟩ := (Finset.mem_filter.mp hk).2
        rw [op, Bool.and_eq_true] at h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,h,h2.2⟩
    · right; refine ⟨Finset.mem_filter.mpr ⟨hw,fw⟩,i,hi,j,hj,fun k hk => ?_⟩
      obtain ⟨hz,_,h2⟩ := (Finset.mem_filter.mp hk).2
      rw [op, Bool.or_eq_true] at h2
      rw [op, Bool.or_eq_false_iff] at fw
      apply Finset.mem_union.mpr
      rcases h2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,fw.1,h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,fw.2,h⟩)
  have hcount := count step
  have hs : (Finset.univ.filter fun v => dm m v = false) ⊆ ({a,b} : Finset ℕ).biUnion f := by
    intro v hv
    have h0 := (Finset.mem_filter.mp hv).2
    obtain ⟨e,he1,he2⟩ := boundary m v h0
    have rel (i : V) (hh : ep e i = true) : flipped M v i = true := by
      simp only [ep,decide_eq_true_eq] at hh
      rcases hh with rfl | rfl <;> assumption
    rcases pos e with h | h
    · exact Finset.mem_biUnion.mpr ⟨a,by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0,fa,monoW sh rel a h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨b,by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0,fb,monoW sh rel b h⟩⟩
  have lower := Finset.card_le_card hs
  rw [nz20] at lower
  have roots : ({a,b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  change 18 ≤ B.card
  omega


def sing (W : ℕ → X → Bool) (w : ℕ) : Finset V :=
  Finset.univ.filter fun v => W w zero = false ∧ W w (one v) = true

def special (W : ℕ → X → Bool) (O : Finset ℕ) := O.filter fun w => (sing W w).Nonempty

lemma memSing {w : ℕ} {v : V} : v ∈ sing W w ↔ W w zero = false ∧ W w (one v) = true := by
  simp [sing]

theorem specialSmall (sh : Shape W O) (tests : Tests W) (small : O.card ≤ 19) :
    (special W O).card ≤ 2 := by
  classical
  have budget (m : E) : (O.filter fun w => W w (dm m) = true).card ≤ 1 := by
    have low := falseBudget sh tests m
    have h := Finset.card_filter_add_card_filter_not (s := O) (p := fun w => W w (dm m) = false)
    simp only [Bool.not_eq_false] at h
    omega
  let S := special W O
  let half := fun b : Bool => S.filter fun w => ∃ v ∈ sing W w, decide (v.val < 13) = b
  have each (t : Bool) : (half t).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, i, hi, hside⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, j, hj, hside'⟩ := Finset.mem_filter.mp hb
    obtain ⟨m, mi, mj⟩ := commonMask i j (by
      have e := hside.trans hside'.symm
      simpa only [decide_eq_decide] using e)
    have lift (v : V) (h : dm m v = true) (k : ℕ) (hk : v ∈ sing W k) : W k (dm m) = true :=
      monoW sh (x := one v) (y := dm m) (fun i hh => by
        have e : i = v := by simpa [one] using hh
        simpa only [e] using h) k (memSing.mp hk).2
    exact Finset.card_le_one.mp (budget m) a (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,lift i mi a hi⟩)
      b (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1,lift j mj b hj⟩)
  have cover : S ⊆ half true ∪ half false := by
    intro w hw
    obtain ⟨v,hv⟩ := (Finset.mem_filter.mp hw).2
    cases h : decide (v.val < 13) with
    | false => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw,v,hv,h⟩)
    | true => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,v,hv,h⟩)
  have := Finset.card_le_card cover
  have := Finset.card_union_le (half true) (half false)
  have := each true
  have := each false
  change S.card ≤ 2
  omega

def exc (W : ℕ → X → Bool) (O : Finset ℕ) := (special W O).biUnion (sing W)

theorem excSmall (sh : Shape W O) (hs : (special W O).card ≤ 2) :
    (exc W O).card ≤ 4 := by
  classical
  have bound := dag_union_bound (sing W) (special W O) (special W O)
  have step : ∀ w, 1 < (sing W w).card → (∃ a < w, sing W w ⊆ sing W a) ∨
      (w ∈ special W O ∧ ∃ a < w, ∃ b < w, sing W w ⊆ sing W a ∪ sing W b) := by
    intro w large
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (sing W w).card)
    obtain ⟨off,on⟩ := memSing.mp hv
    rcases sh w with ⟨c,op⟩ | ⟨i,op⟩ | ⟨a,ha,b,hb,op | ⟨hw,op⟩⟩
    · rw [op] at off on
      exact (Bool.false_ne_true (off.symm.trans on)).elim
    · have sub : sing W w ⊆ {i} := by
        intro k hk
        have h := (memSing.mp hk).2
        rw [op] at h
        exact Finset.mem_singleton.mpr ((of_decide_eq_true h).symm)
      have := Finset.card_le_card sub
      simp at this
      omega
    · rw [op, Bool.and_eq_false_iff] at off
      rcases off with off | off
      · left; refine ⟨a,ha,fun k hk => ?_⟩
        have h := (memSing.mp hk).2
        rw [op,Bool.and_eq_true] at h
        exact memSing.mpr ⟨off,h.1⟩
      · left; refine ⟨b,hb,fun k hk => ?_⟩
        have h := (memSing.mp hk).2
        rw [op,Bool.and_eq_true] at h
        exact memSing.mpr ⟨off,h.2⟩
    · rw [op,Bool.or_eq_false_iff] at off
      right; refine ⟨Finset.mem_filter.mpr ⟨hw,v,hv⟩,a,ha,b,hb,fun k hk => ?_⟩
      have h := (memSing.mp hk).2
      rw [op,Bool.or_eq_true] at h
      exact Finset.mem_union.mpr (h.imp (fun t => memSing.mpr ⟨off.1,t⟩) (fun t => memSing.mpr ⟨off.2,t⟩))
  have := bound step
  change ((special W O).biUnion (sing W)).card ≤ 4
  omega


def cleanEdges (W : ℕ → X → Bool) (O : Finset ℕ) : Finset E :=
  Finset.univ \ (exc W O).biUnion (fun v => Finset.univ.filter fun e : E => ep e v)

theorem cleanLarge (he : (exc W O).card ≤ 4) : 36 ≤ (cleanEdges W O).card := by
  classical
  let bad := (exc W O).biUnion (fun v => Finset.univ.filter fun e : E => ep e v)
  have hb : bad.card ≤ 16 := by
    have hh := Finset.card_biUnion_le (s := exc W O) (t := fun v => Finset.univ.filter fun e : E => ep e v)
    simp only [deg4,Finset.sum_const,smul_eq_mul] at hh
    change bad.card ≤ (exc W O).card * 4 at hh
    omega
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  change 36 ≤ ((Finset.univ : Finset E) \ bad).card
  simp only [Finset.card_univ,Fintype.card_fin] at h
  omega

theorem literal (sh : Shape W O) {u : V} (hu : u ∉ exc W O) (w : ℕ)
    (off : W w zero = false) (on : W w (one u) = true) (e : E) (yes : W w (ep e) = true) :
    ep e u = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases sh w with ⟨c,op⟩ | ⟨i,op⟩ | ⟨a,ha,b,hb,op | ⟨hw,op⟩⟩
    · rw [op] at on off
      exact (Bool.false_ne_true (off.symm.trans on)).elim
    · have t : i = u := by simpa only [op,one,decide_eq_true_eq] using on
      simpa only [op,t] using yes
    · rw [op,Bool.and_eq_false_iff] at off
      rw [op,Bool.and_eq_true] at yes on
      exact off.elim (fun z => ih a ha z on.1 yes.1) (fun z => ih b hb z on.2 yes.2)
    · have mem := memSing.mpr ⟨off,on⟩
      exact (hu (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,u,mem⟩,mem⟩)).elim

def Hidden (W : ℕ → X → Bool) (O : Finset ℕ) (w : ℕ) : Prop :=
  W w zero = false ∧ ∀ v : V, v ∉ exc W O → W w (one v) = false

theorem reveal (h : ¬Hidden W O w) (off : W w zero = false) :
    ∃ v : V, v ∉ exc W O ∧ W w (one v) = true := by
  classical
  by_contra! hn
  apply h
  refine ⟨off, fun v hv => ?_⟩
  simpa using hn v hv

theorem zeroOn (sh : Shape W O) {w : ℕ} (h : W w zero = true) (x : X) : W w x = true :=
  monoW sh (x := zero) (y := x) (fun i hh => by simp [zero] at hh) w h

theorem endCount (sh : Shape W O) (tests : Tests W) (small : O.card ≤ 19)
    (he : 36 ≤ (cleanEdges W O).card) : False := by
  classical
  let U := cleanEdges W O
  let q := fun w => U.filter fun e => W w (ep e) = true
  let f := fun w => if Hidden W O w then q w else ∅
  have step : ∀ w, 1 < (f w).card → (∃ a < w, f w ⊆ f a) ∨
      (w ∈ O ∧ ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b) := by
    intro w big
    by_cases h : Hidden W O w
    · rw [show f w = q w by simp [f,h]] at big ⊢
      rcases sh w with ⟨c,op⟩ | ⟨i,op⟩ | ⟨a,ha,b,hb,op | ⟨hw,op⟩⟩
      · obtain ⟨e,hy⟩ := Finset.card_pos.mp (by omega : 0 < (q w).card)
        have hn := h.1
        have hp := (Finset.mem_filter.mp hy).2
        rw [op] at hn hp
        exact (Bool.false_ne_true (hn.symm.trans hp)).elim
      · obtain ⟨e,hy⟩ := Finset.card_pos.mp (by omega : 0 < (q w).card)
        obtain ⟨heU,yes⟩ := Finset.mem_filter.mp hy
        have hit : ep e i = true := by simpa only [op] using yes
        have outside : i ∉ exc W O := by
          intro mem
          exact (Finset.mem_sdiff.mp heU).2 (Finset.mem_biUnion.mpr
            ⟨i,mem,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩⟩)
        have bad := h.2 i outside
        simp [op,one] at bad
      · have inherit (k : ℕ) (hk : k < w) (hid : Hidden W O k)
            (inc : ∀ e, W w (ep e) = true → W k (ep e) = true) :
            ∃ t < w, q w ⊆ f t := by
          refine ⟨k,hk,?_⟩
          simp only [f,ite_eq_left hid]
          intro e heq
          obtain ⟨he1,he2⟩ := Finset.mem_filter.mp heq
          exact Finset.mem_filter.mpr ⟨he1,inc e he2⟩
        by_cases ach : Hidden W O a
        · exact Or.inl (inherit a ha ach (fun e yes => by rw [op,Bool.and_eq_true] at yes; exact yes.1))
        by_cases bch : Hidden W O b
        · exact Or.inl (inherit b hb bch (fun e yes => by rw [op,Bool.and_eq_true] at yes; exact yes.2))
        have aoff : W a zero = false := by
          by_contra! hon
          apply bch
          have same (x : X) : W w x = W b x := by simp [op,zeroOn sh (by simpa using hon)]
          exact ⟨(same _).symm.trans h.1,fun v hv => (same _).symm.trans (h.2 v hv)⟩
        have boff : W b zero = false := by
          by_contra! hon
          apply ach
          have same (x : X) : W w x = W a x := by simp [op,zeroOn sh (by simpa using hon)]
          exact ⟨(same _).symm.trans h.1,fun v hv => (same _).symm.trans (h.2 v hv)⟩
        obtain ⟨u,hu,au⟩ := reveal ach aoff
        obtain ⟨v,hv,bv⟩ := reveal bch boff
        have ne : u ≠ v := by
          rintro rfl
          have hh := h.2 u hu
          simp [op,au,bv] at hh
        have sub : q w ⊆ Finset.univ.filter (fun e : E => ep e u && ep e v) := by
          intro e eq
          have yes := (Finset.mem_filter.mp eq).2
          rw [op,Bool.and_eq_true] at yes
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [literal sh hu a aoff au e yes.1,literal sh hv b boff bv e yes.2]⟩
        have := Finset.card_le_card sub
        have := twoHit u v ne
        omega
      · right
        have off := h.1
        rw [op,Bool.or_eq_false_iff] at off
        have singOff (v : V) (hv : v ∉ exc W O) := h.2 v hv
        simp only [op,Bool.or_eq_false_iff] at singOff
        have ah : Hidden W O a := ⟨off.1,fun v hv => (singOff v hv).1⟩
        have bh : Hidden W O b := ⟨off.2,fun v hv => (singOff v hv).2⟩
        refine ⟨hw,a,ha,b,hb,?_⟩
        simp only [f,ite_eq_left ah,ite_eq_left bh]
        intro e eq
        obtain ⟨eu,yes⟩ := Finset.mem_filter.mp eq
        rw [op,Bool.or_eq_true] at yes
        exact Finset.mem_union.mpr (yes.imp (fun t => Finset.mem_filter.mpr ⟨eu,t⟩)
          (fun t => Finset.mem_filter.mpr ⟨eu,t⟩))
    · simp [f,h] at big
  obtain ⟨a,b,fa,fb,pos⟩ := tests 0
  have bound := dag_union_bound f {a,b} O step
  let other := fun w => if Hidden W O w then (∅ : Finset E) else q w
  have other_le (w : ℕ) (off : W w (dm 0) = false) : (other w).card ≤ 4 := by
    by_cases h : Hidden W O w
    · simp [other,h]
    have hz : W w zero = false := by
      by_contra! hon
      rw [zeroOn sh (by simpa using hon)] at off
      contradiction
    obtain ⟨v,hv,on⟩ := reveal h hz
    have sub : q w ⊆ Finset.univ.filter (fun e : E => ep e v) := by
      intro e he'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,literal sh hv w hz on e (Finset.mem_filter.mp he').2⟩
    simpa only [other,h,ite_false,deg4] using Finset.card_le_card sub
  let R : Finset ℕ := {a,b}
  have use (w : ℕ) (hw : w ∈ R) (e : E) (eq : e ∈ q w) : e ∈ R.biUnion f ∨ e ∈ other w := by
    by_cases h : Hidden W O w
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨w,hw,by simpa only [f,ite_eq_left h] using eq⟩)
    · exact Or.inr (by simpa only [other,ite_eq_right h] using eq)
  have sub : U ⊆ (R.biUnion f ∪ other a) ∪ other b := by
    intro e he'
    rcases pos e with ea | eb
    · exact Finset.mem_union_left _ (Finset.mem_union.mpr (use a (by simp [R]) e (Finset.mem_filter.mpr ⟨he',ea⟩)))
    · rcases use b (by simp [R]) e (Finset.mem_filter.mpr ⟨he',eb⟩) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h
  have := Finset.card_le_card sub
  have := Finset.card_union_le (R.biUnion f ∪ other a) (other b)
  have := Finset.card_union_le (R.biUnion f) (other a)
  have := other_le a fa
  have := other_le b fb
  have rootcard : R.card ≤ 2 := Finset.card_le_two
  change (R.biUnion f).card ≤ R.card + O.card at bound
  change 36 ≤ U.card at he
  omega
end Model

end PEqualNP.Outside.L_meta_7868

open PEqualNP.Outside.L_meta_7868 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_7868 : (let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → Fin (26 : ℕ) → Bool := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → Fin (26 : ℕ) → Bool := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (20 : ℕ) ≤ {x20 ∈ Finset.range x9.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x20).op.eval [Bool.false, Bool.true] = Bool.true}.card) := by
  intro I d R misses Xs pairs inputs kind C hm W covers join rejects S hs cost good hbeh
  have valid : ∀ m : E, kind (pts m) ∧ inputs (pts m) = dm m := by
    dsimp only [kind,inputs,misses,R,d,I]
    decide +kernel
  have positive : ∀ e : E, R (pidx e) (lidx e) := by
    dsimp only [R,d,I]
    decide +kernel
  have tests : Tests (wire C) := by
    intro m
    obtain ⟨z,hz,off⟩ := hbeh (pts m) (valid m).1
    change ¬(wire C z.1 (inputs (pts m)) || wire C z.2 (inputs (pts m))) = true at off
    rw [(valid m).2] at off
    have ff := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr off)
    refine ⟨z.1,z.2,ff.1,ff.2,?_⟩
    intro e
    have p := (good z hz).1 (pidx e) (lidx e) (positive e)
    change (wire C z.1 (ep e) || wire C z.2 (ep e)) = true at p
    simpa only [Bool.or_eq_true] using p
  have ocard : (ors C).card = ((Finset.range C.size).filter fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [false,true]).card :=
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
  rw [← ocard]
  by_contra! h
  have low : (ors C).card ≤ 19 := by omega
  have sh := shape C hm
  exact endCount sh tests low (cleanLarge (excSmall sh (specialSmall sh tests low)))
