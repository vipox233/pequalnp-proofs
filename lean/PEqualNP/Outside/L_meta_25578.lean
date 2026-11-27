import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25578_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private theorem foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) {i : Nat}
    (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun idx => acc.getD idx false)]).length := by
      simp
      omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

private theorem wires_getD_input (C : Circuit) (x : List Bool) {i : Nat} (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_getD_lt C.gates x hi

private theorem wires_getD_gate (C : Circuit) (x : List Bool) {j : Nat}
    (hj : j < C.gates.length) (hback : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  have hgate : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  set f : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  set w1 : List Bool := (C.gates.take j).foldl f x
  have hw1_len : w1.length = x.length + j := by
    have h := foldl_wires_len (C.gates.take j) x
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h
    exact h
  have hw_eq : C.wires x = (C.gates.drop (j + 1)).foldl f (f w1 C.gates[j]) := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hidx_lt : x.length + j < (f w1 C.gates[j]).length := by
    simp only [f, List.length_append, List.length_singleton, hw1_len]
    omega
  have hget : (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false) := by
    rw [hw_eq, foldl_wires_getD_lt _ _ hidx_lt]
    simp only [f, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega : w1.length ≤ x.length + j)]
    simp [hw1_len]
  rw [hget, hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := by
    have hb := hback j hj i
    rw [hgate] at hb
    exact hb hi
  have hiw1 : i < w1.length := by omega
  have hilen : i < (f w1 C.gates[j]).length := by
    dsimp only [f]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hw_eq, foldl_wires_getD_lt _ _ hilen]
  dsimp only [f]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiw1]

private theorem oneEach_len {n m : Nat} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_row {n m : Nat} (u : Fin n) (v : Fin m) {i : Nat} (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hi])]
  simp [hi, Fin.ext_iff]

private theorem oneEach_getD_col {n m : Nat} (u : Fin n) (v : Fin m) {j : Nat} (hj : j < m) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp [hj, Fin.ext_iff]

private theorem readsIn_eq_one_unique (C : Circuit) (G : Finset Nat) (w : Nat)
    (h : readsIn C G w = 1) :
    ∃ j ∈ G, w ∈ (gateAt C j).inputs ∧ (gateAt C j).inputs.count w = 1 ∧
      ∀ j' ∈ G, w ∈ (gateAt C j').inputs → j' = j := by
  unfold readsIn at h
  have hex : ∃ j ∈ G, 0 < (gateAt C j).inputs.count w := by
    by_contra hall
    have hall' : ∀ j ∈ G, (gateAt C j).inputs.count w = 0 := by
      intro j hj
      by_contra hne
      exact hall ⟨j, hj, Nat.pos_of_ne_zero hne⟩
    have h0 : ∑ j ∈ G, (gateAt C j).inputs.count w = 0 := Finset.sum_eq_zero hall'
    omega
  rcases hex with ⟨j, hjG, hpos⟩
  have hle : (gateAt C j).inputs.count w ≤ 1 := by
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hjG
    omega
  have heq1 : (gateAt C j).inputs.count w = 1 := by omega
  refine ⟨j, hjG, List.count_pos_iff.mp hpos, heq1, ?_⟩
  intro j' hj'G hmem'
  by_contra hne
  have hpos' : 0 < (gateAt C j').inputs.count w := List.count_pos_iff.mpr hmem'
  have hsum2 : (gateAt C j).inputs.count w + (gateAt C j').inputs.count w ≤
      ∑ i ∈ G, (gateAt C i).inputs.count w := by
    have hsub : ({j, j'} : Finset Nat) ⊆ G := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle2 := Finset.sum_le_sum_of_subset (f := fun i => (gateAt C i).inputs.count w) hsub
    rw [Finset.sum_pair (Ne.symm hne)] at hle2
    exact hle2
  omega

private theorem readsIn_eq_zero_not_mem (C : Circuit) (G : Finset Nat) (w : Nat)
    (h : readsIn C G w = 0) : ∀ j ∈ G, w ∉ (gateAt C j).inputs := by
  unfold readsIn at h
  intro j hj hmem
  have hpos : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hmem
  have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
  omega

private def descOf (raw : Nat) (C : Circuit) (region : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) : Nat → Finset Nat
  | w =>
    if h : raw ≤ w ∧ w - raw ∈ region then
      insert w (((gateAt C (w - raw)).inputs.attach.map (fun ⟨u, hu⟩ =>
        have hlt : u < w := by
          have hmem := hreg h.2
          rw [Finset.mem_range] at hmem
          have hb := hback (w - raw) hmem u hu
          omega
        descOf raw C region hback hreg u)).foldr (· ∪ ·) ∅)
    else {w}
termination_by w => w

private theorem mem_descOf_self (raw : Nat) (C : Circuit) (region : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) (w : Nat) :
    w ∈ descOf raw C region hback hreg w := by
  rw [descOf]
  split_ifs <;> simp

private theorem mem_descOf_le (raw : Nat) (C : Circuit) (region : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size) :
    ∀ w z, z ∈ descOf raw C region hback hreg w → z ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z hz
    rw [descOf] at hz
    split_ifs at hz with h
    · simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Nat.le_refl _
      · have hfold : ∀ (ls : List (Finset Nat)), z ∈ ls.foldr (· ∪ ·) ∅ → ∃ s ∈ ls, z ∈ s := by
          intro ls
          induction ls with
          | nil => simp
          | cons a ls ih2 =>
            intro hm
            simp only [List.foldr_cons, Finset.mem_union] at hm
            rcases hm with h1 | h2
            · exact ⟨a, by simp, h1⟩
            · rcases ih2 h2 with ⟨s, hs, hzs⟩
              exact ⟨s, by simp [hs], hzs⟩
        rcases hfold _ hz with ⟨s, hs, hzs⟩
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hs
        rcases hs with ⟨u, hu, rfl⟩
        have hmem := hreg h.2
        rw [Finset.mem_range] at hmem
        have hlt : u < w := by
          have hb := hback (w - raw) hmem u hu
          omega
        exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih u hlt z hzs) hlt)
    · simp only [Finset.mem_singleton] at hz
      omega

private theorem descOf_gate_eq (raw : Nat) (C : Circuit) (region : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    {k u₁ u₂ : Nat} (hk : k ∈ region) (hinp : (gateAt C k).inputs = [u₁, u₂]) :
    descOf raw C region hback hreg (raw + k) =
      insert (raw + k) (descOf raw C region hback hreg u₁ ∪ descOf raw C region hback hreg u₂) := by
  rw [descOf]
  have hcond : raw ≤ raw + k ∧ raw + k - raw ∈ region := ⟨by omega, by simpa using hk⟩
  rw [dif_pos hcond]
  congr 1
  have hsub : raw + k - raw = k := Nat.add_sub_cancel_left raw k
  ext z
  simp only [Finset.mem_union]
  have hfold : ∀ (ls : List (Finset Nat)), z ∈ ls.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ ls, z ∈ s := by
    intro ls
    induction ls with
    | nil => simp
    | cons a ls ih2 =>
      simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp, ih2]
  rw [hfold]
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hzu⟩
    rw [hsub, hinp] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · left; exact hzu
    · right; exact hzu
  · rintro (hz1 | hz2)
    · refine ⟨descOf raw C region hback hreg u₁, ⟨u₁, ?_, rfl⟩, hz1⟩
      rw [hsub, hinp]; simp
    · refine ⟨descOf raw C region hback hreg u₂, ⟨u₂, ?_, rfl⟩, hz2⟩
      rw [hsub, hinp]; simp

private theorem descOf_leaf_eq (raw : Nat) (C : Circuit) (region : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    {w : Nat} (hw : ¬ (raw ≤ w ∧ w - raw ∈ region)) :
    descOf raw C region hback hreg w = {w} := by
  rw [descOf]
  rw [dif_neg hw]

private def evalTree (raw : Nat) (C : Circuit) (region entry : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (sVal : Nat → Bool) (eVal : Bool) : Nat → Bool
  | w =>
    if h : raw ≤ w ∧ w - raw ∈ region then
      (gateAt C (w - raw)).op.eval ((gateAt C (w - raw)).inputs.attach.map (fun ⟨u, hu⟩ =>
        have hlt : u < w := by
          have hmem := hreg h.2
          rw [Finset.mem_range] at hmem
          have hb := hback (w - raw) hmem u hu
          omega
        evalTree raw C region entry hback hreg sVal eVal u))
    else if w ∈ entry then eVal else sVal w
termination_by w => w

private theorem evalTree_gate_eq (raw : Nat) (C : Circuit) (region entry : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (sVal : Nat → Bool) (eVal : Bool)
    {k u₁ u₂ : Nat} (hk : k ∈ region) (hinp : (gateAt C k).inputs = [u₁, u₂]) :
    evalTree raw C region entry hback hreg sVal eVal (raw + k) =
      (gateAt C k).op.eval
        [evalTree raw C region entry hback hreg sVal eVal u₁,
         evalTree raw C region entry hback hreg sVal eVal u₂] := by
  rw [evalTree]
  have hcond : raw ≤ raw + k ∧ raw + k - raw ∈ region := ⟨by omega, by simpa using hk⟩
  rw [dif_pos hcond]
  have hsub : raw + k - raw = k := Nat.add_sub_cancel_left raw k
  congr 1
  · rw [hsub]
  · generalize_proofs pf
    have hmap : ∀ (l : List Nat) (hl : ∀ u ∈ l, u < raw + k),
        l.attach.map (fun ⟨u, hu⟩ => evalTree raw C region entry hback hreg sVal eVal u) =
        l.map (evalTree raw C region entry hback hreg sVal eVal) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.attach_cons, List.map_cons, List.map_map]
        congr 1
        exact ih (fun u hu => hl u (List.mem_cons_of_mem a hu))
    rw [hmap _ (fun u hu => pf u hu), hsub, hinp]
    rfl

private theorem evalTree_entry_eq (raw : Nat) (C : Circuit) (region entry : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (sVal : Nat → Bool) (eVal : Bool)
    {w : Nat} (hnot : ¬ (raw ≤ w ∧ w - raw ∈ region)) (he : w ∈ entry) :
    evalTree raw C region entry hback hreg sVal eVal w = eVal := by
  rw [evalTree, dif_neg hnot, if_pos he]

private theorem evalTree_src_eq (raw : Nat) (C : Circuit) (region entry : Finset Nat)
    (hback : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (sVal : Nat → Bool) (eVal : Bool)
    {w : Nat} (hnot : ¬ (raw ≤ w ∧ w - raw ∈ region)) (hne : w ∉ entry) :
    evalTree raw C region entry hback hreg sVal eVal w = sVal w := by
  rw [evalTree, dif_neg hnot, if_neg hne]

private theorem solve_25578 (n m : Nat) (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset Nat) (root : Nat)
    (hback : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hreg : region ⊆ Finset.range C.size)
    (hroot : root ∈ (R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)) ∪
        region.image (fun idx => (n + m) + idx))
    (hentry_card : entry.card ≤ 1)
    (hentry_prop : ∀ w ∈ entry,
      w ∉ ((R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)) ∪
        region.image (fun idx => (n + m) + idx)) ∧
      w < root ∧ readsIn C region w = 1)
    (hgates : ∀ k ∈ region,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C k).inputs,
        w ∈ ((R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)) ∪
          region.image (fun idx => (n + m) + idx)) ∨ w ∈ entry)
    (hroot_reads : readsIn C region root = 0)
    (hpriv : ∀ w ∈ ((R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)) ∪
        region.image (fun idx => (n + m) + idx)),
      w ≠ root → readsIn C region w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) :
    let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
    let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
    let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ witnessCol ∈ B, G keptRow witnessCol ≠ rowPol)
    let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ witnessRow ∈ R, G witnessRow keptCol ≠ colPol)
    rowTypes.card ≤ 2 + entry.card ∧
    colTypes.card ≤ 2 + entry.card ∧
    ∃ mark : Bool,
      ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark, ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
        G a x = mark → G b x = mark → G b y = mark → G a y = mark := by
  intro rowTypes colTypes coreRows coreCols
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let desc := descOf raw C region hback hreg
  have hsrc_lt : ∀ w ∈ sources, w < raw := by
    intro w hw
    simp only [sources, Finset.mem_union, Finset.mem_image] at hw
    rcases hw with ⟨r, _, rfl⟩ | ⟨c, _, rfl⟩ <;> omega
  have hwire_split : ∀ w ∈ wires, (w < raw ∧ w ∈ sources) ∨ (raw ≤ w ∧ w - raw ∈ region) := by
    intro w hw
    simp only [wires, Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hs | ⟨k, hk, rfl⟩
    · left; exact ⟨hsrc_lt w hs, hs⟩
    · right; exact ⟨by omega, by simpa using hk⟩
  have hentry_not_reg : ∀ w ∈ entry, ¬ (raw ≤ w ∧ w - raw ∈ region) := by
    intro w hw ⟨hge, hkr⟩
    have hnw := (hentry_prop w hw).1
    apply hnw
    simp only [Finset.mem_union, Finset.mem_image]
    right
    exact ⟨w - raw, hkr, by omega⟩
  have hdesc_sub_we : ∀ w, w ∈ wires ∨ w ∈ entry → desc w ⊆ wires ∪ entry := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rcases hw with hw | he
      · rcases hwire_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hd : desc w = {w} := descOf_leaf_eq raw C region hback hreg (by omega)
          rw [hd]
          intro z hz
          simp only [Finset.mem_singleton] at hz
          subst hz
          exact Finset.mem_union_left _ hw
        · set k := w - raw
          have hwk : w = raw + k := by omega
          rcases hgates k hk with ⟨_, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hd : desc w = insert w (desc u₁ ∪ desc u₂) := by
            rw [hwk]; exact descOf_gate_eq raw C region hback hreg hk hinp
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1lt : u₁ < w := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < w := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          rw [hd]
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_union] at hz
          rcases hz with rfl | hz1 | hz2
          · exact Finset.mem_union_left _ hw
          · exact ih u₁ hu1lt hu1w hz1
          · exact ih u₂ hu2lt hu2w hz2
      · have hd : desc w = {w} := descOf_leaf_eq raw C region hback hreg (hentry_not_reg w he)
        rw [hd]
        intro z hz
        simp only [Finset.mem_singleton] at hz
        subst hz
        exact Finset.mem_union_right _ he
  have hdesc_step : ∀ x, x ∈ wires ∨ x ∈ entry → ∀ z ∈ desc x,
      z = x ∨ ∃ j ∈ region, z ∈ (gateAt C j).inputs ∧ raw + j ∈ desc x := by
    intro x
    induction x using Nat.strong_induction_on with
    | ind x ih =>
      intro hx z hz
      rcases hx with hx | he
      · rcases hwire_split x hx with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hd : desc x = {x} := descOf_leaf_eq raw C region hback hreg (by omega)
          rw [hd, Finset.mem_singleton] at hz
          left; exact hz
        · set k := x - raw
          have hxk : x = raw + k := by omega
          rcases hgates k hk with ⟨_, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hd : desc x = insert x (desc u₁ ∪ desc u₂) := by
            rw [hxk]; exact descOf_gate_eq raw C region hback hreg hk hinp
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1lt : u₁ < x := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < x := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          rw [hd] at hz
          simp only [Finset.mem_insert, Finset.mem_union] at hz
          rcases hz with rfl | hz1 | hz2
          · left; rfl
          · right
            rcases ih u₁ hu1lt hu1w z hz1 with rfl | ⟨j, hj, hzj, hjmem⟩
            · exact ⟨k, hk, by rw [hinp]; simp, by rw [← hxk]; exact mem_descOf_self _ _ _ _ _ x⟩
            · exact ⟨j, hj, hzj, by rw [hd]; simp [hjmem]⟩
          · right
            rcases ih u₂ hu2lt hu2w z hz2 with rfl | ⟨j, hj, hzj, hjmem⟩
            · exact ⟨k, hk, by rw [hinp]; simp, by rw [← hxk]; exact mem_descOf_self _ _ _ _ _ x⟩
            · exact ⟨j, hj, hzj, by rw [hd]; simp [hjmem]⟩
      · have hd : desc x = {x} := descOf_leaf_eq raw C region hback hreg (hentry_not_reg x he)
        rw [hd, Finset.mem_singleton] at hz
        left; exact hz
  have hlocal_one : ∀ w, (w ∈ wires ∨ w ∈ entry) → w ≠ root → readsIn C region w = 1 := by
    intro w hw hne
    rcases hw with hw | he
    · exact (hpriv w hw hne).1
    · exact (hentry_prop w he).2.2
  have hchildren_disj : ∀ k ∈ region, ∀ u₁ u₂, (gateAt C k).inputs = [u₁, u₂] →
      Disjoint (desc u₁) (desc u₂) := by
    intro k hk u₁ u₂ hinp
    have hu1w := (hgates k hk).2.2 u₁ (by rw [hinp]; simp)
    have hu2w := (hgates k hk).2.2 u₂ (by rw [hinp]; simp)
    have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
    have hu1lt : u₁ < raw + k := hback k hkr u₁ (by rw [hinp]; simp)
    have hu2lt : u₂ < raw + k := hback k hkr u₂ (by rw [hinp]; simp)
    have hu1_nr : u₁ ≠ root := by
      intro heq; subst heq
      exact readsIn_eq_zero_not_mem C region u₁ hroot_reads k hk (by rw [hinp]; simp)
    have hu2_nr : u₂ ≠ root := by
      intro heq; subst heq
      exact readsIn_eq_zero_not_mem C region u₂ hroot_reads k hk (by rw [hinp]; simp)
    have hu1_ne_u2 : u₁ ≠ u₂ := by
      intro heq; subst heq
      have hlr := hlocal_one u₁ hu1w hu1_nr
      rcases readsIn_eq_one_unique C region u₁ hlr with ⟨j, hj, _, hcnt, huniq⟩
      have hjk : k = j := huniq k hk (by rw [hinp]; simp)
      subst hjk
      rw [hinp] at hcnt
      simp at hcnt
    rw [Finset.disjoint_left]
    intro z0 hz1 hz2
    let I := desc u₁ ∩ desc u₂
    have hIne : I.Nonempty := ⟨z0, Finset.mem_inter.mpr ⟨hz1, hz2⟩⟩
    let z := I.max' hIne
    have hzI : z ∈ I := Finset.max'_mem I hIne
    have hz_in1 : z ∈ desc u₁ := (Finset.mem_inter.mp hzI).1
    have hz_in2 : z ∈ desc u₂ := (Finset.mem_inter.mp hzI).2
    have hzw : z ∈ wires ∨ z ∈ entry := Finset.mem_union.mp (hdesc_sub_we u₁ hu1w hz_in1)
    have hznr : z ≠ root := by
      intro heq
      rcases hdesc_step u₁ hu1w z hz_in1 with hzu | ⟨j, hj, hzj, _⟩
      · exact hu1_nr (hzu.symm.trans heq)
      · exact readsIn_eq_zero_not_mem C region root hroot_reads j hj (heq ▸ hzj)
    rcases readsIn_eq_one_unique C region z (hlocal_one z hzw hznr) with ⟨j, hj, hzj, _, huniq⟩
    have hj1 : raw + j ∈ desc u₁ ∨ z = u₁ := by
      rcases hdesc_step u₁ hu1w z hz_in1 with heq1 | ⟨j', hj', hzj', hj'in⟩
      · right; exact heq1
      · left
        have heq : j' = j := huniq j' hj' hzj'
        subst heq; exact hj'in
    have hj2 : raw + j ∈ desc u₂ ∨ z = u₂ := by
      rcases hdesc_step u₂ hu2w z hz_in2 with heq2 | ⟨j', hj', hzj', hj'in⟩
      · right; exact heq2
      · left
        have heq : j' = j := huniq j' hj' hzj'
        subst heq; exact hj'in
    rcases hj1 with h1 | heq1
    · rcases hj2 with h2 | heq2
      · have hparI : raw + j ∈ I := Finset.mem_inter.mpr ⟨h1, h2⟩
        have hle := Finset.le_max' I (raw + j) hparI
        have hjr : j < C.size := Finset.mem_range.mp (hreg hj)
        have hlt : z < raw + j := hback j hjr z hzj
        omega
      · have hkj : k = j := huniq k hk (by rw [heq2, hinp]; simp)
        subst hkj
        have hle := mem_descOf_le raw C region hback hreg u₁ (raw + k) h1
        omega
    · rcases hj2 with h2 | heq2
      · have hkj : k = j := huniq k hk (by rw [heq1, hinp]; simp)
        subst hkj
        have hle := mem_descOf_le raw C region hback hreg u₂ (raw + k) h2
        omega
      · exact hu1_ne_u2 (heq1.symm.trans heq2)
  have hout_indep_lt_root : ∀ x₁ x₂ : List Bool, x₁.length = raw → x₂.length = raw →
      (∀ i < raw, i ∉ sources → x₁.getD i false = x₂.getD i false) →
      ∀ w < root, w ∉ wires → (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
    intro x₁ x₂ hx1 hx2 hag w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt hwnw
      by_cases hwraw : w < raw
      · rw [wires_getD_input C x₁ (by omega), wires_getD_input C x₂ (by omega)]
        exact hag w hwraw (fun hs => hwnw (Finset.mem_union_left _ hs))
      · set j := w - raw
        have hwj : w = raw + j := by omega
        by_cases hjlt : j < C.size
        · have hgate1 := wires_getD_gate C x₁ hjlt (by rw [hx1]; exact hback)
          rw [hx1] at hgate1
          have hgate2 := wires_getD_gate C x₂ hjlt (by rw [hx2]; exact hback)
          rw [hx2] at hgate2
          rw [hwj, hgate1, hgate2]
          congr 1
          apply List.map_congr_left
          intro a ha
          have halt : a < w := by have hb := hback j hjlt a ha; omega
          have hanw : a ∉ wires := by
            intro haw
            have hanr : a ≠ root := by omega
            have hpr := hpriv a haw hanr
            rcases readsIn_eq_one_unique C region a hpr.1 with ⟨j0, hj0, haj0, _, _⟩
            rcases readsIn_eq_one_unique C (Finset.range C.size) a hpr.2.1 with ⟨j1, _, _, _, huniq⟩
            have h1 : j0 = j1 := huniq j0 (hreg hj0) haj0
            have h2 : j = j1 := huniq j (Finset.mem_range.mpr hjlt) ha
            have hjreg : j ∈ region := by rw [h2, ← h1]; exact hj0
            apply hwnw
            rw [hwj]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjreg, rfl⟩)
          exact ih a halt (by omega) hanw
        · have hlen1 : (C.wires x₁).length = raw + C.size := by rw [wires_len, hx1]; rfl
          have hlen2 : (C.wires x₂).length = raw + C.size := by rw [wires_len, hx2]; rfl
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega : (C.wires x₁).length ≤ w),
            List.getElem?_eq_none (by omega : (C.wires x₂).length ≤ w)]
  have hbottleneck : ∀ x₁ x₂ : List Bool, x₁.length = raw → x₂.length = raw →
      (∀ i < raw, i ∉ sources → x₁.getD i false = x₂.getD i false) →
      (C.wires x₁).getD root false = (C.wires x₂).getD root false →
      C.eval x₁ = C.eval x₂ := by
    intro x₁ x₂ hx1 hx2 hag hreq
    have hwire_out : ∀ w < raw + C.size, (w ∈ wires → w = root) →
        (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hnot
        by_cases hwr : w = root
        · subst hwr; exact hreq
        · by_cases hwraw : w < raw
          · rw [wires_getD_input C x₁ (by omega), wires_getD_input C x₂ (by omega)]
            exact hag w hwraw (fun hs => hwr (hnot (Finset.mem_union_left _ hs)))
          · set j := w - raw
            have hwj : w = raw + j := by omega
            have hjlt : j < C.size := by omega
            have hjnr : j ∉ region := by
              intro hjr
              have hww : w ∈ wires := by
                rw [hwj]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjr, rfl⟩)
              exact hwr (hnot hww)
            have hgate1 := wires_getD_gate C x₁ hjlt (by rw [hx1]; exact hback)
            rw [hx1] at hgate1
            have hgate2 := wires_getD_gate C x₂ hjlt (by rw [hx2]; exact hback)
            rw [hx2] at hgate2
            rw [hwj, hgate1, hgate2]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < w := by have hb := hback j hjlt a ha; omega
            apply ih a halt (by omega)
            intro haw
            by_contra hanr
            have hpr := hpriv a haw hanr
            rcases readsIn_eq_one_unique C region a hpr.1 with ⟨j0, hj0, haj0, _, _⟩
            rcases readsIn_eq_one_unique C (Finset.range C.size) a hpr.2.1 with ⟨j1, _, _, _, huniq⟩
            have h1 : j0 = j1 := huniq j0 (hreg hj0) haj0
            have h2 : j = j1 := huniq j (Finset.mem_range.mpr hjlt) ha
            exact hjnr (by rw [h2, ← h1]; exact hj0)
    unfold Circuit.eval
    by_cases hout_lt : C.output < raw + C.size
    · apply hwire_out C.output hout_lt
      intro how
      by_contra honr
      exact (hpriv C.output how honr).2.2 rfl
    · have hlen1 : (C.wires x₁).length = raw + C.size := by rw [wires_len, hx1]; rfl
      have hlen2 : (C.wires x₂).length = raw + C.size := by rw [wires_len, hx2]; rfl
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega : (C.wires x₁).length ≤ C.output),
        List.getElem?_eq_none (by omega : (C.wires x₂).length ≤ C.output)]
  have hevalTree_eq_wires : ∀ (x : List Bool) (eVal : Bool), x.length = raw →
      (∀ e ∈ entry, (C.wires x).getD e false = eVal) →
      ∀ w, w ∈ wires ∨ w ∈ entry →
        (C.wires x).getD w false =
          evalTree raw C region entry hback hreg (fun i => x.getD i false) eVal w := by
    intro x eVal hx heq w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rcases hw with hw | he
      · rcases hwire_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hne : w ∉ entry := fun he => (hentry_prop w he).1 hw
          rw [evalTree_src_eq raw C region entry hback hreg _ eVal (by omega) hne,
              wires_getD_input C x (by omega)]
        · set k := w - raw
          have hwk : w = raw + k := by omega
          rcases hgates k hk with ⟨_, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hu1lt : u₁ < w := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < w := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          have hgate := wires_getD_gate C x hkr (by rw [hx]; exact hback)
          rw [hx] at hgate
          rw [hwk, hgate,
              evalTree_gate_eq raw C region entry hback hreg _ eVal hk hinp, hinp]
          simp only [List.map_cons, List.map_nil, ih u₁ hu1lt hu1w, ih u₂ hu2lt hu2w]
      · rw [evalTree_entry_eq raw C region entry hback hreg _ eVal (hentry_not_reg w he) he]
        exact heq w he
  have hevalTree_mono : ∀ (s₁ s₂ : Nat → Bool) (e₁ e₂ : Bool),
      (∀ i, s₁ i = true → s₂ i = true) → (e₁ = true → e₂ = true) →
      ∀ w, w ∈ wires ∨ w ∈ entry →
        evalTree raw C region entry hback hreg s₁ e₁ w = true →
        evalTree raw C region entry hback hreg s₂ e₂ w = true := by
    intro s₁ s₂ e₁ e₂ hs he w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw htrue
      rcases hw with hw | hen
      · rcases hwire_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hne : w ∉ entry := fun h => (hentry_prop w h).1 hw
          rw [evalTree_src_eq raw C region entry hback hreg _ _ (by omega) hne] at htrue ⊢
          exact hs w htrue
        · set k := w - raw
          have hwk : w = raw + k := by omega
          rcases hgates k hk with ⟨hop, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hu1lt : u₁ < w := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < w := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          rw [hwk, evalTree_gate_eq raw C region entry hback hreg _ _ hk hinp] at htrue ⊢
          rcases hop with hop | hop
          · rw [hop] at htrue ⊢
            simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at htrue ⊢
            exact ⟨ih u₁ hu1lt hu1w htrue.1, ih u₂ hu2lt hu2w htrue.2⟩
          · rw [hop] at htrue ⊢
            simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at htrue ⊢
            rcases htrue with h1 | h2
            · left; exact ih u₁ hu1lt hu1w h1
            · right; exact ih u₂ hu2lt hu2w h2
      · rw [evalTree_entry_eq raw C region entry hback hreg _ _ (hentry_not_reg w hen) hen] at htrue ⊢
        exact he htrue
  have hevalTree_congr : ∀ (s₁ s₂ : Nat → Bool) (e₁ e₂ : Bool) (w : Nat),
      w ∈ wires ∨ w ∈ entry →
      (∀ i ∈ desc w, i < raw → i ∉ entry → s₁ i = s₂ i) →
      (∀ e ∈ entry, e ∈ desc w → e₁ = e₂) →
      evalTree raw C region entry hback hreg s₁ e₁ w =
        evalTree raw C region entry hback hreg s₂ e₂ w := by
    intro s₁ s₂ e₁ e₂ w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hs he
      rcases hw with hw | hen
      · rcases hwire_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hne : w ∉ entry := fun h => (hentry_prop w h).1 hw
          rw [evalTree_src_eq raw C region entry hback hreg _ _ (by omega) hne,
              evalTree_src_eq raw C region entry hback hreg _ _ (by omega) hne]
          exact hs w (mem_descOf_self _ _ _ _ _ w) hlt hne
        · set k := w - raw
          have hwk : w = raw + k := by omega
          rcases hgates k hk with ⟨_, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hu1lt : u₁ < w := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < w := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          have hd : desc w = insert w (desc u₁ ∪ desc u₂) := by
            rw [hwk]; exact descOf_gate_eq raw C region hback hreg hk hinp
          rw [hwk, evalTree_gate_eq raw C region entry hback hreg _ _ hk hinp,
              evalTree_gate_eq raw C region entry hback hreg _ _ hk hinp]
          have h1 := ih u₁ hu1lt hu1w
            (fun i hi hlt hne => hs i (by rw [hd]; simp [hi]) hlt hne)
            (fun e hee hi => he e hee (by rw [hd]; simp [hi]))
          have h2 := ih u₂ hu2lt hu2w
            (fun i hi hlt hne => hs i (by rw [hd]; simp [hi]) hlt hne)
            (fun e hee hi => he e hee (by rw [hd]; simp [hi]))
          rw [h1, h2]
      · rw [evalTree_entry_eq raw C region entry hback hreg _ _ (hentry_not_reg w hen) hen,
            evalTree_entry_eq raw C region entry hback hreg _ _ (hentry_not_reg w hen) hen]
        exact he w hen (mem_descOf_self _ _ _ _ _ w)
  have hrow_card : rowTypes.card ≤ 2 + entry.card := by
    let fR : Fin n → Bool × Bool := fun r =>
      (evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) false root,
       evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) true root)
    have hrow_eq_of_fR : ∀ r₁ ∈ R, ∀ r₂ ∈ R, fR r₁ = fR r₂ →
        (Finset.univ \ B).filter (fun outCol => G r₁ outCol = true) =
        (Finset.univ \ B).filter (fun outCol => G r₂ outCol = true) := by
      intro r₁ hr₁ r₂ hr₂ hfeq
      ext c
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hcB, hG⟩ <;> refine ⟨hcB, ?_⟩
      · have hagree_out : ∀ i < raw, i ∉ sources →
            (oneEach r₁ c).getD i false = (oneEach r₂ c).getD i false := by
          intro i hir hins
          by_cases hin : i < n
          · have h1 : i ≠ r₁.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₁, hr₁, h.symm⟩))
            have h2 : i ≠ r₂.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₂, hr₂, h.symm⟩))
            rw [oneEach_getD_row r₁ c hin, oneEach_getD_row r₂ c hin]; simp [h1, h2]
          · have hij : i - n < m := by omega
            have hi_eq : i = n + (i - n) := by omega
            rw [hi_eq, oneEach_getD_col r₁ c hij, oneEach_getD_col r₂ c hij]
        have hsrc_r : ∀ r : Fin n, ∀ i ∈ desc root, i < raw → i ∉ entry →
            (oneEach r c).getD i false = decide (i = r.val) := by
          intro r i hi hilt hine
          have hiw : i ∈ wires ∨ i ∈ entry := Finset.mem_union.mp (hdesc_sub_we root (Or.inl hroot) hi)
          have hisrc : i ∈ sources := by
            rcases hiw with hiw | hie
            · rcases hwire_split i hiw with ⟨_, hs⟩ | ⟨hge, _⟩
              · exact hs
              · omega
            · exact absurd hie hine
          simp only [sources, Finset.mem_union, Finset.mem_image] at hisrc
          rcases hisrc with ⟨r', _, rfl⟩ | ⟨c', hc', rfl⟩
          · exact oneEach_getD_row r c r'.isLt
          · rw [oneEach_getD_col r c c'.isLt]
            have hne1 : c'.val ≠ c.val := fun h => hcB (Fin.ext h ▸ hc')
            have hne2 : n + c'.val ≠ r.val := by omega
            simp [hne1, hne2]
        by_cases hempty : entry = ∅
        · have hv1 : (C.wires (oneEach r₁ c)).getD root false = (fR r₁).1 := by
            rw [hevalTree_eq_wires (oneEach r₁ c) false (oneEach_len r₁ c) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_r r₁) (by simp [hempty])
          have hv2 : (C.wires (oneEach r₂ c)).getD root false = (fR r₂).1 := by
            rw [hevalTree_eq_wires (oneEach r₂ c) false (oneEach_len r₂ c) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_r r₂) (by simp [hempty])
          have hbot := hbottleneck (oneEach r₁ c) (oneEach r₂ c) (oneEach_len r₁ c) (oneEach_len r₂ c)
            hagree_out (by rw [hv1, hv2, hfeq])
          rw [hrep r₁ c, hrep r₂ c] at hbot
          exact hbot.symm.trans hG
        · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨e0, he0⟩
          have he_uniq : ∀ e ∈ entry, e = e0 := fun e he =>
            Finset.card_le_one.mp hentry_card e he e0 he0
          let eVal := (C.wires (oneEach r₁ c)).getD e0 false
          have hev1 : ∀ e ∈ entry, (C.wires (oneEach r₁ c)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
          have hev2 : ∀ e ∈ entry, (C.wires (oneEach r₂ c)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
            exact (hout_indep_lt_root (oneEach r₁ c) (oneEach r₂ c) (oneEach_len r₁ c) (oneEach_len r₂ c)
              hagree_out e0 (hentry_prop e0 he0).2.1 (hentry_prop e0 he0).1).symm
          have hv1 := hevalTree_eq_wires (oneEach r₁ c) eVal (oneEach_len r₁ c) hev1 root (Or.inl hroot)
          have hv2 := hevalTree_eq_wires (oneEach r₂ c) eVal (oneEach_len r₂ c) hev2 root (Or.inl hroot)
          have hcon1 := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_r r₁) (fun _ _ _ => rfl)
          have hcon2 := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_r r₂) (fun _ _ _ => rfl)
          have hreq : (C.wires (oneEach r₁ c)).getD root false = (C.wires (oneEach r₂ c)).getD root false := by
            rw [hv1, hv2, hcon1, hcon2]
            cases eVal
            · exact congrArg Prod.fst hfeq
            · exact congrArg Prod.snd hfeq
          have hbot := hbottleneck (oneEach r₁ c) (oneEach r₂ c) (oneEach_len r₁ c) (oneEach_len r₂ c)
            hagree_out hreq
          rw [hrep r₁ c, hrep r₂ c] at hbot
          exact hbot.symm.trans hG
      · have hagree_out : ∀ i < raw, i ∉ sources →
            (oneEach r₂ c).getD i false = (oneEach r₁ c).getD i false := by
          intro i hir hins
          by_cases hin : i < n
          · have h1 : i ≠ r₁.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₁, hr₁, h.symm⟩))
            have h2 : i ≠ r₂.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r₂, hr₂, h.symm⟩))
            rw [oneEach_getD_row r₂ c hin, oneEach_getD_row r₁ c hin]; simp [h1, h2]
          · have hij : i - n < m := by omega
            have hi_eq : i = n + (i - n) := by omega
            rw [hi_eq, oneEach_getD_col r₂ c hij, oneEach_getD_col r₁ c hij]
        have hsrc_r : ∀ r : Fin n, ∀ i ∈ desc root, i < raw → i ∉ entry →
            (oneEach r c).getD i false = decide (i = r.val) := by
          intro r i hi hilt hine
          have hiw : i ∈ wires ∨ i ∈ entry := Finset.mem_union.mp (hdesc_sub_we root (Or.inl hroot) hi)
          have hisrc : i ∈ sources := by
            rcases hiw with hiw | hie
            · rcases hwire_split i hiw with ⟨_, hs⟩ | ⟨hge, _⟩
              · exact hs
              · omega
            · exact absurd hie hine
          simp only [sources, Finset.mem_union, Finset.mem_image] at hisrc
          rcases hisrc with ⟨r', _, rfl⟩ | ⟨c', hc', rfl⟩
          · exact oneEach_getD_row r c r'.isLt
          · rw [oneEach_getD_col r c c'.isLt]
            have hne1 : c'.val ≠ c.val := fun h => hcB (Fin.ext h ▸ hc')
            have hne2 : n + c'.val ≠ r.val := by omega
            simp [hne1, hne2]
        by_cases hempty : entry = ∅
        · have hv1 : (C.wires (oneEach r₁ c)).getD root false = (fR r₁).1 := by
            rw [hevalTree_eq_wires (oneEach r₁ c) false (oneEach_len r₁ c) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_r r₁) (by simp [hempty])
          have hv2 : (C.wires (oneEach r₂ c)).getD root false = (fR r₂).1 := by
            rw [hevalTree_eq_wires (oneEach r₂ c) false (oneEach_len r₂ c) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_r r₂) (by simp [hempty])
          have hbot := hbottleneck (oneEach r₂ c) (oneEach r₁ c) (oneEach_len r₂ c) (oneEach_len r₁ c)
            hagree_out (by rw [hv1, hv2, hfeq])
          rw [hrep r₂ c, hrep r₁ c] at hbot
          exact hbot.symm.trans hG
        · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨e0, he0⟩
          have he_uniq : ∀ e ∈ entry, e = e0 := fun e he =>
            Finset.card_le_one.mp hentry_card e he e0 he0
          let eVal := (C.wires (oneEach r₂ c)).getD e0 false
          have hev2 : ∀ e ∈ entry, (C.wires (oneEach r₂ c)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
          have hev1 : ∀ e ∈ entry, (C.wires (oneEach r₁ c)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
            exact (hout_indep_lt_root (oneEach r₂ c) (oneEach r₁ c) (oneEach_len r₂ c) (oneEach_len r₁ c)
              hagree_out e0 (hentry_prop e0 he0).2.1 (hentry_prop e0 he0).1).symm
          have hv1 := hevalTree_eq_wires (oneEach r₁ c) eVal (oneEach_len r₁ c) hev1 root (Or.inl hroot)
          have hv2 := hevalTree_eq_wires (oneEach r₂ c) eVal (oneEach_len r₂ c) hev2 root (Or.inl hroot)
          have hcon1 := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_r r₁) (fun _ _ _ => rfl)
          have hcon2 := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_r r₂) (fun _ _ _ => rfl)
          have hreq : (C.wires (oneEach r₂ c)).getD root false = (C.wires (oneEach r₁ c)).getD root false := by
            rw [hv1, hv2, hcon1, hcon2]
            cases eVal
            · exact (congrArg Prod.fst hfeq).symm
            · exact (congrArg Prod.snd hfeq).symm
          have hbot := hbottleneck (oneEach r₂ c) (oneEach r₁ c) (oneEach_len r₂ c) (oneEach_len r₁ c)
            hagree_out hreq
          rw [hrep r₂ c, hrep r₁ c] at hbot
          exact hbot.symm.trans hG
    have hcard_le : rowTypes.card ≤ (R.image fR).card := by
      have hsub : rowTypes.card ≤ (R.image fR).card := by
        classical
        have hsurj : ∀ t : Finset (Fin m), ∃ p : Bool × Bool, t ∈ rowTypes →
            p ∈ R.image fR ∧ ∃ r ∈ R, fR r = p ∧
            (Finset.univ \ B).filter (fun outCol => G r outCol = true) = t := by
          intro t
          by_cases ht : t ∈ rowTypes
          · rcases Finset.mem_image.mp ht with ⟨r, hr, rfl⟩
            exact ⟨fR r, fun _ => ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩, r, hr, rfl, rfl⟩⟩
          · exact ⟨(false, false), fun h => absurd h ht⟩
        choose g hg using hsurj
        have hinj : Set.InjOn g (rowTypes : Set (Finset (Fin m))) := by
          intro t₁ ht₁ t₂ ht₂ heq
          rcases (hg t₁ ht₁).2 with ⟨r₁, hr₁, hfr₁, hrt₁⟩
          rcases (hg t₂ ht₂).2 with ⟨r₂, hr₂, hfr₂, hrt₂⟩
          rw [← hrt₁, ← hrt₂]
          exact hrow_eq_of_fR r₁ hr₁ r₂ hr₂ (hfr₁.trans (heq.trans hfr₂.symm))
        exact Finset.card_le_card_of_injOn g (fun t ht => (hg t ht).1) hinj
      exact hsub
    have hfR_card : (R.image fR).card ≤ 2 + entry.card := by
      by_cases hempty : entry = ∅
      · have hsub : R.image fR ⊆ {(false, false), (true, true)} := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨r, _, rfl⟩
          have heq : (fR r).1 = (fR r).2 :=
            hevalTree_congr _ _ false true root (Or.inl hroot) (fun _ _ _ _ => rfl) (by simp [hempty])
          dsimp only [fR] at heq ⊢
          cases h1 : evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) false root <;>
          cases h2 : evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) true root <;>
          simp [h1, h2] at heq ⊢
        have hle := Finset.card_le_card hsub
        have h2 : ({(false, false), (true, true)} : Finset (Bool × Bool)).card ≤ 2 := by decide
        omega
      · have hpos : 1 ≤ entry.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hsub : R.image fR ⊆ {(false, false), (false, true), (true, true)} := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨r, _, rfl⟩
          have hmono := hevalTree_mono (fun i => decide (i = r.val)) (fun i => decide (i = r.val))
            false true (fun _ h => h) (fun _ => rfl) root (Or.inl hroot)
          dsimp only [fR]
          cases h1 : evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) false root
          · cases evalTree raw C region entry hback hreg (fun i => decide (i = r.val)) true root <;> simp
          · have h2 := hmono h1
            simp [h2]
        have hle := Finset.card_le_card hsub
        have h3 : ({(false, false), (false, true), (true, true)} : Finset (Bool × Bool)).card ≤ 3 := by decide
        omega
    omega
  have hcol_card : colTypes.card ≤ 2 + entry.card := by
    let fB : Fin m → Bool × Bool := fun c =>
      (evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) false root,
       evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) true root)
    have hcol_eq_of_fB : ∀ c₁ ∈ B, ∀ c₂ ∈ B, fB c₁ = fB c₂ →
        (Finset.univ \ R).filter (fun outRow => G outRow c₁ = true) =
        (Finset.univ \ R).filter (fun outRow => G outRow c₂ = true) := by
      intro c₁ hc₁ c₂ hc₂ hfeq
      ext r
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      have hsym : ∀ ca cb : Fin m, ca ∈ B → cb ∈ B → fB ca = fB cb → r ∉ R → G r ca = G r cb := by
        intro ca cb hca hcb hfab hrR
        have hagree_out : ∀ i < raw, i ∉ sources →
            (oneEach r ca).getD i false = (oneEach r cb).getD i false := by
          intro i hir hins
          by_cases hin : i < n
          · rw [oneEach_getD_row r ca hin, oneEach_getD_row r cb hin]
          · have hij : i - n < m := by omega
            have hi_eq : i = n + (i - n) := by omega
            have h1 : i - n ≠ ca.val := fun h => hins (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨ca, hca, by omega⟩))
            have h2 : i - n ≠ cb.val := fun h => hins (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨cb, hcb, by omega⟩))
            rw [hi_eq, oneEach_getD_col r ca hij, oneEach_getD_col r cb hij]
            simp [h1, h2]
        have hsrc_c : ∀ c : Fin m, ∀ i ∈ desc root, i < raw → i ∉ entry →
            (oneEach r c).getD i false = decide (i = n + c.val) := by
          intro c i hi hilt hine
          have hiw : i ∈ wires ∨ i ∈ entry := Finset.mem_union.mp (hdesc_sub_we root (Or.inl hroot) hi)
          have hisrc : i ∈ sources := by
            rcases hiw with hiw | hie
            · rcases hwire_split i hiw with ⟨_, hs⟩ | ⟨hge, _⟩
              · exact hs
              · omega
            · exact absurd hie hine
          simp only [sources, Finset.mem_union, Finset.mem_image] at hisrc
          rcases hisrc with ⟨r', hr', rfl⟩ | ⟨c', _, rfl⟩
          · rw [oneEach_getD_row r c r'.isLt]
            have hne1 : r'.val ≠ r.val := fun h => hrR (Fin.ext h ▸ hr')
            have hne2 : r'.val ≠ n + c.val := by omega
            simp [hne1, hne2]
          · rw [oneEach_getD_col r c c'.isLt]
            simp
        by_cases hempty : entry = ∅
        · have hva : (C.wires (oneEach r ca)).getD root false = (fB ca).1 := by
            rw [hevalTree_eq_wires (oneEach r ca) false (oneEach_len r ca) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_c ca) (by simp [hempty])
          have hvb : (C.wires (oneEach r cb)).getD root false = (fB cb).1 := by
            rw [hevalTree_eq_wires (oneEach r cb) false (oneEach_len r cb) (by simp [hempty]) root (Or.inl hroot)]
            exact hevalTree_congr _ _ false false root (Or.inl hroot) (hsrc_c cb) (by simp [hempty])
          have hbot := hbottleneck (oneEach r ca) (oneEach r cb) (oneEach_len r ca) (oneEach_len r cb)
            hagree_out (by rw [hva, hvb, hfab])
          rw [hrep r ca, hrep r cb] at hbot
          exact hbot
        · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨e0, he0⟩
          have he_uniq : ∀ e ∈ entry, e = e0 := fun e he =>
            Finset.card_le_one.mp hentry_card e he e0 he0
          let eVal := (C.wires (oneEach r ca)).getD e0 false
          have heva : ∀ e ∈ entry, (C.wires (oneEach r ca)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
          have hevb : ∀ e ∈ entry, (C.wires (oneEach r cb)).getD e false = eVal := by
            intro e he; rw [he_uniq e he]
            exact (hout_indep_lt_root (oneEach r ca) (oneEach r cb) (oneEach_len r ca) (oneEach_len r cb)
              hagree_out e0 (hentry_prop e0 he0).2.1 (hentry_prop e0 he0).1).symm
          have hva := hevalTree_eq_wires (oneEach r ca) eVal (oneEach_len r ca) heva root (Or.inl hroot)
          have hvb := hevalTree_eq_wires (oneEach r cb) eVal (oneEach_len r cb) hevb root (Or.inl hroot)
          have hcona := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_c ca) (fun _ _ _ => rfl)
          have hconb := hevalTree_congr _ _ eVal eVal root (Or.inl hroot) (hsrc_c cb) (fun _ _ _ => rfl)
          have hreq : (C.wires (oneEach r ca)).getD root false = (C.wires (oneEach r cb)).getD root false := by
            rw [hva, hvb, hcona, hconb]
            cases eVal
            · exact congrArg Prod.fst hfab
            · exact congrArg Prod.snd hfab
          have hbot := hbottleneck (oneEach r ca) (oneEach r cb) (oneEach_len r ca) (oneEach_len r cb)
            hagree_out hreq
          rw [hrep r ca, hrep r cb] at hbot
          exact hbot
      constructor <;> rintro ⟨hrR, hG⟩ <;> refine ⟨hrR, ?_⟩
      · rw [← hsym c₁ c₂ hc₁ hc₂ hfeq hrR]; exact hG
      · rw [hsym c₁ c₂ hc₁ hc₂ hfeq hrR]; exact hG
    have hcard_le : colTypes.card ≤ (B.image fB).card := by
      classical
      have hsurj : ∀ t : Finset (Fin n), ∃ p : Bool × Bool, t ∈ colTypes →
          p ∈ B.image fB ∧ ∃ c ∈ B, fB c = p ∧
          (Finset.univ \ R).filter (fun outRow => G outRow c = true) = t := by
        intro t
        by_cases ht : t ∈ colTypes
        · rcases Finset.mem_image.mp ht with ⟨c, hc, rfl⟩
          exact ⟨fB c, fun _ => ⟨Finset.mem_image.mpr ⟨c, hc, rfl⟩, c, hc, rfl, rfl⟩⟩
        · exact ⟨(false, false), fun h => absurd h ht⟩
      choose g hg using hsurj
      have hinj : Set.InjOn g (colTypes : Set (Finset (Fin n))) := by
        intro t₁ ht₁ t₂ ht₂ heq
        rcases (hg t₁ ht₁).2 with ⟨c₁, hc₁, hfc₁, hct₁⟩
        rcases (hg t₂ ht₂).2 with ⟨c₂, hc₂, hfc₂, hct₂⟩
        rw [← hct₁, ← hct₂]
        exact hcol_eq_of_fB c₁ hc₁ c₂ hc₂ (hfc₁.trans (heq.trans hfc₂.symm))
      exact Finset.card_le_card_of_injOn g (fun t ht => (hg t ht).1) hinj
    have hfB_card : (B.image fB).card ≤ 2 + entry.card := by
      by_cases hempty : entry = ∅
      · have hsub : B.image fB ⊆ {(false, false), (true, true)} := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨c, _, rfl⟩
          have heq : (fB c).1 = (fB c).2 :=
            hevalTree_congr _ _ false true root (Or.inl hroot) (fun _ _ _ _ => rfl) (by simp [hempty])
          dsimp only [fB] at heq ⊢
          cases h1 : evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) false root <;>
          cases h2 : evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) true root <;>
          simp [h1, h2] at heq ⊢
        have hle := Finset.card_le_card hsub
        have h2 : ({(false, false), (true, true)} : Finset (Bool × Bool)).card ≤ 2 := by decide
        omega
      · have hpos : 1 ≤ entry.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hsub : B.image fB ⊆ {(false, false), (false, true), (true, true)} := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨c, _, rfl⟩
          have hmono := hevalTree_mono (fun i => decide (i = n + c.val)) (fun i => decide (i = n + c.val))
            false true (fun _ h => h) (fun _ => rfl) root (Or.inl hroot)
          dsimp only [fB]
          cases h1 : evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) false root
          · cases evalTree raw C region entry hback hreg (fun i => decide (i = n + c.val)) true root <;> simp
          · have h2 := hmono h1
            simp [h2]
        have hle := Finset.card_le_card hsub
        have h3 : ({(false, false), (false, true), (true, true)} : Finset (Bool × Bool)).card ≤ 3 := by decide
        omega
    omega
  refine ⟨hrow_card, hcol_card, ?_⟩
  let allZero : List Bool := List.replicate raw false
  have hallZero_len : allZero.length = raw := List.length_replicate
  let e0 : Bool :=
    if h : entry.Nonempty then (C.wires allZero).getD (entry.min' h) false else false
  let V : Nat → Fin n → Fin m → Bool := fun w a x =>
    evalTree raw C region entry hback hreg (fun i => decide (i = a.val ∨ i = n + x.val)) e0 w
  let val0 : Nat → Bool := fun w =>
    evalTree raw C region entry hback hreg (fun _ => false) e0 w
  let valR : Nat → Fin n → Bool := fun w a =>
    evalTree raw C region entry hback hreg (fun i => decide (i = a.val)) e0 w
  let valB : Nat → Fin m → Bool := fun w x =>
    evalTree raw C region entry hback hreg (fun i => decide (i = n + x.val)) e0 w
  have htree_rect : ∀ w, w ∈ wires ∨ w ∈ entry →
      ∀ (a b : Fin n) (x y : Fin m),
        valR w a = false → valR w b = false → valB w x = false → valB w y = false →
        V w a x = true → V w b x = true → V w b y = true → V w a y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw a b x y hra hrb hbx hby hax hbx' hby'
      rcases hw with hw | hen
      · rcases hwire_split w hw with ⟨hlt, _⟩ | ⟨hge, hk⟩
        · have hne : w ∉ entry := fun h => (hentry_prop w h).1 hw
          dsimp only [V, valR, valB] at hra hbx hax
          rw [evalTree_src_eq raw C region entry hback hreg _ e0 (by omega) hne] at hra hbx hax
          simp at hra hbx hax
          rcases hax with h1 | h2
          · exact absurd h1 hra
          · exact absurd h2 hbx
        · set k := w - raw
          have hwk : w = raw + k := by omega
          rcases hgates k hk with ⟨hop, hlen2, hinp_w⟩
          rcases List.length_eq_two.mp hlen2 with ⟨u₁, u₂, hinp⟩
          have hkr : k < C.size := Finset.mem_range.mp (hreg hk)
          have hu1w := hinp_w u₁ (by rw [hinp]; simp)
          have hu2w := hinp_w u₂ (by rw [hinp]; simp)
          have hu1lt : u₁ < w := by have hb := hback k hkr u₁ (by rw [hinp]; simp); omega
          have hu2lt : u₂ < w := by have hb := hback k hkr u₂ (by rw [hinp]; simp); omega
          have hdisj := hchildren_disj k hk u₁ u₂ hinp
          have hnot_in_R : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ (r : Fin n) (c : Fin m),
              r.val ∉ desc u → V u r c = valB u c := by
            intro u hu r c hrnot
            apply hevalTree_congr _ _ e0 e0 u hu _ (fun _ _ _ => rfl)
            intro i hi _ _
            have hne : i ≠ r.val := fun h => hrnot (h ▸ hi)
            simp [hne]
          have hnot_in_B : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ (r : Fin n) (c : Fin m),
              n + c.val ∉ desc u → V u r c = valR u r := by
            intro u hu r c hcnot
            apply hevalTree_congr _ _ e0 e0 u hu _ (fun _ _ _ => rfl)
            intro i hi _ _
            have hne : i ≠ n + c.val := fun h => hcnot (h ▸ hi)
            simp [hne]
          have hnot_in_0 : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ (r : Fin n),
              r.val ∉ desc u → valR u r = val0 u := by
            intro u hu r hrnot
            apply hevalTree_congr _ _ e0 e0 u hu _ (fun _ _ _ => rfl)
            intro i hi _ _
            have hne : i ≠ r.val := fun h => hrnot (h ▸ hi)
            simp [hne]
          have hnot_in_both : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ (r : Fin n) (c : Fin m),
              r.val ∉ desc u → n + c.val ∉ desc u → V u r c = val0 u := by
            intro u hu r c hrnot hcnot
            rw [hnot_in_B u hu r c hcnot, hnot_in_0 u hu r hrnot]
          have hmono_R : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ r c, valR u r = true → V u r c = true :=
            fun u hu r c hr => hevalTree_mono _ _ e0 e0 (fun i hi => by simp at hi ⊢; left; exact hi) (fun h => h) u hu hr
          have hmono_B : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ r c, valB u c = true → V u r c = true :=
            fun u hu r c hc => hevalTree_mono _ _ e0 e0 (fun i hi => by simp at hi ⊢; right; exact hi) (fun h => h) u hu hc
          have hmono_0R : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ r, val0 u = true → valR u r = true :=
            fun u hu r h0 => hevalTree_mono _ _ e0 e0 (fun _ h => by cases h) (fun h => h) u hu h0
          have hmono_0B : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ c, val0 u = true → valB u c = true :=
            fun u hu c h0 => hevalTree_mono _ _ e0 e0 (fun _ h => by cases h) (fun h => h) u hu h0
          have hmono_0V : ∀ u, u ∈ wires ∨ u ∈ entry → ∀ r c, val0 u = true → V u r c = true :=
            fun u hu r c h0 => hevalTree_mono _ _ e0 e0 (fun _ h => by cases h) (fun h => h) u hu h0
          rcases hop with hop | hop
          · have hstep_and : ∀ (sVal : Nat → Bool),
                evalTree raw C region entry hback hreg sVal e0 w =
                  (evalTree raw C region entry hback hreg sVal e0 u₁ &&
                   evalTree raw C region entry hback hreg sVal e0 u₂) := by
              intro sVal
              rw [hwk, evalTree_gate_eq raw C region entry hback hreg sVal e0 hk hinp, hop]
              simp [GateOp.eval]
            have hax12 : V u₁ a x = true ∧ V u₂ a x = true := by
              have h := hstep_and (fun i => decide (i = a.val ∨ i = n + x.val))
              change V w a x = (V u₁ a x && V u₂ a x) at h
              rw [h] at hax; exact Bool.and_eq_true_iff.mp hax
            have hbx12 : V u₁ b x = true ∧ V u₂ b x = true := by
              have h := hstep_and (fun i => decide (i = b.val ∨ i = n + x.val))
              change V w b x = (V u₁ b x && V u₂ b x) at h
              rw [h] at hbx'; exact Bool.and_eq_true_iff.mp hbx'
            have hby12 : V u₁ b y = true ∧ V u₂ b y = true := by
              have h := hstep_and (fun i => decide (i = b.val ∨ i = n + y.val))
              change V w b y = (V u₁ b y && V u₂ b y) at h
              rw [h] at hby'; exact Bool.and_eq_true_iff.mp hby'
            have hgoal : V u₁ a y = true → V u₂ a y = true → V w a y = true := by
              intro h1 h2
              have h := hstep_and (fun i => decide (i = a.val ∨ i = n + y.val))
              change V w a y = (V u₁ a y && V u₂ a y) at h
              rw [h, h1, h2]; rfl
            cases hv01 : val0 u₁
            · cases hv02 : val0 u₂
              · have h1_has : a.val ∈ desc u₁ ∨ n + x.val ∈ desc u₁ := by
                  by_contra h
                  have := hnot_in_both u₁ hu1w a x (fun ha => h (Or.inl ha)) (fun hx => h (Or.inr hx))
                  rw [hax12.1, hv01] at this; cases this
                have h2_has : a.val ∈ desc u₂ ∨ n + x.val ∈ desc u₂ := by
                  by_contra h
                  have := hnot_in_both u₂ hu2w a x (fun ha => h (Or.inl ha)) (fun hx => h (Or.inr hx))
                  rw [hax12.2, hv02] at this; cases this
                rcases h1_has with ha1 | hx1
                · have ha2 : a.val ∉ desc u₂ := Finset.disjoint_left.mp hdisj ha1
                  have hx2 : n + x.val ∈ desc u₂ := by rcases h2_has with h | h; exact absurd h ha2; exact h
                  have hx1n : n + x.val ∉ desc u₁ := Finset.disjoint_right.mp hdisj hx2
                  have hRa1 : valR u₁ a = true := by rw [← hnot_in_B u₁ hu1w a x hx1n]; exact hax12.1
                  have hRb1 : valR u₁ b = true := by rw [← hnot_in_B u₁ hu1w b x hx1n]; exact hbx12.1
                  have hb1 : b.val ∈ desc u₁ := by
                    by_contra hbn
                    have := hnot_in_0 u₁ hu1w b hbn
                    rw [hRb1, hv01] at this; cases this
                  have hb2 : b.val ∉ desc u₂ := Finset.disjoint_left.mp hdisj hb1
                  have hBy2 : valB u₂ y = true := by rw [← hnot_in_R u₂ hu2w b y hb2]; exact hby12.2
                  exact hgoal (hmono_R u₁ hu1w a y hRa1) (hmono_B u₂ hu2w a y hBy2)
                · have hx2 : n + x.val ∉ desc u₂ := Finset.disjoint_left.mp hdisj hx1
                  have ha2 : a.val ∈ desc u₂ := by rcases h2_has with h | h; exact h; exact absurd h hx2
                  have hRa2 : valR u₂ a = true := by rw [← hnot_in_B u₂ hu2w a x hx2]; exact hax12.2
                  have hRb2 : valR u₂ b = true := by rw [← hnot_in_B u₂ hu2w b x hx2]; exact hbx12.2
                  have hb2 : b.val ∈ desc u₂ := by
                    by_contra hbn
                    have := hnot_in_0 u₂ hu2w b hbn
                    rw [hRb2, hv02] at this; cases this
                  have hb1 : b.val ∉ desc u₁ := Finset.disjoint_right.mp hdisj hb2
                  have hBy1 : valB u₁ y = true := by rw [← hnot_in_R u₁ hu1w b y hb1]; exact hby12.1
                  exact hgoal (hmono_B u₁ hu1w a y hBy1) (hmono_R u₂ hu2w a y hRa2)
              · have hR1 : ∀ r, valR w r = false → valR u₁ r = false := by
                  intro r hr
                  have h := hstep_and (fun i => decide (i = r.val))
                  change valR w r = (valR u₁ r && valR u₂ r) at h
                  rw [hmono_0R u₂ hu2w r hv02, Bool.and_true] at h
                  rw [← h]; exact hr
                have hB1 : ∀ c, valB w c = false → valB u₁ c = false := by
                  intro c hc
                  have h := hstep_and (fun i => decide (i = n + c.val))
                  change valB w c = (valB u₁ c && valB u₂ c) at h
                  rw [hmono_0B u₂ hu2w c hv02, Bool.and_true] at h
                  rw [← h]; exact hc
                exact hgoal
                  (ih u₁ hu1lt hu1w a b x y (hR1 a hra) (hR1 b hrb) (hB1 x hbx) (hB1 y hby) hax12.1 hbx12.1 hby12.1)
                  (hmono_0V u₂ hu2w a y hv02)
            · have hR2 : ∀ r, valR w r = false → valR u₂ r = false := by
                intro r hr
                have h := hstep_and (fun i => decide (i = r.val))
                change valR w r = (valR u₁ r && valR u₂ r) at h
                rw [hmono_0R u₁ hu1w r hv01, Bool.true_and] at h
                rw [← h]; exact hr
              have hB2 : ∀ c, valB w c = false → valB u₂ c = false := by
                intro c hc
                have h := hstep_and (fun i => decide (i = n + c.val))
                change valB w c = (valB u₁ c && valB u₂ c) at h
                rw [hmono_0B u₁ hu1w c hv01, Bool.true_and] at h
                rw [← h]; exact hc
              exact hgoal
                (hmono_0V u₁ hu1w a y hv01)
                (ih u₂ hu2lt hu2w a b x y (hR2 a hra) (hR2 b hrb) (hB2 x hbx) (hB2 y hby) hax12.2 hbx12.2 hby12.2)
          · have hstep_or : ∀ (sVal : Nat → Bool),
                evalTree raw C region entry hback hreg sVal e0 w =
                  (evalTree raw C region entry hback hreg sVal e0 u₁ ||
                   evalTree raw C region entry hback hreg sVal e0 u₂) := by
              intro sVal
              rw [hwk, evalTree_gate_eq raw C region entry hback hreg sVal e0 hk hinp, hop]
              simp [GateOp.eval]
            have hR12 : ∀ r, valR w r = false → valR u₁ r = false ∧ valR u₂ r = false := by
              intro r hr
              have h := hstep_or (fun i => decide (i = r.val))
              change valR w r = (valR u₁ r || valR u₂ r) at h
              rw [h] at hr; exact Bool.or_eq_false_iff.mp hr
            have hB12 : ∀ c, valB w c = false → valB u₁ c = false ∧ valB u₂ c = false := by
              intro c hc
              have h := hstep_or (fun i => decide (i = n + c.val))
              change valB w c = (valB u₁ c || valB u₂ c) at h
              rw [h] at hc; exact Bool.or_eq_false_iff.mp hc
            have hax12 : V u₁ a x = true ∨ V u₂ a x = true := by
              have h := hstep_or (fun i => decide (i = a.val ∨ i = n + x.val))
              change V w a x = (V u₁ a x || V u₂ a x) at h
              rw [h] at hax; exact Bool.or_eq_true_iff.mp hax
            have hbx12 : V u₁ b x = true ∨ V u₂ b x = true := by
              have h := hstep_or (fun i => decide (i = b.val ∨ i = n + x.val))
              change V w b x = (V u₁ b x || V u₂ b x) at h
              rw [h] at hbx'; exact Bool.or_eq_true_iff.mp hbx'
            have hby12 : V u₁ b y = true ∨ V u₂ b y = true := by
              have h := hstep_or (fun i => decide (i = b.val ∨ i = n + y.val))
              change V w b y = (V u₁ b y || V u₂ b y) at h
              rw [h] at hby'; exact Bool.or_eq_true_iff.mp hby'
            have hgoal1 : V u₁ a y = true → V w a y = true := by
              intro h1
              have h := hstep_or (fun i => decide (i = a.val ∨ i = n + y.val))
              change V w a y = (V u₁ a y || V u₂ a y) at h
              rw [h, h1]; rfl
            have hgoal2 : V u₂ a y = true → V w a y = true := by
              intro h2
              have h := hstep_or (fun i => decide (i = a.val ∨ i = n + y.val))
              change V w a y = (V u₁ a y || V u₂ a y) at h
              rw [h, h2]; simp
            rcases hbx12 with hbx1 | hbx2
            · have hb1 : b.val ∈ desc u₁ := by
                by_contra hbn
                have := hnot_in_R u₁ hu1w b x hbn
                rw [hbx1, (hB12 x hbx).1] at this; cases this
              have hx1 : n + x.val ∈ desc u₁ := by
                by_contra hxn
                have := hnot_in_B u₁ hu1w b x hxn
                rw [hbx1, (hR12 b hrb).1] at this; cases this
              have hb2 : b.val ∉ desc u₂ := Finset.disjoint_left.mp hdisj hb1
              have hx2 : n + x.val ∉ desc u₂ := Finset.disjoint_left.mp hdisj hx1
              have hax1 : V u₁ a x = true := by
                rcases hax12 with h | h
                · exact h
                · have := hnot_in_B u₂ hu2w a x hx2
                  rw [h, (hR12 a hra).2] at this; cases this
              have hby1 : V u₁ b y = true := by
                rcases hby12 with h | h
                · exact h
                · have := hnot_in_R u₂ hu2w b y hb2
                  rw [h, (hB12 y hby).2] at this; cases this
              exact hgoal1 (ih u₁ hu1lt hu1w a b x y
                (hR12 a hra).1 (hR12 b hrb).1 (hB12 x hbx).1 (hB12 y hby).1 hax1 hbx1 hby1)
            · have hb2 : b.val ∈ desc u₂ := by
                by_contra hbn
                have := hnot_in_R u₂ hu2w b x hbn
                rw [hbx2, (hB12 x hbx).2] at this; cases this
              have hx2 : n + x.val ∈ desc u₂ := by
                by_contra hxn
                have := hnot_in_B u₂ hu2w b x hxn
                rw [hbx2, (hR12 b hrb).2] at this; cases this
              have hb1 : b.val ∉ desc u₁ := Finset.disjoint_right.mp hdisj hb2
              have hx1 : n + x.val ∉ desc u₁ := Finset.disjoint_right.mp hdisj hx2
              have hax2 : V u₂ a x = true := by
                rcases hax12 with h | h
                · have := hnot_in_B u₁ hu1w a x hx1
                  rw [h, (hR12 a hra).1] at this; cases this
                · exact h
              have hby2 : V u₂ b y = true := by
                rcases hby12 with h | h
                · have := hnot_in_R u₁ hu1w b y hb1
                  rw [h, (hB12 y hby).1] at this; cases this
                · exact h
              exact hgoal2 (ih u₂ hu2lt hu2w a b x y
                (hR12 a hra).2 (hR12 b hrb).2 (hB12 x hbx).2 (hB12 y hby).2 hax2 hbx2 hby2)
      · dsimp only [V, valR] at hra hax
        rw [evalTree_entry_eq raw C region entry hback hreg _ e0 (hentry_not_reg w hen) hen] at hra hax
        rw [hra] at hax; cases hax
  have hroot_RB : ∀ a ∈ R, ∀ x ∈ B, (C.wires (oneEach a x)).getD root false = V root a x := by
    intro a ha x hx
    have hagree0 : ∀ i < raw, i ∉ sources → (oneEach a x).getD i false = allZero.getD i false := by
      intro i hir hins
      have hz : allZero.getD i false = false := by
        simp [allZero, List.getD_eq_getElem?_getD, hir]
      rw [hz]
      by_cases hin : i < n
      · have hne : i ≠ a.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, h.symm⟩))
        rw [oneEach_getD_row a x hin]; simp [hne]
      · have hij : i - n < m := by omega
        have hi_eq : i = n + (i - n) := by omega
        have hne : i - n ≠ x.val := fun h => hins (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, by omega⟩))
        rw [hi_eq, oneEach_getD_col a x hij]; simp [hne]
    have hev : ∀ e ∈ entry, (C.wires (oneEach a x)).getD e false = e0 := by
      intro e he
      have hne : entry.Nonempty := ⟨e, he⟩
      have he_eq : e = entry.min' hne := Finset.card_le_one.mp hentry_card e he (entry.min' hne) (Finset.min'_mem entry hne)
      rw [he_eq]
      dsimp only [e0]
      rw [dif_pos hne]
      exact hout_indep_lt_root (oneEach a x) allZero (oneEach_len a x) hallZero_len hagree0
        (entry.min' hne) (hentry_prop _ (Finset.min'_mem entry hne)).2.1
        (hentry_prop _ (Finset.min'_mem entry hne)).1
    rw [hevalTree_eq_wires (oneEach a x) e0 (oneEach_len a x) hev root (Or.inl hroot)]
    apply hevalTree_congr _ _ e0 e0 root (Or.inl hroot) _ (fun _ _ _ => rfl)
    intro i _ hilt _
    by_cases hin : i < n
    · rw [oneEach_getD_row a x hin]
      have hne : i ≠ n + x.val := by omega
      simp [hne]
    · have hij : i - n < m := by omega
      have hi_eq : i = n + (i - n) := by omega
      rw [hi_eq, oneEach_getD_col a x hij]
      have hne : n + (i - n) ≠ a.val := by omega
      simp [hne]
  have hG_of_V : ∀ a₁ ∈ R, ∀ x₁ ∈ B, ∀ a₂ ∈ R, ∀ x₂ ∈ B,
      V root a₁ x₁ = V root a₂ x₂ → G a₁ x₁ = G a₂ x₂ := by
    intro a₁ ha₁ x₁ hx₁ a₂ ha₂ x₂ hx₂ hveq
    rw [← hrep a₁ x₁, ← hrep a₂ x₂]
    apply hbottleneck (oneEach a₁ x₁) (oneEach a₂ x₂) (oneEach_len a₁ x₁) (oneEach_len a₂ x₂)
    · intro i hir hins
      by_cases hin : i < n
      · have h1 : i ≠ a₁.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a₁, ha₁, h.symm⟩))
        have h2 : i ≠ a₂.val := fun h => hins (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a₂, ha₂, h.symm⟩))
        rw [oneEach_getD_row a₁ x₁ hin, oneEach_getD_row a₂ x₂ hin]; simp [h1, h2]
      · have hij : i - n < m := by omega
        have hi_eq : i = n + (i - n) := by omega
        have h1 : i - n ≠ x₁.val := fun h => hins (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x₁, hx₁, by omega⟩))
        have h2 : i - n ≠ x₂.val := fun h => hins (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x₂, hx₂, by omega⟩))
        rw [hi_eq, oneEach_getD_col a₁ x₁ hij, oneEach_getD_col a₂ x₂ hij]; simp [h1, h2]
    · rw [hroot_RB a₁ ha₁ x₁ hx₁, hroot_RB a₂ ha₂ x₂ hx₂, hveq]
  by_cases hex1 : ∃ a0 ∈ R, ∃ x0 ∈ B, V root a0 x0 = true
  · rcases hex1 with ⟨a0, ha0, x0, hx0, hv0⟩
    refine ⟨G a0 x0, ?_⟩
    intro a ha b hb x hx y hy hax hbx hby
    rcases Finset.mem_filter.mp ha with ⟨haR, x_wa, hxwaB, hG_awa⟩
    rcases Finset.mem_filter.mp hb with ⟨hbR, x_wb, hxwbB, hG_bwb⟩
    rcases Finset.mem_filter.mp hx with ⟨hxB, a_wx, hawxR, hG_awx⟩
    rcases Finset.mem_filter.mp hy with ⟨hyB, a_wy, hawyR, hG_awy⟩
    have hV_false_of_ne : ∀ r ∈ R, ∀ c ∈ B, G r c ≠ G a0 x0 → V root r c = false := by
      intro r hr c hc hne
      cases hv : V root r c
      · rfl
      · exact absurd (hG_of_V r hr c hc a0 ha0 x0 hx0 (hv.trans hv0.symm)) hne
    have hV_true_of_eq : ∀ r ∈ R, ∀ c ∈ B, G r c = G a0 x0 → V root r c = true := by
      intro r hr c hc heq
      cases hv : V root r c
      · exfalso
        have hne_ax : G a x_wa ≠ G a0 x0 := hG_awa
        have hv_ax : V root a x_wa = false := hV_false_of_ne a haR x_wa hxwaB hne_ax
        have heq2 := hG_of_V r hr c hc a haR x_wa hxwaB (hv.trans hv_ax.symm)
        exact hne_ax (heq2.symm.trans heq)
      · rfl
    have hRa : valR root a = false := by
      cases hr : valR root a
      · rfl
      · have h1 : V root a x_wa = true := hevalTree_mono (fun i => decide (i = a.val))
          (fun i => decide (i = a.val ∨ i = n + x_wa.val)) e0 e0
          (fun i hi => by simp at hi ⊢; left; exact hi) (fun h => h) root (Or.inl hroot) hr
        have h2 := hV_false_of_ne a haR x_wa hxwaB hG_awa
        rw [h2] at h1; cases h1
    have hRb : valR root b = false := by
      cases hr : valR root b
      · rfl
      · have h1 : V root b x_wb = true := hevalTree_mono (fun i => decide (i = b.val))
          (fun i => decide (i = b.val ∨ i = n + x_wb.val)) e0 e0
          (fun i hi => by simp at hi ⊢; left; exact hi) (fun h => h) root (Or.inl hroot) hr
        have h2 := hV_false_of_ne b hbR x_wb hxwbB hG_bwb
        rw [h2] at h1; cases h1
    have hBx : valB root x = false := by
      cases hc : valB root x
      · rfl
      · have h1 : V root a_wx x = true := hevalTree_mono (fun i => decide (i = n + x.val))
          (fun i => decide (i = a_wx.val ∨ i = n + x.val)) e0 e0
          (fun i hi => by simp at hi ⊢; right; exact hi) (fun h => h) root (Or.inl hroot) hc
        have h2 := hV_false_of_ne a_wx hawxR x hxB hG_awx
        rw [h2] at h1; cases h1
    have hBy : valB root y = false := by
      cases hc : valB root y
      · rfl
      · have h1 : V root a_wy y = true := hevalTree_mono (fun i => decide (i = n + y.val))
          (fun i => decide (i = a_wy.val ∨ i = n + y.val)) e0 e0
          (fun i hi => by simp at hi ⊢; right; exact hi) (fun h => h) root (Or.inl hroot) hc
        have h2 := hV_false_of_ne a_wy hawyR y hyB hG_awy
        rw [h2] at h1; cases h1
    have hvay := htree_rect root (Or.inl hroot) a b x y hRa hRb hBx hBy
      (hV_true_of_eq a haR x hxB hax) (hV_true_of_eq b hbR x hxB hbx) (hV_true_of_eq b hbR y hyB hby)
    exact hG_of_V a haR y hyB a0 ha0 x0 hx0 (hvay.trans hv0.symm)
  · have hall_false : ∀ a ∈ R, ∀ x ∈ B, V root a x = false := by
      intro a ha x hx
      cases hv : V root a x
      · rfl
      · exact absurd ⟨a, ha, x, hx, hv⟩ hex1
    by_cases hex0 : ∃ a0 ∈ R, ∃ x0 ∈ B, True
    · rcases hex0 with ⟨a0, ha0, x0, hx0, _⟩
      refine ⟨G a0 x0, ?_⟩
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haR, x_wa, hxwaB, hG_awa⟩
      exact absurd (hG_of_V a haR x_wa hxwaB a0 ha0 x0 hx0
        ((hall_false a haR x_wa hxwaB).trans (hall_false a0 ha0 x0 hx0).symm)) hG_awa
    · refine ⟨false, ?_⟩
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haR, x_wa, hxwaB, _⟩
      exact absurd ⟨a, haR, x_wa, hxwaB, trivial⟩ hex0

end PEqualNP.Outside.L_meta_25578_aux

theorem PEqualNP.Outside.L_meta_25578 :
∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
  let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
  let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ witnessCol ∈ B, G keptRow witnessCol ≠ rowPol)
  let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ witnessRow ∈ R, G witnessRow keptCol ≠ colPol)
  let rectangles := ∃ mark : Bool,
    ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark, ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
      G a x = mark → G b x = mark → G b y = mark → G a y = mark
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  rowTypes.card ≤ 2 + entry.card ∧ colTypes.card ≤ 2 + entry.card ∧ rectangles :=
  PEqualNP.Outside.L_meta_25578_aux.solve_25578
