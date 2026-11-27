import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25644_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

abbrev gatesOf (C : Circuit) : Finset ℕ := Finset.range C.size
abbrev readsOf (C : Circuit) (w : ℕ) : ℕ := readsIn C (Finset.range C.size) w
def isBinOp (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or

theorem readsIn_empty (C : Circuit) (w : ℕ) : readsIn C ∅ w = 0 := by
  simp [readsIn]

theorem readsIn_insert (C : Circuit) (G : Finset ℕ) (j w : ℕ) (hj : j ∉ G) :
    readsIn C (insert j G) w = (gateAt C j).inputs.count w + readsIn C G w := by
  unfold readsIn
  exact Finset.sum_insert hj

theorem readsIn_union (C : Circuit) (G1 G2 : Finset ℕ) (w : ℕ) (h : Disjoint G1 G2) :
    readsIn C (G1 ∪ G2) w = readsIn C G1 w + readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_union h

theorem readsIn_mono (C : Circuit) {G1 G2 : Finset ℕ} (h : G1 ⊆ G2) (w : ℕ) :
    readsIn C G1 w ≤ readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset h

theorem readsIn_eq_zero_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    readsIn C G w = 0 ↔ ∀ j ∈ G, w ∉ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj hw
    have hp : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hz := h j hj
    omega
  · intro h j hj
    exact List.count_eq_zero.mpr (h j hj)

theorem readsIn_pos_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    0 < readsIn C G w ↔ ∃ j ∈ G, w ∈ (gateAt C j).inputs := by
  constructor
  · intro hp
    by_contra h
    have hz : readsIn C G w = 0 := (readsIn_eq_zero_iff C G w).2 (fun j hj hw => h ⟨j, hj, hw⟩)
    omega
  · rintro ⟨j, hj, hw⟩
    have hc : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn
    omega

theorem readsIn_ge_of_mem (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ G) (hw : w ∈ (gateAt C j).inputs) : 1 ≤ readsIn C G w :=
  (readsIn_pos_iff C G w).2 ⟨j, hj, hw⟩

theorem readsIn_eq_one_unique (C : Circuit) (G : Finset ℕ) (w : ℕ) (h : readsIn C G w = 1) :
    ∃ j ∈ G, w ∈ (gateAt C j).inputs ∧ (gateAt C j).inputs.count w = 1 ∧
      ∀ j' ∈ G, w ∈ (gateAt C j').inputs → j' = j := by
  obtain ⟨j, hj, hw⟩ := (readsIn_pos_iff C G w).1 (by omega)
  have hcpos : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have hcle : (gateAt C j).inputs.count w ≤ 1 := by
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn at h
    omega
  refine ⟨j, hj, hw, by omega, ?_⟩
  intro j' hj' hw'
  by_contra hne
  have hc' : 0 < (gateAt C j').inputs.count w := List.count_pos_iff.mpr hw'
  have hsub : ({j, j'} : Finset ℕ) ⊆ G := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun i => (gateAt C i).inputs.count w) hsub
  rw [Finset.sum_pair (Ne.symm hne)] at hle
  unfold readsIn at h
  omega

theorem readsIn_disjoint_zero (C : Circuit) {G1 G2 : Finset ℕ} {w : ℕ}
    (h1 : G1 ⊆ gatesOf C) (h2 : G2 ⊆ gatesOf C) (hdisj : Disjoint G1 G2)
    (hr : readsOf C w = 1) (h1r : readsIn C G1 w = 1) : readsIn C G2 w = 0 := by
  have hsub : G1 ∪ G2 ⊆ gatesOf C := Finset.union_subset h1 h2
  have hle := readsIn_mono C hsub w
  rw [readsIn_union C G1 G2 w hdisj] at hle
  change readsIn C (gatesOf C) w = 1 at hr
  omega

theorem readsIn_zero_of_count_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ gatesOf C) (hG : G ⊆ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (hc : (gateAt C j).inputs.count w = 1) : readsIn C G w = 0 := by
  refine readsIn_disjoint_zero C (G1 := {j}) (G2 := G)
    (Finset.singleton_subset_iff.2 hj) hG (Finset.disjoint_singleton_left.2 hn) hr ?_
  simpa [readsIn] using hc

theorem count_zero_of_readsIn_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hG : G ⊆ gatesOf C) (hj : j ∈ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (h1 : readsIn C G w = 1) : (gateAt C j).inputs.count w = 0 := by
  have hz := readsIn_disjoint_zero C (G1 := G) (G2 := {j})
    hG (Finset.singleton_subset_iff.2 hj) (Finset.disjoint_singleton_right.2 hn) hr h1
  simpa [readsIn] using hz

theorem readsIn_ge_bound_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    {G : Finset ℕ} (hG : G ⊆ gatesOf C) {r : ℕ} (hbound : ∀ j ∈ G, n + j ≤ r) :
    readsIn C G r = 0 := by
  rw [readsIn_eq_zero_iff]
  intro j hj hr
  have hjlt : j < C.gates.length := Finset.mem_range.1 (hG hj)
  have hlt := hback j hjlt r hr
  have hle := hbound j hj
  omega

theorem reads_output_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) : readsOf C C.output = 0 := by
  refine readsIn_ge_bound_zero n C hback (Finset.Subset.refl _) ?_
  intro j hj
  have hjlt : j < C.size := Finset.mem_range.1 hj
  omega

theorem ne_output_of_reads_pos (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {w : ℕ} (hw : 0 < readsOf C w) : C.output ≠ w := by
  rintro rfl
  have hz := reads_output_zero n C hback hout
  omega

theorem gateAt_mem_gates (C : Circuit) {j : ℕ} (hj : j < C.size) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  have hlen : j < C.gates.length := hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

theorem list_len2_eq (l : List ℕ) (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at h ⊢

theorem list_len1_eq (l : List ℕ) (h : l.length = 1) :
    l = [l.getD 0 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h ⊢

theorem count_pair_eq_one_left {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count a = 1 := by
  simp [h]

theorem count_pair_eq_one_right {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count b = 1 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

theorem count_pair_eq_two {a : ℕ} : ([a, a] : List ℕ).count a = 2 := by
  simp

theorem count_pair_eq_zero {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) :
    ([a, b] : List ℕ).count x = 0 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

inductive BTree
  | priv (w : ℕ) : BTree
  | mark (w : ℕ) : BTree
  | node (j : ℕ) (l r : BTree) : BTree

def BTree.root (n : ℕ) : BTree → ℕ
  | BTree.priv w => w
  | BTree.mark w => w
  | BTree.node j _ _ => n + j

def BTree.marks : BTree → ℕ
  | BTree.priv _ => 0
  | BTree.mark _ => 1
  | BTree.node _ l r => l.marks + r.marks

def BTree.privs : BTree → Finset ℕ
  | BTree.priv w => {w}
  | BTree.mark _ => ∅
  | BTree.node _ l r => l.privs ∪ r.privs

def BTree.gates : BTree → Finset ℕ
  | BTree.priv _ => ∅
  | BTree.mark _ => ∅
  | BTree.node j l r => insert j (l.gates ∪ r.gates)

def BTree.wires (n : ℕ) (t : BTree) : Finset ℕ :=
  t.privs ∪ t.gates.image (fun k => n + k)

def BTree.nonMark : BTree → Prop
  | BTree.mark _ => False
  | _ => True

def GoodTree (n : ℕ) (C : Circuit) : BTree → Prop
  | BTree.priv w => w < n ∧ readsOf C w = 1
  | BTree.mark _ => True
  | BTree.node j l r =>
      j < C.size ∧ isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs = [l.root n, r.root n] ∧
      GoodTree n C l ∧ GoodTree n C r ∧
      (l.nonMark → readsOf C (l.root n) = 1) ∧
      (r.nonMark → readsOf C (r.root n) = 1)

theorem BTree.wires_node (n j : ℕ) (l r : BTree) :
    (BTree.node j l r).wires n = insert (n + j) (l.wires n ∪ r.wires n) := by
  ext w
  simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_insert, Finset.image_union,
    Finset.mem_union, Finset.mem_insert]
  tauto

theorem BTree.root_mem_wires (n : ℕ) {t : BTree} (ht : t.nonMark) : t.root n ∈ t.wires n := by
  cases t with
  | priv w => simp [BTree.wires, BTree.privs, BTree.root]
  | mark w => exact False.elim ht
  | node j l r =>
    rw [BTree.wires_node, BTree.root]
    exact Finset.mem_insert_self _ _

theorem BTree.nonMark_of_marks_zero {t : BTree} (h : t.marks = 0) : t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.marks] at h
  | node _ _ _ => trivial

theorem BTree.nonMark_of_wires_nonempty (n : ℕ) {t : BTree} {w : ℕ} (hw : w ∈ t.wires n) :
    t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.wires, BTree.privs, BTree.gates] at hw
  | node _ _ _ => trivial

theorem good_gates_sub {n : ℕ} {C : Circuit} {t : BTree} (ht : GoodTree n C t) :
    t.gates ⊆ gatesOf C := by
  induction t with
  | priv _ => simp [BTree.gates]
  | mark _ => simp [BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, _, hgl, hgr, _, _⟩
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · exact Finset.mem_range.2 hj
    · exact ihl hgl hkl
    · exact ihr hgr hkr

theorem good_wires_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ w ∈ t.wires n, w ≤ t.root n := by
  induction t with
  | priv w =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu ⊢
    omega
  | mark _ =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
    have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
    have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
    intro w hw
    rw [BTree.wires_node] at hw
    rw [BTree.root]
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihl hgl w hwl) hl_lt)
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihr hgr w hwr) hr_lt)

theorem good_gates_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ k ∈ t.gates, n + k ≤ t.root n := by
  intro k hk
  refine good_wires_le hback ht (n + k) ?_
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)

theorem good_readsIn_top_zero {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : readsIn C t.gates (t.root n) = 0 :=
  readsIn_ge_bound_zero n C hback (good_gates_sub ht) (good_gates_le hback ht)

theorem good_node_not_mem_sub {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {j : ℕ} {l r : BTree}
    (ht : GoodTree n C (BTree.node j l r)) : j ∉ l.gates ∧ j ∉ r.gates := by
  rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
  have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
  have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
  constructor
  · intro hjl
    have := good_gates_le hback hgl j hjl
    omega
  · intro hjr
    have := good_gates_le hback hgr j hjr
    omega

theorem good_internal_reads {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree} (ht : GoodTree n C t) :
    (∀ w ∈ t.wires n, w ≠ t.root n → readsIn C t.gates w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) ∧
    (∀ j l r, t = BTree.node j l r → Disjoint (l.wires n) (r.wires n)) := by
  induction t with
  | priv w =>
    refine ⟨fun u hu hne => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu hne
    exact absurd hu hne
  | mark _ =>
    refine ⟨fun u hu => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    obtain ⟨ihl_int, _⟩ := ihl hgl
    obtain ⟨ihr_int, _⟩ := ihr hgr
    have hnot : j ∉ l.gates ∧ j ∉ r.gates :=
      good_node_not_mem_sub hback ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
    have hl_sub : l.gates ⊆ gatesOf C := good_gates_sub hgl
    have hr_sub : r.gates ⊆ gatesOf C := good_gates_sub hgr
    have hdisj_wires : Disjoint (l.wires n) (r.wires n) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      have hnon : (l.wires n ∩ r.wires n).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
      let w := (l.wires n ∩ r.wires n).max' hnon
      have hw_mem : w ∈ l.wires n ∩ r.wires n := Finset.max'_mem _ hnon
      have hwl : w ∈ l.wires n := (Finset.mem_inter.1 hw_mem).1
      have hwr : w ∈ r.wires n := (Finset.mem_inter.1 hw_mem).2
      have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      by_cases h1 : w = l.root n
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hcnt : (gateAt C j).inputs.count w = 2 := by
            rw [hinp, ← h1, ← h2]
            exact count_pair_eq_two
          have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hjG
          change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count w = 1 at hrw
          omega
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hrr : readsIn C r.gates w = 1 := (ihr_int w hwr h2).1
          have hdisj_j : Disjoint r.gates {j} := by simp [hnot.2]
          have hsub_rj : r.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hr_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_rj w
          rw [readsIn_union C r.gates {j} w hdisj_j] at hle
          have hjr : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h1]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h2 ▸ hr1 hrnm
          have hrl : readsIn C l.gates w = 1 := (ihl_int w hwl h1).1
          have hdisj_j : Disjoint l.gates {j} := by simp [hnot.1]
          have hsub_lj : l.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hl_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_lj w
          rw [readsIn_union C l.gates {j} w hdisj_j] at hle
          have hjl : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h2]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
        · have hrl := ihl_int w hwl h1
          have hrr := ihr_int w hwr h2
          obtain ⟨p, hpG, hpw, _, hpuniq⟩ := readsIn_eq_one_unique C (gatesOf C) w hrl.2.1
          obtain ⟨pl, hpl, hplw⟩ := (readsIn_pos_iff C l.gates w).1 (by omega)
          obtain ⟨pr, hpr, hprw⟩ := (readsIn_pos_iff C r.gates w).1 (by omega)
          have hpl_eq : pl = p := hpuniq pl (hl_sub hpl) hplw
          have hpr_eq : pr = p := hpuniq pr (hr_sub hpr) hprw
          subst hpl_eq
          have hpr' : pl ∈ r.gates := by rwa [← hpr_eq]
          have hmem_inter : n + pl ∈ l.wires n ∩ r.wires n := Finset.mem_inter.2
            ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpl, rfl⟩),
             Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpr', rfl⟩)⟩
          have hle_max : n + pl ≤ w := Finset.le_max' _ _ hmem_inter
          have hlt := hback pl (Finset.mem_range.1 (hl_sub hpl)) w hplw
          omega
    have hdisj_gates : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_wires
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hj_not_u : j ∉ l.gates ∪ r.gates := by
      simp [hnot.1, hnot.2]
    refine ⟨?_, fun j' l' r' heq => by cases heq; exact hdisj_wires⟩
    intro w hw hne
    rw [BTree.wires_node] at hw
    rw [BTree.root] at hne
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact absurd rfl hne
    · have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1l : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 2 := by
          rw [hinp, ← heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (l.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (l.root n) = 1 at hr1l
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = l.root n
      · subst hwr_eq
        have hrw : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_left hlr_ne
        have hrl0 : readsIn C l.gates (l.root n) = 0 := good_readsIn_top_zero hback hgl
        have hrr0 : readsIn C r.gates (l.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hr_sub hnot.2 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihl_int w hwl hwr_eq
        have hrr0 : readsIn C r.gates w = 0 :=
          readsIn_disjoint_zero C hl_sub hr_sub hdisj_gates hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hl_sub hjG hnot.1 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩
    · have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1r : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 2 := by
          rw [hinp, heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (r.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (r.root n) = 1 at hr1r
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = r.root n
      · subst hwr_eq
        have hrw : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_right hlr_ne
        have hrr0 : readsIn C r.gates (r.root n) = 0 := good_readsIn_top_zero hback hgr
        have hrl0 : readsIn C l.gates (r.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hl_sub hnot.1 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihr_int w hwr hwr_eq
        have hrl0 : readsIn C l.gates w = 0 :=
          readsIn_disjoint_zero C hr_sub hl_sub hdisj_gates.symm hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hr_sub hjG hnot.2 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩

theorem good_markFree_inputs {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) :
    ∀ j ∈ t.gates, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ t.wires n := by
  induction t with
  | priv _ =>
    intro j hj
    simp [BTree.gates] at hj
  | mark _ =>
    simp [BTree.marks] at hm
  | node j l r ihl ihr =>
    rcases ht with ⟨_, hop, hinp, hgl, hgr, _, _⟩
    simp only [BTree.marks] at hm
    have hml : l.marks = 0 := by omega
    have hmr : r.marks = 0 := by omega
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · refine ⟨hop, by rw [hinp]; rfl, fun w hw => ?_⟩
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [BTree.wires_node]
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hml)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmr)))
    · obtain ⟨ho, hl2, hwin⟩ := ihl hgl hml k hkl
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · obtain ⟨ho, hl2, hwin⟩ := ihr hgr hmr k hkr
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hwin w hw))

def IsTree (n : ℕ) (C : Circuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := readsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

theorem good_markFree_isTree {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) : IsTree n C t.privs ∅ := by
  refine ⟨t.gates, t.root n, good_gates_sub ht,
    BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hm),
    good_readsIn_top_zero hback ht, fun _ hb => absurd hb (Finset.notMem_empty _), ?_,
    (good_internal_reads hback hout ht).1⟩
  intro j hj
  obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs ht hm j hj
  exact ⟨ho, hl, fun w hw => Or.inl (hwin w hw)⟩

def IsTopStretch (n : ℕ) (C : Circuit) (t : BTree) (reg priv : Finset ℕ) (b : ℕ) : Prop :=
  reg ⊆ t.gates ∧ priv ⊆ t.privs ∧ b ≤ t.root n ∧
  ((reg = ∅ ∧ priv = ∅ ∧ b = t.root n) ∨
   (let wires := priv ∪ reg.image (fun k => n + k)
    t.root n ∈ wires ∧ b ∉ wires ∧ b < t.root n ∧ readsIn C reg b = 1 ∧
    (∀ j ∈ reg, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ t.root n → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w)))

theorem isTree_of_topStretch {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) {reg priv : Finset ℕ} {b : ℕ}
    (hs : IsTopStretch n C t reg priv b) (hnp : priv.Nonempty) : IsTree n C priv {b} := by
  rcases hs with ⟨hreg, _, _, ⟨_, hpe, _⟩ | ⟨hrm, hbn, hblt, hbr, hgj, hwint⟩⟩
  · rw [hpe] at hnp
    exact absurd hnp Finset.not_nonempty_empty
  · refine ⟨reg, t.root n, hreg.trans (good_gates_sub ht), hrm,
      readsIn_ge_bound_zero n C hback (hreg.trans (good_gates_sub ht))
        (fun k hk => good_gates_le hback ht k (hreg hk)),
      fun b' hb' => by
        rw [Finset.mem_singleton.1 hb']
        exact ⟨hbn, hblt, hbr⟩,
      fun j hj => by
        obtain ⟨ho, hl, hwin⟩ := hgj j hj
        exact ⟨ho, hl, fun w hw => (hwin w hw).imp id (fun h => Finset.mem_singleton.2 h)⟩,
      hwint⟩

theorem extend_stretch_aux {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {j : ℕ} {mf mk : BTree}
    (hj : j < C.size) (hop : isBinOp (gateAt C j).op)
    (hinp : (gateAt C j).inputs = [mf.root n, mk.root n] ∨
      (gateAt C j).inputs = [mk.root n, mf.root n])
    (hgf : GoodTree n C mf) (hgk : GoodTree n C mk)
    (hmf : mf.marks = 0)
    (hrf1 : readsOf C (mf.root n) = 1)
    (hrk1 : mk.nonMark → readsOf C (mk.root n) = 1)
    (hdisj_w : Disjoint (mf.wires n) (mk.wires n))
    (hdisj_g : Disjoint mf.gates mk.gates)
    (hj_mf : j ∉ mf.gates) (hj_mk : j ∉ mk.gates)
    {reg_k priv_k : Finset ℕ} {b : ℕ}
    (hsk : IsTopStretch n C mk reg_k priv_k b) :
    let reg := insert j (mf.gates ∪ reg_k)
    let priv := mf.privs ∪ priv_k
    let wires := priv ∪ reg.image (fun k => n + k)
    (n + j) ∈ wires ∧ b ∉ wires ∧ b < n + j ∧ readsIn C reg b = 1 ∧
    (∀ k ∈ reg, isBinOp (gateAt C k).op ∧ (gateAt C k).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ n + j → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) := by
  intro reg priv wires
  have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
  have hmf_sub : mf.gates ⊆ gatesOf C := good_gates_sub hgf
  have hmk_sub : mk.gates ⊆ gatesOf C := good_gates_sub hgk
  have hmf_int := (good_internal_reads hback hout hgf).1
  have hmf_lt : mf.root n < n + j := hback j hj (mf.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmk_lt : mk.root n < n + j := hback j hj (mk.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmf_ne_mk : mf.root n ≠ mk.root n := by
    intro heq
    have hcnt : (gateAt C j).inputs.count (mf.root n) = 2 := by
      rcases hinp with h | h <;> rw [h, heq] <;> exact count_pair_eq_two
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (mf.root n))) hjG
    change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (mf.root n) = 1 at hrf1
    omega
  have hcnt_mf : (gateAt C j).inputs.count (mf.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_left hmf_ne_mk
    · exact count_pair_eq_one_right hmf_ne_mk.symm
  have hcnt_mk : (gateAt C j).inputs.count (mk.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_right hmf_ne_mk
    · exact count_pair_eq_one_left hmf_ne_mk.symm
  rcases hsk with ⟨hreg_k, hpriv_k, hb_le, hcase⟩
  have hdisj_rk : Disjoint mf.gates reg_k := Disjoint.mono_right hreg_k hdisj_g
  have hj_not_u : j ∉ mf.gates ∪ reg_k := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hj_mf, fun h => hj_mk (hreg_k h)⟩
  have hwires_eq : wires = insert (n + j) (mf.wires n ∪ (priv_k ∪ reg_k.image (fun k => n + k))) := by
    ext w
    simp only [wires, priv, reg, BTree.wires, Finset.image_insert, Finset.image_union,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h1 | h2) | (h3 | h4 | h5))
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h3
      · exact Or.inr (Or.inl (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inr h5))
    · rintro (h1 | (h2 | h3) | (h4 | h5))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inr (Or.inr h5))
  have hwk_sub : priv_k ∪ reg_k.image (fun k => n + k) ⊆ mk.wires n := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hp | ⟨k, hk, rfl⟩
    · exact Finset.mem_union_left _ (hpriv_k hp)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hreg_k hk, rfl⟩)
  have hmf_reads_sub : ∀ w ∈ mf.wires n, readsIn C reg_k w = 0 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · subst hwr
      exact readsIn_zero_of_count_one C hjG (hreg_k.trans hmk_sub) (fun h => hj_mk (hreg_k h)) hrf1 hcnt_mf
    · have hi := hmf_int w hw hwr
      exact readsIn_disjoint_zero C hmf_sub (hreg_k.trans hmk_sub) hdisj_rk hi.2.1 hi.1
  have hmf_all_reads1 : ∀ w ∈ mf.wires n, readsOf C w = 1 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · exact hwr ▸ hrf1
    · exact (hmf_int w hw hwr).2.1
  have hb_not_mf : b ∉ mf.wires n := by
    intro hbm
    have hrb1 : readsOf C b = 1 := hmf_all_reads1 b hbm
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, _, hbr1, _, _⟩
    · subst hbeq
      have hne_root : mk.root n ≠ mf.root n := hmf_ne_mk.symm
      have hi := hmf_int (mk.root n) hbm hne_root
      have h0 := count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
      omega
    · have h0 := hmf_reads_sub b hbm
      omega
  have hmf_reads_b : readsIn C mf.gates b = 0 := by
    rw [readsIn_eq_zero_iff]
    intro k hk hbk
    have hwin := (good_markFree_inputs hgf hmf k hk).2.2 b hbk
    exact hb_not_mf hwin
  have hroot_mem : n + j ∈ wires := by
    rw [hwires_eq]
    exact Finset.mem_insert_self _ _
  have hb_lt : b < n + j := Nat.lt_of_le_of_lt hb_le hmk_lt
  have hb_not_w : b ∉ wires := by
    rw [hwires_eq]
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨by omega, hb_not_mf, ?_⟩
    rcases hcase with ⟨hre, hpe, _⟩ | ⟨_, hbn, _, _, _, _⟩
    · simp [hre, hpe]
    · simpa [Finset.mem_union, not_or] using hbn
  have hb_reads : readsIn C reg b = 1 := by
    rw [readsIn_insert C _ j b hj_not_u, readsIn_union C mf.gates reg_k b hdisj_rk, hmf_reads_b]
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, hblt_k, hbr1, _, _⟩
    · subst hbeq
      rw [hre, readsIn_empty, hcnt_mk]
    · have hcj0 : (gateAt C j).inputs.count b = 0 := by
        have hbn1 : b ≠ mf.root n := fun heq =>
          hb_not_mf (heq ▸ BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf))
        have hbn2 : b ≠ mk.root n := by omega
        rcases hinp with h | h <;> rw [h]
        · exact count_pair_eq_zero hbn1 hbn2
        · exact count_pair_eq_zero hbn2 hbn1
      rw [hcj0, hbr1]
  refine ⟨hroot_mem, hb_not_w, hb_lt, hb_reads, ?_, ?_⟩
  · intro k hk
    simp only [reg, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkm | hkk
    · refine ⟨hop, by rcases hinp with h | h <;> rw [h] <;> rfl, fun w hw => ?_⟩
      have hwf : w = mf.root n ∨ w = mk.root n := by
        rcases hinp with h | h <;> rw [h] at hw <;> simp at hw <;> tauto
      rcases hwf with rfl | rfl
      · left
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf)))
      · rcases hcase with ⟨_, _, hbeq⟩ | ⟨hrm, _, _, _, _, _⟩
        · exact Or.inr hbeq.symm
        · left
          rw [hwires_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hrm)
    · obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs hgf hmf k hkm
      refine ⟨ho, hl, fun w hw => Or.inl ?_⟩
      rw [hwires_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · rcases hcase with ⟨hre, _, _⟩ | ⟨_, _, _, _, hgj, _⟩
      · rw [hre] at hkk
        exact absurd hkk (Finset.notMem_empty _)
      · obtain ⟨ho, hl, hwin⟩ := hgj k hkk
        refine ⟨ho, hl, fun w hw => (hwin w hw).imp (fun h => ?_) id⟩
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
  · intro w hw hne
    rw [hwires_eq] at hw
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwm | hwk
    · exact absurd rfl hne
    · rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk,
        hmf_reads_sub w hwm]
      by_cases hwr : w = mf.root n
      · subst hwr
        rw [hcnt_mf, good_readsIn_top_zero hback hgf]
        exact ⟨by omega, hrf1, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := hmf_int w hwm hwr
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
        rw [hcj0, hi.1]
        exact ⟨by omega, hi.2.1, hi.2.2⟩
    · rcases hcase with ⟨hre, hpe, _⟩ | ⟨hrm, _, _, _, _, hwint⟩
      · simp [hre, hpe] at hwk
      · have hw_in_mk : w ∈ mk.wires n := hwk_sub (Finset.mem_union.2 hwk)
        have hmknm : mk.nonMark := BTree.nonMark_of_wires_nonempty n hw_in_mk
        rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk]
        by_cases hwr : w = mk.root n
        · subst hwr
          have hrk := hrk1 hmknm
          have hrl0 : readsIn C mf.gates (mk.root n) = 0 :=
            readsIn_zero_of_count_one C hjG hmf_sub hj_mf hrk hcnt_mk
          have hrr0 : readsIn C reg_k (mk.root n) = 0 :=
            readsIn_ge_bound_zero n C hback (hreg_k.trans hmk_sub)
              (fun k hk => good_gates_le hback hgk k (hreg_k hk))
          rw [hcnt_mk, hrl0, hrr0]
          exact ⟨by omega, hrk, ne_output_of_reads_pos n C hback hout (by omega)⟩
        · have hi := hwint w (Finset.mem_union.2 hwk) hwr
          have hrl0 : readsIn C mf.gates w = 0 :=
            readsIn_disjoint_zero C (hreg_k.trans hmk_sub) hmf_sub hdisj_rk.symm hi.2.1 hi.1
          have hcj0 : (gateAt C j).inputs.count w = 0 :=
            count_zero_of_readsIn_one C (hreg_k.trans hmk_sub) hjG (fun h => hj_mk (hreg_k h)) hi.2.1 hi.1
          rw [hcj0, hrl0, hi.1]
          exact ⟨by omega, hi.2.1, hi.2.2⟩

theorem decomp_marked {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ (reg_top priv_top : Finset ℕ) (b_top : ℕ) (rest : List (Finset ℕ)),
      IsTopStretch n C t reg_top priv_top b_top ∧
      rest.length + 2 ≤ 2 * t.marks ∧
      (∀ S ∈ rest, S.Nonempty ∧ S ⊆ t.privs ∧ Disjoint S priv_top ∧ ∃ b, IsTree n C S {b}) ∧
      rest.Pairwise Disjoint ∧
      priv_top ∪ rest.toFinset.biUnion (fun S => S) = t.privs := by
  induction t with
  | priv _ =>
    simp [BTree.marks] at hm
  | mark w =>
    refine ⟨∅, ∅, w, [], ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _,
      Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [BTree.marks], fun _ h => by simp at h, List.Pairwise.nil,
      by simp [BTree.privs]⟩
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hgt_node : GoodTree n C (BTree.node j l r) := ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hdisj_w : Disjoint (l.wires n) (r.wires n) :=
      (good_internal_reads hback hout hgt_node).2 j l r rfl
    have hdisj_g : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_w
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hdisj_p : Disjoint l.privs r.privs :=
      Disjoint.mono (Finset.subset_union_left) (Finset.subset_union_left) hdisj_w
    have hnot := good_node_not_mem_sub hback hgt_node
    simp only [BTree.marks] at hm
    by_cases hml : l.marks = 0
    · have hmr : 1 ≤ r.marks := by omega
      obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr
      have hrf1 : readsOf C (l.root n) = 1 := hl1 (BTree.nonMark_of_marks_zero hml)
      have hext := extend_stretch_aux hback hout hj hop (Or.inl hinp) hgl hgr hml hrf1 hr1
        hdisj_w hdisj_g hnot.1 hnot.2 hsr
      refine ⟨insert j (l.gates ∪ reg_r), l.privs ∪ priv_r, b_r, rest_r, ?_, ?_, ?_, hpw_r, ?_⟩
      · refine ⟨Finset.insert_subset_insert j (Finset.union_subset_union_right hsr.1),
          Finset.union_subset_union_right hsr.2.1, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
      · simp only [BTree.marks]
        omega
      · intro S hS
        obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_r S hS
        refine ⟨hnp, hsub.trans Finset.subset_union_right, ?_, htr⟩
        rw [Finset.disjoint_union_right]
        exact ⟨Disjoint.mono_left hsub hdisj_p.symm, hdp⟩
      · simp only [BTree.privs]
        rw [Finset.union_assoc, hcov_r]
    · by_cases hmr : r.marks = 0
      · have hml1 : 1 ≤ l.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        have hrf1 : readsOf C (r.root n) = 1 := hr1 (BTree.nonMark_of_marks_zero hmr)
        have hext := extend_stretch_aux hback hout hj hop (Or.inr hinp) hgr hgl hmr hrf1 hl1
          hdisj_w.symm hdisj_g.symm hnot.2 hnot.1 hsl
        refine ⟨insert j (r.gates ∪ reg_l), r.privs ∪ priv_l, b_l, rest_l, ?_, ?_, ?_, hpw_l, ?_⟩
        · refine ⟨?_, ?_, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
          · intro k hk
            simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk ⊢
            rcases hk with rfl | h1 | h2
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h1)
            · exact Or.inr (Or.inl (hsl.1 h2))
          · intro w hw
            simp only [BTree.privs, Finset.mem_union] at hw ⊢
            rcases hw with h1 | h2
            · exact Or.inr h1
            · exact Or.inl (hsl.2.1 h2)
        · simp only [BTree.marks]
          omega
        · intro S hS
          obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_l S hS
          refine ⟨hnp, hsub.trans Finset.subset_union_left, ?_, htr⟩
          rw [Finset.disjoint_union_right]
          exact ⟨Disjoint.mono_left hsub hdisj_p, hdp⟩
        · simp only [BTree.privs]
          rw [Finset.union_assoc, hcov_l, Finset.union_comm]
      · have hml1 : 1 ≤ l.marks := by omega
        have hmr1 : 1 ≤ r.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr1
        let Ll : List (Finset ℕ) := if priv_l.Nonempty then priv_l :: rest_l else rest_l
        let Lr : List (Finset ℕ) := if priv_r.Nonempty then priv_r :: rest_r else rest_r
        have hLl_len : Ll.length ≤ rest_l.length + 1 := by
          dsimp only [Ll]
          split_ifs <;> simp
        have hLr_len : Lr.length ≤ rest_r.length + 1 := by
          dsimp only [Lr]
          split_ifs <;> simp
        have hLl_prop : ∀ S ∈ Ll, S.Nonempty ∧ S ⊆ l.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Ll] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsl.2.1, b_l, isTree_of_topStretch hback hgl hsl hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_l S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_l S hS
            exact ⟨a, b, c⟩
        have hLr_prop : ∀ S ∈ Lr, S.Nonempty ∧ S ⊆ r.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Lr] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsr.2.1, b_r, isTree_of_topStretch hback hgr hsr hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_r S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_r S hS
            exact ⟨a, b, c⟩
        have hLl_pw : Ll.Pairwise Disjoint := by
          dsimp only [Ll]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_l S hS).2.2.1.symm, hpw_l⟩
          · exact hpw_l
        have hLr_pw : Lr.Pairwise Disjoint := by
          dsimp only [Lr]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_r S hS).2.2.1.symm, hpw_r⟩
          · exact hpw_r
        have hLl_cov : Ll.toFinset.biUnion (fun S => S) = l.privs := by
          dsimp only [Ll]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_l]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_l
            exact hcov_l
        have hLr_cov : Lr.toFinset.biUnion (fun S => S) = r.privs := by
          dsimp only [Lr]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_r]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_r
            exact hcov_r
        refine ⟨∅, ∅, n + j, Ll ++ Lr,
          ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, BTree.marks]
          omega
        · intro S hS
          rcases List.mem_append.1 hS with h1 | h2
          · obtain ⟨a, b, c⟩ := hLl_prop S h1
            exact ⟨a, b.trans Finset.subset_union_left, Finset.disjoint_empty_right S, c⟩
          · obtain ⟨a, b, c⟩ := hLr_prop S h2
            exact ⟨a, b.trans Finset.subset_union_right, Finset.disjoint_empty_right S, c⟩
        · rw [List.pairwise_append]
          refine ⟨hLl_pw, hLr_pw, fun S1 h1 S2 h2 => ?_⟩
          exact Disjoint.mono (hLl_prop S1 h1).2.1 (hLr_prop S2 h2).2.1 hdisj_p
        · rw [Finset.empty_union, List.toFinset_append, Finset.union_biUnion, hLl_cov, hLr_cov]
          rfl

theorem marked_tree_chains {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ L : List (Finset ℕ),
      L.length + 1 ≤ 2 * t.marks ∧
      (∀ S ∈ L, S.Nonempty ∧ S ⊆ t.privs ∧ ∃ b, IsTree n C S {b}) ∧
      L.Pairwise Disjoint ∧
      L.toFinset.biUnion (fun S => S) = t.privs := by
  obtain ⟨reg, priv, b, rest, hs, hlen, hrest, hpw, hcov⟩ := decomp_marked hback hout ht hm
  by_cases hnp : priv.Nonempty
  · refine ⟨priv :: rest, by simp; omega, ?_, ?_, ?_⟩
    · intro S hS
      rcases List.mem_cons.1 hS with rfl | hSr
      · exact ⟨hnp, hs.2.1, b, isTree_of_topStretch hback ht hs hnp⟩
      · obtain ⟨a, b', _, c⟩ := hrest S hSr
        exact ⟨a, b', c⟩
    · exact List.pairwise_cons.2 ⟨fun S hS => (hrest S hS).2.2.1.symm, hpw⟩
    · rw [List.toFinset_cons, Finset.biUnion_insert, hcov]
  · refine ⟨rest, by omega, fun S hS => ?_, hpw, ?_⟩
    · obtain ⟨a, b', _, c⟩ := hrest S hS
      exact ⟨a, b', c⟩
    · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov
      exact hcov

def isInternalChild (n : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  readsOf C u = 1 ∧ ¬ (n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not)

open Classical in
noncomputable def buildTree (n : ℕ) (C : Circuit) (r : ℕ) : BTree :=
  if h : n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not then
    let j := r - n
    let u0 := (gateAt C j).inputs.getD 0 0
    let u1 := (gateAt C j).inputs.getD 1 0
    let child : ℕ → BTree := fun u =>
      if hu : u < r ∧ isInternalChild n C u then
        if u < n then BTree.priv u else buildTree n C u
      else BTree.mark u
    BTree.node j (child u0) (child u1)
  else if r < n ∧ readsOf C r = 1 then
    BTree.priv r
  else
    BTree.mark r
termination_by r

theorem buildTree_root (n : ℕ) (C : Circuit) (r : ℕ) : (buildTree n C r).root n = r := by
  rw [buildTree]
  split_ifs with h1 h2
  · simp [BTree.root]
    omega
  · rfl
  · rfl

theorem buildTree_good (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C) : ∀ r : ℕ, GoodTree n C (buildTree n C r) := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    rw [buildTree]
    split_ifs with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      classical
      have hchild_prop : ∀ u : ℕ, u < r →
          let ch := if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u
          ch.root n = u ∧ GoodTree n C ch ∧ (ch.nonMark → readsOf C u = 1) := by
        intro u hult
        dsimp only
        split_ifs with hu hun
        · refine ⟨rfl, ⟨hun, hu.2.1⟩, fun _ => hu.2.1⟩
        · refine ⟨buildTree_root n C u, ih u hult, fun _ => hu.2.1⟩
        · refine ⟨rfl, trivial, fun h => False.elim h⟩
      have hc0 := hchild_prop _ hu0_lt
      have hc1 := hchild_prop _ hu1_lt
      refine ⟨hj, hbin.1, ?_, hc0.2.1, hc1.2.1, ?_, ?_⟩
      · rw [hc0.1, hc1.1]
        exact hinp
      · rw [hc0.1]
        exact hc0.2.2
      · rw [hc1.1]
        exact hc1.2.2
    · exact h2
    · trivial

open Classical in
noncomputable def parentGate (C : Circuit) (w : ℕ) : ℕ :=
  if h : ∃ j ∈ gatesOf C, w ∈ (gateAt C j).inputs then Classical.choose h else 0

theorem parentGate_spec (C : Circuit) {w : ℕ} (h : readsOf C w = 1) :
    parentGate C w ∈ gatesOf C ∧ w ∈ (gateAt C (parentGate C w)).inputs ∧
    ∀ j ∈ gatesOf C, w ∈ (gateAt C j).inputs → j = parentGate C w := by
  obtain ⟨j, hj, hw, _, huniq⟩ := readsIn_eq_one_unique C (gatesOf C) w h
  have hex : ∃ j' ∈ gatesOf C, w ∈ (gateAt C j').inputs := ⟨j, hj, hw⟩
  have hdef : parentGate C w = Classical.choose hex := by
    unfold parentGate
    exact dif_pos hex
  rw [hdef]
  have hch := Classical.choose_spec hex
  have heq : Classical.choose hex = j := huniq _ hch.1 hch.2
  rw [heq]
  exact ⟨hj, hw, huniq⟩

open Classical in
noncomputable def owner (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if h : w < n + C.size ∧ readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not ∧
      w < n + parentGate C w then
    owner n C (n + parentGate C w)
  else w
termination_by n + C.size - w

open Classical in
theorem owner_step (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {w : ℕ}
    (hw1 : readsOf C w = 1) (hnot : (gateAt C (parentGate C w)).op ≠ GateOp.not) :
    owner n C w = owner n C (n + parentGate C w) := by
  obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hw1
  have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
  have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
  have hcond : w < n + C.size ∧ readsOf C w = 1 ∧
      (gateAt C (parentGate C w)).op ≠ GateOp.not ∧ w < n + parentGate C w :=
    ⟨by omega, hw1, hnot, hwlt⟩
  rw [owner]
  exact dif_pos hcond

theorem owner_fixed (n : ℕ) (C : Circuit) {w : ℕ}
    (h : ¬ (readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not)) :
    owner n C w = w := by
  rw [owner]
  split_ifs with h1
  · exact absurd ⟨h1.2.1, h1.2.2.1⟩ h
  · rfl

theorem owner_of_good_child (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {j u : ℕ}
    (hj : j < C.size) (hop : (gateAt C j).op ≠ GateOp.not)
    (hu : u ∈ (gateAt C j).inputs) (hr1 : readsOf C u = 1) :
    owner n C u = owner n C (n + j) := by
  obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
  have hpeq : j = parentGate C u := huniq j (Finset.mem_range.2 hj) hu
  rw [owner_step n C hback hr1 (by rwa [← hpeq]), ← hpeq]

open Classical in
theorem owner_eq_of_mem_wires (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ), ∀ w ∈ (buildTree n C r).wires n, owner n C w = owner n C r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro w hw
    rw [buildTree] at hw
    split_ifs at hw with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      have hchild : ∀ (u : ℕ), u ∈ (gateAt C (r - n)).inputs →
          w ∈ (if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u : BTree).wires n → owner n C w = owner n C r := by
        intro u hu hwu
        split_ifs at hwu with huc hun
        · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
            Finset.union_empty, Finset.mem_singleton] at hwu
          subst hwu
          rw [owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · rw [ih u huc.1 w hwu, owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · simp [BTree.wires, BTree.privs, BTree.gates] at hwu
      rw [BTree.wires_node] at hw
      simp only [Finset.mem_insert, Finset.mem_union] at hw
      rcases hw with rfl | hwl | hwr
      · rw [hnj]
      · exact hchild _ (by rw [hinp]; simp) hwl
      · exact hchild _ (by rw [hinp]; simp) hwr
    · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
        Finset.mem_singleton] at hw
      rw [hw]
    · simp [BTree.wires, BTree.privs, BTree.gates] at hw

open Classical in
theorem mem_wires_buildTree_owner (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (w : ℕ),
      ((w < n ∧ readsOf C w = 1) ∨
        (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not)) →
      w ∈ (buildTree n C (owner n C w)).wires n := by
  intro w
  induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
  | ind d ih =>
    intro hw
    by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
    · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
      have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
      have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
      have hown : owner n C w = owner n C (n + parentGate C w) :=
        owner_step n C hback hstep.1 hstep.2
      have hnp_in : n + parentGate C w ∈ (buildTree n C (owner n C (n + parentGate C w))).wires n :=
        ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      rw [hown]
      have hrec : ∀ (r : ℕ), n + parentGate C w ∈ (buildTree n C r).wires n →
          w ∈ (buildTree n C r).wires n := by
        intro r
        induction r using Nat.strong_induction_on with
        | ind r ihr =>
          intro hrw
          rw [buildTree] at hrw ⊢
          split_ifs at hrw ⊢ with h1 h2
          · have hj : r - n < C.size := h1.2.1
            have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
            have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
              rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
              · exact ⟨ho, hl⟩
              · exact absurd hn h1.2.2
            have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
            have hnj : n + (r - n) = r := by omega
            rw [BTree.wires_node] at hrw ⊢
            simp only [Finset.mem_insert, Finset.mem_union] at hrw ⊢
            rcases hrw with hreq | hwl | hwr
            · have hpeq : r - n = parentGate C w := by omega
              have hwin_r : w ∈ (gateAt C (r - n)).inputs := by rwa [hpeq]
              rw [hinp] at hwin_r
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin_r
              have hint_w : isInternalChild n C w := by
                refine ⟨hstep.1, ?_⟩
                rintro ⟨hle, _, hnot⟩
                rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
                · omega
                · exact hne hnot
              have hw_in_child : ∀ u : ℕ, w = u →
                  w ∈ (if hu : u < r ∧ isInternalChild n C u then
                    if u < n then BTree.priv u else buildTree n C u
                  else BTree.mark u : BTree).wires n := by
                intro u hu
                subst hu
                have hcond : w < r ∧ isInternalChild n C w := ⟨by omega, hint_w⟩
                rw [dif_pos hcond]
                by_cases hwn : w < n
                · rw [if_pos hwn]
                  simp [BTree.wires, BTree.privs]
                · rw [if_neg hwn, buildTree]
                  have hwb : n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not := by
                    rcases hw with ⟨hlt, _⟩ | hgood
                    · omega
                    · exact hgood
                  rw [dif_pos hwb, BTree.wires_node]
                  have : n + (w - n) = w := by omega
                  rw [this]
                  exact Finset.mem_insert_self _ _
              rcases hwin_r with h0 | h1'
              · exact Or.inr (Or.inl (hw_in_child _ h0))
              · exact Or.inr (Or.inr (hw_in_child _ h1'))
            · refine Or.inr (Or.inl ?_)
              split_ifs at hwl ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwl
                omega
              · exact ihr _ huc.1 hwl
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwl
            · refine Or.inr (Or.inr ?_)
              split_ifs at hwr ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwr
                omega
              · exact ihr _ huc.1 hwr
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwr
          · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
              Finset.mem_singleton] at hrw
            omega
          · simp [BTree.wires, BTree.privs, BTree.gates] at hrw
      exact hrec _ hnp_in
    · rw [owner_fixed n C hstep, buildTree]
      rcases hw with ⟨hlt, hr1⟩ | hbin
      · have hnotb : ¬ (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not) := by omega
        rw [dif_neg hnotb, if_pos ⟨hlt, hr1⟩]
        simp [BTree.wires, BTree.privs, BTree.gates]
      · rw [dif_pos hbin, BTree.wires_node]
        have : n + (w - n) = w := by omega
        rw [this]
        exact Finset.mem_insert_self _ _

theorem mem_privs_iff_lt (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ w, w ∈ t.privs ↔ w ∈ t.wires n ∧ w < n := by
  induction t with
  | priv u =>
    intro w
    simp only [BTree.privs, BTree.wires, BTree.gates, Finset.image_empty, Finset.union_empty,
      Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, ht.1⟩
    · exact fun h => h.1
  | mark _ =>
    intro w
    simp [BTree.privs, BTree.wires, BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro w
    rw [BTree.wires_node]
    simp only [BTree.privs, Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · have := (ihl hgl w).1 h
        exact ⟨Or.inr (Or.inl this.1), this.2⟩
      · have := (ihr hgr w).1 h
        exact ⟨Or.inr (Or.inr this.1), this.2⟩
    · rintro ⟨rfl | h | h, hlt⟩
      · omega
      · exact Or.inl ((ihl hgl w).2 ⟨h, hlt⟩)
      · exact Or.inr ((ihr hgr w).2 ⟨h, hlt⟩)

theorem mem_gates_iff_ge (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ k, k ∈ t.gates ↔ n + k ∈ t.wires n := by
  induction t with
  | priv u =>
    intro k
    have hu : u < n := ht.1
    simp only [BTree.gates, BTree.wires, BTree.privs, Finset.image_empty, Finset.union_empty,
      Finset.notMem_empty, Finset.mem_singleton, false_iff]
    omega
  | mark _ =>
    intro k
    simp [BTree.gates, BTree.wires, BTree.privs]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro k
    rw [BTree.wires_node]
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
    rw [ihl hgl k, ihr hgr k]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (heq | h | h)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

open Classical in
theorem buildTree_marks_eq_sum (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ),
      ((r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)) →
      (buildTree n C r).marks =
        ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hgt := buildTree_good n C hshape hback r
    have hdisj_from_good := (good_internal_reads hback hout hgt).2
    have hnot_from_good : ∀ j l r', buildTree n C r = BTree.node j l r' → j ∉ l.gates ∧ j ∉ r'.gates := by
      intro j l r' heq
      rw [heq] at hgt
      exact good_node_not_mem_sub hback hgt
    rw [buildTree] at hgt hdisj_from_good hnot_from_good ⊢
    split_ifs at hgt hdisj_from_good hnot_from_good ⊢ with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      set ch : ℕ → BTree := fun u =>
        if hu : u < r ∧ isInternalChild n C u then
          if u < n then BTree.priv u else buildTree n C u
        else BTree.mark u
      have hnot := good_node_not_mem_sub hback hgt
      have hdisjw := hdisj_from_good (r - n) _ _ rfl
      have hdisjg : Disjoint (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates := by
        rw [Finset.disjoint_left]
        intro k hkl hkr
        exact Finset.disjoint_left.1 hdisjw
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
      have hj_not_u : r - n ∉ (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates ∪
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates :=
        Finset.notMem_union.2 hnot
      simp only [BTree.marks, BTree.gates]
      rw [Finset.sum_insert hj_not_u, Finset.sum_union hdisjg]
      have hch_eq : ∀ u : ℕ, u < r →
          (ch u).marks =
            (if ¬ isInternalChild n C u then 1 else 0) +
            ∑ j ∈ (ch u).gates,
              @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
                (gateAt C j).inputs := by
        intro u hult
        dsimp only [ch]
        by_cases huc : u < r ∧ isInternalChild n C u
        · rw [dif_pos huc, if_neg (not_not.2 huc.2), zero_add]
          by_cases hun : u < n
          · rw [if_pos hun]
            simp [BTree.marks, BTree.gates]
          · rw [if_neg hun]
            have hvalid : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op ≠ GateOp.not :=
              ⟨by omega, by omega, fun hnot => huc.2.2 ⟨by omega, by omega, hnot⟩⟩
            exact ih u hult (Or.inr hvalid)
        · rw [dif_neg huc]
          have hni : ¬ isInternalChild n C u := fun hi => huc ⟨hult, hi⟩
          rw [if_pos hni]
          simp [BTree.marks, BTree.gates]
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      rw [hch_eq _ hu0_lt, hch_eq _ hu1_lt]
      have hcnt_pair :
          @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
            (gateAt C (r - n)).inputs =
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 0 0) then 1 else 0) +
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 1 0) then 1 else 0) := by
        conv_lhs => rw [hinp]
        simp only [List.countP_cons, List.countP_nil]
        have hdec : ∀ (P : Prop),
            (if (@decide P (Classical.propDecidable P)) = true then 1 else 0) =
            if P then 1 else 0 := by
          intro P
          by_cases hP : P
          · rw [@decide_eq_true P (Classical.propDecidable P) hP, if_pos rfl, if_pos hP]
          · rw [@decide_eq_false P (Classical.propDecidable P) hP, if_neg Bool.false_ne_true, if_neg hP]
        rw [hdec, hdec, Nat.zero_add, Nat.add_comm]
        congr 1
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
      rw [hcnt_pair]
      omega
    · simp [BTree.marks, BTree.gates]
    · rcases hr with h | h
      · exact absurd h h2
      · exact absurd h h1

theorem list_countP_le_sum_count (l : List ℕ) (S : Finset ℕ) :
    @List.countP ℕ (fun u => @decide (u ∈ S) (Classical.propDecidable _)) l =
      ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    simp only [List.countP_cons, List.count_cons, Finset.sum_add_distrib, ih]
    have h1 : (∑ w ∈ S, if a == w then 1 else 0) = if a ∈ S then 1 else 0 := by
      by_cases ha : a ∈ S
      · rw [if_pos ha, Finset.sum_eq_single a]
        · simp
        · intro w _ hwa
          simp [beq_eq_false_iff_ne.2 (Ne.symm hwa)]
        · intro h
          exact absurd ha h
      · rw [if_neg ha, Finset.sum_eq_zero]
        intro w hw
        have hne : a ≠ w := fun h => ha (h ▸ hw)
        simp [beq_eq_false_iff_ne.2 hne]
    rw [h1]
    by_cases ha : a ∈ S <;> simp [ha] <;> omega

theorem list_flatMap_collect {α : Type*} [DecidableEq α] (L : List α) (f : α → List (Finset ℕ))
    (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ S ∈ f a, S ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise Disjoint)
    (hf_cov : ∀ a ∈ L, (f a).toFinset.biUnion (fun S => S) = g a) :
    (L.flatMap f).Pairwise Disjoint ∧
    (L.flatMap f).toFinset.biUnion (fun S => S) = L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ S ∈ f a, S ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw : (f a).Pairwise Disjoint := hf_pw a (List.mem_cons_self ..)
    have hfa_cov : (f a).toFinset.biUnion (fun S => S) = g a := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun S1 h1 S2 h2 => ?_⟩
      obtain ⟨b, hb, hS2⟩ := List.mem_flatMap.1 h2
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub S1 h1) (hf_sub b (List.mem_cons_of_mem a hb) S2 hS2)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov, hrec.2.1,
        List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

theorem main (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C)
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (n + j)) :
    let gates := Finset.range C.size
    let gate := gateAt C
    let reads := readsIn C gates
    let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
      (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
      pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
      chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
      (0 < markedReads + neg.card → 0 < markedComponents) ∧
      (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
      (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
      (∀ S ∈ pure, S.Nonempty ∧ IsTree n C S ∅) ∧
      (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, IsTree n C S {b}) := by
  classical
  intro gates gate reads neg shared sharedGates markedReads once
  let validRoot : ℕ → Prop := fun r =>
    (r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)
  let Rout : Finset ℕ := if (gateAt C (C.size - 1)).op ≠ GateOp.not then {C.output} else ∅
  let Rsh : Finset ℕ :=
    (sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not)).image (fun k => n + k)
  let Rneg : Finset ℕ :=
    (neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0))).image
      (fun j => (gateAt C j).inputs.getD 0 0)
  let Roots : Finset ℕ := Rout ∪ Rsh ∪ Rneg
  have hRout_card : Rout.card ≤ 1 := by
    dsimp only [Rout]
    split_ifs <;> simp
  have hRsh_card : Rsh.card ≤ sharedGates.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRneg_card : Rneg.card ≤ neg.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRoots_le3 : Roots.card ≤ Rout.card + Rsh.card + Rneg.card :=
    (Finset.card_union_le (Rout ∪ Rsh) Rneg).trans
      (Nat.add_le_add_right (Finset.card_union_le Rout Rsh) _)
  have hRoots_card : Roots.card ≤ sharedGates.card + neg.card + 1 := by
    omega
  have hRoots_valid : ∀ r ∈ Roots, validRoot r := by
    intro r hr
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        exact Or.inr ⟨by omega, by omega, by rwa [show C.output - n = C.size - 1 by omega]⟩
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates, gates, Finset.mem_range] at hk
      exact Or.inr ⟨by omega, by omega, by simpa using hk.2⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      have hlt : (gateAt C j).inputs.getD 0 0 < n + j := hback j hj.1.1 _ hmem0
      by_cases hlt_n : (gateAt C j).inputs.getD 0 0 < n
      · exact Or.inl ⟨hlt_n, hj.2.1⟩
      · exact Or.inr ⟨by omega, by omega, fun hnot => hj.2.2 ⟨by omega, by omega, hnot⟩⟩
  have hRoots_fixed : ∀ r ∈ Roots, owner n C r = r := by
    intro r hr
    refine owner_fixed n C ?_
    rintro ⟨hr1, hnot⟩
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        have hz := reads_output_zero n C hback hout
        omega
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates] at hk
      have h2r : 2 ≤ readsOf C (n + k) := hk.1.2
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
      have hpeq : j = parentGate C ((gateAt C j).inputs.getD 0 0) :=
        huniq j (Finset.mem_range.2 hj.1.1) hmem0
      rw [← hpeq] at hnot
      exact hnot hj.1.2
  have howner_mem : ∀ w : ℕ, validRoot w → owner n C w ∈ Roots := by
    intro w
    induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
    | ind d ih =>
      intro hw
      by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
      · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
        have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
        have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
        rw [owner_step n C hback hstep.1 hstep.2]
        exact ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      · rw [owner_fixed n C hstep]
        by_cases hr1 : readsOf C w = 1
        · have hpnot : (gateAt C (parentGate C w)).op = GateOp.not := by
            by_contra hne
            exact hstep ⟨hr1, hne⟩
          obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hr1
          have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
          have hgs := hshape (gateAt C (parentGate C w)) (gateAt_mem_gates C hplt)
          have hlen1 : (gateAt C (parentGate C w)).inputs.length = 1 := by
            rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
            · rcases ho with ho | ho <;> rw [hpnot] at ho <;> cases ho
            · exact hl
          have hweq : (gateAt C (parentGate C w)).inputs.getD 0 0 = w := by
            rw [list_len1_eq _ hlen1] at hpw
            simp only [List.mem_singleton] at hpw
            exact hpw.symm
          have hint : isInternalChild n C w := by
            refine ⟨hr1, ?_⟩
            rintro ⟨hle, _, hnot⟩
            rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
            · omega
            · exact hne hnot
          refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨parentGate C w, ?_, hweq⟩)
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.2 ⟨hpG, hpnot⟩, by rwa [hweq]⟩
        · rcases hw with ⟨_, hr1'⟩ | ⟨hle, hlt, hne⟩
          · exact absurd hr1' hr1
          · by_cases hlast : w - n = C.size - 1
            · have hwout : w = C.output := by omega
              subst hwout
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              dsimp only [Rout]
              have hop : (gateAt C (C.size - 1)).op ≠ GateOp.not := by
                rwa [← hlast]
              simp [hop]
            · have hpos := hused (w - n) hlt (by omega)
              have hge2 : 2 ≤ readsOf C (n + (w - n)) := by
                have heq : n + (w - n) = w := by omega
                rw [heq] at hpos ⊢
                change 0 < readsOf C w at hpos
                omega
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_image.2 ⟨w - n, ?_, by omega⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hge2⟩, hne⟩
  have hpriv_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).privs (buildTree n C r2).privs := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 w (Finset.mem_union_left _ hw1)
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 w (Finset.mem_union_left _ hw2)
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hgates_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).gates (buildTree n C r2).gates := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk1, rfl⟩))
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk2, rfl⟩))
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hpriv_cov : Roots.biUnion (fun r => (buildTree n C r).privs) = once := by
    ext w
    simp only [Finset.mem_biUnion, once, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, hwp⟩
      have hgt := buildTree_good n C hshape hback r
      have hlt := ((mem_privs_iff_lt n C hgt w).1 hwp).2
      have hwr : readsOf C w = 1 := by
        by_cases hweq : w = r
        · subst hweq
          rcases hRoots_valid w hr with ⟨_, hr1⟩ | ⟨hle, _, _⟩
          · exact hr1
          · omega
        · have hroot : (buildTree n C r).root n = r := buildTree_root n C r
          exact ((good_internal_reads hback hout hgt).1 w (Finset.mem_union_left _ hwp)
            (by rwa [hroot])).2.1
      exact ⟨hlt, hwr⟩
    · rintro ⟨hlt, hr1⟩
      have hmemR : owner n C w ∈ Roots := howner_mem w (Or.inl ⟨hlt, hr1⟩)
      refine ⟨owner n C w, hmemR, ?_⟩
      have hw := mem_wires_buildTree_owner n C hback hshape w (Or.inl ⟨hlt, hr1⟩)
      exact (mem_privs_iff_lt n C (buildTree_good n C hshape hback _) w).2 ⟨hw, hlt⟩
  have hsum_marks : ∑ r ∈ Roots, (buildTree n C r).marks ≤ markedReads + neg.card := by
    have h1 : ∑ r ∈ Roots, (buildTree n C r).marks =
        ∑ r ∈ Roots, ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_congr rfl (fun r hr => buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hr))
    rw [h1, ← Finset.sum_biUnion (fun r1 hr1 r2 hr2 hne => hgates_disj r1 hr1 r2 hr2 hne)]
    have hsub_g : Roots.biUnion (fun r => (buildTree n C r).gates) ⊆ gates := by
      intro j hj
      obtain ⟨r, _, hjr⟩ := Finset.mem_biUnion.1 hj
      exact good_gates_sub (buildTree_good n C hshape hback r) hjr
    have hle1 :
        ∑ j ∈ Roots.biUnion (fun r => (buildTree n C r).gates),
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_le_sum_of_subset hsub_g
    let negOnly : Finset ℕ := (neg.filter (fun k => readsOf C (n + k) = 1)).image (fun k => n + k)
    have hterm_le : ∀ j ∈ gates,
        @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
          (gateAt C j).inputs ≤
        @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
          (gateAt C j).inputs +
        @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
          (gateAt C j).inputs := by
      intro j hj
      have hjlt : j < C.size := Finset.mem_range.1 hj
      have hgen : ∀ (l : List ℕ), (∀ u ∈ l, u < n + j) →
          (∀ u ∈ l, 1 ≤ readsOf C u) →
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _)) l ≤
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _)) l +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _)) l := by
        intro l
        induction l with
        | nil => intros; simp
        | cons u ls ih =>
          intro hlt_l hpos_l
          simp only [List.countP_cons]
          have ih' := ih (fun v hv => hlt_l v (List.mem_cons_of_mem u hv))
            (fun v hv => hpos_l v (List.mem_cons_of_mem u hv))
          have hult : u < n + j := hlt_l u (List.mem_cons_self ..)
          have hupos : 1 ≤ readsOf C u := hpos_l u (List.mem_cons_self ..)
          by_cases hni : ¬ isInternalChild n C u
          · have hor : u ∈ shared ∨ u ∈ negOnly := by
              by_cases hr2 : 2 ≤ readsOf C u
              · left
                exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr2⟩
              · right
                have hr1 : readsOf C u = 1 := by omega
                have hnotg : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not := by
                  by_contra h
                  exact hni ⟨hr1, h⟩
                refine Finset.mem_image.2 ⟨u - n, ?_, by omega⟩
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hnotg.2.1, hnotg.2.2⟩, ?_⟩
                have : n + (u - n) = u := by omega
                rwa [this]
            have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = true :=
              @decide_eq_true _ (Classical.propDecidable _) hni
            rw [hd1, if_pos rfl]
            rcases hor with hsh | hno
            · have hd2 : (@decide (u ∈ shared) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hsh
              rw [hd2, if_pos rfl]
              split_ifs <;> omega
            · have hd3 : (@decide (u ∈ negOnly) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hno
              rw [hd3, if_pos rfl]
              split_ifs <;> omega
          · have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = false :=
              @decide_eq_false _ (Classical.propDecidable _) hni
            rw [hd1]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split_ifs <;> omega
      exact hgen (gateAt C j).inputs (fun u hu => hback j hjlt u hu)
        (fun u hu => readsIn_ge_of_mem C hj hu)
    have hle2 :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          (@List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs) :=
      Finset.sum_le_sum hterm_le
    rw [Finset.sum_add_distrib] at hle2
    have hsum_sh :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs = markedReads := by
      simp_rw [list_countP_le_sum_count _ shared]
      rw [Finset.sum_comm]
      rfl
    have hsum_no :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs ≤ neg.card := by
      simp_rw [list_countP_le_sum_count _ negOnly]
      rw [Finset.sum_comm]
      calc ∑ w ∈ negOnly, readsOf C w
          = ∑ _w ∈ negOnly, 1 := by
            refine Finset.sum_congr rfl (fun w hw => ?_)
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
            exact (Finset.mem_filter.1 hk).2
        _ = negOnly.card := by simp
        _ ≤ neg.card := (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    omega
  let Rpure : Finset ℕ := Roots.filter (fun r => (buildTree n C r).marks = 0)
  let Rmark : Finset ℕ := Roots.filter (fun r => 1 ≤ (buildTree n C r).marks)
  have hpart_card : Rpure.card + Rmark.card = Roots.card := by
    have hdisj : Disjoint Rpure Rmark := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Rpure, Rmark, Finset.mem_filter] at hr1 hr2
      omega
    have hunion : Rpure ∪ Rmark = Roots := by
      ext r
      simp only [Rpure, Rmark, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hm : (buildTree n C r).marks = 0
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hroots_strict : 0 < markedReads + neg.card → Rmark.card = 0 →
      Roots.card ≤ sharedGates.card + neg.card := by
    intro hpos hR0
    have hall0 : ∀ r ∈ Roots, (buildTree n C r).marks = 0 := by
      intro r hr
      by_contra hne
      have hmem : r ∈ Rmark := Finset.mem_filter.2 ⟨hr, by omega⟩
      have hcp : 0 < Rmark.card := Finset.card_pos.2 ⟨r, hmem⟩
      omega
    by_cases hneg : neg.Nonempty
    · obtain ⟨j0, hj0⟩ := hneg
      have hj0lt : j0 < C.size := Finset.mem_range.1 (Finset.mem_filter.1 hj0).1
      have hj0not : (gateAt C j0).op = GateOp.not := (Finset.mem_filter.1 hj0).2
      by_cases hlast : j0 = C.size - 1
      · have hRout0 : Rout.card = 0 := by
          dsimp only [Rout]
          rw [← hlast, if_neg (not_not.2 hj0not)]
          simp
        omega
      · by_cases hsh : j0 ∈ sharedGates
        · have hRsh_lt : Rsh.card < sharedGates.card := by
            have hss : sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not) ⊂ sharedGates := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
              have hmem : j0 ∈ sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not) := by
                rwa [heq]
              exact (Finset.mem_filter.1 hmem).2 hj0not
            exact Nat.lt_of_le_of_lt Finset.card_image_le (Finset.card_lt_card hss)
          omega
        · have hposj := hused j0 hj0lt (by omega)
          have hr1j : readsOf C (n + j0) = 1 := by
            change 0 < readsOf C (n + j0) at hposj
            by_contra hne1
            have hge2 : 2 ≤ readsOf C (n + j0) := by omega
            exact hsh (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj0lt, hge2⟩)
          obtain ⟨q, hqG, hqin, _, _⟩ := readsIn_eq_one_unique C (gatesOf C) (n + j0) hr1j
          have hqlt : q < C.size := Finset.mem_range.1 hqG
          by_cases hqnot : (gateAt C q).op = GateOp.not
          · have hqneg : q ∈ neg := Finset.mem_filter.2 ⟨hqG, hqnot⟩
            have hgs := hshape (gateAt C q) (gateAt_mem_gates C hqlt)
            have hlen1 : (gateAt C q).inputs.length = 1 := by
              rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
              · rcases ho with ho | ho <;> rw [hqnot] at ho <;> cases ho
              · exact hl
            have hq0 : (gateAt C q).inputs.getD 0 0 = n + j0 := by
              rw [list_len1_eq _ hlen1] at hqin
              simp only [List.mem_singleton] at hqin
              exact hqin.symm
            have hq_out : ¬ isInternalChild n C ((gateAt C q).inputs.getD 0 0) := by
              rw [hq0]
              rintro ⟨_, h⟩
              exact h ⟨by omega, by omega, by simpa using hj0not⟩
            have hRneg_lt : Rneg.card < neg.card := by
              have hss : neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0)) ⊂ neg := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
                have hmem : q ∈ neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0)) := by
                  rwa [heq]
                exact hq_out (Finset.mem_filter.1 hmem).2
              exact Nat.lt_of_le_of_lt Finset.card_image_le (Finset.card_lt_card hss)
            omega
          · exfalso
            have hvq : validRoot (n + q) := Or.inr ⟨by omega, by omega, by simpa using hqnot⟩
            let r := owner n C (n + q)
            have hrR : r ∈ Roots := howner_mem (n + q) hvq
            have hqw : n + q ∈ (buildTree n C r).wires n :=
              mem_wires_buildTree_owner n C hback hshape (n + q) hvq
            have hqg : q ∈ (buildTree n C r).gates :=
              (mem_gates_iff_ge n C (buildTree_good n C hshape hback r) q).2 hqw
            have hm0 := hall0 r hrR
            rw [buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hrR)] at hm0
            have hcnt0 : @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
                (Classical.propDecidable _)) (gateAt C q).inputs = 0 :=
              Finset.sum_eq_zero_iff.1 hm0 q hqg
            have hni : ¬ isInternalChild n C (n + j0) := by
              rintro ⟨_, h⟩
              exact h ⟨by omega, by omega, by simpa using hj0not⟩
            have hcp : 0 < @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
                (Classical.propDecidable _)) (gateAt C q).inputs :=
              List.countP_pos_iff.2 ⟨n + j0, hqin, by simp [hni]⟩
            omega
    · exfalso
      have hneg0 : neg.card = 0 := Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hneg)
      have hmkpos : 0 < markedReads := by omega
      have hsh_non : shared.Nonempty := by
        by_contra h
        dsimp only [markedReads] at hmkpos
        rw [Finset.not_nonempty_iff_eq_empty.1 h] at hmkpos
        simp at hmkpos
      obtain ⟨w0, hw0⟩ := hsh_non
      have hr2 : 2 ≤ readsIn C (gatesOf C) w0 := (Finset.mem_filter.1 hw0).2
      obtain ⟨q, hqG, hqin⟩ := (readsIn_pos_iff C (gatesOf C) w0).1 (by omega)
      have hqlt : q < C.size := Finset.mem_range.1 hqG
      have hqnot : (gateAt C q).op ≠ GateOp.not := by
        intro h
        exact hneg ⟨q, Finset.mem_filter.2 ⟨hqG, h⟩⟩
      have hvq : validRoot (n + q) := Or.inr ⟨by omega, by omega, by simpa using hqnot⟩
      let r := owner n C (n + q)
      have hrR : r ∈ Roots := howner_mem (n + q) hvq
      have hqw : n + q ∈ (buildTree n C r).wires n :=
        mem_wires_buildTree_owner n C hback hshape (n + q) hvq
      have hqg : q ∈ (buildTree n C r).gates :=
        (mem_gates_iff_ge n C (buildTree_good n C hshape hback r) q).2 hqw
      have hm0 := hall0 r hrR
      rw [buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hrR)] at hm0
      have hcnt0 : @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
          (Classical.propDecidable _)) (gateAt C q).inputs = 0 :=
        Finset.sum_eq_zero_iff.1 hm0 q hqg
      have hni : ¬ isInternalChild n C w0 := by
        rintro ⟨hr1, _⟩
        change readsIn C (gatesOf C) w0 = 1 at hr1
        omega
      have hcp : 0 < @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
          (Classical.propDecidable _)) (gateAt C q).inputs :=
        List.countP_pos_iff.2 ⟨w0, hqin, by simp [hni]⟩
      omega
  let pureFun : ℕ → List (Finset ℕ) := fun r =>
    if (buildTree n C r).privs.Nonempty then [(buildTree n C r).privs] else []
  let pure : List (Finset ℕ) := Rpure.toList.flatMap pureFun
  have hpure_col := list_flatMap_collect Rpure.toList pureFun (fun r => (buildTree n C r).privs)
    (Finset.nodup_toList Rpure)
    (fun r1 h1 r2 h2 hne => hpriv_disj r1 (Finset.mem_filter.1 (Finset.mem_toList.1 h1)).1
      r2 (Finset.mem_filter.1 (Finset.mem_toList.1 h2)).1 hne)
    (fun r _ S hS => by
      dsimp only [pureFun] at hS
      split_ifs at hS
      · rw [List.mem_singleton.1 hS]
      · simp at hS)
    (fun r _ => by
      dsimp only [pureFun]
      split_ifs <;> simp)
    (fun r _ => by
      dsimp only [pureFun]
      split_ifs with hnp
      · simp
      · simp [Finset.not_nonempty_iff_eq_empty.1 hnp])
  have hpure_len : pure.length ≤ Rpure.card := by
    rw [hpure_col.2.2, Finset.toList_toFinset]
    calc ∑ r ∈ Rpure, (pureFun r).length
        ≤ ∑ _r ∈ Rpure, 1 := Finset.sum_le_sum (fun r _ => by dsimp only [pureFun]; split_ifs <;> simp)
      _ = Rpure.card := by simp
  have hpure_prop : ∀ S ∈ pure, S.Nonempty ∧ IsTree n C S ∅ := by
    intro S hS
    obtain ⟨r, hr, hSr⟩ := List.mem_flatMap.1 hS
    have hr' := Finset.mem_filter.1 (Finset.mem_toList.1 hr)
    dsimp only [pureFun] at hSr
    split_ifs at hSr with hnp
    · rw [List.mem_singleton.1 hSr]
      exact ⟨hnp, good_markFree_isTree hback hout (buildTree_good n C hshape hback r) hr'.2⟩
    · simp at hSr
  let chainFun : ℕ → List (Finset ℕ) := fun r =>
    if h : 1 ≤ (buildTree n C r).marks then
      Classical.choose (marked_tree_chains hback hout (buildTree_good n C hshape hback r) h)
    else []
  have hchain_spec : ∀ r ∈ Rmark,
      (chainFun r).length + 1 ≤ 2 * (buildTree n C r).marks ∧
      (∀ S ∈ chainFun r, S.Nonempty ∧ S ⊆ (buildTree n C r).privs ∧ ∃ b, IsTree n C S {b}) ∧
      (chainFun r).Pairwise Disjoint ∧
      (chainFun r).toFinset.biUnion (fun S => S) = (buildTree n C r).privs := by
    intro r hr
    have hm : 1 ≤ (buildTree n C r).marks := (Finset.mem_filter.1 hr).2
    have hdef : chainFun r =
        Classical.choose (marked_tree_chains hback hout (buildTree_good n C hshape hback r) hm) := by
      dsimp only [chainFun]
      simp only [hm, ↓reduceDIte]
    rw [hdef]
    exact Classical.choose_spec (marked_tree_chains hback hout (buildTree_good n C hshape hback r) hm)
  let chains : List (Finset ℕ) := Rmark.toList.flatMap chainFun
  have hchains_col := list_flatMap_collect Rmark.toList chainFun (fun r => (buildTree n C r).privs)
    (Finset.nodup_toList Rmark)
    (fun r1 h1 r2 h2 hne => hpriv_disj r1 (Finset.mem_filter.1 (Finset.mem_toList.1 h1)).1
      r2 (Finset.mem_filter.1 (Finset.mem_toList.1 h2)).1 hne)
    (fun r hr S hS => (hchain_spec r (Finset.mem_toList.1 hr)).2.1 S hS |>.2.1)
    (fun r hr => (hchain_spec r (Finset.mem_toList.1 hr)).2.2.1)
    (fun r hr => (hchain_spec r (Finset.mem_toList.1 hr)).2.2.2)
  have hchains_len : chains.length + Rmark.card ≤ 2 * (markedReads + neg.card) := by
    rw [hchains_col.2.2, Finset.toList_toFinset]
    have h1 : (∑ r ∈ Rmark, (chainFun r).length) + Rmark.card =
        ∑ r ∈ Rmark, ((chainFun r).length + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [h1]
    calc ∑ r ∈ Rmark, ((chainFun r).length + 1)
        ≤ ∑ r ∈ Rmark, 2 * (buildTree n C r).marks :=
          Finset.sum_le_sum (fun r hr => (hchain_spec r hr).1)
      _ = 2 * ∑ r ∈ Rmark, (buildTree n C r).marks := by rw [← Finset.mul_sum]
      _ ≤ 2 * ∑ r ∈ Roots, (buildTree n C r).marks :=
          Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ ≤ 2 * (markedReads + neg.card) := Nat.mul_le_mul_left 2 hsum_marks
  have hchains_prop : ∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, IsTree n C S {b} := by
    intro S hS
    obtain ⟨r, hr, hSr⟩ := List.mem_flatMap.1 hS
    have hs := (hchain_spec r (Finset.mem_toList.1 hr)).2.1 S hSr
    exact ⟨hs.1, hs.2.2⟩
  let markedComponents : ℕ := if 0 < markedReads + neg.card ∧ Rmark.card = 0 then 1 else Rmark.card
  refine ⟨pure, chains, markedComponents, ?_, ?_, ?_, ?_, ?_, hpure_prop, hchains_prop⟩
  · dsimp only [markedComponents]
    split_ifs with h
    · have hst := hroots_strict h.1 h.2
      omega
    · omega
  · dsimp only [markedComponents]
    split_ifs with h
    · have hR0 : Rmark = ∅ := Finset.card_eq_zero.1 h.2
      have hc0 : chains.length = 0 := by
        simp [chains, hR0]
      omega
    · exact hchains_len
  · intro hpos
    dsimp only [markedComponents]
    split_ifs with h
    · omega
    · by_contra hle
      exact h ⟨hpos, by omega⟩
  · rw [List.pairwise_append]
    refine ⟨hpure_col.1, hchains_col.1, fun S1 h1 S2 h2 => ?_⟩
    obtain ⟨r1, hr1, hS1⟩ := List.mem_flatMap.1 h1
    obtain ⟨r2, hr2, hS2⟩ := List.mem_flatMap.1 h2
    have hr1' := Finset.mem_filter.1 (Finset.mem_toList.1 hr1)
    have hr2' := Finset.mem_filter.1 (Finset.mem_toList.1 hr2)
    have hne : r1 ≠ r2 := by
      intro heq
      rw [heq] at hr1'
      omega
    have hsub1 : S1 ⊆ (buildTree n C r1).privs := by
      dsimp only [pureFun] at hS1
      split_ifs at hS1
      · rw [List.mem_singleton.1 hS1]
      · simp at hS1
    have hsub2 : S2 ⊆ (buildTree n C r2).privs :=
      ((hchain_spec r2 (Finset.mem_toList.1 hr2)).2.1 S2 hS2).2.1
    exact Disjoint.mono hsub1 hsub2 (hpriv_disj r1 hr1'.1 r2 hr2'.1 hne)
  · rw [List.toFinset_append, Finset.union_biUnion, hpure_col.2.1, hchains_col.2.1,
      Finset.toList_toFinset, Finset.toList_toFinset, ← Finset.union_biUnion]
    have hunion : Rpure ∪ Rmark = Roots := by
      ext r
      simp only [Rpure, Rmark, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hm : (buildTree n C r).marks = 0
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [hunion, hpriv_cov]

end PEqualNP.Outside.L_meta_25644_aux

theorem PEqualNP.Outside.L_meta_25644 :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro n C gates gate reads neg shared sharedGates markedReads once tree hshape hback hsz hout hused
  exact PEqualNP.Outside.L_meta_25644_aux.main n C hshape hback hsz hout hused
