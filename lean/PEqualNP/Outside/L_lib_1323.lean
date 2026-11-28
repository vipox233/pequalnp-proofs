import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1323

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def WS (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stepW x

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = WS C.gates x := rfl

theorem WS_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    WS (gs ++ [g]) x = stepW (WS gs x) g := by
  simp [WS, List.foldl_append]

theorem foldl_ext (hs : List Gate) : ∀ w : List Bool, ∃ t, hs.foldl stepW w = w ++ t := by
  induction hs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g hs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht]; simp [stepW]

theorem WS_len (gs : List Gate) (x : List Bool) : (WS gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [WS]
  | append_singleton gs g ih => rw [WS_snoc]; simp [stepW, ih]; omega

theorem WS_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (WS (gs ++ hs) x).getD i false = (WS gs x).getD i false := by
  have : WS (gs ++ hs) x = hs.foldl stepW (WS gs x) := by simp [WS, List.foldl_append]
  rw [this]
  obtain ⟨t, ht⟩ := foldl_ext hs (WS gs x)
  rw [ht]
  have hl := WS_len gs x
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem WS_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (WS gs x).getD i false = x.getD i false := by
  have := WS_prefix [] gs x i (by simpa using hi)
  simpa [WS] using this

theorem WS_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (WS (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (WS gs x).getD i false) := by
  rw [WS_snoc]
  have hl := WS_len gs x
  simp only [stepW, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp [hl]

theorem WS_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hR : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (WS gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (WS gs x).getD i false) := by
  have hsplit : gs = (gs.take j ++ [gs[j]]) ++ gs.drop (j+1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  have hlt : (gs.take j).length = j := by simp; omega
  conv_lhs => rw [hsplit]
  rw [WS_prefix _ _ _ _ (by simp; omega)]
  have := WS_last (gs.take j) gs[j] x
  rw [hlt] at this
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h1 := hR i hi
  conv_rhs => rw [hsplit]
  rw [WS_prefix _ _ _ _ (by simp; omega), WS_prefix _ _ _ _ (by omega)]

def nc (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_append (gs hs : List Gate) : nc (gs ++ hs) = nc gs + nc hs := by
  simp [nc, PEqualNP.NotBracket.notCount, List.filter_append]

theorem nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem nc_le (gs : List Gate) : nc gs ≤ gs.length := by
  simp only [nc, PEqualNP.NotBracket.notCount]
  exact List.length_filter_le _ _

def chg (b : ℕ → Bool) (L : ℕ) : Finset ℕ := (Finset.range L).filter (fun s => b s ≠ b (s+1))
def fal (b : ℕ → Bool) (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun s => b s = true ∧ b (s+1) = false)
def ris (b : ℕ → Bool) (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun s => b s = false ∧ b (s+1) = true)

theorem ris_fal_eq (b : ℕ → Bool) (L : ℕ) :
    (ris b L).card + (if b 0 then 1 else 0) = (fal b L).card + (if b L then 1 else 0) := by
  induction L with
  | zero => simp [ris, fal]
  | succ L ih =>
    simp only [ris, fal, Finset.range_add_one, Finset.filter_insert] at ih ⊢
    have hn1 : L ∉ (Finset.range L).filter (fun s => b s = false ∧ b (s+1) = true) := by simp
    have hn2 : L ∉ (Finset.range L).filter (fun s => b s = true ∧ b (s+1) = false) := by simp
    cases h1 : b L <;> cases h2 : b (L+1) <;> simp_all [Finset.card_insert_of_notMem] <;> omega

theorem ris_le (b : ℕ → Bool) (L : ℕ) : (ris b L).card ≤ (fal b L).card + 1 := by
  have := ris_fal_eq b L
  split_ifs at this <;> omega

theorem chg_le (b : ℕ → Bool) (L : ℕ) : (chg b L).card ≤ (ris b L).card + (fal b L).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro s hs
  simp only [chg, ris, fal, Finset.mem_filter, Finset.mem_union] at hs ⊢
  cases h1 : b s <;> cases h2 : b (s+1) <;> simp_all

theorem fal_le (b : ℕ → Bool) (L : ℕ) : (fal b L).card ≤ L := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem ris_le_L (b : ℕ → Bool) (L : ℕ) : (ris b L).card ≤ L := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem mono_fal (b : ℕ → Bool) (L : ℕ) (hb : ∀ s t, s ≤ t → b s = true → b t = true) :
    fal b L = ∅ := by
  ext s
  simp only [fal, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ h1 h2
  have := hb s (s+1) (by omega) h1
  simp_all

theorem mono_chg (b : ℕ → Bool) (L : ℕ) (hb : ∀ s t, s ≤ t → b s = true → b t = true) :
    (chg b L).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s hs t ht
  simp only [chg, Finset.mem_filter] at hs ht
  have k1 : b s = false ∧ b (s+1) = true := by
    cases h1 : b s <;> cases h2 : b (s+1) <;> simp_all
    exact absurd (hb s (s+1) (by omega) h1) (by simp [h2])
  have k2 : b t = false ∧ b (t+1) = true := by
    cases h1 : b t <;> cases h2 : b (t+1) <;> simp_all
    exact absurd (hb t (t+1) (by omega) h1) (by simp [h2])
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hb (s+1) t (by omega) k1.2; simp_all
  · have := hb (t+1) s (by omega) k2.2; simp_all

theorem not_chg (b : ℕ → Bool) (L : ℕ) : chg (fun s => !b s) L = chg b L := by
  ext s; simp [chg]

theorem not_fal (b : ℕ → Bool) (L : ℕ) : fal (fun s => !b s) L = ris b L := by
  ext s; simp [fal, ris]

theorem andor_chg (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (b : ℕ → Bool) (c : ℕ → ℕ → Bool) (L : ℕ) (hb : ∀ s, b s = op.eval (l.map fun x => c x s)) :
    chg b L ⊆ l.toFinset.biUnion (fun x => chg (c x) L) := by
  intro s hs
  simp only [chg, Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset] at hs ⊢
  by_contra hcon
  push Not at hcon
  apply hs.2
  rw [hb, hb]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hcon x hx hs.1

theorem andor_fal (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (b : ℕ → Bool) (c : ℕ → ℕ → Bool) (L : ℕ) (hb : ∀ s, b s = op.eval (l.map fun x => c x s)) :
    fal b L ⊆ l.toFinset.biUnion (fun x => fal (c x) L) := by
  intro s hs
  simp only [fal, Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset] at hs ⊢
  obtain ⟨hsL, h1, h2⟩ := hs
  rw [hb] at h1 h2
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.all_eq_false, List.mem_map] at h1 h2
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := h2
    exact ⟨x, hx, hsL, by simpa using h1 _ ⟨x, hx, rfl⟩, by simpa using hy⟩
  · simp only [GateOp.eval, List.any_eq_true, List.any_eq_false, List.mem_map] at h1 h2
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := h1
    refine ⟨x, hx, hsL, by simpa using hy, ?_⟩
    have := h2 _ ⟨x, hx, rfl⟩
    simpa using this

def inp (n : ℕ) (S : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j ∈ S)) ++ [false, true]

theorem inp_len (n : ℕ) (S : Finset (Fin n)) : (inp n S).length = n + 2 := by simp [inp]

theorem inp_fin (n : ℕ) (S : Finset (Fin n)) (j : Fin n) : (inp n S).getD j false = decide (j ∈ S) := by
  simp only [inp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp)]
  simp

theorem inp_mono (n : ℕ) (S T : Finset (Fin n)) (hST : S ⊆ T) (i : ℕ)
    (h : (inp n S).getD i false = true) : (inp n T).getD i false = true := by
  by_cases hi : i < n
  · have := inp_fin n S ⟨i, hi⟩
    have h2 := inp_fin n T ⟨i, hi⟩
    simp only at this h2
    rw [this] at h; rw [h2]
    simp only [decide_eq_true_eq] at h ⊢
    exact hST h
  · simp only [inp, List.getD_eq_getElem?_getD] at h ⊢
    rw [List.getElem?_append_right (by simp; omega)] at h ⊢
    simpa using h

def val (n : ℕ) (gs : List Gate) (X : ℕ → Finset (Fin n)) (g s : ℕ) : Bool :=
  (WS gs (inp n (X s))).getD g false

theorem val_gate (n : ℕ) (gs : List Gate) (X : ℕ → Finset (Fin n))
    (hR : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + 2 + j) (j : ℕ) (hj : j < gs.length)
    (s : ℕ) :
    val n gs X (n + 2 + j) s = gs[j].op.eval (gs[j].inputs.map fun i => val n gs X i s) := by
  have := WS_gate gs (inp n (X s)) j hj (by rw [inp_len]; exact hR j hj)
  rw [inp_len] at this
  exact this

theorem val_input (n : ℕ) (gs : List Gate) (X : ℕ → Finset (Fin n)) (hX : Monotone X) (i : ℕ)
    (hi : i < n + 2) : ∀ s t, s ≤ t → val n gs X i s = true → val n gs X i t = true := by
  intro s t hst h
  unfold val at *
  rw [WS_input _ _ _ (by rw [inp_len]; exact hi)] at h ⊢
  exact inp_mono n _ _ (hX hst) i h

def pc (gs : List Gate) : ℕ := gs.length - nc gs

theorem nc_single (g : Gate) (h : g.op = GateOp.not) : nc [g] = 1 := by
  obtain ⟨o, l⟩ := g; simp only at h; subst h; exact nc_not l

theorem nc_single' (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) : nc [g] = 0 := by
  obtain ⟨o, l⟩ := g; simp only at h
  rcases h with h | h <;> subst h
  · exact nc_and l
  · exact nc_or l

theorem pc_snoc (gs : List Gate) (g : Gate) : pc (gs ++ [g]) + nc [g] = pc gs + 1 := by
  have h1 := nc_le gs
  have h2 := nc_append gs [g]
  have h3 : nc [g] ≤ 1 := by simpa using nc_le [g]
  simp only [pc, List.length_append, List.length_singleton]
  omega

theorem sum_le_card_biUnion (W : Finset ℕ) (F : ℕ → Finset ℕ) (h : ∀ g ∈ W, (F g).card ≤ 1) :
    (W.biUnion F).card ≤ W.card := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ g ∈ W, (F g).card ≤ ∑ _g ∈ W, 1 := Finset.sum_le_sum h
    _ = W.card := by simp

theorem core (n : ℕ) (gs : List Gate) (X : ℕ → Finset (Fin n)) (L : ℕ)
    (hR : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + 2 + j)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : Monotone X) (K : ℕ) (hK : L ≤ K) :
    ∀ s', s' ≤ gs.length → ∀ W : Finset ℕ, (∀ g ∈ W, g < n + 2 + s') →
      ∑ g ∈ W, (fal (val n gs X g) L).card +
        K * (W.biUnion (fun g => chg (val n gs X g) L)).card
        ≤ nc (gs.take s') + K * (W.card + pc (gs.take s')) := by
  intro s'
  induction s' with
  | zero =>
    intro _ W hW
    have h1 : ∀ g ∈ W, fal (val n gs X g) L = ∅ := fun g hg =>
      mono_fal _ L (val_input n gs X hX g (by have := hW g hg; omega))
    have h2 : ∀ g ∈ W, (chg (val n gs X g) L).card ≤ 1 := fun g hg =>
      mono_chg _ L (val_input n gs X hX g (by have := hW g hg; omega))
    rw [Finset.sum_eq_zero (fun g hg => by rw [h1 g hg]; rfl)]
    have h3 := sum_le_card_biUnion W _ h2
    have h4 := Nat.mul_le_mul_left K h3
    have h5 : K * W.card ≤ K * (W.card + pc (List.take 0 gs)) := Nat.mul_le_mul_left K (by omega)
    omega
  | succ s' ih =>
    intro hs W hW
    have hlt : s' < gs.length := by omega
    have htake : gs.take (s'+1) = gs.take s' ++ [gs[s']] := List.take_succ_eq_append_getElem hlt
    have hpc := pc_snoc (gs.take s') gs[s']
    have hnc := nc_append (gs.take s') [gs[s']]
    rw [htake]
    rw [hnc]
    by_cases hm : n + 2 + s' ∈ W
    swap
    · have := ih (by omega) W (fun g hg => by
        have h1 := hW g hg
        have h2 : g ≠ n + 2 + s' := fun h => hm (h ▸ hg)
        omega)
      have h3 : nc [gs[s']] ≤ 1 := by simpa using nc_le [gs[s']]
      rcases (show nc [gs[s']] = 0 ∨ nc [gs[s']] = 1 by omega) with hc | hc
      · rw [hc] at hpc ⊢
        have : pc (List.take s' gs ++ [gs[s']]) = pc (List.take s' gs) + 1 := by omega
        rw [this]
        have := Nat.mul_le_mul_left K (show W.card + pc (List.take s' gs) ≤
          W.card + (pc (List.take s' gs) + 1) by omega)
        omega
      · rw [hc] at hpc ⊢
        have : pc (List.take s' gs ++ [gs[s']]) = pc (List.take s' gs) := by omega
        rw [this]
        omega
    · set m := n + 2 + s' with hmdef
      set A := W.erase m with hAdef
      have hWA : W = insert m A := (Finset.insert_erase hm).symm
      have hmA : m ∉ A := Finset.notMem_erase m W
      have hA : ∀ g ∈ A, g < n + 2 + s' := by
        intro g hg
        have h1 := hW g (Finset.mem_of_mem_erase hg)
        have h2 := Finset.ne_of_mem_erase hg
        omega
      have hin : ∀ i ∈ gs[s'].inputs, i < n + 2 + s' := hR s' hlt
      have hg := val_gate n gs X hR s' hlt
      obtain ⟨hop, hlen⟩ := hF gs[s'] (List.getElem_mem hlt)
      rw [hWA, Finset.sum_insert hmA, Finset.biUnion_insert, Finset.card_insert_of_notMem hmA]
      have hKL : ∀ b, (fal b L).card ≤ K := fun b => (fal_le b L).trans hK
      rcases hop with hop | hop | hop
      ·
        have hc := nc_single' gs[s'] (Or.inl hop)
        rw [hc] at hpc ⊢
        have hpc' : pc (List.take s' gs ++ [gs[s']]) = pc (List.take s' gs) + 1 := by omega
        rw [hpc', Nat.add_zero]
        have hB : gs[s'].inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hlen
        have hBlt : ∀ g ∈ gs[s'].inputs.toFinset, g < n + 2 + s' :=
          fun g hg => hin g (List.mem_toFinset.mp hg)
        have hchm := andor_chg gs[s'].op (Or.inl hop) gs[s'].inputs (val n gs X m)
          (fun x s => val n gs X x s) L hg
        have hfam := andor_fal gs[s'].op (Or.inl hop) gs[s'].inputs (val n gs X m)
          (fun x s => val n gs X x s) L hg
        have := ih (by omega) (A ∪ gs[s'].inputs.toFinset) (by
          intro g hg
          rcases Finset.mem_union.mp hg with h | h
          · exact hA g h
          · exact hBlt g h)
        have hsubU : chg (val n gs X m) L ∪ A.biUnion (fun g => chg (val n gs X g) L) ⊆
            (A ∪ gs[s'].inputs.toFinset).biUnion (fun g => chg (val n gs X g) L) := by
          apply Finset.union_subset
          · exact hchm.trans (Finset.biUnion_subset_biUnion_of_subset_left _
              Finset.subset_union_right)
          · exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
        have hKU := Nat.mul_le_mul_left K (Finset.card_le_card hsubU)
        have hU : A ∪ gs[s'].inputs.toFinset = A ∪ (gs[s'].inputs.toFinset \ A) := by
          simp
        have hdisj : Disjoint A (gs[s'].inputs.toFinset \ A) := Finset.disjoint_sdiff
        rw [hU, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj] at this
        rw [hU] at hKU
        have e1 : K * (A.card + 1 + (pc (List.take s' gs) + 1)) =
            K * A.card + K * pc (List.take s' gs) + 2 * K := by ring
        have e2 : K * (A.card + (gs[s'].inputs.toFinset \ A).card + pc (List.take s' gs)) =
            K * A.card + K * (gs[s'].inputs.toFinset \ A).card + K * pc (List.take s' gs) := by
          ring
        by_cases hBA : gs[s'].inputs.toFinset \ A = gs[s'].inputs.toFinset
        · have es : ∑ g ∈ gs[s'].inputs.toFinset \ A, (fal (val n gs X g) L).card =
              ∑ g ∈ gs[s'].inputs.toFinset, (fal (val n gs X g) L).card := by rw [hBA]
          have f1 : (fal (val n gs X m) L).card ≤ ∑ g ∈ gs[s'].inputs.toFinset,
              (fal (val n gs X g) L).card :=
            (Finset.card_le_card hfam).trans Finset.card_biUnion_le
          have f2 := Nat.mul_le_mul_left K (show (gs[s'].inputs.toFinset \ A).card ≤ 2 by
            rw [hBA]; exact hB)
          omega
        · have hlt2 : (gs[s'].inputs.toFinset \ A).card < gs[s'].inputs.toFinset.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, hBA⟩)
          have f2 := Nat.mul_le_mul_left K (show (gs[s'].inputs.toFinset \ A).card ≤ 1 by omega)
          have f1 := hKL (val n gs X m)
          omega

      ·
        have hc := nc_single' gs[s'] (Or.inr hop)
        rw [hc] at hpc ⊢
        have hpc' : pc (List.take s' gs ++ [gs[s']]) = pc (List.take s' gs) + 1 := by omega
        rw [hpc', Nat.add_zero]
        have hB : gs[s'].inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hlen
        have hBlt : ∀ g ∈ gs[s'].inputs.toFinset, g < n + 2 + s' :=
          fun g hg => hin g (List.mem_toFinset.mp hg)
        have hchm := andor_chg gs[s'].op (Or.inr hop) gs[s'].inputs (val n gs X m)
          (fun x s => val n gs X x s) L hg
        have hfam := andor_fal gs[s'].op (Or.inr hop) gs[s'].inputs (val n gs X m)
          (fun x s => val n gs X x s) L hg
        have := ih (by omega) (A ∪ gs[s'].inputs.toFinset) (by
          intro g hg
          rcases Finset.mem_union.mp hg with h | h
          · exact hA g h
          · exact hBlt g h)
        have hsubU : chg (val n gs X m) L ∪ A.biUnion (fun g => chg (val n gs X g) L) ⊆
            (A ∪ gs[s'].inputs.toFinset).biUnion (fun g => chg (val n gs X g) L) := by
          apply Finset.union_subset
          · exact hchm.trans (Finset.biUnion_subset_biUnion_of_subset_left _
              Finset.subset_union_right)
          · exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
        have hKU := Nat.mul_le_mul_left K (Finset.card_le_card hsubU)
        have hU : A ∪ gs[s'].inputs.toFinset = A ∪ (gs[s'].inputs.toFinset \ A) := by
          simp
        have hdisj : Disjoint A (gs[s'].inputs.toFinset \ A) := Finset.disjoint_sdiff
        rw [hU, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj] at this
        rw [hU] at hKU
        have e1 : K * (A.card + 1 + (pc (List.take s' gs) + 1)) =
            K * A.card + K * pc (List.take s' gs) + 2 * K := by ring
        have e2 : K * (A.card + (gs[s'].inputs.toFinset \ A).card + pc (List.take s' gs)) =
            K * A.card + K * (gs[s'].inputs.toFinset \ A).card + K * pc (List.take s' gs) := by
          ring
        by_cases hBA : gs[s'].inputs.toFinset \ A = gs[s'].inputs.toFinset
        · have es : ∑ g ∈ gs[s'].inputs.toFinset \ A, (fal (val n gs X g) L).card =
              ∑ g ∈ gs[s'].inputs.toFinset, (fal (val n gs X g) L).card := by rw [hBA]
          have f1 : (fal (val n gs X m) L).card ≤ ∑ g ∈ gs[s'].inputs.toFinset,
              (fal (val n gs X g) L).card :=
            (Finset.card_le_card hfam).trans Finset.card_biUnion_le
          have f2 := Nat.mul_le_mul_left K (show (gs[s'].inputs.toFinset \ A).card ≤ 2 by
            rw [hBA]; exact hB)
          omega
        · have hlt2 : (gs[s'].inputs.toFinset \ A).card < gs[s'].inputs.toFinset.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, hBA⟩)
          have f2 := Nat.mul_le_mul_left K (show (gs[s'].inputs.toFinset \ A).card ≤ 1 by omega)
          have f1 := hKL (val n gs X m)
          omega

      ·
        have hc := nc_single gs[s'] hop
        rw [hc] at hpc ⊢
        have hpc' : pc (List.take s' gs ++ [gs[s']]) = pc (List.take s' gs) := by omega
        rw [hpc']
        cases hl : gs[s'].inputs with
        | nil =>
          have hv : ∀ s, val n gs X m s = true := by
            intro s; rw [hg s, hop, hl]; rfl
          have hf : fal (val n gs X m) L = ∅ := mono_fal _ L (fun s t _ _ => hv t)
          have hch : chg (val n gs X m) L = ∅ := by
            ext s; simp [chg, hv]
          rw [hf, hch, Finset.empty_union, Finset.card_empty]
          have := ih (by omega) A hA
          have e1 : K * (A.card + 1 + pc (List.take s' gs)) =
              K * (A.card + pc (List.take s' gs)) + K := by ring
          omega
        | cons a rest =>
          have hv : ∀ s, val n gs X m s = !(val n gs X a s) := by
            intro s; rw [hg s, hop, hl]; rfl
          have hvf : val n gs X m = fun s => !(val n gs X a s) := funext hv
          have ha : a < n + 2 + s' := hin a (by rw [hl]; simp)
          rw [hvf, not_fal, not_chg]
          by_cases haA : a ∈ A
          · have hsub : chg (val n gs X a) L ⊆ A.biUnion (fun g => chg (val n gs X g) L) :=
              Finset.subset_biUnion_of_mem (fun g => chg (val n gs X g) L) haA
            rw [Finset.union_eq_right.mpr hsub]
            have := ih (by omega) A hA
            have h1 := (ris_le_L (val n gs X a) L).trans hK
            have e1 : K * (A.card + 1 + pc (List.take s' gs)) =
                K * (A.card + pc (List.take s' gs)) + K := by ring
            omega
          · have := ih (by omega) (insert a A) (by
              intro g hg; rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact ha
              · exact hA g hg)
            rw [Finset.sum_insert haA, Finset.biUnion_insert, Finset.card_insert_of_notMem haA] at this
            have h1 := ris_le (val n gs X a) L
            omega

theorem sum_div2 {α : Type*} (S : Finset α) (m : α → ℕ) :
    ∑ a ∈ S, m a / 2 ≤ (∑ a ∈ S, m a) / 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    omega

def chainX (n k : ℕ) (u v : Fin k → Finset (Fin n)) (E : Fin k → Finset (Fin n)) (s : ℕ) :
    Finset (Fin n) :=
  if h : s / 2 < k then (if s % 2 = 0 then u ⟨s/2, h⟩ ∩ v ⟨s/2, h⟩ else E ⟨s/2, h⟩)
  else Finset.univ

theorem chainX_mono (n k : ℕ) (u v : Fin k → Finset (Fin n)) (E : Fin k → Finset (Fin n))
    (hE : ∀ i, E i = u i ∨ E i = v i)
    (hc : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j) : Monotone (chainX n k u v E) := by
  apply monotone_nat_of_le_succ
  intro s
  show chainX n k u v E s ⊆ chainX n k u v E (s+1)
  unfold chainX
  by_cases h1 : s / 2 < k
  · rw [dif_pos h1]
    rcases Nat.mod_two_eq_zero_or_one s with h2 | h2
    · have e : (s+1)/2 = s/2 := by omega
      have h3 : (s+1)/2 < k := by omega
      rw [dif_pos h3, if_pos h2, if_neg (by omega)]
      have : (⟨(s+1)/2, h3⟩ : Fin k) = ⟨s/2, h1⟩ := Fin.ext e
      rw [this]
      rcases hE ⟨s/2, h1⟩ with h | h <;> rw [h]
      · exact Finset.inter_subset_left
      · exact Finset.inter_subset_right
    · rw [if_neg (by omega)]
      by_cases h3 : (s+1)/2 < k
      · rw [dif_pos h3, if_pos (by omega)]
        have hl : (⟨s/2, h1⟩ : Fin k) < ⟨(s+1)/2, h3⟩ := by
          rw [Fin.lt_def]; simp only; omega
        have := hc _ _ hl
        rcases hE ⟨s/2, h1⟩ with h | h <;> rw [h]
        · exact Finset.subset_union_left.trans this
        · exact Finset.subset_union_right.trans this
      · rw [dif_neg h3]; exact Finset.subset_univ _
  · rw [dif_neg h1, dif_neg (by omega)]

theorem lower (n t k : ℕ) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t)
    (hc : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j)
    (C : Circuit) (tap : Fin t → ℕ) (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C)
    (htap : ∀ a, tap a < n + 2 + C.size)
    (hval : ∀ i, (WS C.gates (inp n (u i))).getD (tap (name i)) false = false ∧
      (WS C.gates (inp n (v i))).getD (tap (name i)) false = true) :
    k ≤ C.size - PEqualNP.NotBracket.notCount C + (Finset.univ.image name).card ∧
    (C.size - PEqualNP.NotBracket.notCount C = k - (Finset.univ.image name).card →
      ∑ a ∈ Finset.univ.image name, (Finset.univ.filter (fun i => name i = a)).card / 2
        ≤ PEqualNP.NotBracket.notCount C) := by
  classical
  set gs := C.gates with hgs
  let wv : Fin k → Finset (Fin n) → Bool := fun i S => (WS gs (inp n S)).getD (tap (name i)) false
  let E : Fin k → Finset (Fin n) := fun i =>
    if wv i (u i ∩ v i) = wv i (u i) then v i else u i
  have hE : ∀ i, E i = u i ∨ E i = v i := by
    intro i; simp only [E]; split_ifs <;> simp
  have hwE : ∀ i, wv i (u i ∩ v i) ≠ wv i (E i) := by
    intro i
    have := hval i
    simp only [E]
    split_ifs with h
    · rw [h]; simp only [wv]; rw [this.1, this.2]; simp
    · exact h
  set X := chainX n k u v E with hXdef
  have hX : Monotone X := chainX_mono n k u v E hE hc
  set L := 2 * k with hL
  have hRd : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + 2 + j := by
    intro j hj i hi
    apply hR j hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    exact hi
  have hFd : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hF g hg
    simpa using this
  set names := Finset.univ.image name with hnames
  set W := names.image tap with hW
  have hWlt : ∀ g ∈ W, g < n + 2 + gs.length := by
    intro g hg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
    exact htap a
  have hrec : ∀ i : Fin k, 2 * i.val ∈ chg (val n gs X (tap (name i))) L := by
    intro i
    simp only [chg, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have e1 : X (2 * i.val) = u i ∩ v i := by
      simp only [hXdef, chainX]
      rw [dif_pos (by omega), if_pos (by omega)]
      congr 2 <;> exact Fin.ext (by simp)
    have e2 : X (2 * i.val + 1) = E i := by
      simp only [hXdef, chainX]
      rw [dif_pos (by omega), if_neg (by omega)]
      congr 1; exact Fin.ext (by simp; omega)
    simp only [val]
    rw [e1, e2]
    exact hwE i
  have hcoreL := core n gs X L hRd hFd hX
  have htk : gs.take gs.length = gs := List.take_length
  have hncC : PEqualNP.NotBracket.notCount C = nc gs := rfl
  have hsize : C.size = gs.length := rfl
  have hpc : pc gs = C.size - PEqualNP.NotBracket.notCount C := by
    rw [hncC, hsize]; rfl

  have hRU : (Finset.univ.image (fun i : Fin k => 2 * i.val)) ⊆
      W.biUnion (fun g => chg (val n gs X g) L) := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_biUnion.mpr ⟨tap (name i), Finset.mem_image.mpr
      ⟨name i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩, hrec i⟩
  have hRc : (Finset.univ.image (fun i : Fin k => 2 * i.val)).card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h; exact Fin.ext (by simp at h; omega)
  have hkU := Finset.card_le_card hRU
  rw [hRc] at hkU
  have hWh : W.card ≤ names.card := Finset.card_image_le
  have hhk : names.card ≤ k := by
    simpa using (Finset.card_image_le : (Finset.univ.image name).card ≤ (Finset.univ : Finset (Fin k)).card)
  constructor
  · have h1 := hcoreL (L + nc gs + 1) (by omega) gs.length le_rfl W hWlt
    rw [htk] at h1
    have h2 : (W.biUnion (fun g => chg (val n gs X g) L)).card ≤ W.card + pc gs := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_left (L + nc gs + 1) (show W.card + pc gs + 1 ≤
        (W.biUnion (fun g => chg (val n gs X g) L)).card by omega)
      have e : (L + nc gs + 1) * (W.card + pc gs + 1) =
          (L + nc gs + 1) * (W.card + pc gs) + (L + nc gs + 1) := by ring
      omega
    omega
  · intro htight
    have h1 := hcoreL L le_rfl gs.length le_rfl W hWlt
    rw [htk] at h1
    have h3 := Nat.mul_le_mul_left L (show W.card + pc gs ≤
        (W.biUnion (fun g => chg (val n gs X g) L)).card by omega)
    have hFW : ∑ g ∈ W, (fal (val n gs X g) L).card ≤ nc gs := by omega
    rw [hncC]
    refine le_trans ?_ hFW
    rw [← Finset.sum_fiberwise_of_maps_to (s := names) (t := W) (g := tap)
      (fun a ha => Finset.mem_image_of_mem tap ha)]
    apply Finset.sum_le_sum
    intro g hg
    refine (sum_div2 _ _).trans ?_
    have hsum : ∑ a ∈ names with tap a = g, (Finset.univ.filter (fun i => name i = a)).card ≤
        (chg (val n gs X g) L).card := by
      rw [← Finset.card_biUnion]
      · apply Finset.card_le_card_of_injOn (fun i : Fin k => 2 * i.val)
        · intro i hi
          simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_filter,
            Finset.mem_univ, true_and] at hi
          obtain ⟨a, ⟨_, hag⟩, hia⟩ := hi
          have := hrec i
          rw [hia, hag] at this
          exact this
        · intro a _ b _ h; exact Fin.ext (by simp at h; omega)
      · intro a _ b _ hab
        simp only [Function.onFun]
        rw [Finset.disjoint_filter]
        intro i _ h1 h2
        exact hab (h1 ▸ h2)
    have h4 := chg_le (val n gs X g) L
    have h5 := ris_le (val n gs X g) L
    omega

def GP (n j : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧
    ∀ i ∈ g.inputs, i < n + 2 + j

def S1 (n : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length), GP n j gs[j]

theorem S1_append (n : ℕ) (gs hs : List Gate) (h1 : S1 n gs)
    (h2 : ∀ j (hj : j < hs.length), GP n (gs.length + j) hs[j]) : S1 n (gs ++ hs) := by
  intro j hj
  rw [List.length_append] at hj
  by_cases hjl : j < gs.length
  · rw [List.getElem_append_left hjl]; exact h1 j hjl
  · rw [List.getElem_append_right (by omega)]
    have := h2 (j - gs.length) (by omega)
    have e : gs.length + (j - gs.length) = j := by omega
    rw [e] at this
    exact this

def bstep (n : ℕ) {t : ℕ} (a : Fin t) (xi yi : ℕ)
    (st : List Gate × (Fin t → ℕ) × (Fin t → ℕ)) : List Gate × (Fin t → ℕ) × (Fin t → ℕ) :=
  if st.2.2 a = 0 then (st.1, Function.update st.2.1 a xi, Function.update st.2.2 a 1)
  else if st.2.2 a % 2 = 1 then
    (st.1 ++ [⟨GateOp.not, [yi]⟩, ⟨GateOp.and, [st.2.1 a, n + 2 + st.1.length]⟩],
      Function.update st.2.1 a (n + 2 + st.1.length + 1),
      Function.update st.2.2 a (st.2.2 a + 1))
  else (st.1 ++ [⟨GateOp.or, [st.2.1 a, xi]⟩], Function.update st.2.1 a (n + 2 + st.1.length),
      Function.update st.2.2 a (st.2.2 a + 1))

def build (n t k : ℕ) (name : Fin k → Fin t) (x y : Fin k → Fin n) :
    ℕ → List Gate × (Fin t → ℕ) × (Fin t → ℕ)
  | 0 => ([], fun _ => 0, fun _ => 0)
  | r + 1 => if h : r < k then bstep n (name ⟨r, h⟩) (x ⟨r, h⟩) (y ⟨r, h⟩) (build n t k name x y r)
      else build n t k name x y r

def V (n : ℕ) (gs : List Gate) (S : Finset (Fin n)) (g : ℕ) : Bool := (WS gs (inp n S)).getD g false

theorem V_pres (n : ℕ) (gs hs : List Gate) (S : Finset (Fin n)) (g : ℕ)
    (hg : g < n + 2 + gs.length) : V n (gs ++ hs) S g = V n gs S g := by
  unfold V
  exact WS_prefix gs hs _ g (by rw [inp_len]; exact hg)

theorem V_in (n : ℕ) (gs : List Gate) (S : Finset (Fin n)) (i : Fin n) :
    V n gs S i = decide (i ∈ S) := by
  unfold V
  rw [WS_input _ _ _ (by rw [inp_len]; omega)]
  exact inp_fin n S i

theorem V_last (n : ℕ) (gs : List Gate) (g : Gate) (S : Finset (Fin n)) :
    V n (gs ++ [g]) S (n + 2 + gs.length) = g.op.eval (g.inputs.map fun i => V n gs S i) := by
  unfold V
  have := WS_last gs g (inp n S)
  rw [inp_len] at this
  exact this

theorem sum_upd {t : ℕ} (f : Fin t → ℕ) (a0 : Fin t) (c : ℕ) (F : ℕ → ℕ) :
    ∑ a, F (Function.update f a0 c a) + F (f a0) = ∑ a, F (f a) + F c := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0), ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl (fun a ha => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)])]
  ring

def Inv (n t k : ℕ) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t) (r : ℕ)
    (st : List Gate × (Fin t → ℕ) × (Fin t → ℕ)) : Prop :=
  S1 n st.1 ∧ (∀ a, st.2.1 a < n + 2 + st.1.length) ∧
  (∀ a, st.2.2 a = (Finset.univ.filter (fun i : Fin k => i.val < r ∧ name i = a)).card) ∧
  nc st.1 = ∑ a, st.2.2 a / 2 ∧
  st.1.length = ∑ a, (st.2.2 a - 1 + st.2.2 a / 2) ∧
  (∀ a, ∀ l : Fin k, l.val < r → name l = a →
    V n st.1 (u l) (st.2.1 a) = false ∧ V n st.1 (v l) (st.2.1 a) = true) ∧
  (∀ a, ∀ q : Finset (Fin n), (∀ j : Fin k, j.val < r → u j ∪ v j ⊆ q) → st.2.2 a ≠ 0 →
    V n st.1 q (st.2.1 a) = decide (st.2.2 a % 2 = 1))

theorem cnt_succ {t k : ℕ} (name : Fin k → Fin t) (r : ℕ) (h : r < k) (a : Fin t) :
    (Finset.univ.filter (fun i : Fin k => i.val < r + 1 ∧ name i = a)).card =
      (Finset.univ.filter (fun i : Fin k => i.val < r ∧ name i = a)).card +
        (if name ⟨r, h⟩ = a then 1 else 0) := by
  split_ifs with hn
  · have : Finset.univ.filter (fun i : Fin k => i.val < r + 1 ∧ name i = a) =
        insert ⟨r, h⟩ (Finset.univ.filter (fun i : Fin k => i.val < r ∧ name i = a)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hi : i.val = r
        · left; exact Fin.ext hi
        · right; exact ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by simp, hn⟩
        · exact ⟨by omega, h2⟩
    rw [this, Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_or_ge i.val r with h3 | h3
      · exact h3
      · exact absurd ((show i = ⟨r, h⟩ from Fin.ext (by simp; omega)) ▸ h2) hn
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem V_notand (n : ℕ) (gs : List Gate) (S : Finset (Fin n)) (c : ℕ) (y : Fin n)
    (hc : c < n + 2 + gs.length) :
    V n (gs ++ [⟨GateOp.not, [(y : ℕ)]⟩, ⟨GateOp.and, [c, n + 2 + gs.length]⟩]) S
      (n + 2 + gs.length + 1) = (V n gs S c && !decide (y ∈ S)) := by
  have e : gs ++ [(⟨GateOp.not, [(y : ℕ)]⟩ : Gate), ⟨GateOp.and, [c, n + 2 + gs.length]⟩] =
      (gs ++ [(⟨GateOp.not, [(y : ℕ)]⟩ : Gate)]) ++ [⟨GateOp.and, [c, n + 2 + gs.length]⟩] := by simp
  rw [e]
  have h1 := V_last n (gs ++ [⟨GateOp.not, [(y : ℕ)]⟩]) ⟨GateOp.and, [c, n + 2 + gs.length]⟩ S
  have e2 : n + 2 + (gs ++ [(⟨GateOp.not, [(y : ℕ)]⟩ : Gate)]).length = n + 2 + gs.length + 1 := by simp; omega
  rw [e2] at h1
  rw [h1]
  have h2 := V_last n gs ⟨GateOp.not, [(y : ℕ)]⟩ S
  have h3 := V_pres n gs [⟨GateOp.not, [(y : ℕ)]⟩] S c hc
  simp only [GateOp.eval, List.map_cons, List.map_nil] at h2 ⊢
  rw [h2, h3, V_in]
  simp

theorem V_or (n : ℕ) (gs : List Gate) (S : Finset (Fin n)) (c : ℕ) (x : Fin n) :
    V n (gs ++ [⟨GateOp.or, [c, (x : ℕ)]⟩]) S (n + 2 + gs.length) = (V n gs S c || decide (x ∈ S)) := by
  rw [V_last]
  simp only [GateOp.eval, List.map_cons, List.map_nil]
  rw [V_in]
  simp

theorem inv_step (n t k : ℕ) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t)
    (x y : Fin k → Fin n) (hx : ∀ i, x i ∈ v i ∧ x i ∉ u i) (hy : ∀ i, y i ∈ u i ∧ y i ∉ v i)
    (hc : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j) (r : ℕ) (h : r < k)
    (st : List Gate × (Fin t → ℕ) × (Fin t → ℕ)) (hI : Inv n t k u v name r st) :
    Inv n t k u v name (r + 1) (bstep n (name ⟨r, h⟩) (x ⟨r, h⟩) (y ⟨r, h⟩) st) := by
  obtain ⟨gs, cur, cnt⟩ := st
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hV1, hV2⟩ := hI
  simp only at hS1 hS2 hS3 hS4 hS5 hV1 hV2
  set R : Fin k := ⟨r, h⟩ with hRdef
  set a0 := name R with ha0
  have hcl : ∀ l : Fin k, l.val < r → u l ∪ v l ⊆ u R ∩ v R := fun l hl => hc l R hl
  have hS3' : ∀ a, (Finset.univ.filter (fun i : Fin k => i.val < r + 1 ∧ name i = a)).card =
      cnt a + (if a0 = a then 1 else 0) := by
    intro a; rw [cnt_succ name r h a, hS3 a]
  have hlR : ∀ l : Fin k, l.val < r + 1 → ¬ l.val < r → l = R := fun l h1 h2 =>
    Fin.ext (by simp [hRdef]; omega)
  have hpre : ∀ q : Finset (Fin n), (∀ j : Fin k, j.val < r + 1 → u j ∪ v j ⊆ q) →
      ∀ j : Fin k, j.val < r → u j ∪ v j ⊆ q := fun q hq j hj => hq j (by omega)
  have hRq : ∀ q : Finset (Fin n), (∀ j : Fin k, j.val < r + 1 → u j ∪ v j ⊆ q) →
      u R ∪ v R ⊆ q := fun q hq => hq R (by simp [hRdef])
  have hpreR : ∀ j : Fin k, j.val < r → u j ∪ v j ⊆ u R :=
    fun j hj => (hcl j hj).trans Finset.inter_subset_left
  have hpreR' : ∀ j : Fin k, j.val < r → u j ∪ v j ⊆ v R :=
    fun j hj => (hcl j hj).trans Finset.inter_subset_right
  have hxn : ((x R : Fin n) : ℕ) < n := (x R).isLt
  have hyn : ((y R : Fin n) : ℕ) < n := (y R).isLt
  unfold bstep
  simp only
  by_cases hc0 : cnt a0 = 0
  · rw [if_pos hc0]
    unfold Inv
    dsimp only
    refine ⟨hS1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = a0
      · subst ha; rw [Function.update_self]; omega
      · rw [Function.update_of_ne ha]; exact hS2 a
    · intro a
      rw [hS3' a]
      by_cases ha : a = a0
      · subst ha; rw [Function.update_self, hc0]; simp
      · rw [Function.update_of_ne ha, if_neg (Ne.symm ha)]; rfl
    · have := sum_upd cnt a0 1 (fun c => c / 2)
      simp only [hc0] at this
      omega
    · have := sum_upd cnt a0 1 (fun c => c - 1 + c / 2)
      simp only [hc0] at this
      omega
    · intro a l hl hla
      by_cases ha : a = a0
      · subst ha
        rw [Function.update_self]
        by_cases hlr : l.val < r
        · exfalso
          have : 0 < (Finset.univ.filter (fun i : Fin k => i.val < r ∧ name i = a0)).card :=
            Finset.card_pos.mpr ⟨l, by simp [hlr, hla]⟩
          rw [← hS3 a0, hc0] at this
          exact absurd this (lt_irrefl 0)
        · have := hlR l hl hlr
          subst this
          rw [V_in, V_in]
          simp [(hx R).1, (hx R).2]
      · rw [Function.update_of_ne ha]
        have hlr : l.val < r := by
          by_contra hlr
          have := hlR l hl hlr
          subst this
          exact ha hla.symm
        exact hV1 a l hlr hla
    · intro a q hq hne
      by_cases ha : a = a0
      · subst ha
        simp only [Function.update_self, V_in]
        have := hRq q hq
        simp [this (Finset.mem_union_right _ (hx R).1)]
      · simp only [Function.update_of_ne ha] at hne ⊢
        exact hV2 a q (hpre q hq) hne
  · rw [if_neg hc0]
    by_cases hodd : cnt a0 % 2 = 1
    · rw [if_pos hodd]
      unfold Inv
      dsimp only
      have hN := hS2 a0
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply S1_append n gs _ hS1
        intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · refine ⟨Or.inr (Or.inr rfl), by simp, ?_⟩
          intro i hi; simp at hi; omega
        · refine ⟨Or.inl rfl, by simp, ?_⟩
          intro i hi; simp at hi; omega
      · intro a
        by_cases ha : a = a0
        · subst ha; simp only [Function.update_self, List.length_append, List.length_cons,
            List.length_nil]; omega
        · rw [Function.update_of_ne ha]; have := hS2 a; simp only [List.length_append,
            List.length_cons, List.length_nil]; omega
      · intro a
        rw [hS3' a]
        by_cases ha : a = a0
        · subst ha; rw [Function.update_self]; simp
        · rw [Function.update_of_ne ha, if_neg (Ne.symm ha)]; rfl
      · have := sum_upd cnt a0 (cnt a0 + 1) (fun c => c / 2)
        have e : nc (gs ++ [⟨GateOp.not, [((y R : Fin n) : ℕ)]⟩,
            ⟨GateOp.and, [cur a0, n + 2 + gs.length]⟩]) = nc gs + 1 := by
          rw [nc_append]
          have : nc [⟨GateOp.not, [((y R : Fin n) : ℕ)]⟩, ⟨GateOp.and, [cur a0, n + 2 + gs.length]⟩] =
              nc [⟨GateOp.not, [((y R : Fin n) : ℕ)]⟩] + nc [⟨GateOp.and, [cur a0, n + 2 + gs.length]⟩] :=
            nc_append [_] [_]
          rw [this, nc_not, nc_and]
        rw [e]
        omega
      · have := sum_upd cnt a0 (cnt a0 + 1) (fun c => c - 1 + c / 2)
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
      · intro a l hl hla
        by_cases ha : a = a0
        · subst ha
          simp only [Function.update_self]
          rw [V_notand _ _ _ _ _ hN, V_notand _ _ _ _ _ hN]
          by_cases hlr : l.val < r
          · have h1 := hV1 a0 l hlr hla
            have h2 : y R ∉ v l := fun hh => (hy R).2 (hpreR' l hlr (Finset.mem_union_right _ hh))
            rw [h1.1, h1.2]; simp [h2]
          · have := hlR l hl hlr
            subst this
            have h3 := hV2 a0 (v R) hpreR' hc0
            rw [h3]; simp [(hy R).1, (hy R).2, hodd]
        · rw [Function.update_of_ne ha]
          have hlr : l.val < r := by
            by_contra hlr
            have := hlR l hl hlr
            subst this
            exact ha hla.symm
          rw [V_pres _ _ _ _ _ (hS2 a), V_pres _ _ _ _ _ (hS2 a)]
          exact hV1 a l hlr hla
      · intro a q hq hne
        by_cases ha : a = a0
        · subst ha
          simp only [Function.update_self]
          rw [V_notand _ _ _ _ _ hN]
          have := hRq q hq
          have hyq : y R ∈ q := this (Finset.mem_union_left _ (hy R).1)
          simp [hyq]
          omega
        · simp only [Function.update_of_ne ha] at hne ⊢
          rw [V_pres _ _ _ _ _ (hS2 a)]
          exact hV2 a q (hpre q hq) hne

    · rw [if_neg hodd]
      unfold Inv
      dsimp only
      have hN := hS2 a0
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply S1_append n gs _ hS1
        intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        interval_cases j
        refine ⟨Or.inr (Or.inl rfl), by simp, ?_⟩
        intro i hi; simp at hi; omega
      · intro a
        by_cases ha : a = a0
        · subst ha; simp only [Function.update_self, List.length_append, List.length_cons,
            List.length_nil]; omega
        · rw [Function.update_of_ne ha]; have := hS2 a; simp only [List.length_append,
            List.length_cons, List.length_nil]; omega
      · intro a
        rw [hS3' a]
        by_cases ha : a = a0
        · subst ha; rw [Function.update_self]; simp
        · rw [Function.update_of_ne ha, if_neg (Ne.symm ha)]; rfl
      · have := sum_upd cnt a0 (cnt a0 + 1) (fun c => c / 2)
        rw [nc_append, nc_or]
        omega
      · have := sum_upd cnt a0 (cnt a0 + 1) (fun c => c - 1 + c / 2)
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
      · intro a l hl hla
        by_cases ha : a = a0
        · subst ha
          simp only [Function.update_self]
          rw [V_or, V_or]
          by_cases hlr : l.val < r
          · have h1 := hV1 a0 l hlr hla
            have h2 : x R ∉ u l := fun hh => (hx R).2 (hpreR l hlr (Finset.mem_union_left _ hh))
            rw [h1.1, h1.2]; simp [h2]
          · have := hlR l hl hlr
            subst this
            have h3 := hV2 a0 (u R) hpreR hc0
            rw [h3]; simp [(hx R).1, (hx R).2, hodd]
        · rw [Function.update_of_ne ha]
          have hlr : l.val < r := by
            by_contra hlr
            have := hlR l hl hlr
            subst this
            exact ha hla.symm
          rw [V_pres _ _ _ _ _ (hS2 a), V_pres _ _ _ _ _ (hS2 a)]
          exact hV1 a l hlr hla
      · intro a q hq hne
        by_cases ha : a = a0
        · subst ha
          simp only [Function.update_self]
          rw [V_or]
          have := hRq q hq
          have hxq : x R ∈ q := this (Finset.mem_union_right _ (hx R).1)
          simp [hxq]
          omega
        · simp only [Function.update_of_ne ha] at hne ⊢
          rw [V_pres _ _ _ _ _ (hS2 a)]
          exact hV2 a q (hpre q hq) hne

theorem inv_build (n t k : ℕ) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t)
    (x y : Fin k → Fin n) (hx : ∀ i, x i ∈ v i ∧ x i ∉ u i) (hy : ∀ i, y i ∈ u i ∧ y i ∉ v i)
    (hc : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j) :
    ∀ r, r ≤ k → Inv n t k u v name r (build n t k name x y r) := by
  intro r
  induction r with
  | zero =>
    intro _
    unfold Inv build
    dsimp only
    refine ⟨fun j hj => by simp at hj, fun a => by simp, fun a => by simp, ?_, ?_,
      fun a l hl => by omega, fun a q _ hne => absurd rfl hne⟩
    · simp [nc, PEqualNP.NotBracket.notCount]
    · simp
  | succ r ih =>
    intro hr
    have h : r < k := by omega
    have := inv_step n t k u v name x y hx hy hc r h _ (ih (by omega))
    unfold build
    rw [dif_pos h]
    exact this

theorem upper (n t k : ℕ) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t)
    (hu : ∀ i, ¬ u i ⊆ v i) (hv : ∀ i, ¬ v i ⊆ u i)
    (hc : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j) :
    ∃ (C : Circuit) (tap : Fin t → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧
      (∀ i, (WS C.gates (inp n (u i))).getD (tap (name i)) false = false ∧
        (WS C.gates (inp n (v i))).getD (tap (name i)) false = true) ∧
      C.size - PEqualNP.NotBracket.notCount C = k - (Finset.univ.image name).card ∧
      PEqualNP.NotBracket.notCount C =
        ∑ a ∈ Finset.univ.image name, (Finset.univ.filter (fun i => name i = a)).card / 2 := by
  classical
  have hx : ∀ i, ∃ z, z ∈ v i ∧ z ∉ u i := fun i => by
    have := hv i
    rw [Finset.not_subset] at this
    exact this
  have hy : ∀ i, ∃ z, z ∈ u i ∧ z ∉ v i := fun i => by
    have := hu i
    rw [Finset.not_subset] at this
    exact this
  choose x hx using hx
  choose y hy using hy
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hV1, -⟩ :=
    inv_build n t k u v name x y hx hy hc k le_rfl
  set st := build n t k name x y k with hst
  have hm : ∀ a, st.2.2 a = (Finset.univ.filter (fun i => name i = a)).card := by
    intro a
    rw [hS3 a]
    congr 1
    ext i
    simp
  refine ⟨⟨st.1, 0⟩, st.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have := hS1 j hj
    refine ⟨?_, this.2.1⟩
    rcases this.1 with h | h | h <;> simp [h]
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact (hS1 j hj).2.2 i hi
  · show 0 < n + 2 + st.1.length; omega
  · intro a; exact hS2 a
  · intro i
    exact hV1 (name i) i i.isLt rfl
  · show st.1.length - nc st.1 = _
    rw [hS5, hS4]
    have hk : ∑ a, (Finset.univ.filter (fun i => name i = a)).card = k := by
      have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
        (t := (Finset.univ : Finset (Fin t))) (f := name) (fun _ _ => Finset.mem_univ _)
      simpa using this.symm
    have hsub : ∑ a, (st.2.2 a - 1) = ∑ a ∈ Finset.univ.image name, (st.2.2 a - 1) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [hm a]
      have : Finset.univ.filter (fun i => name i = a) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro h; exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
      rw [this]; simp
    have hsub2 : ∑ a, st.2.2 a = ∑ a ∈ Finset.univ.image name, st.2.2 a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [hm a]
      have : Finset.univ.filter (fun i => name i = a) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro h; exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
      rw [this]; simp
    have hpos : ∑ a ∈ Finset.univ.image name, (st.2.2 a - 1) + (Finset.univ.image name).card =
        ∑ a ∈ Finset.univ.image name, st.2.2 a := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      have : 0 < st.2.2 (name i) := by
        rw [hm]; exact Finset.card_pos.mpr ⟨i, by simp⟩
      omega
    have hsplit : ∑ a, (st.2.2 a - 1 + st.2.2 a / 2) = ∑ a, (st.2.2 a - 1) + ∑ a, st.2.2 a / 2 :=
      Finset.sum_add_distrib
    have hk' : ∑ a, st.2.2 a = k := by rw [← hk]; exact Finset.sum_congr rfl (fun a _ => hm a)
    omega
  · show nc st.1 = _
    rw [hS4]
    symm
    rw [Finset.sum_congr rfl (fun a _ => by rw [← hm a])]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    rw [hm a]
    have : Finset.univ.filter (fun i => name i = a) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro h; exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
    rw [this]; simp

end PEqualNP.Outside.L_lib_1323

theorem PEqualNP.Outside.L_lib_1323 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n t k : Nat) (u v : Fin k → Finset (Fin n)) (name : Fin k → Fin t),
  (∀ i, ¬ u i ⊆ v i) → (∀ i, ¬ v i ⊆ u i) →
  (∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j) →
  let names := Finset.univ.image name
  let h := names.card
  let f := names.sum (fun a => (Finset.univ.filter (fun i => name i=a)).card/2)
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧
    ∀ i, let val := fun (x : Finset (Fin n)) =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true])).getD (tap (name i)) false
      val (u i) = false ∧ val (v i) = true
  (∀ C tap, fits C tap → k ≤ C.size - PEqualNP.NotBracket.notCount C + h ∧
    (C.size - PEqualNP.NotBracket.notCount C = k-h → f ≤ PEqualNP.NotBracket.notCount C)) ∧
  ∃ C tap, fits C tap ∧ C.size - PEqualNP.NotBracket.notCount C = k-h ∧
    PEqualNP.NotBracket.notCount C = f) := by
  intro n t k u v name hu hv hc names h f fits
  have hinp : ∀ x : Finset (Fin n),
      (List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _)) ++ [false, true]) =
      PEqualNP.Outside.L_lib_1323.inp n x := by
    intro x
    unfold PEqualNP.Outside.L_lib_1323.inp
    congr 1
    congr 1
    funext j
    exact decide_eq_decide.mpr Iff.rfl
  have hnames : names = Finset.univ.image name := by
    simp only [names]
    congr 1
    exact Subsingleton.elim _ _
  have hc' : ∀ i j, i < j → u i ∪ v i ⊆ u j ∩ v j := by
    intro i j hij
    convert hc i j hij
  have hf : f = ∑ a ∈ Finset.univ.image name, (Finset.univ.filter (fun i => name i = a)).card / 2 := by
    simp only [f, names]
    congr
    · funext a
      congr
  refine ⟨fun C tap hfit => ?_, ?_⟩
  · obtain ⟨hF, hR, -, htap, hval⟩ := hfit
    have hval' : ∀ i, (PEqualNP.Outside.L_lib_1323.WS C.gates
        (PEqualNP.Outside.L_lib_1323.inp n (u i))).getD (tap (name i)) false = false ∧
        (PEqualNP.Outside.L_lib_1323.WS C.gates
        (PEqualNP.Outside.L_lib_1323.inp n (v i))).getD (tap (name i)) false = true := by
      intro i
      have := hval i
      simp only at this
      rw [hinp, hinp] at this
      exact this
    have := PEqualNP.Outside.L_lib_1323.lower n t k u v name hc' C tap hF hR htap hval'
    simp only [h, hf, hnames]
    exact this
  · obtain ⟨C, tap, hF, hR, hout, htap, hval, hsz, hnc⟩ :=
      PEqualNP.Outside.L_lib_1323.upper n t k u v name hu hv hc'
    refine ⟨C, tap, ⟨hF, hR, hout, htap, ?_⟩, ?_, ?_⟩
    · intro i
      simp only
      rw [hinp, hinp]
      exact hval i
    · simp only [h, hnames]; exact hsz
    · rw [hf]; exact hnc
