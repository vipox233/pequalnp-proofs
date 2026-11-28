import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29950
open PEqualNP.CircuitLowerBounds

def RO : ℕ → Bool → Finset ℕ → ((ℕ → Bool) → Bool) → Prop
  | 0, c, S, g => c = false ∧ ∃ i, S = {i} ∧ g = fun z => z i
  | d+1, c, S, g => RO d c S g ∨
      (∃ S1 S2 g1 g2, ∃ b : Bool, Disjoint S1 S2 ∧ S = S1 ∪ S2 ∧ RO d c S1 g1 ∧ RO d false S2 g2 ∧
          g = fun z => if b then (g1 z && g2 z) else (g1 z || g2 z)) ∨
      (c = true ∧ ∃ g', RO d false S g' ∧ g = fun z => !g' z)

def ROx (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool) : Prop := ∃ d, RO d c S g

def DepOn (S : Finset ℕ) (g : (ℕ → Bool) → Bool) : Prop :=
  ∀ z z' : ℕ → Bool, (∀ i ∈ S, z i = z' i) → g z = g z'

def single (i : ℕ) : ℕ → Bool := fun j => decide (j = i)
def pair (i j : ℕ) : ℕ → Bool := fun l => decide (l = i ∨ l = j)

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def fn (gs : List Gate) (N : ℕ) (w : ℕ) : (ℕ → Bool) → Bool :=
  fun z => ((Circuit.mk gs 0).wires (List.ofFn fun i : Fin N => z i)).getD w false

def b2 (gs : List Gate) : ℕ := gs.countP (fun g => !isNot g.op && decide (g.inputs.length = 2))
def nots (gs : List Gate) : ℕ := gs.countP (fun g => isNot g.op)

theorem RO_mono_fuel {d : ℕ} {c : Bool} {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : RO d c S g) :
    ∀ e, d ≤ e → RO e c S g := by
  intro e he
  induction he with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem ROx_var (i : ℕ) : ROx false {i} (fun z => z i) := ⟨0, rfl, i, rfl, rfl⟩

theorem ROx_comb {c : Bool} {S1 S2 : Finset ℕ} {g1 g2 : (ℕ → Bool) → Bool} (b : Bool)
    (hd : Disjoint S1 S2) (h1 : ROx c S1 g1) (h2 : ROx false S2 g2) :
    ROx c (S1 ∪ S2) (fun z => if b then (g1 z && g2 z) else (g1 z || g2 z)) := by
  obtain ⟨d1, h1⟩ := h1
  obtain ⟨d2, h2⟩ := h2
  exact ⟨max d1 d2 + 1, Or.inr (Or.inl ⟨S1, S2, g1, g2, b, hd, rfl,
    RO_mono_fuel h1 _ (le_max_left _ _), RO_mono_fuel h2 _ (le_max_right _ _), rfl⟩)⟩

theorem ROx_comb' {c : Bool} {S1 S2 : Finset ℕ} {g1 g2 : (ℕ → Bool) → Bool} (b : Bool)
    (hd : Disjoint S1 S2) (h1 : ROx false S1 g1) (h2 : ROx c S2 g2) :
    ROx c (S1 ∪ S2) (fun z => if b then (g1 z && g2 z) else (g1 z || g2 z)) := by
  have h := ROx_comb b hd.symm h2 h1
  rw [Finset.union_comm] at h
  have e : (fun z => if b then (g2 z && g1 z) else (g2 z || g1 z)) =
      (fun z => if b then (g1 z && g2 z) else (g1 z || g2 z)) := by
    funext z; cases b <;> simp [Bool.and_comm, Bool.or_comm]
  rw [e] at h; exact h

theorem ROx_not {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx false S g) :
    ROx true S (fun z => !g z) := by
  obtain ⟨d, h⟩ := h
  exact ⟨d + 1, Or.inr (Or.inr ⟨rfl, g, h, rfl⟩)⟩

theorem ROx_induct {P : Bool → Finset ℕ → ((ℕ → Bool) → Bool) → Prop}
    (hvar : ∀ i, P false {i} (fun z => z i))
    (hcomb : ∀ (c : Bool) (S1 S2 : Finset ℕ) (g1 g2 : (ℕ → Bool) → Bool) (b : Bool),
      Disjoint S1 S2 → ROx c S1 g1 → ROx false S2 g2 → P c S1 g1 → P false S2 g2 →
      P c (S1 ∪ S2) (fun z => if b then (g1 z && g2 z) else (g1 z || g2 z)))
    (hnot : ∀ (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx false S g → P false S g →
      P true S (fun z => !g z)) :
    ∀ (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx c S g → P c S g := by
  intro c S g ⟨d, h⟩
  induction d generalizing c S g with
  | zero =>
    obtain ⟨rfl, i, rfl, rfl⟩ := h
    exact hvar i
  | succ d ih =>
    rcases h with h | ⟨S1, S2, g1, g2, b, hd, rfl, h1, h2, rfl⟩ | ⟨rfl, g', h', rfl⟩
    · exact ih c S g h
    · exact hcomb c S1 S2 g1 g2 b hd ⟨d, h1⟩ ⟨d, h2⟩ (ih _ _ _ h1) (ih _ _ _ h2)
    · exact hnot S g' ⟨d, h'⟩ (ih _ _ _ h')


theorem A_wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem A_wires_len (gs : List Gate) (x : List Bool) :
    ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => rw [A_wires_snoc]; simp [ih]; omega

theorem A_fn_ge (gs : List Gate) (N w : ℕ) (z : ℕ → Bool) (h : N + gs.length ≤ w) :
    fn gs N w z = false := by
  unfold fn
  apply List.getD_eq_default
  rw [A_wires_len]; simpa using h

theorem A_fn_snoc_lt (gs : List Gate) (g : Gate) (N w : ℕ) (z : ℕ → Bool)
    (h : w < N + gs.length) : fn (gs ++ [g]) N w z = fn gs N w z := by
  unfold fn
  rw [A_wires_snoc, List.getD_append]
  rw [A_wires_len]; simpa using h

theorem A_fn_snoc_eq (gs : List Gate) (g : Gate) (N : ℕ) (z : ℕ → Bool) :
    fn (gs ++ [g]) N (N + gs.length) z = g.op.eval (g.inputs.map fun i => fn gs N i z) := by
  unfold fn
  rw [A_wires_snoc, List.getD_append_right]
  · rw [A_wires_len]; simp
  · rw [A_wires_len]; simp

theorem A_fn_nil (N w : ℕ) (z : ℕ → Bool) (h : w < N) : fn [] N w z = z w := by
  simp [fn, Circuit.wires, List.getD_eq_getElem?_getD, h]

theorem A_b2_snoc_left (gs : List Gate) (g : Gate) (h1 : isNot g.op = false)
    (h2 : g.inputs.length = 2) : b2 (gs ++ [g]) = b2 gs + 1 := by
  simp [b2, List.countP_append, h1, h2]

theorem A_b2_snoc_right (gs : List Gate) (g : Gate)
    (h : isNot g.op = true ∨ g.inputs.length ≠ 2) : b2 (gs ++ [g]) = b2 gs := by
  rcases h with h | h <;> simp [b2, List.countP_append, h]

theorem A_b2_le (gs : List Gate) (g : Gate) : b2 gs ≤ b2 (gs ++ [g]) := by
  simp [b2, List.countP_append]

theorem A_nots_snoc_false (gs : List Gate) (g : Gate) (h : isNot g.op = false) :
    nots (gs ++ [g]) = nots gs := by
  simp [nots, List.countP_append, h]

theorem A_nots_snoc_true (gs : List Gate) (g : Gate) (h : isNot g.op = true) :
    nots (gs ++ [g]) = nots gs + 1 := by
  simp [nots, List.countP_append, h]

theorem A_nots_le (gs : List Gate) (g : Gate) : nots gs ≤ nots (gs ++ [g]) := by
  simp [nots, List.countP_append]

theorem A_filter_dep (N : ℕ) (gs : List Gate) (S : Finset ℕ) (z z' : ℕ → Bool)
    (h : ∀ i ∈ S.filter (fun i => i < N + gs.length), fn gs N i z = fn gs N i z') (i : ℕ)
    (hi : i ∈ S) : fn gs N i z = fn gs N i z' := by
  by_cases hl : i < N + gs.length
  · exact h i (Finset.mem_filter.mpr ⟨hi, hl⟩)
  · rw [A_fn_ge _ _ _ _ (by omega), A_fn_ge _ _ _ _ (by omega)]

theorem A_gate (N : ℕ) (gs : List Gate) (g : Gate)
    (hfan : g.inputs.length ≤ 2 ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)) :
    ∃ E : Finset ℕ, (∀ i ∈ E, i < N + gs.length) ∧
      (∀ z z' : ℕ → Bool, (∀ i ∈ E, fn gs N i z = fn gs N i z') →
        fn (gs ++ [g]) N (N + gs.length) z = fn (gs ++ [g]) N (N + gs.length) z') ∧
      ((isNot g.op = false ∧ g.inputs.length = 2 ∧ E.card ≤ 2 ∧
          (E.card = 2 → ∃ a b : ℕ, ∃ bb : Bool, a ≠ b ∧ E = {a, b} ∧
            fn (gs ++ [g]) N (N + gs.length) =
              fun z => if bb then (fn gs N a z && fn gs N b z) else (fn gs N a z || fn gs N b z)))
        ∨ ((isNot g.op = true ∨ g.inputs.length ≠ 2) ∧ E.card ≤ 1 ∧
          (E.card = 1 → ∃ a : ℕ, E = {a} ∧
            ((isNot g.op = false ∧ fn (gs ++ [g]) N (N + gs.length) = fn gs N a) ∨
             (isNot g.op = true ∧
               fn (gs ++ [g]) N (N + gs.length) = fun z => !fn gs N a z))))) := by
  have hh : ∀ z, fn (gs ++ [g]) N (N + gs.length) z =
      g.op.eval (g.inputs.map fun i => fn gs N i z) := A_fn_snoc_eq gs g N
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hlen, hop⟩ := hfan
  simp only at hlen hop hh ⊢
  match inputs, hlen with
  | [], _ =>
    refine ⟨∅, by simp, ?_, Or.inr ⟨Or.inr (by simp), by simp, by simp⟩⟩
    intro z z' _; rw [hh, hh]; simp
  | [a], _ =>
    refine ⟨({a} : Finset ℕ).filter (fun i => i < N + gs.length),
      fun i hi => (Finset.mem_filter.mp hi).2, ?_, Or.inr ⟨Or.inr (by simp), ?_, ?_⟩⟩
    · intro z z' hz; rw [hh, hh]
      have := A_filter_dep N gs {a} z z' hz a (by simp)
      simp [this]
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · intro hc
      have hE : ({a} : Finset ℕ).filter (fun i => i < N + gs.length) = {a} :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hc]; simp)
      refine ⟨a, hE, ?_⟩
      rcases hop with rfl | rfl | rfl
      · left; exact ⟨rfl, funext fun z => by rw [hh]; simp [GateOp.eval]⟩
      · left; exact ⟨rfl, funext fun z => by rw [hh]; simp [GateOp.eval]⟩
      · right; exact ⟨rfl, funext fun z => by rw [hh]; simp [GateOp.eval]⟩
  | [a, b], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨({a, b} : Finset ℕ).filter (fun i => i < N + gs.length),
        fun i hi => (Finset.mem_filter.mp hi).2, ?_, Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩
      · intro z z' hz; rw [hh, hh]
        have ha := A_filter_dep N gs {a, b} z z' hz a (by simp)
        have hb := A_filter_dep N gs {a, b} z z' hz b (by simp)
        simp [ha, hb]
      · exact (Finset.card_filter_le _ _).trans Finset.card_le_two
      · intro hc
        have hE : ({a, b} : Finset ℕ).filter (fun i => i < N + gs.length) = {a, b} :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            (by rw [hc]; exact Finset.card_le_two)
        have hab : a ≠ b := by
          rintro rfl; rw [hE] at hc; simp at hc
        exact ⟨a, b, true, hab, hE, funext fun z => by rw [hh]; simp [GateOp.eval]⟩
    · refine ⟨({a, b} : Finset ℕ).filter (fun i => i < N + gs.length),
        fun i hi => (Finset.mem_filter.mp hi).2, ?_, Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩
      · intro z z' hz; rw [hh, hh]
        have ha := A_filter_dep N gs {a, b} z z' hz a (by simp)
        have hb := A_filter_dep N gs {a, b} z z' hz b (by simp)
        simp [ha, hb]
      · exact (Finset.card_filter_le _ _).trans Finset.card_le_two
      · intro hc
        have hE : ({a, b} : Finset ℕ).filter (fun i => i < N + gs.length) = {a, b} :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            (by rw [hc]; exact Finset.card_le_two)
        have hab : a ≠ b := by
          rintro rfl; rw [hE] at hc; simp at hc
        exact ⟨a, b, false, hab, hE, funext fun z => by rw [hh]; simp [GateOp.eval]⟩
    · refine ⟨({a} : Finset ℕ).filter (fun i => i < N + gs.length),
        fun i hi => (Finset.mem_filter.mp hi).2, ?_, Or.inr ⟨Or.inl rfl, ?_, ?_⟩⟩
      · intro z z' hz; rw [hh, hh]
        have := A_filter_dep N gs {a} z z' hz a (by simp)
        simp [GateOp.eval, this]
      · exact (Finset.card_filter_le _ _).trans (by simp)
      · intro hc
        have hE : ({a} : Finset ℕ).filter (fun i => i < N + gs.length) = {a} :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hc]; simp)
        exact ⟨a, hE, Or.inr ⟨rfl, funext fun z => by rw [hh]; simp [GateOp.eval]⟩⟩
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

def A_T (N : ℕ) (gs : List Gate) (W : Finset ℕ) (D : ℕ → Finset ℕ) : Prop :=
  (∀ w1 ∈ W, ∀ w2 ∈ W, w1 ≠ w2 → Disjoint (D w1) (D w2)) ∧
  (nots gs = 0 → ∀ w ∈ W, ROx false (D w) (fn gs N w)) ∧
  (nots gs ≤ 1 → (∀ w ∈ W, ∃ c, ROx c (D w) (fn gs N w)) ∧
     ∀ w1 ∈ W, ∀ w2 ∈ W, w1 ≠ w2 →
       ROx false (D w1) (fn gs N w1) ∨ ROx false (D w2) (fn gs N w2))

def A_Inv (N : ℕ) (gs : List Gate) : Prop :=
  ∀ W : Finset ℕ, (∀ w ∈ W, w < N + gs.length) → ∃ D : ℕ → Finset ℕ,
    (∀ w ∈ W, D w ⊆ Finset.range N ∧ DepOn (D w) (fn gs N w)) ∧
    (W.biUnion D).card ≤ W.card + b2 gs ∧
    ((W.biUnion D).card = W.card + b2 gs → A_T N gs W D)

theorem A_inv_nil (N : ℕ) : A_Inv N [] := by
  intro W hW
  have hfn : ∀ w ∈ W, fn [] N w = fun z => z w := fun w hw =>
    funext fun z => A_fn_nil N w z (by simpa using hW w hw)
  refine ⟨fun w => {w}, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨by simpa using hW w hw, ?_⟩
    rw [hfn w hw]
    intro z z' h; exact h w (by simp)
  · rw [Finset.biUnion_singleton_eq_self]; omega
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro w1 _ w2 _ hne; simpa using hne
    · intro _ w hw; rw [hfn w hw]; exact ROx_var w
    · intro _
      exact ⟨fun w hw => ⟨false, by rw [hfn w hw]; exact ROx_var w⟩,
        fun w1 hw1 _ _ _ => Or.inl (by rw [hfn w1 hw1]; exact ROx_var w1)⟩

theorem A_step (N : ℕ) (gs : List Gate) (g : Gate)
    (hfan : g.inputs.length ≤ 2 ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not))
    (ih : A_Inv N gs) : A_Inv N (gs ++ [g]) := by
  intro W hW
  have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
  obtain ⟨L, hLdef⟩ : ∃ L, L = N + gs.length := ⟨_, rfl⟩
  have hb := A_b2_le gs g
  have hn := A_nots_le gs g
  by_cases hLW : L ∈ W
  swap
  · have hW' : ∀ w ∈ W, w < N + gs.length := by
      intro w hw
      have h1 := hW w hw
      have h2 : w ≠ L := fun h => hLW (h ▸ hw)
      rw [hlen] at h1; omega
    obtain ⟨D, h1, h2, h3⟩ := ih W hW'
    have hfn : ∀ w ∈ W, fn (gs ++ [g]) N w = fn gs N w := fun w hw =>
      funext fun z => A_fn_snoc_lt gs g N w z (hW' w hw)
    refine ⟨D, ?_, ?_, ?_⟩
    · intro w hw; rw [hfn w hw]; exact h1 w hw
    · omega
    · intro ht
      obtain ⟨t1, t2, t3⟩ := h3 (by omega)
      refine ⟨t1, ?_, ?_⟩
      · intro h0 w hw; rw [hfn w hw]; exact t2 (by omega) w hw
      · intro h0
        obtain ⟨u1, u2⟩ := t3 (by omega)
        refine ⟨fun w hw => by rw [hfn w hw]; exact u1 w hw, fun w1 h1' w2 h2' hne => ?_⟩
        rw [hfn w1 h1', hfn w2 h2']; exact u2 w1 h1' w2 h2' hne
  · obtain ⟨E, hE, hdep, hkind⟩ := A_gate N gs g hfan
    rw [← hLdef] at hE hdep hkind
    obtain ⟨W', hW'def⟩ : ∃ W', W' = W.erase L := ⟨_, rfl⟩
    obtain ⟨W'', hW''def⟩ : ∃ W'', W'' = W' ∪ E := ⟨_, rfl⟩
    have hLW' : L ∉ W' := by rw [hW'def]; exact Finset.notMem_erase L W
    have hmemW' : ∀ w ∈ W, w ≠ L → w ∈ W' := fun w hw hne => by
      rw [hW'def]; exact Finset.mem_erase.mpr ⟨hne, hw⟩
    have hW'W : ∀ w ∈ W', w ∈ W := fun w hw => by
      rw [hW'def] at hw; exact Finset.mem_of_mem_erase hw
    have hW'ne : ∀ w ∈ W', w ≠ L := fun w hw h => hLW' (h ▸ hw)
    have hW'lt : ∀ w ∈ W', w < L := by
      intro w hw
      have h1 := hW w (hW'W w hw)
      have h2 := hW'ne w hw
      rw [hlen] at h1; omega
    have hW'W'' : ∀ w ∈ W', w ∈ W'' := fun w hw => by
      rw [hW''def]; exact Finset.mem_union_left _ hw
    have hEW'' : ∀ w ∈ E, w ∈ W'' := fun w hw => by
      rw [hW''def]; exact Finset.mem_union_right _ hw
    have hW''lt : ∀ w ∈ W'', w < N + gs.length := by
      intro w hw
      rw [hW''def] at hw
      rcases Finset.mem_union.mp hw with h | h
      · have := hW'lt w h; omega
      · have := hE w h; omega
    obtain ⟨D'', h1, h2, h3⟩ := ih W'' hW''lt
    obtain ⟨D, hDdef⟩ : ∃ D : ℕ → Finset ℕ, D = fun w => if w = L then E.biUnion D'' else D'' w :=
      ⟨_, rfl⟩
    have hDL : D L = E.biUnion D'' := by rw [hDdef]; simp
    have hDne : ∀ w, w ≠ L → D w = D'' w := fun w h => by rw [hDdef]; simp [h]
    have hfn : ∀ w ∈ W', fn (gs ++ [g]) N w = fn gs N w := fun w hw =>
      funext fun z => A_fn_snoc_lt gs g N w z (by have := hW'lt w hw; omega)
    have hWeq : W = insert L W' := by rw [hW'def]; exact (Finset.insert_erase hLW).symm
    have hbu : W.biUnion D = W''.biUnion D'' := by
      rw [hWeq, Finset.biUnion_insert, hDL, hW''def, Finset.union_biUnion, Finset.union_comm]
      congr 1
      exact Finset.biUnion_congr rfl (fun w hw => hDne w (hW'ne w hw))
    have hcardW : W.card = W'.card + 1 := by
      rw [hWeq, Finset.card_insert_of_notMem hLW']
    have hcu : W''.card ≤ W'.card + E.card := by
      rw [hW''def]; exact Finset.card_union_le _ _
    have hconv : ∀ w ∈ W, w ≠ L → ∀ c, ROx c (D'' w) (fn gs N w) →
        ROx c (D w) (fn (gs ++ [g]) N w) := by
      intro w hw hne c h
      rw [hDne w hne, hfn w (hmemW' w hw hne)]; exact h
    refine ⟨D, ?_, ?_, ?_⟩
    · intro w hw
      by_cases hwL : w = L
      · rw [hwL, hDL]
        refine ⟨Finset.biUnion_subset.mpr fun i hi => (h1 i (hEW'' i hi)).1, ?_⟩
        intro z z' hz
        apply hdep
        intro i hi
        exact (h1 i (hEW'' i hi)).2 z z' (fun j hj => hz j (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩))
      · rw [hDne w hwL, hfn w (hmemW' w hw hwL)]
        exact h1 w (hW'W'' w (hmemW' w hw hwL))
    · rw [hbu]
      rcases hkind with ⟨hk1, hk2, hc, _⟩ | ⟨hk, hc, _⟩
      · have := A_b2_snoc_left gs g hk1 hk2; omega
      · have := A_b2_snoc_right gs g hk; omega
    · intro ht
      rw [hbu] at ht
      have key : (W''.biUnion D'').card = W''.card + b2 gs ∧ W''.card = W'.card + E.card := by
        rcases hkind with ⟨hk1, hk2, hc, _⟩ | ⟨hk, hc, _⟩
        · have := A_b2_snoc_left gs g hk1 hk2; omega
        · have := A_b2_snoc_right gs g hk; omega
      obtain ⟨t1, t2, t3⟩ := h3 key.1
      have hdis : Disjoint W' E := by
        rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
        have := Finset.card_union_add_card_inter W' E
        rw [← hW''def] at this; omega
      have hEne : ∀ i ∈ E, ∀ w ∈ W', i ≠ w := fun i hi w hw h =>
        Finset.disjoint_left.mp hdis hw (h ▸ hi)
      have hLw : ∀ w ∈ W', Disjoint (D L) (D'' w) := by
        intro w hw
        rw [hDL, Finset.disjoint_biUnion_left]
        intro i hi
        exact t1 i (hEW'' i hi) w (hW'W'' w hw) (hEne i hi w hw)
      have hdisj : ∀ w1 ∈ W, ∀ w2 ∈ W, w1 ≠ w2 → Disjoint (D w1) (D w2) := by
        intro w1 hw1 w2 hw2 hne
        by_cases e1 : w1 = L
        · have e2 : w2 ≠ L := fun h => hne (e1.trans h.symm)
          rw [e1, hDne w2 e2]; exact hLw w2 (hmemW' w2 hw2 e2)
        · by_cases e2 : w2 = L
          · rw [e2, hDne w1 e1]; exact (hLw w1 (hmemW' w1 hw1 e1)).symm
          · rw [hDne w1 e1, hDne w2 e2]
            exact t1 w1 (hW'W'' _ (hmemW' w1 hw1 e1)) w2 (hW'W'' _ (hmemW' w2 hw2 e2)) hne
      refine ⟨hdisj, ?_⟩
      rcases hkind with ⟨hk1, hk2, hc, htight⟩ | ⟨hk, hc, htight⟩
      · have hb2 := A_b2_snoc_left gs g hk1 hk2
        have hnn := A_nots_snoc_false gs g hk1
        obtain ⟨a, b, bb, hab, hEeq, hfnL⟩ := htight (by omega)
        have haE : a ∈ E := by rw [hEeq]; simp
        have hbE : b ∈ E := by rw [hEeq]; simp
        have haW := hEW'' a haE
        have hbW := hEW'' b hbE
        have hDL' : D L = D'' a ∪ D'' b := by
          rw [hDL, hEeq, Finset.biUnion_insert, Finset.singleton_biUnion]
        have hdab : Disjoint (D'' a) (D'' b) := t1 a haW b hbW hab
        have hLfalse : ROx false (D'' a) (fn gs N a) → ROx false (D'' b) (fn gs N b) →
            ROx false (D L) (fn (gs ++ [g]) N L) := by
          intro ha hb'
          rw [hDL', hfnL]; exact ROx_comb bb hdab ha hb'
        refine ⟨?_, ?_⟩
        · intro h0 w hw
          by_cases hwL : w = L
          · rw [hwL]; exact hLfalse (t2 (by omega) a haW) (t2 (by omega) b hbW)
          · exact hconv w hw hwL false (t2 (by omega) w (hW'W'' _ (hmemW' w hw hwL)))
        · intro h1'
          obtain ⟨u1, u2⟩ := t3 (by omega)
          have hLc : ∃ c, ROx c (D L) (fn (gs ++ [g]) N L) := by
            rcases u2 a haW b hbW hab with ha | hb'
            · obtain ⟨c, hc'⟩ := u1 b hbW
              exact ⟨c, by rw [hDL', hfnL]; exact ROx_comb' bb hdab ha hc'⟩
            · obtain ⟨c, hc'⟩ := u1 a haW
              exact ⟨c, by rw [hDL', hfnL]; exact ROx_comb bb hdab hc' hb'⟩
          have hpair : ∀ w ∈ W, w ≠ L → ROx false (D L) (fn (gs ++ [g]) N L) ∨
              ROx false (D w) (fn (gs ++ [g]) N w) := by
            intro w hw hne
            have hw' := hmemW' w hw hne
            rcases u2 a haW w (hW'W'' w hw') (hEne a haE w hw') with ha | hw2
            · rcases u2 b hbW w (hW'W'' w hw') (hEne b hbE w hw') with hb' | hw2
              · left; exact hLfalse ha hb'
              · right; exact hconv w hw hne false hw2
            · right; exact hconv w hw hne false hw2
          refine ⟨?_, ?_⟩
          · intro w hw
            by_cases hwL : w = L
            · rw [hwL]; exact hLc
            · obtain ⟨c, hc'⟩ := u1 w (hW'W'' _ (hmemW' w hw hwL))
              exact ⟨c, hconv w hw hwL c hc'⟩
          · intro w1 hw1 w2 hw2 hne
            by_cases e1 : w1 = L
            · have e2 : w2 ≠ L := fun h => hne (e1.trans h.symm)
              rw [e1]; exact hpair w2 hw2 e2
            · by_cases e2 : w2 = L
              · rw [e2]; exact (hpair w1 hw1 e1).symm
              · rcases u2 w1 (hW'W'' _ (hmemW' w1 hw1 e1)) w2 (hW'W'' _ (hmemW' w2 hw2 e2)) hne
                  with h | h
                · left; exact hconv w1 hw1 e1 false h
                · right; exact hconv w2 hw2 e2 false h
      · have hb2 := A_b2_snoc_right gs g hk
        obtain ⟨a, hEeq, hcase⟩ := htight (by omega)
        have haE : a ∈ E := by rw [hEeq]; simp
        have haW := hEW'' a haE
        have hDL' : D L = D'' a := by rw [hDL, hEeq, Finset.singleton_biUnion]
        rcases hcase with ⟨hk1, hfnL⟩ | ⟨hk1, hfnL⟩
        · have hnn := A_nots_snoc_false gs g hk1
          have hLconv : ∀ c, ROx c (D'' a) (fn gs N a) → ROx c (D L) (fn (gs ++ [g]) N L) := by
            intro c h; rw [hDL', hfnL]; exact h
          refine ⟨?_, ?_⟩
          · intro h0 w hw
            by_cases hwL : w = L
            · rw [hwL]; exact hLconv false (t2 (by omega) a haW)
            · exact hconv w hw hwL false (t2 (by omega) w (hW'W'' _ (hmemW' w hw hwL)))
          · intro h1'
            obtain ⟨u1, u2⟩ := t3 (by omega)
            have hpair : ∀ w ∈ W, w ≠ L → ROx false (D L) (fn (gs ++ [g]) N L) ∨
                ROx false (D w) (fn (gs ++ [g]) N w) := by
              intro w hw hne
              have hw' := hmemW' w hw hne
              rcases u2 a haW w (hW'W'' w hw') (hEne a haE w hw') with ha | hw2
              · left; exact hLconv false ha
              · right; exact hconv w hw hne false hw2
            refine ⟨?_, ?_⟩
            · intro w hw
              by_cases hwL : w = L
              · rw [hwL]
                obtain ⟨c, hc'⟩ := u1 a haW
                exact ⟨c, hLconv c hc'⟩
              · obtain ⟨c, hc'⟩ := u1 w (hW'W'' _ (hmemW' w hw hwL))
                exact ⟨c, hconv w hw hwL c hc'⟩
            · intro w1 hw1 w2 hw2 hne
              by_cases e1 : w1 = L
              · have e2 : w2 ≠ L := fun h => hne (e1.trans h.symm)
                rw [e1]; exact hpair w2 hw2 e2
              · by_cases e2 : w2 = L
                · rw [e2]; exact (hpair w1 hw1 e1).symm
                · rcases u2 w1 (hW'W'' _ (hmemW' w1 hw1 e1)) w2 (hW'W'' _ (hmemW' w2 hw2 e2)) hne
                    with h | h
                  · left; exact hconv w1 hw1 e1 false h
                  · right; exact hconv w2 hw2 e2 false h
        · have hnn := A_nots_snoc_true gs g hk1
          refine ⟨fun h0 => absurd h0 (by omega), ?_⟩
          intro h1'
          have t2' := t2 (by omega)
          have hLt : ROx true (D L) (fn (gs ++ [g]) N L) := by
            rw [hDL', hfnL]; exact ROx_not (t2' a haW)
          have hf : ∀ w ∈ W, w ≠ L → ROx false (D w) (fn (gs ++ [g]) N w) := fun w hw hne =>
            hconv w hw hne false (t2' w (hW'W'' _ (hmemW' w hw hne)))
          refine ⟨?_, ?_⟩
          · intro w hw
            by_cases hwL : w = L
            · rw [hwL]; exact ⟨true, hLt⟩
            · exact ⟨false, hf w hw hwL⟩
          · intro w1 hw1 w2 hw2 hne
            by_cases e1 : w1 = L
            · have e2 : w2 ≠ L := fun h => hne (e1.trans h.symm)
              right; exact hf w2 hw2 e2
            · left; exact hf w1 hw1 e1

theorem A_inv (N : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)) : A_Inv N gs := by
  induction gs using List.reverseRecOn with
  | nil => exact A_inv_nil N
  | append_singleton gs g ih =>
    exact A_step N gs g (hfan g (by simp)) (ih fun g' hg' => hfan g' (by simp [hg']))

theorem A_tight (N : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not))
    (o : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ DepOn S (fn gs N o) ∧ S.card ≤ 1 + b2 gs ∧
      (S.card = 1 + b2 gs → (nots gs = 0 → ROx false S (fn gs N o)) ∧
        (nots gs ≤ 1 → ∃ c, ROx c S (fn gs N o))) := by
  by_cases ho : o < N + gs.length
  · obtain ⟨D, h1, h2, h3⟩ := A_inv N gs hfan {o} (by simpa using ho)
    rw [Finset.singleton_biUnion, Finset.card_singleton] at h2 h3
    refine ⟨D o, (h1 o (by simp)).1, (h1 o (by simp)).2, h2, ?_⟩
    intro ht
    obtain ⟨_, t2, t3⟩ := h3 ht
    exact ⟨fun h0 => t2 h0 o (by simp), fun h1' => (t3 h1').1 o (by simp)⟩
  · refine ⟨∅, by simp, ?_, by simp, ?_⟩
    · intro z z' _
      rw [A_fn_ge gs N o z (by omega), A_fn_ge gs N o z' (by omega)]
    · intro h; simp at h; omega

theorem A_mono_all (N : ℕ) (gs : List Gate)
    (hmon : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (o : ℕ) (z z' : ℕ → Bool), (∀ i, z i = true → z' i = true) →
      fn gs N o z = true → fn gs N o z' = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro o z z' hz h
    by_cases ho : o < N
    · rw [A_fn_nil N o z ho] at h; rw [A_fn_nil N o z' ho]; exact hz o h
    · rw [A_fn_ge [] N o z (by simpa using ho)] at h; cases h
  | append_singleton gs g ih =>
    have ih' := ih fun g' hg' => hmon g' (by simp [hg'])
    intro o z z' hz h
    rcases Nat.lt_trichotomy o (N + gs.length) with ho | ho | ho
    · rw [A_fn_snoc_lt gs g N o z ho] at h; rw [A_fn_snoc_lt gs g N o z' ho]
      exact ih' o z z' hz h
    · rw [ho, A_fn_snoc_eq] at h; rw [ho, A_fn_snoc_eq]
      rcases hmon g (by simp) with hop | hop
      · rw [hop] at h ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
        rintro x ⟨i, hi, rfl⟩
        exact ih' i z z' hz (h _ ⟨i, hi, rfl⟩)
      · rw [hop] at h ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
        obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := h
        exact ⟨_, ⟨i, hi, rfl⟩, ih' i z z' hz hx⟩
    · rw [A_fn_ge (gs ++ [g]) N o z (by simp; omega)] at h; cases h

theorem A_mono (N : ℕ) (gs : List Gate) (hmon : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (o : ℕ) : ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) →
      fn gs N o z = true → fn gs N o z' = true :=
  A_mono_all N gs hmon o


theorem B_dep {c : Bool} {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx c S g) : DepOn S g := by
  refine ROx_induct (P := fun _ S g => DepOn S g) ?_ ?_ ?_ c S g h
  · intro i z z' hz; exact hz i (Finset.mem_singleton_self i)
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 z z' hz
    have e1 := ih1 z z' (fun i hi => hz i (Finset.mem_union_left _ hi))
    have e2 := ih2 z z' (fun i hi => hz i (Finset.mem_union_right _ hi))
    simp only [e1, e2]
  · intro S g _ ih z z' hz
    simp only [ih z z' hz]

theorem B1_zero_aux : ∀ (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx c S g →
    c = false → g (fun _ => false) = false := by
  refine ROx_induct (P := fun c _ g => c = false → g (fun _ => false) = false) ?_ ?_ ?_
  · intro i _; rfl
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 hc
    have a1 := ih1 hc
    have a2 := ih2 rfl
    cases b <;> simp [a1, a2]
  · intro S g _ _ hc; exact absurd hc (by decide)

theorem B_zero {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx false S g) :
    g (fun _ => false) = false := B1_zero_aux false S g h rfl

theorem B1_mono_aux : ∀ (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx c S g →
    c = false → ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) → g z = true → g z' = true := by
  refine ROx_induct (P := fun c _ g => c = false → ∀ z z' : ℕ → Bool,
    (∀ i, z i = true → z' i = true) → g z = true → g z' = true) ?_ ?_ ?_
  · intro i _ z z' hz h; exact hz i h
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 hc z z' hz h
    have a1 := ih1 hc z z' hz
    have a2 := ih2 rfl z z' hz
    cases b
    · simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at h ⊢
      exact h.imp a1 a2
    · simp only [ite_true, Bool.and_eq_true] at h ⊢
      exact ⟨a1 h.1, a2 h.2⟩
  · intro S g _ _ hc; exact absurd hc (by decide)

theorem B_mono {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx false S g) :
    ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) → g z = true → g z' = true :=
  B1_mono_aux false S g h rfl

theorem B_nonempty {c : Bool} {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx c S g) : S.Nonempty := by
  refine ROx_induct (P := fun _ S _ => S.Nonempty) ?_ ?_ ?_ c S g h
  · intro i; exact ⟨i, Finset.mem_singleton_self i⟩
  · intro c S1 S2 g1 g2 b _ _ _ ih1 _
    exact ih1.mono Finset.subset_union_left
  · intro S g _ ih; exact ih

theorem B1_zero_off {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (hd : DepOn S g)
    (h0 : g (fun _ => false) = false) (z : ℕ → Bool) (hz : ∀ i ∈ S, z i = false) : g z = false := by
  rw [hd z (fun _ => false) hz]; exact h0

theorem B1_pair_comm (a b : ℕ) : pair a b = pair b a := by
  funext l; simp only [pair, or_comm]

theorem B1_pair_left {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (hd : DepOn S g) (a b : ℕ)
    (hb : b ∉ S) : g (pair a b) = g (single a) := by
  apply hd; intro i hi
  have : i ≠ b := fun e => hb (e ▸ hi)
  simp [pair, single, this]

theorem B1_pair_right {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (hd : DepOn S g) (a b : ℕ)
    (ha : a ∉ S) : g (pair a b) = g (single b) := by
  rw [B1_pair_comm]; exact B1_pair_left hd b a ha

theorem B1_single_off {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (hd : DepOn S g)
    (h0 : g (fun _ => false) = false) (a : ℕ) (ha : a ∉ S) : g (single a) = false := by
  apply B1_zero_off hd h0; intro i hi
  have : i ≠ a := fun e => ha (e ▸ hi)
  simp [single, this]

theorem B1_pair_off {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (hd : DepOn S g)
    (h0 : g (fun _ => false) = false) (a b : ℕ) (ha : a ∉ S) (hb : b ∉ S) :
    g (pair a b) = false := by
  rw [B1_pair_left hd a b hb]; exact B1_single_off hd h0 a ha

theorem B1_allsingles : ∀ (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx c S g →
    c = false → (∀ i ∈ S, g (single i) = true) → ∀ z : ℕ → Bool, (g z = true ↔ ∃ i ∈ S, z i = true) := by
  refine ROx_induct (P := fun c S g => c = false → (∀ i ∈ S, g (single i) = true) →
    ∀ z : ℕ → Bool, (g z = true ↔ ∃ i ∈ S, z i = true)) ?_ ?_ ?_
  · intro i _ _ z
    constructor
    · intro h; exact ⟨i, Finset.mem_singleton_self i, h⟩
    · rintro ⟨j, hj, h⟩; rw [Finset.mem_singleton] at hj; subst hj; exact h
  · intro c S1 S2 g1 g2 b hdis r1 r2 ih1 ih2 hc hs z
    subst hc
    have d1 := B_dep r1
    have d2 := B_dep r2
    have z1 := B_zero r1
    have z2 := B_zero r2
    have nl : ∀ i, i ∈ S1 → i ∉ S2 := fun i h => Finset.disjoint_left.mp hdis h
    have nr : ∀ i, i ∈ S2 → i ∉ S1 := fun i h => Finset.disjoint_right.mp hdis h
    cases b
    · have h1' : ∀ i ∈ S1, g1 (single i) = true := by
        intro i hi
        have := hs i (Finset.mem_union_left _ hi)
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at this
        rcases this with h | h
        · exact h
        · rw [B1_single_off d2 z2 i (nl i hi)] at h; exact absurd h (by decide)
      have h2' : ∀ i ∈ S2, g2 (single i) = true := by
        intro i hi
        have := hs i (Finset.mem_union_right _ hi)
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at this
        rcases this with h | h
        · rw [B1_single_off d1 z1 i (nr i hi)] at h; exact absurd h (by decide)
        · exact h
      simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true, ih1 rfl h1' z, ih2 rfl h2' z]
      constructor
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · exact ⟨i, Finset.mem_union_left _ hi, h⟩
        · exact ⟨i, Finset.mem_union_right _ hi, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Finset.mem_union.mp hi with a | a
        · exact Or.inl ⟨i, a, h⟩
        · exact Or.inr ⟨i, a, h⟩
    · exfalso
      obtain ⟨i, hi⟩ := B_nonempty r1
      have := hs i (Finset.mem_union_left _ hi)
      simp only [ite_true, Bool.and_eq_true] at this
      rw [B1_single_off d2 z2 i (nl i hi)] at this
      exact absurd this.2 (by decide)
  · intro S g _ _ hc; exact absurd hc (by decide)

def B1_Stmt (d : ℕ) (S : Finset ℕ) (g : (ℕ → Bool) → Bool) : Prop :=
  ∀ (U P : Finset ℕ), (∀ u ∈ U, u < d) → (∀ p ∈ P, p ∉ U ∧ ∀ u ∈ U, p ≠ d + u) →
    S = U ∪ U.image (fun u => d + u) ∪ P →
    (∀ p ∈ P, g (single p) = true) →
    (∀ u ∈ U, g (single u) = false ∧ g (single (d + u)) = false) →
    (∀ u ∈ U, ∀ v ∈ U, g (pair u (d + v)) = decide (u = v)) →
    (∀ z : ℕ → Bool, g z = true ↔ ((∃ p ∈ P, z p = true) ∨ (∃ u ∈ U, z u = true ∧ z (d + u) = true) ∨
      ∃ u ∈ U, ∃ v ∈ U, u ≠ v ∧ g (pair u v) = true ∧
        ((z u = true ∧ z v = true) ∨ (z (d + u) = true ∧ z (d + v) = true)))) ∧
    (∀ u ∈ U, ∀ v ∈ U, ∀ w ∈ U, u ≠ v → u ≠ w → g (pair u v) = true → g (pair u w) = true → v = w)

theorem B1_var_case (d i : ℕ) : B1_Stmt d {i} (fun z => z i) := by
  intro U P hU hP hS h1 h2 h3
  have hUe : ∀ u ∈ U, False := by
    intro u hu
    have a : u ∈ ({i} : Finset ℕ) := by
      rw [hS]; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl hu)
    have b : d + u ∈ ({i} : Finset ℕ) := by
      rw [hS]; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    rw [Finset.mem_singleton] at a b
    have := hU u hu
    omega
  refine ⟨fun z => ?_, fun u hu => (hUe u hu).elim⟩
  constructor
  · intro hz
    have hi : i ∈ U ∪ U.image (fun u => d + u) ∪ P := by rw [← hS]; exact Finset.mem_singleton_self i
    simp only [Finset.mem_union, Finset.mem_image] at hi
    rcases hi with (h | ⟨u, hu, _⟩) | h
    · exact (hUe i h).elim
    · exact (hUe u hu).elim
    · exact Or.inl ⟨i, h, hz⟩
  · rintro (⟨p, hp, zp⟩ | ⟨u, hu, _⟩ | ⟨u, hu, _⟩)
    · have : p ∈ ({i} : Finset ℕ) := by rw [hS]; exact Finset.mem_union_right _ hp
      rw [Finset.mem_singleton] at this; subst this; exact zp
    · exact (hUe u hu).elim
    · exact (hUe u hu).elim

theorem B1_or_side (d : ℕ) (S1 S2 : Finset ℕ) (g g1 g2 : (ℕ → Bool) → Bool)
    (hdis : Disjoint S1 S2) (d1 : DepOn S1 g1) (d2 : DepOn S2 g2)
    (hg : ∀ z, g z = (g1 z || g2 z)) (U P : Finset ℕ)
    (hS : S1 ∪ S2 = U ∪ U.image (fun u => d + u) ∪ P)
    (h2 : ∀ u ∈ U, g (single u) = false ∧ g (single (d + u)) = false)
    (h3 : ∀ u ∈ U, ∀ v ∈ U, g (pair u (d + v)) = decide (u = v)) :
    ∀ u ∈ U, u ∈ S1 → d + u ∈ S1 := by
  intro u hu hu1
  by_contra hn
  have h := h3 u hu u hu
  have ha := (h2 u hu).1
  have hb := (h2 u hu).2
  rw [hg] at h ha hb
  rw [Bool.or_eq_false_iff] at ha hb
  rw [B1_pair_left d1 u (d + u) hn, B1_pair_right d2 u (d + u) (Finset.disjoint_left.mp hdis hu1),
    ha.1, hb.2] at h
  simp at h

theorem B1_or_transfer (d : ℕ) (S1 S2 : Finset ℕ) (g g1 g2 : (ℕ → Bool) → Bool)
    (hdis : Disjoint S1 S2) (d1 : DepOn S1 g1) (d2 : DepOn S2 g2)
    (z2 : g2 (fun _ => false) = false)
    (hg : ∀ z, g z = (g1 z || g2 z)) (U P : Finset ℕ)
    (hS : S1 ∪ S2 = U ∪ U.image (fun u => d + u) ∪ P)
    (h1 : ∀ p ∈ P, g (single p) = true)
    (h2 : ∀ u ∈ U, g (single u) = false ∧ g (single (d + u)) = false)
    (h3 : ∀ u ∈ U, ∀ v ∈ U, g (pair u (d + v)) = decide (u = v))
    (hc1 : ∀ u ∈ U, u ∈ S1 → d + u ∈ S1) (hc2 : ∀ u ∈ U, u ∈ S2 → d + u ∈ S2) :
    S1 = U.filter (fun u => u ∈ S1) ∪ (U.filter (fun u => u ∈ S1)).image (fun u => d + u) ∪
        P.filter (fun u => u ∈ S1) ∧
    (∀ p ∈ P.filter (fun u => u ∈ S1), g1 (single p) = true) ∧
    (∀ u ∈ U.filter (fun u => u ∈ S1), g1 (single u) = false ∧ g1 (single (d + u)) = false) ∧
    (∀ u ∈ U.filter (fun u => u ∈ S1), ∀ v ∈ U.filter (fun u => u ∈ S1),
      g1 (pair u (d + v)) = decide (u = v)) ∧
    (∀ u ∈ U.filter (fun u => u ∈ S1), ∀ v ∈ U.filter (fun u => u ∈ S1),
      g (pair u v) = g1 (pair u v)) ∧
    (∀ u ∈ U, ∀ v ∈ U, u ∈ S1 → v ∈ S2 → g (pair u v) = false) := by
  have nl : ∀ i, i ∈ S1 → i ∉ S2 := fun i h => Finset.disjoint_left.mp hdis h
  have nr : ∀ i, i ∈ S2 → i ∉ S1 := fun i h => Finset.disjoint_right.mp hdis h
  have memS : ∀ i, (i ∈ S1 ∨ i ∈ S2) ↔ (i ∈ U ∨ (∃ u ∈ U, d + u = i)) ∨ i ∈ P := by
    intro i; rw [← Finset.mem_union, hS]; simp only [Finset.mem_union, Finset.mem_image]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hi
      rcases (memS i).mp (Or.inl hi) with (h | ⟨u, hu, rfl⟩) | h
      · exact Or.inl (Or.inl ⟨h, hi⟩)
      · refine Or.inl (Or.inr ⟨u, ⟨hu, ?_⟩, rfl⟩)
        rcases (memS u).mpr (Or.inl (Or.inl hu)) with a | a
        · exact a
        · exact absurd hi (nr _ (hc2 u hu a))
      · exact Or.inr ⟨h, hi⟩
    · rintro ((⟨_, h⟩ | ⟨u, ⟨hu, a⟩, rfl⟩) | ⟨_, h⟩)
      · exact h
      · exact hc1 u hu a
      · exact h
  · intro p hp
    rw [Finset.mem_filter] at hp
    have := h1 p hp.1
    rw [hg, B1_single_off d2 z2 p (nl p hp.2)] at this
    simpa using this
  · intro u hu
    rw [Finset.mem_filter] at hu
    have ha := (h2 u hu.1).1
    have hb := (h2 u hu.1).2
    rw [hg, Bool.or_eq_false_iff] at ha hb
    exact ⟨ha.1, hb.1⟩
  · intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    have := h3 u hu.1 v hv.1
    rw [hg, B1_pair_off d2 z2 u (d + v) (nl u hu.2) (nl _ (hc1 v hv.1 hv.2))] at this
    simpa using this
  · intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    rw [hg, B1_pair_off d2 z2 u v (nl u hu.2) (nl v hv.2)]
    simp
  · intro u hu v hv a b
    have ha := (h2 u hu).1
    have hb := (h2 v hv).1
    rw [hg, Bool.or_eq_false_iff] at ha hb
    rw [hg, B1_pair_left d1 u v (nr v b), B1_pair_right d2 u v (nl u a), ha.1, hb.2]
    rfl

theorem B1_or_case (d : ℕ) (S1 S2 : Finset ℕ) (g g1 g2 : (ℕ → Bool) → Bool)
    (hdis : Disjoint S1 S2) (r1 : ROx false S1 g1) (r2 : ROx false S2 g2)
    (ih1 : B1_Stmt d S1 g1) (ih2 : B1_Stmt d S2 g2)
    (hg : ∀ z, g z = (g1 z || g2 z)) : B1_Stmt d (S1 ∪ S2) g := by
  intro U P hU hP hS h1 h2 h3
  have d1 := B_dep r1
  have d2 := B_dep r2
  have z1 := B_zero r1
  have z2 := B_zero r2
  have hg' : ∀ z, g z = (g2 z || g1 z) := fun z => by rw [hg, Bool.or_comm]
  have hS' : S2 ∪ S1 = U ∪ U.image (fun u => d + u) ∪ P := by rw [Finset.union_comm]; exact hS
  have hc1 := B1_or_side d S1 S2 g g1 g2 hdis d1 d2 hg U P hS h2 h3
  have hc2 := B1_or_side d S2 S1 g g2 g1 hdis.symm d2 d1 hg' U P hS' h2 h3
  obtain ⟨e1, p1, q1, t1, s1, x1⟩ :=
    B1_or_transfer d S1 S2 g g1 g2 hdis d1 d2 z2 hg U P hS h1 h2 h3 hc1 hc2
  obtain ⟨e2, p2, q2, t2, s2, x2⟩ :=
    B1_or_transfer d S2 S1 g g2 g1 hdis.symm d2 d1 z1 hg' U P hS' h1 h2 h3 hc2 hc1
  have I1 := ih1 (U.filter (fun u => u ∈ S1)) (P.filter (fun u => u ∈ S1))
    (fun u hu => hU u (Finset.mem_filter.mp hu).1)
    (fun p hp => ⟨fun h => (hP p (Finset.mem_filter.mp hp).1).1 (Finset.mem_filter.mp h).1,
      fun u hu => (hP p (Finset.mem_filter.mp hp).1).2 u (Finset.mem_filter.mp hu).1⟩)
    e1 p1 q1 t1
  have I2 := ih2 (U.filter (fun u => u ∈ S2)) (P.filter (fun u => u ∈ S2))
    (fun u hu => hU u (Finset.mem_filter.mp hu).1)
    (fun p hp => ⟨fun h => (hP p (Finset.mem_filter.mp hp).1).1 (Finset.mem_filter.mp h).1,
      fun u hu => (hP p (Finset.mem_filter.mp hp).1).2 u (Finset.mem_filter.mp hu).1⟩)
    e2 p2 q2 t2
  have memS : ∀ i, (i ∈ S1 ∨ i ∈ S2) ↔ (i ∈ U ∨ (∃ u ∈ U, d + u = i)) ∨ i ∈ P := by
    intro i; rw [← Finset.mem_union, hS]; simp only [Finset.mem_union, Finset.mem_image]
  have side : ∀ u ∈ U, u ∈ S1 ∨ u ∈ S2 := fun u hu => (memS u).mpr (Or.inl (Or.inl hu))
  have sideP : ∀ p ∈ P, p ∈ S1 ∨ p ∈ S2 := fun p hp => (memS p).mpr (Or.inr hp)
  have mf : ∀ (T : Finset ℕ) (X : Finset ℕ) (u : ℕ), u ∈ X → u ∈ T → u ∈ X.filter (fun u => u ∈ T) :=
    fun T X u a b => Finset.mem_filter.mpr ⟨a, b⟩
  refine ⟨fun z => ?_, ?_⟩
  · rw [hg, Bool.or_eq_true, I1.1 z, I2.1 z]
    constructor
    · rintro (H | H)
      · rcases H with ⟨p, hp, zp⟩ | ⟨u, hu, zu⟩ | ⟨u, hu, v, hv, huv, hgp, hz⟩
        · exact Or.inl ⟨p, (Finset.mem_filter.mp hp).1, zp⟩
        · exact Or.inr (Or.inl ⟨u, (Finset.mem_filter.mp hu).1, zu⟩)
        · exact Or.inr (Or.inr ⟨u, (Finset.mem_filter.mp hu).1, v, (Finset.mem_filter.mp hv).1, huv,
            by rw [s1 u hu v hv]; exact hgp, hz⟩)
      · rcases H with ⟨p, hp, zp⟩ | ⟨u, hu, zu⟩ | ⟨u, hu, v, hv, huv, hgp, hz⟩
        · exact Or.inl ⟨p, (Finset.mem_filter.mp hp).1, zp⟩
        · exact Or.inr (Or.inl ⟨u, (Finset.mem_filter.mp hu).1, zu⟩)
        · exact Or.inr (Or.inr ⟨u, (Finset.mem_filter.mp hu).1, v, (Finset.mem_filter.mp hv).1, huv,
            by rw [s2 u hu v hv]; exact hgp, hz⟩)
    · rintro (⟨p, hp, zp⟩ | ⟨u, hu, zu⟩ | ⟨u, hu, v, hv, huv, hgp, hz⟩)
      · rcases sideP p hp with a | a
        · exact Or.inl (Or.inl ⟨p, mf _ _ _ hp a, zp⟩)
        · exact Or.inr (Or.inl ⟨p, mf _ _ _ hp a, zp⟩)
      · rcases side u hu with a | a
        · exact Or.inl (Or.inr (Or.inl ⟨u, mf _ _ _ hu a, zu⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨u, mf _ _ _ hu a, zu⟩))
      · rcases side u hu with a | a <;> rcases side v hv with b | b
        · exact Or.inl (Or.inr (Or.inr ⟨u, mf _ _ _ hu a, v, mf _ _ _ hv b, huv,
            by rw [← s1 u (mf _ _ _ hu a) v (mf _ _ _ hv b)]; exact hgp, hz⟩))
        · rw [x1 u hu v hv a b] at hgp; exact absurd hgp (by decide)
        · rw [x2 u hu v hv a b] at hgp; exact absurd hgp (by decide)
        · exact Or.inr (Or.inr (Or.inr ⟨u, mf _ _ _ hu a, v, mf _ _ _ hv b, huv,
            by rw [← s2 u (mf _ _ _ hu a) v (mf _ _ _ hv b)]; exact hgp, hz⟩))
  · intro u hu v hv w hw huv huw hv' hw'
    rcases side u hu with a | a
    · have bv : v ∈ S1 := by
        rcases side v hv with b | b
        · exact b
        · rw [x1 u hu v hv a b] at hv'; exact absurd hv' (by decide)
      have bw : w ∈ S1 := by
        rcases side w hw with b | b
        · exact b
        · rw [x1 u hu w hw a b] at hw'; exact absurd hw' (by decide)
      exact I1.2 u (mf _ _ _ hu a) v (mf _ _ _ hv bv) w (mf _ _ _ hw bw) huv huw
        (by rw [← s1 u (mf _ _ _ hu a) v (mf _ _ _ hv bv)]; exact hv')
        (by rw [← s1 u (mf _ _ _ hu a) w (mf _ _ _ hw bw)]; exact hw')
    · have bv : v ∈ S2 := by
        rcases side v hv with b | b
        · rw [x2 u hu v hv a b] at hv'; exact absurd hv' (by decide)
        · exact b
      have bw : w ∈ S2 := by
        rcases side w hw with b | b
        · rw [x2 u hu w hw a b] at hw'; exact absurd hw' (by decide)
        · exact b
      exact I2.2 u (mf _ _ _ hu a) v (mf _ _ _ hv bv) w (mf _ _ _ hw bw) huv huw
        (by rw [← s2 u (mf _ _ _ hu a) v (mf _ _ _ hv bv)]; exact hv')
        (by rw [← s2 u (mf _ _ _ hu a) w (mf _ _ _ hw bw)]; exact hw')

theorem B1_and_case (d : ℕ) (S1 S2 : Finset ℕ) (g g1 g2 : (ℕ → Bool) → Bool)
    (hdis : Disjoint S1 S2) (r1 : ROx false S1 g1) (r2 : ROx false S2 g2)
    (hg : ∀ z, g z = (g1 z && g2 z)) : B1_Stmt d (S1 ∪ S2) g := by
  intro U P hU hP hS h1 h2 h3
  have d1 := B_dep r1
  have d2 := B_dep r2
  have z1 := B_zero r1
  have z2 := B_zero r2
  have nl : ∀ i, i ∈ S1 → i ∉ S2 := fun i h => Finset.disjoint_left.mp hdis h
  have nr : ∀ i, i ∈ S2 → i ∉ S1 := fun i h => Finset.disjoint_right.mp hdis h
  have memS : ∀ i, (i ∈ S1 ∨ i ∈ S2) ↔ (i ∈ U ∨ (∃ u ∈ U, d + u = i)) ∨ i ∈ P := by
    intro i; rw [← Finset.mem_union, hS]; simp only [Finset.mem_union, Finset.mem_image]
  have hPe : ∀ p ∈ P, False := by
    intro p hp
    have hp1 := h1 p hp
    rw [hg, Bool.and_eq_true] at hp1
    rcases (memS p).mpr (Or.inr hp) with hs | hs
    · rw [B1_single_off d2 z2 p (nl p hs)] at hp1; exact absurd hp1.2 (by decide)
    · rw [B1_single_off d1 z1 p (nr p hs)] at hp1; exact absurd hp1.1 (by decide)
  have hpp : ∀ u ∈ U, g1 (pair u (d + u)) = true ∧ g2 (pair u (d + u)) = true := by
    intro u hu
    have h : g (pair u (d + u)) = true := by rw [h3 u hu u hu]; simp
    rw [hg, Bool.and_eq_true] at h
    exact h
  have F1 : ∀ u ∈ U, (u ∈ S1 ∧ d + u ∈ S2) ∨ (u ∈ S2 ∧ d + u ∈ S1) := by
    intro u hu
    have h := hpp u hu
    rcases (memS u).mpr (Or.inl (Or.inl hu)) with a | a <;>
      rcases (memS (d + u)).mpr (Or.inl (Or.inr ⟨u, hu, rfl⟩)) with b | b
    · rw [B1_pair_off d2 z2 u (d + u) (nl u a) (nl _ b)] at h; exact absurd h.2 (by decide)
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, b⟩
    · rw [B1_pair_off d1 z1 u (d + u) (nr u a) (nr _ b)] at h; exact absurd h.1 (by decide)
  have F2a : ∀ i ∈ S1, g1 (single i) = true := by
    intro i hi
    rcases (memS i).mp (Or.inl hi) with (hu | ⟨u, hu, rfl⟩) | hp
    · rcases F1 i hu with ⟨_, b⟩ | ⟨a, _⟩
      · rw [← B1_pair_left d1 i (d + i) (nr _ b)]; exact (hpp i hu).1
      · exact absurd hi (nr _ a)
    · rcases F1 u hu with ⟨_, b⟩ | ⟨a, _⟩
      · exact absurd hi (nr _ b)
      · rw [← B1_pair_right d1 u (d + u) (nr _ a)]; exact (hpp u hu).1
    · exact (hPe _ hp).elim
  have F2b : ∀ i ∈ S2, g2 (single i) = true := by
    intro i hi
    rcases (memS i).mp (Or.inr hi) with (hu | ⟨u, hu, rfl⟩) | hp
    · rcases F1 i hu with ⟨a, _⟩ | ⟨_, b⟩
      · exact absurd hi (nl _ a)
      · rw [← B1_pair_left d2 i (d + i) (nl _ b)]; exact (hpp i hu).2
    · rcases F1 u hu with ⟨a, _⟩ | ⟨_, b⟩
      · rw [← B1_pair_right d2 u (d + u) (nl _ a)]; exact (hpp u hu).2
      · exact absurd hi (nl _ b)
    · exact (hPe _ hp).elim
  have c1 := B1_allsingles false S1 g1 r1 rfl F2a
  have c2 := B1_allsingles false S2 g2 r2 rfl F2b
  have hgz : ∀ z, g z = true ↔ (∃ i ∈ S1, z i = true) ∧ (∃ j ∈ S2, z j = true) := by
    intro z; rw [hg, Bool.and_eq_true, c1, c2]
  have pl : ∀ a b : ℕ, pair a b a = true := by intro a b; simp [pair]
  have pr : ∀ a b : ℕ, pair a b b = true := by intro a b; simp [pair]
  have F3 : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → (u ∈ S1 → v ∈ S2) ∧ (u ∈ S2 → v ∈ S1) := by
    intro u hu v hv huv
    have hf : g (pair u (d + v)) = false := by rw [h3 u hu v hv]; simp [huv]
    constructor
    · intro a
      rcases F1 v hv with ⟨_, b⟩ | ⟨a', _⟩
      · have : g (pair u (d + v)) = true := (hgz _).mpr ⟨⟨u, a, pl _ _⟩, ⟨d + v, b, pr _ _⟩⟩
        rw [hf] at this; exact absurd this (by decide)
      · exact a'
    · intro a
      rcases F1 v hv with ⟨a', _⟩ | ⟨_, b⟩
      · exact a'
      · have : g (pair u (d + v)) = true := (hgz _).mpr ⟨⟨d + v, b, pr _ _⟩, ⟨u, a, pl _ _⟩⟩
        rw [hf] at this; exact absurd this (by decide)
  refine ⟨fun z => ?_, ?_⟩
  · rw [hgz]
    constructor
    · rintro ⟨⟨i, hi, zi⟩, ⟨j, hj, zj⟩⟩
      rcases (memS i).mp (Or.inl hi) with (hu | ⟨u, hu, rfl⟩) | hp
      · rcases (memS j).mp (Or.inr hj) with (hv | ⟨v, hv, rfl⟩) | hp
        · have hij : i ≠ j := fun e => nl i hi (e ▸ hj)
          exact Or.inr (Or.inr ⟨i, hu, j, hv, hij,
            (hgz _).mpr ⟨⟨i, hi, pl _ _⟩, ⟨j, hj, pr _ _⟩⟩, Or.inl ⟨zi, zj⟩⟩)
        · by_cases e : i = v
          · subst e; exact Or.inr (Or.inl ⟨i, hu, zi, zj⟩)
          · exfalso
            rcases F1 v hv with ⟨a, _⟩ | ⟨_, b⟩
            · exact nl v a ((F3 i hu v hv e).1 hi)
            · exact nl _ b hj
        · exact (hPe _ hp).elim
      · have huS2 : u ∈ S2 := by
          rcases F1 u hu with ⟨_, b⟩ | ⟨a, _⟩
          · exact absurd hi (nr _ b)
          · exact a
        rcases (memS j).mp (Or.inr hj) with (hv | ⟨v, hv, rfl⟩) | hp
        · by_cases e : u = j
          · subst e; exact Or.inr (Or.inl ⟨u, hu, zj, zi⟩)
          · exfalso; exact nr j hj ((F3 u hu j hv e).2 huS2)
        · have hvS1 : v ∈ S1 := by
            rcases F1 v hv with ⟨a, _⟩ | ⟨_, b⟩
            · exact a
            · exact absurd hj (nl _ b)
          have e : u ≠ v := fun e => nr u huS2 (e ▸ hvS1)
          exact Or.inr (Or.inr ⟨u, hu, v, hv, e,
            (hgz _).mpr ⟨⟨v, hvS1, pr _ _⟩, ⟨u, huS2, pl _ _⟩⟩, Or.inr ⟨zi, zj⟩⟩)
        · exact (hPe _ hp).elim
      · exact (hPe _ hp).elim
    · rintro (⟨p, hp, _⟩ | ⟨u, hu, zu, zdu⟩ | ⟨u, hu, v, hv, huv, _, (⟨zu, zv⟩ | ⟨zu, zv⟩)⟩)
      · exact (hPe p hp).elim
      · rcases F1 u hu with ⟨a, b⟩ | ⟨a, b⟩
        · exact ⟨⟨u, a, zu⟩, ⟨d + u, b, zdu⟩⟩
        · exact ⟨⟨d + u, b, zdu⟩, ⟨u, a, zu⟩⟩
      · rcases F1 u hu with ⟨a, _⟩ | ⟨a, _⟩
        · exact ⟨⟨u, a, zu⟩, ⟨v, (F3 u hu v hv huv).1 a, zv⟩⟩
        · exact ⟨⟨v, (F3 u hu v hv huv).2 a, zv⟩, ⟨u, a, zu⟩⟩
      · rcases F1 u hu with ⟨a, b⟩ | ⟨a, b⟩
        · have hv2 := (F3 u hu v hv huv).1 a
          rcases F1 v hv with ⟨a', _⟩ | ⟨_, b'⟩
          · exact absurd hv2 (nl _ a')
          · exact ⟨⟨d + v, b', zv⟩, ⟨d + u, b, zu⟩⟩
        · have hv1 := (F3 u hu v hv huv).2 a
          rcases F1 v hv with ⟨_, b'⟩ | ⟨a', _⟩
          · exact ⟨⟨d + u, b, zu⟩, ⟨d + v, b', zv⟩⟩
          · exact absurd hv1 (nr _ a')
  · intro u hu v hv w hw huv huw _ _
    by_contra hvw
    rcases F1 u hu with ⟨a, _⟩ | ⟨a, _⟩
    · have hv2 := (F3 u hu v hv huv).1 a
      have hw2 := (F3 u hu w hw huw).1 a
      exact nl w ((F3 v hv w hw hvw).2 hv2) hw2
    · have hv1 := (F3 u hu v hv huv).2 a
      have hw1 := (F3 u hu w hw huw).2 a
      exact nl w hw1 ((F3 v hv w hw hvw).1 hv1)

theorem B1_main (d : ℕ) : ∀ (c : Bool) (S : Finset ℕ) (g : (ℕ → Bool) → Bool), ROx c S g →
    c = false → B1_Stmt d S g := by
  refine ROx_induct (P := fun c S g => c = false → B1_Stmt d S g) ?_ ?_ ?_
  · intro i _; exact B1_var_case d i
  · intro c S1 S2 g1 g2 b hdis r1 r2 ih1 ih2 hc
    subst hc
    cases b
    · exact B1_or_case d S1 S2 _ g1 g2 hdis r1 r2 (ih1 rfl) (ih2 rfl) (fun z => rfl)
    · exact B1_and_case d S1 S2 _ g1 g2 hdis r1 r2 (fun z => rfl)
  · intro S g _ _ hc; exact absurd hc (by decide)

theorem B_matching (d : ℕ) (S : Finset ℕ) (g : (ℕ → Bool) → Bool) (h : ROx false S g)
    (U P : Finset ℕ) (hU : ∀ u ∈ U, u < d) (hP : ∀ p ∈ P, p ∉ U ∧ ∀ u ∈ U, p ≠ d + u)
    (hS : S = U ∪ U.image (fun u => d + u) ∪ P)
    (h1 : ∀ p ∈ P, g (single p) = true)
    (h2 : ∀ u ∈ U, g (single u) = false ∧ g (single (d + u)) = false)
    (h3 : ∀ u ∈ U, ∀ v ∈ U, g (pair u (d + v)) = decide (u = v)) :
    (∀ z : ℕ → Bool, g z = true ↔ ((∃ p ∈ P, z p = true) ∨ (∃ u ∈ U, z u = true ∧ z (d + u) = true) ∨
      ∃ u ∈ U, ∃ v ∈ U, u ≠ v ∧ g (pair u v) = true ∧
        ((z u = true ∧ z v = true) ∨ (z (d + u) = true ∧ z (d + v) = true)))) ∧
    (∀ u ∈ U, ∀ v ∈ U, ∀ w ∈ U, u ≠ v → u ≠ w → g (pair u v) = true → g (pair u w) = true → v = w) :=
  B1_main d false S g h rfl U P hU hP hS h1 h2 h3


theorem B2_dep {c : Bool} {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx c S g) : DepOn S g := by
  refine ROx_induct (P := fun _ S g => DepOn S g) ?_ ?_ ?_ c S g h
  · intro i z z' hz
    exact hz i (Finset.mem_singleton_self i)
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 z z' hz
    have e1 : g1 z = g1 z' := ih1 z z' (fun i hi => hz i (Finset.mem_union_left _ hi))
    have e2 : g2 z = g2 z' := ih2 z z' (fun i hi => hz i (Finset.mem_union_right _ hi))
    simp only [e1, e2]
  · intro S g _ ih z z' hz
    have e := ih z z' hz
    simp only [e]

theorem B2_zero {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx false S g) :
    g (fun _ => false) = false := by
  refine ROx_induct (P := fun c _ g => c = false → g (fun _ => false) = false) ?_ ?_ ?_ false S g h rfl
  · intro i _; rfl
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 hc
    have e1 := ih1 hc
    have e2 := ih2 rfl
    simp only [e1, e2]
    cases b <;> rfl
  · intro S g _ _ hc
    exact absurd hc (by decide)

theorem B2_mono {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx false S g) :
    ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) → g z = true → g z' = true := by
  refine ROx_induct (P := fun c _ g => c = false →
    ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) → g z = true → g z' = true) ?_ ?_ ?_ false S g h rfl
  · intro i _ z z' hz hg
    exact hz i hg
  · intro c S1 S2 g1 g2 b _ _ _ ih1 ih2 hc z z' hz hg
    have m1 := ih1 hc z z' hz
    have m2 := ih2 rfl z z' hz
    cases b
    · simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl (m1 hg)
      · exact Or.inr (m2 hg)
    · simp only [ite_true, Bool.and_eq_true] at hg ⊢
      exact ⟨m1 hg.1, m2 hg.2⟩
  · intro S g _ _ hc
    exact absurd hc (by decide)

theorem B2_nonempty {c : Bool} {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx c S g) :
    S.Nonempty := by
  refine ROx_induct (P := fun _ S _ => S.Nonempty) ?_ ?_ ?_ c S g h
  · intro i; exact Finset.singleton_nonempty i
  · intro c S1 S2 g1 g2 b _ _ _ ih1 _
    exact ih1.mono Finset.subset_union_left
  · intro S g _ ih; exact ih

theorem B2_pair_left {S : Finset ℕ} {f : (ℕ → Bool) → Bool} (h : DepOn S f) (a b : ℕ)
    (hb : b ∉ S) : f (pair a b) = f (single a) := by
  apply h
  intro i hi
  have : i ≠ b := fun e => hb (e ▸ hi)
  simp [pair, single, this]

theorem B2_pair_right {S : Finset ℕ} {f : (ℕ → Bool) → Bool} (h : DepOn S f) (a b : ℕ)
    (ha : a ∉ S) : f (pair a b) = f (single b) := by
  apply h
  intro i hi
  have : i ≠ a := fun e => ha (e ▸ hi)
  simp [pair, single, this]

theorem B2_pair_none {S : Finset ℕ} {f : (ℕ → Bool) → Bool} (h : DepOn S f) (a b : ℕ)
    (ha : a ∉ S) (hb : b ∉ S) : f (pair a b) = f (fun _ => false) := by
  apply h
  intro i hi
  have h1 : i ≠ a := fun e => ha (e ▸ hi)
  have h2 : i ≠ b := fun e => hb (e ▸ hi)
  simp [pair, h1, h2]

theorem B2_or_same (d : ℕ) {S1 S2 : Finset ℕ} {g1 g2 : (ℕ → Bool) → Bool}
    (hdis : Disjoint S1 S2) (d1 : DepOn S1 g1) (d2 : DepOn S2 g2)
    (h2 : ∀ u < 3, (g1 (single u) || g2 (single u)) = false ∧
      (g1 (single (d + u)) || g2 (single (d + u))) = false)
    (h3 : ∀ u < 3, ∀ v < 3, (g1 (pair u (d + v)) || g2 (pair u (d + v))) = decide (u ≠ v))
    (u v : ℕ) (hu : u < 3) (hv : v < 3) (huv : u ≠ v) (hu1 : u ∈ S1) (hv2 : d + v ∈ S2) : False := by
  have hv1 : d + v ∉ S1 := fun h => Finset.disjoint_left.mp hdis h hv2
  have hu2 : u ∉ S2 := fun h => Finset.disjoint_left.mp hdis hu1 h
  have e := h3 u hu v hv
  rw [B2_pair_left d1 u (d + v) hv1, B2_pair_right d2 u (d + v) hu2] at e
  have a1 := (h2 u hu).1
  have a2 := (h2 v hv).2
  simp only [Bool.or_eq_false_iff] at a1 a2
  rw [a1.1, a2.2] at e
  simp [huv] at e

theorem B2_or_restrict (d : ℕ) {S1 S2 : Finset ℕ} {g1 g2 : (ℕ → Bool) → Bool}
    (hdis : Disjoint S1 S2) (d2 : DepOn S2 g2) (z2 : g2 (fun _ => false) = false)
    (hS : ∀ u < 3, u ∈ S1 ∧ d + u ∈ S1)
    (h2 : ∀ u < 3, (g1 (single u) || g2 (single u)) = false ∧
      (g1 (single (d + u)) || g2 (single (d + u))) = false)
    (h3 : ∀ u < 3, ∀ v < 3, (g1 (pair u (d + v)) || g2 (pair u (d + v))) = decide (u ≠ v)) :
    (∀ u < 3, g1 (single u) = false ∧ g1 (single (d + u)) = false) ∧
    (∀ u < 3, ∀ v < 3, g1 (pair u (d + v)) = decide (u ≠ v)) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have a := h2 u hu
    simp only [Bool.or_eq_false_iff] at a
    exact ⟨a.1.1, a.2.1⟩
  · intro u hu v hv
    have e := h3 u hu v hv
    have n1 : u ∉ S2 := fun h => Finset.disjoint_left.mp hdis (hS u hu).1 h
    have n2 : d + v ∉ S2 := fun h => Finset.disjoint_left.mp hdis (hS v hv).2 h
    rw [B2_pair_none d2 u (d + v) n1 n2, z2, Bool.or_false] at e
    exact e

theorem B2_and_case (d : ℕ) {S1 S2 : Finset ℕ} {g1 g2 : (ℕ → Bool) → Bool}
    (hdis : Disjoint S1 S2) (d1 : DepOn S1 g1) (d2 : DepOn S2 g2)
    (z1 : g1 (fun _ => false) = false) (z2 : g2 (fun _ => false) = false)
    (hS : ∀ u < 3, (u ∈ S1 ∨ u ∈ S2) ∧ (d + u ∈ S1 ∨ d + u ∈ S2))
    (h3 : ∀ u < 3, ∀ v < 3, (g1 (pair u (d + v)) && g2 (pair u (d + v))) = decide (u ≠ v))
    (h0 : 0 ∈ S1) : False := by
  have hn : ∀ a, a ∈ S1 → a ∉ S2 := fun a h h' => Finset.disjoint_left.mp hdis h h'
  have hn' : ∀ a, a ∈ S2 → a ∉ S1 := fun a h h' => Finset.disjoint_left.mp hdis h' h
  have diff1 : ∀ u < 3, ∀ v < 3, u ≠ v → u ∈ S1 → d + v ∈ S2 := by
    intro u hu v hv huv hu1
    rcases (hS v hv).2 with hv1 | hv2
    · exfalso
      have e := h3 u hu v hv
      rw [B2_pair_none d2 u (d + v) (hn _ hu1) (hn _ hv1), z2] at e
      simp [huv] at e
    · exact hv2
  have diff2 : ∀ u < 3, ∀ v < 3, u ≠ v → d + v ∈ S2 → u ∈ S1 := by
    intro u hu v hv huv hv2
    rcases (hS u hu).1 with hu1 | hu2
    · exact hu1
    · exfalso
      have e := h3 u hu v hv
      rw [B2_pair_none d1 u (d + v) (hn' _ hu2) (hn' _ hv2), z1] at e
      simp [huv] at e
  have y1 : d + 1 ∈ S2 := diff1 0 (by omega) 1 (by omega) (by omega) h0
  have y2 : d + 2 ∈ S2 := diff1 0 (by omega) 2 (by omega) (by omega) h0
  have x1 : 1 ∈ S1 := diff2 1 (by omega) 2 (by omega) (by omega) y2
  have y0 : d + 0 ∈ S2 := diff1 1 (by omega) 0 (by omega) (by omega) x1
  have e1 := h3 0 (by omega) 1 (by omega)
  have e2 := h3 1 (by omega) 0 (by omega)
  have e3 := h3 0 (by omega) 0 (by omega)
  rw [B2_pair_left d1 0 (d + 1) (hn' _ y1)] at e1
  rw [B2_pair_right d2 1 (d + 0) (hn _ x1)] at e2
  rw [B2_pair_left d1 0 (d + 0) (hn' _ y0), B2_pair_right d2 0 (d + 0) (hn _ h0)] at e3
  simp only [ne_eq, Nat.zero_ne_one, not_false_eq_true, decide_true, Bool.and_eq_true] at e1
  simp only [ne_eq, Nat.one_ne_zero, not_false_eq_true, decide_true, Bool.and_eq_true] at e2
  rw [e1.1, e2.2] at e3
  simp at e3

theorem B_crown_mono_impossible (d : ℕ) (hd : 3 ≤ d) (S : Finset ℕ) (g : (ℕ → Bool) → Bool)
    (h : ROx false S g)
    (hS : ∀ u < 3, u ∈ S ∧ d + u ∈ S)
    (h2 : ∀ u < 3, g (single u) = false ∧ g (single (d + u)) = false)
    (h3 : ∀ u < 3, ∀ v < 3, g (pair u (d + v)) = decide (u ≠ v)) : False := by
  refine ROx_induct (P := fun c S g => c = false → (∀ u < 3, u ∈ S ∧ d + u ∈ S) →
    (∀ u < 3, g (single u) = false ∧ g (single (d + u)) = false) →
    (∀ u < 3, ∀ v < 3, g (pair u (d + v)) = decide (u ≠ v)) → False) ?_ ?_ ?_ false S g h rfl hS h2 h3
  · intro i _ hS _ _
    have a := (hS 0 (by omega)).1
    have b := (hS 1 (by omega)).1
    rw [Finset.mem_singleton] at a b
    omega
  · intro c S1 S2 g1 g2 b hdis r1 r2 ih1 ih2 hc hS h2 h3
    subst hc
    have d1 := B2_dep r1
    have d2 := B2_dep r2
    have z1 := B2_zero r1
    have z2 := B2_zero r2
    have hS' : ∀ u < 3, (u ∈ S1 ∨ u ∈ S2) ∧ (d + u ∈ S1 ∨ d + u ∈ S2) := by
      intro u hu
      have a := hS u hu
      simp only [Finset.mem_union] at a
      exact a
    cases b
    · simp only [Bool.false_eq_true, ite_false] at h2 h3
      have h2s : ∀ u < 3, (g2 (single u) || g1 (single u)) = false ∧
          (g2 (single (d + u)) || g1 (single (d + u))) = false := by
        intro u hu
        have a := h2 u hu
        rw [Bool.or_comm (g2 _), Bool.or_comm (g2 _)]
        exact a
      have h3s : ∀ u < 3, ∀ v < 3,
          (g2 (pair u (d + v)) || g1 (pair u (d + v))) = decide (u ≠ v) := by
        intro u hu v hv
        rw [Bool.or_comm]
        exact h3 u hu v hv
      have k12 : ∀ u < 3, ∀ v < 3, u ≠ v → u ∈ S1 → d + v ∈ S1 := by
        intro u hu v hv huv hu1
        rcases (hS' v hv).2 with q | q
        · exact q
        · exact (B2_or_same d hdis d1 d2 h2 h3 u v hu hv huv hu1 q).elim
      have k21 : ∀ u < 3, ∀ v < 3, u ≠ v → u ∈ S2 → d + v ∈ S2 := by
        intro u hu v hv huv hu2
        rcases (hS' v hv).2 with q | q
        · exact (B2_or_same d hdis.symm d2 d1 h2s h3s u v hu hv huv hu2 q).elim
        · exact q
      have k12' : ∀ u < 3, ∀ v < 3, u ≠ v → d + v ∈ S1 → u ∈ S1 := by
        intro u hu v hv huv hv1
        rcases (hS' u hu).1 with q | q
        · exact q
        · exact (Finset.disjoint_left.mp hdis hv1 (k21 u hu v hv huv q)).elim
      have k21' : ∀ u < 3, ∀ v < 3, u ≠ v → d + v ∈ S2 → u ∈ S2 := by
        intro u hu v hv huv hv2
        rcases (hS' u hu).1 with q | q
        · exact (Finset.disjoint_left.mp hdis (k12 u hu v hv huv q) hv2).elim
        · exact q
      rcases (hS' 0 (by omega)).1 with q | q
      · have y1 := k12 0 (by omega) 1 (by omega) (by omega) q
        have y2 := k12 0 (by omega) 2 (by omega) (by omega) q
        have x2 := k12' 2 (by omega) 1 (by omega) (by omega) y1
        have x1 := k12' 1 (by omega) 2 (by omega) (by omega) y2
        have y0 := k12 1 (by omega) 0 (by omega) (by omega) x1
        have all1 : ∀ u < 3, u ∈ S1 ∧ d + u ∈ S1 := by
          intro u hu
          have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
          rcases this with rfl | rfl | rfl
          · exact ⟨q, y0⟩
          · exact ⟨x1, y1⟩
          · exact ⟨x2, y2⟩
        obtain ⟨a, b⟩ := B2_or_restrict d hdis d2 z2 all1 h2 h3
        exact ih1 rfl all1 a b
      · have y1 := k21 0 (by omega) 1 (by omega) (by omega) q
        have y2 := k21 0 (by omega) 2 (by omega) (by omega) q
        have x2 := k21' 2 (by omega) 1 (by omega) (by omega) y1
        have x1 := k21' 1 (by omega) 2 (by omega) (by omega) y2
        have y0 := k21 1 (by omega) 0 (by omega) (by omega) x1
        have all2 : ∀ u < 3, u ∈ S2 ∧ d + u ∈ S2 := by
          intro u hu
          have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
          rcases this with rfl | rfl | rfl
          · exact ⟨q, y0⟩
          · exact ⟨x1, y1⟩
          · exact ⟨x2, y2⟩
        obtain ⟨a, b⟩ := B2_or_restrict d hdis.symm d1 z1 all2 h2s h3s
        exact ih2 rfl all2 a b
    · simp only [ite_true] at h2 h3
      rcases (hS' 0 (by omega)).1 with q | q
      · exact B2_and_case d hdis d1 d2 z1 z2 hS' h3 q
      · refine B2_and_case d hdis.symm d2 d1 z2 z1 (fun u hu => ⟨(hS' u hu).1.symm, (hS' u hu).2.symm⟩) ?_ q
        intro u hu v hv
        rw [Bool.and_comm]
        exact h3 u hu v hv
  · intro S g _ _ hc
    exact absurd hc (by decide)

theorem B_decomp {S : Finset ℕ} {g : (ℕ → Bool) → Bool} (h : ROx true S g) :
    ∃ (S1 S2 : Finset ℕ) (s : (ℕ → Bool) → Bool) (T : Bool → (ℕ → Bool) → Bool),
      Disjoint S1 S2 ∧ S = S1 ∪ S2 ∧ ROx false S2 s ∧ (∀ b, DepOn S1 (T b)) ∧
      (∀ b (z z' : ℕ → Bool), (∀ i, z i = true → z' i = true) → T b z = true → T b z' = true) ∧
      (∀ z, T false z = true → T true z = true) ∧ (∀ z, g z = T (!s z) z) ∧
      (S1 = ∅ → ∀ b z, T b z = b) := by
  refine ROx_induct (P := fun c S g => c = true →
    ∃ (S1 S2 : Finset ℕ) (s : (ℕ → Bool) → Bool) (T : Bool → (ℕ → Bool) → Bool),
      Disjoint S1 S2 ∧ S = S1 ∪ S2 ∧ ROx false S2 s ∧ (∀ b, DepOn S1 (T b)) ∧
      (∀ b (z z' : ℕ → Bool), (∀ i, z i = true → z' i = true) → T b z = true → T b z' = true) ∧
      (∀ z, T false z = true → T true z = true) ∧ (∀ z, g z = T (!s z) z) ∧
      (S1 = ∅ → ∀ b z, T b z = b)) ?_ ?_ ?_ true S g h rfl
  · intro i hc
    exact absurd hc (by decide)
  · intro c Sa Sb g1 g2 b hdis _ r2 ih1 _ hc
    obtain ⟨S1, S2, s, T, hd12, hSa, rs, hdep, hmono, hft, hg, _⟩ := ih1 hc
    have d2 := B2_dep r2
    have m2 := B2_mono r2
    have hsub : S2 ⊆ Sa := by rw [hSa]; exact Finset.subset_union_right
    have hsub1 : S1 ⊆ Sa := by rw [hSa]; exact Finset.subset_union_left
    refine ⟨S1 ∪ Sb, S2, s, fun bb z => if b then (T bb z && g2 z) else (T bb z || g2 z),
      ?_, ?_, rs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_left]
      exact ⟨hd12, (Finset.disjoint_of_subset_left hsub hdis).symm⟩
    · rw [hSa, Finset.union_right_comm]
    · intro bb z z' hz
      have e1 : T bb z = T bb z' := hdep bb z z' (fun i hi => hz i (Finset.mem_union_left _ hi))
      have e2 : g2 z = g2 z' := d2 z z' (fun i hi => hz i (Finset.mem_union_right _ hi))
      simp only [e1, e2]
    · intro bb z z' hz hT
      have a1 := hmono bb z z' hz
      have a2 := m2 z z' hz
      cases b
      · simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at hT ⊢
        rcases hT with hT | hT
        · exact Or.inl (a1 hT)
        · exact Or.inr (a2 hT)
      · simp only [ite_true, Bool.and_eq_true] at hT ⊢
        exact ⟨a1 hT.1, a2 hT.2⟩
    · intro z hT
      have a1 := hft z
      cases b
      · simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at hT ⊢
        rcases hT with hT | hT
        · exact Or.inl (a1 hT)
        · exact Or.inr hT
      · simp only [ite_true, Bool.and_eq_true] at hT ⊢
        exact ⟨a1 hT.1, hT.2⟩
    · intro z
      simp only [hg z]
    · intro he
      exfalso
      have hb := B2_nonempty r2
      obtain ⟨x, hx⟩ := hb
      have : x ∈ S1 ∪ Sb := Finset.mem_union_right _ hx
      rw [he] at this
      exact absurd this (Finset.notMem_empty x)
  · intro S g r _ _
    refine ⟨∅, S, g, fun bb _ => bb, Finset.disjoint_empty_left S, (Finset.empty_union S).symm, r,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro bb z z' _; rfl
    · intro bb z z' _ hT; exact hT
    · intro z hT; exact absurd hT Bool.false_ne_true
    · intro z; rfl
    · intro _ bb z; rfl


def partner (a : ℕ → Bool) (u : ℕ) : ℕ :=
  6 * (u / 6) + (if a (u / 6) then (if u % 6 % 2 = 0 then u % 6 + 1 else u % 6 - 1)
    else (if u % 6 % 2 = 1 then (u % 6 + 1) % 6 else (u % 6 + 5) % 6))

theorem C_wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    ((Circuit.mk gs o).wires x).length = x.length + gs.length := by
  unfold Circuit.wires
  simp only
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem C_fn_snoc (gs : List Gate) (g : Gate) (N w : ℕ) (z : ℕ → Bool) :
    fn (gs ++ [g]) N w z = if w < N + gs.length then fn gs N w z
      else if w = N + gs.length then g.op.eval (g.inputs.map fun i => fn gs N i z) else false := by
  have hl := C_wires_length gs 0 (List.ofFn fun i : Fin N => z i)
  simp only [List.length_ofFn] at hl
  unfold fn
  unfold Circuit.wires at hl ⊢
  simp only at hl ⊢
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), hl, h2, Nat.sub_self]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have : w - (N + gs.length) ≠ 0 := by omega
    rw [hl]
    cases hh : w - (N + gs.length) with
    | zero => exact absurd hh this
    | succ k => simp

theorem C_fn_snoc_lt (gs : List Gate) (g : Gate) (N w : ℕ) (z : ℕ → Bool) (h : w < N + gs.length) :
    fn (gs ++ [g]) N w z = fn gs N w z := by
  rw [C_fn_snoc, if_pos h]

theorem C_fn_snoc_eq (gs : List Gate) (g : Gate) (N w : ℕ) (z : ℕ → Bool) (h : w = N + gs.length) :
    fn (gs ++ [g]) N w z = g.op.eval (g.inputs.map fun i => fn gs N i z) := by
  rw [C_fn_snoc, if_neg (by omega), if_pos h]

theorem C_fn_input (gs : List Gate) (N w : ℕ) (z : ℕ → Bool) (hw : w < N) :
    fn gs N w z = z w := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold fn Circuit.wires
    simp [List.getD_eq_getElem?_getD, hw]
  | append_singleton gs g ih =>
    rw [C_fn_snoc, if_pos (by omega), ih]

def C_pu (a : ℕ → Bool) (q : ℕ) : ℕ := 6 * (q / 3) + (if a (q / 3) then 2 * (q % 3) else 2 * (q % 3) + 1)
def C_pv (a : ℕ → Bool) (q : ℕ) : ℕ :=
  6 * (q / 3) + (if a (q / 3) then 2 * (q % 3) + 1 else (2 * (q % 3) + 2) % 6)

def C_build (a : ℕ → Bool) (n d N : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, [6 * n, d + 6 * n]⟩]
  | p + 1 => C_build a n d N p ++ [⟨GateOp.or, [C_pu a p, d + C_pv a p]⟩,
      ⟨GateOp.or, [d + C_pu a p, C_pv a p]⟩,
      ⟨GateOp.and, [N + 4 * p + 1, N + 4 * p + 2]⟩,
      ⟨GateOp.or, [N + 4 * p, N + 4 * p + 3]⟩]

theorem C_build_length (a : ℕ → Bool) (n d N p : ℕ) : (C_build a n d N p).length = 4 * p + 1 := by
  induction p with
  | zero => rfl
  | succ p ih => simp [C_build, ih]; omega

theorem C_build_gates (a : ℕ → Bool) (n d N p : ℕ) :
    ∀ g ∈ C_build a n d N p, g.inputs.length ≤ 2 ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  induction p with
  | zero => intro g hg; simp [C_build] at hg; subst hg; simp
  | succ p ih =>
    intro g hg
    simp only [C_build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg | hg | hg
    · exact ih g hg
    all_goals subst hg; simp

theorem C_step (gs : List Gate) (N L L1 L2 L3 o i1 j1 i2 j2 : ℕ) (z : ℕ → Bool)
    (hL : L = N + gs.length) (hL1 : L1 = L + 1) (hL2 : L2 = L + 2) (hL3 : L3 = L + 3)
    (ho : o < L) (h1 : i1 < N) (h2 : j1 < N) (h3 : i2 < N) (h4 : j2 < N) :
    fn (gs ++ [⟨GateOp.or, [i1, j1]⟩, ⟨GateOp.or, [i2, j2]⟩, ⟨GateOp.and, [L, L1]⟩,
      ⟨GateOp.or, [o, L2]⟩]) N L3 z =
      (fn gs N o z || ((z i1 || z j1) && (z i2 || z j2))) := by
  subst hL hL1 hL2 hL3
  have e : gs ++ [(⟨GateOp.or, [i1, j1]⟩ : Gate), ⟨GateOp.or, [i2, j2]⟩,
      ⟨GateOp.and, [N + gs.length, N + gs.length + 1]⟩, ⟨GateOp.or, [o, N + gs.length + 2]⟩] =
      (((gs ++ [⟨GateOp.or, [i1, j1]⟩]) ++ [⟨GateOp.or, [i2, j2]⟩]) ++
        [⟨GateOp.and, [N + gs.length, N + gs.length + 1]⟩]) ++ [⟨GateOp.or, [o, N + gs.length + 2]⟩] := by
    simp
  rw [e]
  have l1 : (gs ++ [(⟨GateOp.or, [i1, j1]⟩ : Gate)]).length = gs.length + 1 := by simp
  have l2 : (gs ++ [(⟨GateOp.or, [i1, j1]⟩ : Gate)] ++ [(⟨GateOp.or, [i2, j2]⟩ : Gate)]).length = gs.length + 2 := by simp
  have l3 : (gs ++ [(⟨GateOp.or, [i1, j1]⟩ : Gate)] ++ [(⟨GateOp.or, [i2, j2]⟩ : Gate)] ++
        [(⟨GateOp.and, [N + gs.length, N + gs.length + 1]⟩ : Gate)]).length = gs.length + 3 := by simp
  rw [C_fn_snoc_eq _ _ _ _ _ (by rw [l3]; omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
  rw [C_fn_snoc_lt _ _ _ _ _ (by rw [l2]; omega), C_fn_snoc_lt _ _ _ _ _ (by rw [l1]; omega),
    C_fn_snoc_lt _ _ _ _ _ ho, C_fn_snoc_eq _ _ _ _ _ (by rw [l2]; omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
  rw [C_fn_snoc_lt _ _ _ _ _ (by rw [l1]; omega), C_fn_snoc_eq _ _ _ _ _ rfl,
    C_fn_snoc_eq _ _ _ _ _ (by rw [l1]; omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
    C_fn_input _ _ _ _ h1, C_fn_input _ _ _ _ h2, C_fn_input _ _ _ _ h3, C_fn_input _ _ _ _ h4]

theorem C_pu_lt (a : ℕ → Bool) (n q : ℕ) (hq : q < 3 * n) : C_pu a q < 6 * n := by
  unfold C_pu; split_ifs <;> omega

theorem C_pv_lt (a : ℕ → Bool) (n q : ℕ) (hq : q < 3 * n) : C_pv a q < 6 * n := by
  unfold C_pv; split_ifs <;> omega

theorem C_build_fn (a : ℕ → Bool) (n d N : ℕ) (_hd : 6 * n + 1 ≤ d) (hN : d + 6 * n + 1 ≤ N)
    (z : ℕ → Bool) (p : ℕ) (hp : p ≤ 3 * n) :
    fn (C_build a n d N p) N (N + 4 * p) z = ((z (6 * n) && z (d + 6 * n)) ||
      decide (∃ q, q < p ∧ (z (C_pu a q) = true ∨ z (d + C_pv a q) = true) ∧
        (z (d + C_pu a q) = true ∨ z (C_pv a q) = true))) := by
  induction p with
  | zero =>
    have : C_build a n d N 0 = [] ++ [(⟨GateOp.and, [6 * n, d + 6 * n]⟩ : Gate)] := rfl
    rw [this, C_fn_snoc_eq _ _ _ _ _ (by simp)]
    simp [GateOp.eval, C_fn_input _ _ _ _ (show 6 * n < N by omega),
      C_fn_input _ _ _ _ (show d + 6 * n < N by omega)]
  | succ p ih =>
    have hu := C_pu_lt a n p (by omega)
    have hv := C_pv_lt a n p (by omega)
    have hl := C_build_length a n d N p
    have := C_step (C_build a n d N p) N (N + 4 * p + 1) (N + 4 * p + 2) (N + 4 * p + 3)
      (N + 4 * (p + 1)) (N + 4 * p) (C_pu a p) (d + C_pv a p) (d + C_pu a p) (C_pv a p) z
      (by rw [hl]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    simp only [C_build]
    rw [this, ih (by omega)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | ⟨q, hq, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, h⟩
      · exact Or.inr ⟨p, by omega, h⟩
    · rintro (h | ⟨q, hq, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h' | h'
        · exact Or.inl (Or.inr ⟨q, h', h⟩)
        · subst h'; exact Or.inr h

theorem C_partner_pu (a : ℕ → Bool) (q : ℕ) : partner a (C_pu a q) = C_pv a q := by
  have e1 : C_pu a q / 6 = q / 3 := by unfold C_pu; split_ifs <;> omega
  unfold partner
  rw [e1]
  unfold C_pu C_pv
  cases h : a (q / 3) <;> simp only [if_true, if_false, Bool.false_eq_true] <;> split_ifs <;> omega

theorem C_partner_pv (a : ℕ → Bool) (q : ℕ) : partner a (C_pv a q) = C_pu a q := by
  have e1 : C_pv a q / 6 = q / 3 := by unfold C_pv; split_ifs <;> omega
  unfold partner
  rw [e1]
  unfold C_pu C_pv
  cases h : a (q / 3) <;> simp only [if_true, if_false, Bool.false_eq_true] <;> split_ifs <;> omega

theorem C_cover (a : ℕ → Bool) (u : ℕ) : ∃ q, q / 3 = u / 6 ∧ (u = C_pu a q ∨ u = C_pv a q) := by
  cases h : a (u / 6)
  · refine ⟨3 * (u / 6) + (u % 6 + 5) % 6 / 2, by omega, ?_⟩
    have e : (3 * (u / 6) + (u % 6 + 5) % 6 / 2) / 3 = u / 6 := by omega
    unfold C_pu C_pv
    rw [e, h]
    simp only [if_false, Bool.false_eq_true]
    omega
  · refine ⟨3 * (u / 6) + u % 6 / 2, by omega, ?_⟩
    have e : (3 * (u / 6) + u % 6 / 2) / 3 = u / 6 := by omega
    unfold C_pu C_pv
    rw [e, h]
    simp only [if_true]
    omega

theorem C_final (a : ℕ → Bool) (n d : ℕ) (z : ℕ → Bool) :
    ((z (6 * n) = true ∧ z (d + 6 * n) = true) ∨
      (∃ q, q < 3 * n ∧ (z (C_pu a q) = true ∨ z (d + C_pv a q) = true) ∧
        (z (d + C_pu a q) = true ∨ z (C_pv a q) = true))) ↔
    ((∃ u, u < 6 * n + 1 ∧ z u = true ∧ z (d + u) = true) ∨
      ∃ u, u < 6 * n ∧ ((z u = true ∧ z (partner a u) = true) ∨
        (z (d + u) = true ∧ z (d + partner a u) = true))) := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨q, hq, h1 | h1, h2 | h2⟩)
    · exact Or.inl ⟨6 * n, by omega, h1, h2⟩
    · exact Or.inl ⟨_, by have := C_pu_lt a n q hq; omega, h1, h2⟩
    · exact Or.inr ⟨_, C_pu_lt a n q hq, Or.inl ⟨h1, by rw [C_partner_pu]; exact h2⟩⟩
    · exact Or.inr ⟨_, C_pu_lt a n q hq, Or.inr ⟨h2, by rw [C_partner_pu]; exact h1⟩⟩
    · exact Or.inl ⟨_, by have := C_pv_lt a n q hq; omega, h2, h1⟩
  · have key : ∀ q, q < 3 * n → (z (C_pu a q) = true ∧ z (d + C_pu a q) = true) ∨
        (z (C_pv a q) = true ∧ z (d + C_pv a q) = true) ∨
        (z (C_pu a q) = true ∧ z (C_pv a q) = true) ∨
        (z (d + C_pu a q) = true ∧ z (d + C_pv a q) = true) →
        ∃ q, q < 3 * n ∧ (z (C_pu a q) = true ∨ z (d + C_pv a q) = true) ∧
          (z (d + C_pu a q) = true ∨ z (C_pv a q) = true) := by
      intro q hq h
      refine ⟨q, hq, ?_⟩
      tauto
    rintro (⟨u, hu, h1, h2⟩ | ⟨u, hu, h⟩)
    · by_cases hu' : u = 6 * n
      · subst hu'; exact Or.inl ⟨h1, h2⟩
      · obtain ⟨q, hq, e | e⟩ := C_cover a u
        · exact Or.inr (key q (by omega) (Or.inl (by rw [← e]; exact ⟨h1, h2⟩)))
        · exact Or.inr (key q (by omega) (Or.inr (Or.inl (by rw [← e]; exact ⟨h1, h2⟩))))
    · obtain ⟨q, hq, e | e⟩ := C_cover a u
      · have ep : partner a u = C_pv a q := by rw [e, C_partner_pu]
        rw [ep] at h
        refine Or.inr (key q (by omega) (Or.inr (Or.inr ?_)))
        rw [← e]; exact h
      · have ep : partner a u = C_pu a q := by rw [e, C_partner_pv]
        rw [ep] at h
        refine Or.inr (key q (by omega) (Or.inr (Or.inr ?_)))
        rw [← e]; tauto

theorem C_clean (n : ℕ) (hn : 0 < n) (a : ℕ → Bool) (crown : Bool) (d N : ℕ)
    (hd : 6 * n + 1 ≤ d) (hd' : crown = true → 6 * n + 3 ≤ d) (hN : d + 6 * n + 1 ≤ N) :
    ∃ gs : List Gate, ∃ o : ℕ,
      gs.length = (if crown then 2 * (6 * n + 1) + 1 else 2 * (6 * n + 1) - 1) ∧
      (∀ g ∈ gs, g.inputs.length ≤ 2 ∧
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (crown = true ∧ g.op = GateOp.not))) ∧
      ∀ z : ℕ → Bool, fn gs N o z = xor crown (decide (
        (crown = true ∧ z (6 * n + 2) = true) ∨
        (∃ u, u < 6 * n + 1 ∧ z u = true ∧ z (d + u) = true) ∨
        ∃ u, u < 6 * n ∧ ((z u = true ∧ z (partner a u) = true) ∨
          (z (d + u) = true ∧ z (d + partner a u) = true)))) := by
  have hl := C_build_length a n d N (3 * n)
  have hg := C_build_gates a n d N (3 * n)
  have hf := fun z => C_build_fn a n d N hd hN z (3 * n) le_rfl
  have hfin := C_final a n d
  cases crown
  · refine ⟨C_build a n d N (3 * n), N + 4 * (3 * n), ?_, ?_, ?_⟩
    · rw [hl]; simp; omega
    · intro g h
      obtain ⟨h1, h2 | h2⟩ := hg g h
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr (Or.inl h2)⟩
    · intro z
      rw [hf z, Bool.eq_iff_iff]
      simp only [Bool.false_bne, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.false_eq_true, false_and, false_or]
      exact hfin z
  · have hd3 := hd' rfl
    refine ⟨(C_build a n d N (3 * n) ++ [⟨GateOp.or, [N + 4 * (3 * n), 6 * n + 2]⟩]) ++
      [⟨GateOp.not, [N + 4 * (3 * n) + 1]⟩], N + 4 * (3 * n) + 2, ?_, ?_, ?_⟩
    · simp [hl]; omega
    · intro g h
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (h | h) | h
      · obtain ⟨h1, h2 | h2⟩ := hg g h
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr (Or.inl h2)⟩
      · subst h; simp
      · subst h; simp
    · intro z
      rw [C_fn_snoc_eq _ _ _ _ _ (by simp [hl]; omega)]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rw [C_fn_snoc_eq _ _ _ _ _ (by rw [hl]; omega)]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
      rw [hf z, C_fn_input _ _ _ _ (by omega)]
      have := hfin z
      rw [Bool.eq_iff_iff]
      simp only [Bool.true_bne, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_imp,
        decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true, true_and]
      by_cases hz : z (6 * n + 2) = true
      · simp [hz]
      · simp only [hz, false_or, ← this]
        simp only [Bool.not_eq_true] at hz
        simp [hz]

def TR (k : ℕ) (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∃ u v, u < k ∧ v < k ∧ u ≠ v ∧ R u v ∧ P u ∧ P v

def tripleP (i s : ℕ) (u : ℕ) : Prop :=
  u = 6 * i + s ∨ u = 6 * i + (s + 1) % 6 ∨ u = 6 * i + (s + 2) % 6

def litP (i : ℕ) (sgn : Bool) (u : ℕ) : Prop :=
  u = 6 * i ∨ u = 6 * i + (if sgn then 1 else 5)

def wordP {n m : ℕ} (clauses : Fin m → Finset (Fin n × Bool)) (j : Fin m) (u : ℕ) : Prop :=
  ∃ lit ∈ clauses j, litP lit.1.val lit.2 u

def Ra (n : ℕ) (a : ℕ → Bool) (u v : ℕ) : Prop := u < 6 * n ∧ v = partner a u

theorem E_partner_block (a : ℕ → Bool) (u : ℕ) : partner a u / 6 = u / 6 := by
  unfold partner
  split_ifs <;> omega

theorem E_partner_true (a : ℕ → Bool) (u : ℕ) (h : a (u / 6) = true) :
    (partner a u = u + 1 ∧ u % 6 % 2 = 0) ∨ (partner a u + 1 = u ∧ u % 6 % 2 = 1) := by
  unfold partner
  rw [h]
  simp only [ite_true]
  split_ifs <;> omega

theorem E_partner_false (a : ℕ → Bool) (u : ℕ) (h : a (u / 6) = false) :
    (u % 6 % 2 = 1 ∧ u % 6 ≠ 5 ∧ partner a u = u + 1) ∨ (u % 6 = 5 ∧ partner a u + 5 = u) ∨
    (u % 6 = 0 ∧ partner a u = u + 5) ∨ (u % 6 % 2 = 0 ∧ u % 6 ≠ 0 ∧ partner a u + 1 = u) := by
  unfold partner
  rw [h]
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> omega

theorem E_partner_ne (a : ℕ → Bool) (u : ℕ) : partner a u ≠ u := by
  cases h : a (u / 6)
  · have := E_partner_false a u h; omega
  · have := E_partner_true a u h; omega

theorem E_partner_invol (a : ℕ → Bool) (u : ℕ) : partner a (partner a u) = u := by
  have hb := E_partner_block a u
  cases h : a (u / 6)
  · have h1 := E_partner_false a u h
    have h2 := E_partner_false a (partner a u) (by rw [hb]; exact h)
    omega
  · have h1 := E_partner_true a u h
    have h2 := E_partner_true a (partner a u) (by rw [hb]; exact h)
    omega

theorem E_conf (k : ℕ) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    {x y x' y' : ℕ} (h1 : R x y) (h2 : R x' y')
    (hc : x < k ∧ y < k ∧ x' < k ∧ y' < k ∧ x ≠ y ∧ x' ≠ y' ∧
      ((x = x' ∧ y ≠ y') ∨ (x = y' ∧ y ≠ x') ∨ (y = x' ∧ x ≠ y') ∨ (y = y' ∧ x ≠ x'))) : False := by
  obtain ⟨hx, hy, hx', hy', hxy, hxy', hc⟩ := hc
  rcases hc with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · subst e
    exact h (hmat x y y' hx hy hy' hxy hxy' h1 h2)
  · subst e
    exact h (hmat x y x' hx hy hx' hxy (Ne.symm hxy') h1 (hsym _ _ h2))
  · subst e
    exact h (hmat y x y' hy hx hy' (Ne.symm hxy) hxy' (hsym _ _ h1) h2)
  · subst e
    exact h (hmat y x x' hy hx hx' (Ne.symm hxy) (Ne.symm hxy') (hsym _ _ h1) (hsym _ _ h2))

theorem E_tri (k : ℕ) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u) (i s : ℕ)
    (h : TR k R (tripleP i s)) :
    R (6 * i + s) (6 * i + (s + 1) % 6) ∨ R (6 * i + (s + 1) % 6) (6 * i + (s + 2) % 6) ∨
      R (6 * i + s) (6 * i + (s + 2) % 6) := by
  obtain ⟨u, v, _, _, hne, hR, hu, hv⟩ := h
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl hR
  · exact Or.inr (Or.inr hR)
  · exact Or.inl (hsym _ _ hR)
  · exact absurd rfl hne
  · exact Or.inr (Or.inl hR)
  · exact Or.inr (Or.inr (hsym _ _ hR))
  · exact Or.inr (Or.inl (hsym _ _ hR))
  · exact absurd rfl hne

theorem E_phase (n k : ℕ) (hk : k = 6 * n + 1) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    (i : ℕ) (hi : i < n) (hs : ∀ s < 6, TR k R (tripleP i s)) :
    (R (6 * i) (6 * i + 1) ∧ R (6 * i + 2) (6 * i + 3) ∧ R (6 * i + 4) (6 * i + 5)) ∨
    (R (6 * i + 5) (6 * i) ∧ R (6 * i + 1) (6 * i + 2) ∧ R (6 * i + 3) (6 * i + 4)) := by
  have t0 : R (6 * i) (6 * i + 1) ∨ R (6 * i + 1) (6 * i + 2) ∨ R (6 * i) (6 * i + 2) :=
    E_tri k R hsym i 0 (hs 0 (by omega))
  have t1 : R (6 * i + 1) (6 * i + 2) ∨ R (6 * i + 2) (6 * i + 3) ∨ R (6 * i + 1) (6 * i + 3) :=
    E_tri k R hsym i 1 (hs 1 (by omega))
  have t2 : R (6 * i + 2) (6 * i + 3) ∨ R (6 * i + 3) (6 * i + 4) ∨ R (6 * i + 2) (6 * i + 4) :=
    E_tri k R hsym i 2 (hs 2 (by omega))
  have t3 : R (6 * i + 3) (6 * i + 4) ∨ R (6 * i + 4) (6 * i + 5) ∨ R (6 * i + 3) (6 * i + 5) :=
    E_tri k R hsym i 3 (hs 3 (by omega))
  have t4 : R (6 * i + 4) (6 * i + 5) ∨ R (6 * i + 5) (6 * i) ∨ R (6 * i + 4) (6 * i) :=
    E_tri k R hsym i 4 (hs 4 (by omega))
  have cf := @E_conf k R hsym hmat
  rcases t0 with a | a | a
  · rcases t1 with b | b | b
    · exact (cf a b (by omega)).elim
    · rcases t3 with c | c | c
      · exact (cf b c (by omega)).elim
      · exact Or.inl ⟨a, b, c⟩
      · exact (cf b c (by omega)).elim
    · exact (cf a b (by omega)).elim
  · rcases t2 with b | b | b
    · exact (cf a b (by omega)).elim
    · rcases t4 with c | c | c
      · exact (cf b c (by omega)).elim
      · exact Or.inr ⟨c, a, b⟩
      · exact (cf b c (by omega)).elim
    · exact (cf a b (by omega)).elim
  · rcases t1 with b | b | b
    · exact (cf a b (by omega)).elim
    · exact (cf a b (by omega)).elim
    · rcases t2 with c | c | c
      · exact (cf a c (by omega)).elim
      · exact (cf b c (by omega)).elim
      · exact (cf a c (by omega)).elim

theorem E_blockpart (n k : ℕ) (hk : k = 6 * n + 1) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    (i : ℕ) (hi : i < n) (hs : ∀ s < 6, TR k R (tripleP i s)) (a : ℕ → Bool)
    (ha : a i = true ↔ TR k R (litP i true)) :
    ∀ s, s < 6 → R (6 * i + s) (partner a (6 * i + s)) := by
  rcases E_phase n k hk R hsym hmat i hi hs with ⟨h01, h23, h45⟩ | ⟨h50, h12, h34⟩
  · have ai : a i = true :=
      ha.mpr ⟨6 * i, 6 * i + 1, by omega, by omega, by omega, h01, Or.inl rfl, Or.inr rfl⟩
    intro s hs'
    have ht := E_partner_true a (6 * i + s) (by rw [show (6 * i + s) / 6 = i by omega]; exact ai)
    interval_cases s
    · rw [show partner a (6 * i + 0) = 6 * i + 1 by omega]; exact h01
    · rw [show partner a (6 * i + 1) = 6 * i + 0 by omega]; exact hsym _ _ h01
    · rw [show partner a (6 * i + 2) = 6 * i + 3 by omega]; exact h23
    · rw [show partner a (6 * i + 3) = 6 * i + 2 by omega]; exact hsym _ _ h23
    · rw [show partner a (6 * i + 4) = 6 * i + 5 by omega]; exact h45
    · rw [show partner a (6 * i + 5) = 6 * i + 4 by omega]; exact hsym _ _ h45
  · have ai : a i = false := by
      cases hai : a i
      · rfl
      · exfalso
        obtain ⟨u, v, hu, hv, hne, hR, pu, pv⟩ := ha.mp hai
        simp only [litP, ite_true] at pu pv
        exact E_conf k R hsym hmat hR h50 (by omega)
    intro s hs'
    have ht := E_partner_false a (6 * i + s) (by rw [show (6 * i + s) / 6 = i by omega]; exact ai)
    interval_cases s
    · rw [show partner a (6 * i + 0) = 6 * i + 5 by omega]; exact hsym _ _ h50
    · rw [show partner a (6 * i + 1) = 6 * i + 2 by omega]; exact h12
    · rw [show partner a (6 * i + 2) = 6 * i + 1 by omega]; exact hsym _ _ h12
    · rw [show partner a (6 * i + 3) = 6 * i + 4 by omega]; exact h34
    · rw [show partner a (6 * i + 4) = 6 * i + 3 by omega]; exact hsym _ _ h34
    · rw [show partner a (6 * i + 5) = 6 * i + 0 by omega]; exact h50

theorem E_sound (n k : ℕ) (hk : k = 6 * n + 1) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    (i : ℕ) (hi : i < n) (hs : ∀ s < 6, TR k R (tripleP i s)) (a : ℕ → Bool)
    (ha : a i = true ↔ TR k R (litP i true)) :
    ∀ u v, u / 6 = i → v < k → u ≠ v → (R u v ↔ v = partner a u) := by
  intro u v hu hv hne
  have hp := E_blockpart n k hk R hsym hmat i hi hs a ha (u % 6) (Nat.mod_lt _ (by omega))
  rw [show 6 * i + u % 6 = u by omega] at hp
  have hb := E_partner_block a u
  have hn := E_partner_ne a u
  constructor
  · intro h
    exact hmat u v (partner a u) (by omega) hv (by omega) hne (Ne.symm hn) h hp
  · intro h
    rw [h]; exact hp

theorem E_sat (n m k : ℕ) (hk : k = 6 * n + 1) (clauses : Fin m → Finset (Fin n × Bool))
    (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    (a : ℕ → Bool) (j : Fin m)
    (hsound : ∀ lit ∈ clauses j, (∀ s < 6, TR k R (tripleP lit.1.val s)) ∧
      (a lit.1.val = true ↔ TR k R (litP lit.1.val true))) :
    TR k R (wordP clauses j) → ∃ lit ∈ clauses j, a lit.1.val = lit.2 := by
  rintro ⟨u, v, hu, hv, hne, hR, ⟨⟨i, b⟩, hl, hlu⟩, ⟨⟨i', b'⟩, hl', hlv⟩⟩
  have hui : u / 6 = i.val := by
    cases b <;> simp only [litP, ite_true, Bool.false_eq_true, ite_false] at hlu <;> omega
  have hvp : v = partner a u :=
    (E_sound n k hk R hsym hmat i.val i.isLt (hsound _ hl).1 a (hsound _ hl).2 u v hui hv hne).mp hR
  have key : a i.val = b ∨ (i' = i ∧ a i.val = b') := by
    cases hai : a i.val
    · have hp := E_partner_false a u (by rw [hui]; exact hai)
      cases b <;> cases b' <;>
        simp only [litP, ite_true, Bool.false_eq_true, ite_false] at hlu hlv <;>
        first
          | (left; rfl)
          | (right; exact ⟨Fin.ext (by omega), rfl⟩)
          | (exfalso; omega)
    · have hp := E_partner_true a u (by rw [hui]; exact hai)
      cases b <;> cases b' <;>
        simp only [litP, ite_true, Bool.false_eq_true, ite_false] at hlu hlv <;>
        first
          | (left; rfl)
          | (right; exact ⟨Fin.ext (by omega), rfl⟩)
          | (exfalso; omega)
  rcases key with h | ⟨rfl, h⟩
  · exact ⟨(i, b), hl, h⟩
  · exact ⟨(i', b'), hl', h⟩

theorem E_Ra_sym (n : ℕ) (a : ℕ → Bool) : ∀ u v, Ra n a u v → Ra n a v u := by
  rintro u v ⟨hu, rfl⟩
  have hb := E_partner_block a u
  exact ⟨by omega, (E_partner_invol a u).symm⟩

theorem E_Ra_mat (n : ℕ) (a : ℕ → Bool) :
    ∀ u v w, u < 6 * n + 1 → v < 6 * n + 1 → w < 6 * n + 1 → u ≠ v → u ≠ w →
      Ra n a u v → Ra n a u w → v = w := by
  intro u v w _ _ _ _ _ h1 h2
  rw [h1.2, h2.2]

theorem E_Ra_triple (n : ℕ) (a : ℕ → Bool) (i s : ℕ) (hi : i < n) (hs : s < 6) :
    TR (6 * n + 1) (Ra n a) (tripleP i s) := by
  have mk : ∀ p : ℕ, p < 6 → tripleP i s (6 * i + p) → tripleP i s (partner a (6 * i + p)) →
      TR (6 * n + 1) (Ra n a) (tripleP i s) := by
    intro p hp h1 h2
    have hb := E_partner_block a (6 * i + p)
    exact ⟨6 * i + p, partner a (6 * i + p), by omega, by omega, (E_partner_ne a _).symm,
      ⟨by omega, rfl⟩, h1, h2⟩
  cases hai : a i
  · have hp : ∀ p, p < 6 → _ := fun p hp6 =>
      E_partner_false a (6 * i + p) (by rw [show (6 * i + p) / 6 = i by omega]; exact hai)
    have h1 := hp 1 (by omega)
    have h3 := hp 3 (by omega)
    have h5 := hp 5 (by omega)
    interval_cases s
    · exact mk 1 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 1 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 3 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 3 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 5 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 5 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
  · have hp : ∀ p, p < 6 → _ := fun p hp6 =>
      E_partner_true a (6 * i + p) (by rw [show (6 * i + p) / 6 = i by omega]; exact hai)
    have h0 := hp 0 (by omega)
    have h2 := hp 2 (by omega)
    have h4 := hp 4 (by omega)
    interval_cases s
    · exact mk 0 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 2 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 2 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 4 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 4 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)
    · exact mk 0 (by omega) (by unfold tripleP; omega) (by unfold tripleP; omega)

theorem E_Ra_lit (n : ℕ) (a : ℕ → Bool) (i : ℕ) (hi : i < n) :
    TR (6 * n + 1) (Ra n a) (litP i true) ↔ a i = true := by
  constructor
  · rintro ⟨u, v, _, _, hne, ⟨_, hv⟩, pu, pv⟩
    simp only [litP, ite_true] at pu pv
    cases hai : a i
    · exfalso
      have hp := E_partner_false a u (by rw [show u / 6 = i by omega]; exact hai)
      omega
    · rfl
  · intro hai
    have hp := E_partner_true a (6 * i) (by rw [show 6 * i / 6 = i by omega]; exact hai)
    exact ⟨6 * i, 6 * i + 1, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      Or.inl rfl, Or.inr rfl⟩

theorem E_Ra_word (n m : ℕ) (clauses : Fin m → Finset (Fin n × Bool)) (a : ℕ → Bool) (j : Fin m) :
    TR (6 * n + 1) (Ra n a) (wordP clauses j) ↔ ∃ lit ∈ clauses j, a lit.1.val = lit.2 := by
  constructor
  · apply E_sat n m (6 * n + 1) rfl clauses (Ra n a) (E_Ra_sym n a) (E_Ra_mat n a) a j
    intro lit _
    exact ⟨fun s hs => E_Ra_triple n a lit.1.val s lit.1.isLt hs,
      (E_Ra_lit n a lit.1.val lit.1.isLt).symm⟩
  · rintro ⟨⟨i, b⟩, hl, hab⟩
    have hi := i.isLt
    simp only at hab
    refine ⟨6 * i.val, 6 * i.val + (if b then 1 else 5), by omega, ?_, ?_, ⟨by omega, ?_⟩,
      ⟨(i, b), hl, Or.inl rfl⟩, ⟨(i, b), hl, Or.inr rfl⟩⟩
    · cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega
    · cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega
    · cases b
      · have hp := E_partner_false a (6 * i.val)
          (by rw [show 6 * i.val / 6 = i.val by omega]; exact hab)
        simp only [Bool.false_eq_true, ite_false]; omega
      · have hp := E_partner_true a (6 * i.val)
          (by rw [show 6 * i.val / 6 = i.val by omega]; exact hab)
        simp only [ite_true]; omega

theorem E_all (n k : ℕ) (hk : k = 6 * n + 1) (R : ℕ → ℕ → Prop) (hsym : ∀ u v, R u v → R v u)
    (hmat : ∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w)
    (hs : ∀ i < n, ∀ s < 6, TR k R (tripleP i s)) (a : ℕ → Bool)
    (ha : ∀ i < n, (a i = true ↔ TR k R (litP i true))) :
    ∀ u v, u < k → v < k → u ≠ v → (R u v ↔ Ra n a u v) := by
  intro u v hu hv hne
  by_cases hu6 : u < 6 * n
  · have hi : u / 6 < n := by omega
    rw [E_sound n k hk R hsym hmat (u / 6) hi (hs _ hi) a (ha _ hi) u v rfl hv hne]
    exact ⟨fun h => ⟨hu6, h⟩, fun h => h.2⟩
  · constructor
    · intro h
      exfalso
      have hv6 : v < 6 * n := by omega
      have hi : v / 6 < n := by omega
      have h' := (E_sound n k hk R hsym hmat (v / 6) hi (hs _ hi) a (ha _ hi) v u rfl hu
        (Ne.symm hne)).mp (hsym _ _ h)
      have hb := E_partner_block a v
      omega
    · intro h
      exact absurd h.1 hu6

def aN {n : ℕ} (a : Fin n → Bool) : ℕ → Bool := fun u => if h : u < n then a ⟨u, h⟩ else false

theorem aN_val {n : ℕ} (a : Fin n → Bool) (i : Fin n) : aN a i.val = a i := by simp [aN]

theorem F_occ (n m : ℕ) (clauses : Fin m → Finset (Fin n × Bool)) (hcl : ∀ j, (clauses j).card ≤ 3) :
    ∑ i : Fin n, (Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i, b) ∈ clauses j)).card ≤ 3 * m := by
  have h1 : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i, b) ∈ clauses j)).card
      = ∑ j : Fin m, if (∃ b : Bool, (i, b) ∈ clauses j) then 1 else 0 := by
    intro i; rw [Finset.card_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin m, (∑ i : Fin n, if (∃ b : Bool, (i, b) ∈ clauses j) then 1 else 0) ≤ 3 := by
    intro j
    rw [← Finset.card_filter]
    refine le_trans ?_ (hcl j)
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := Prod.fst))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨b, hb⟩ := hi
    exact Finset.mem_image.mpr ⟨(i, b), hb, rfl⟩
  calc ∑ j : Fin m, ∑ i : Fin n, (if (∃ b : Bool, (i, b) ∈ clauses j) then 1 else 0)
      ≤ ∑ _j : Fin m, 3 := Finset.sum_le_sum (fun j _ => h2 j)
    _ = 3 * m := by simp [mul_comm]

theorem F_abstract (n m : ℕ) (clauses : Fin m → Finset (Fin n × Bool))
    (hcl : ∀ j, (clauses j).card ≤ 3)
    (Fn Wd : Type) (eligible : Fn → Prop) (test : Fn → Wd → Prop)
    [inst : ∀ f w, Decidable (test f w)]
    (triple : Fin n → Fin 6 → Wd) (litWord : Fin n → Bool → Wd) (word : Fin m → Wd)
    (Rep : Fn → (ℕ → ℕ → Prop) → Prop)
    (H1 : ∀ f, eligible f → ∃ R : ℕ → ℕ → Prop, (∀ u v, R u v → R v u) ∧
      (∀ u v w, u < 6 * n + 1 → v < 6 * n + 1 → w < 6 * n + 1 → u ≠ v → u ≠ w → R u v → R u w → v = w) ∧
      Rep f R)
    (H2 : ∀ a : ℕ → Bool, ∃ f, eligible f ∧ Rep f (Ra n a))
    (H3 : ∀ f f' R R', Rep f R → Rep f' R' →
      (∀ u v, u < 6 * n + 1 → v < 6 * n + 1 → u ≠ v → (R u v ↔ R' u v)) → f = f')
    (H4 : ∀ f R, Rep f R →
      (∀ i s, test f (triple i s) ↔ TR (6 * n + 1) R (tripleP i.val s.val)) ∧
      (∀ i b, test f (litWord i b) ↔ TR (6 * n + 1) R (litP i.val b)) ∧
      (∀ j, test f (word j) ↔ TR (6 * n + 1) R (wordP clauses j))) :
    let decode := fun (f : Fn) (i : Fin n) => decide (test f (litWord i true))
    let satisfied := fun (a : Fin n → Bool) (j : Fin m) => ∃ lit ∈ clauses j, a lit.1 = lit.2
    let occ := fun (i : Fin n) =>
      (Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i,b) ∈ clauses j)).card
    let bad := fun (f : Fn) (i : Fin n) =>
      (Finset.univ.filter (fun s : Fin 6 => ¬ test f (triple i s))).card
    let broken := fun (f : Fn) => (Finset.univ.filter (fun i : Fin n => 0 < bad f i)).card
    let loss := fun (a : Fin n → Bool) => (Finset.univ.filter (fun j => ¬ satisfied a j)).card
    let errs := fun (f : Fn) => (Finset.univ.filter (fun j : Fin m => ¬ test f (word j))).card +
      ∑ i : Fin n, (1+occ i)*bad f i
    let BestA := { a : Fin n → Bool // ∀ z : Fin n → Bool, loss a ≤ loss z }
    let BestF := { f : Fn // eligible f ∧ ∀ g : Fn, eligible g → errs f ≤ errs g }
    (m + (∑ i : Fin n, 6*(1+occ i)) ≤ 6*n+19*m) ∧
    (∀ f : Fn, eligible f → loss (decode f) + broken f ≤ errs f) ∧
    ∃ e : BestA ≃ BestF, ∀ a : BestA,
      decode (e a).val = a.val ∧ errs (e a).val = loss a.val ∧ broken (e a).val = 0 := by
  intro decode satisfied occ bad broken loss errs BestA BestF
  have hbad0 : ∀ f i, bad f i = 0 ↔ ∀ s, test f (triple i s) := by
    intro f i
    simp only [bad, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
      not_not]
  have P2 : ∀ f : Fn, eligible f → loss (decode f) + broken f ≤ errs f := by
    intro f hf
    obtain ⟨R, hsym, hmat, hrep⟩ := H1 f hf
    obtain ⟨hT, hL, hW⟩ := H4 f R hrep
    have key : ∀ j, ¬ satisfied (decode f) j → ¬ test f (word j) ∨
        ∃ i, 0 < bad f i ∧ ∃ b : Bool, (i, b) ∈ clauses j := by
      intro j hj
      by_contra hcon
      rw [not_or, not_not] at hcon
      obtain ⟨ht, hno⟩ := hcon
      apply hj
      have hsound : ∀ lit ∈ clauses j, (∀ s < 6, TR (6 * n + 1) R (tripleP lit.1.val s)) ∧
          (aN (decode f) lit.1.val = true ↔ TR (6 * n + 1) R (litP lit.1.val true)) := by
        intro lit hlit
        have hb : bad f lit.1 = 0 := by
          by_contra hne
          exact hno ⟨lit.1, Nat.pos_of_ne_zero hne, lit.2, hlit⟩
        constructor
        · intro s hs
          exact (hT lit.1 ⟨s, hs⟩).mp ((hbad0 f lit.1).mp hb ⟨s, hs⟩)
        · rw [aN_val, ← hL]
          simp only [decode, decide_eq_true_eq]
      obtain ⟨lit, hlit, hl⟩ := E_sat n m (6 * n + 1) rfl clauses R hsym hmat (aN (decode f)) j hsound
        ((hW j).mp ht)
      exact ⟨lit, hlit, (aN_val (decode f) lit.1).symm.trans hl⟩
    have hsub : (Finset.univ.filter (fun j => ¬ satisfied (decode f) j)) ⊆
        (Finset.univ.filter (fun j : Fin m => ¬ test f (word j))) ∪
        (Finset.univ.filter (fun i : Fin n => 0 < bad f i)).biUnion
          (fun i => Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i,b) ∈ clauses j)) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact key j hj
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le (Finset.univ.filter (fun j : Fin m => ¬ test f (word j)))
      ((Finset.univ.filter (fun i : Fin n => 0 < bad f i)).biUnion
          (fun i => Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i,b) ∈ clauses j)))
    have hc3 : ((Finset.univ.filter (fun i : Fin n => 0 < bad f i)).biUnion
          (fun i => Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i,b) ∈ clauses j))).card ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < bad f i), occ i :=
      Finset.card_biUnion_le
    have hc4 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < bad f i), occ i) +
        (Finset.univ.filter (fun i : Fin n => 0 < bad f i)).card ≤ ∑ i : Fin n, (1+occ i)*bad f i := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      refine le_trans (Finset.sum_le_sum (g := fun i => (1+occ i)*bad f i) ?_)
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      nlinarith [hi]
    show (Finset.univ.filter (fun j => ¬ satisfied (decode f) j)).card +
      (Finset.univ.filter (fun i : Fin n => 0 < bad f i)).card ≤
      (Finset.univ.filter (fun j : Fin m => ¬ test f (word j))).card + ∑ i : Fin n, (1+occ i)*bad f i
    omega
  choose cF hcF_el hcF_rep using H2
  have hclean : ∀ a : Fin n → Bool, decode (cF (aN a)) = a ∧ errs (cF (aN a)) = loss a ∧
      broken (cF (aN a)) = 0 ∧ ∀ i, bad (cF (aN a)) i = 0 := by
    intro a
    obtain ⟨hT, hL, hW⟩ := H4 _ _ (hcF_rep (aN a))
    have hb : ∀ i, bad (cF (aN a)) i = 0 := by
      intro i
      rw [hbad0]
      intro s
      exact (hT i s).mpr (E_Ra_triple n (aN a) i.val s.val i.isLt s.isLt)
    have hbr : broken (cF (aN a)) = 0 := by
      simp only [broken, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        true_implies, hb, lt_irrefl, not_false_eq_true, implies_true]
    refine ⟨?_, ?_, hbr, hb⟩
    · funext i
      have h1 := (hL i true).trans (E_Ra_lit n (aN a) i.val i.isLt)
      rw [aN_val] at h1
      simp only [decode]
      cases hai : a i
      · rw [hai] at h1
        simpa using h1
      · rw [hai] at h1
        simpa using h1
    · have hw : ∀ j, test (cF (aN a)) (word j) ↔ satisfied a j := by
        intro j
        rw [hW j, E_Ra_word]
        constructor
        · rintro ⟨lit, hlit, h⟩
          exact ⟨lit, hlit, (aN_val a lit.1).symm.trans h⟩
        · rintro ⟨lit, hlit, h⟩
          exact ⟨lit, hlit, (aN_val a lit.1).trans h⟩
      show (Finset.univ.filter (fun j : Fin m => ¬ test (cF (aN a)) (word j))).card +
        ∑ i : Fin n, (1+occ i)*bad (cF (aN a)) i = (Finset.univ.filter (fun j => ¬ satisfied a j)).card
      have hz : ∑ i : Fin n, (1+occ i)*bad (cF (aN a)) i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hb i, Nat.mul_zero]
      rw [hz, add_zero]
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [hw j]
  refine ⟨?_, P2, ?_⟩
  · have h := F_occ n m clauses hcl
    have h2 : (∑ i : Fin n, 6*(1+occ i)) = 6 * n + 6 * ∑ i : Fin n, occ i := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp [mul_add]
    rw [h2]
    have h' : ∑ i : Fin n, occ i ≤ 3 * m := h
    omega
  · have hAF : ∀ a : BestA, eligible (cF (aN a.val)) ∧
        ∀ g : Fn, eligible g → errs (cF (aN a.val)) ≤ errs g := by
      intro a
      refine ⟨hcF_el _, ?_⟩
      intro g hg
      rw [(hclean a.val).2.1]
      exact le_trans (a.property (decode g)) (le_trans (Nat.le_add_right _ _) (P2 g hg))
    have hFA : ∀ f : BestF, ∀ z : Fin n → Bool, loss (decode f.val) ≤ loss z := by
      intro f z
      have h1 := P2 f.val f.property.1
      have h2 := f.property.2 (cF (aN z)) (hcF_el _)
      rw [(hclean z).2.1] at h2
      omega
    have hright : ∀ f : BestF, cF (aN (decode f.val)) = f.val := by
      intro f
      obtain ⟨R, hsym, hmat, hrep⟩ := H1 f.val f.property.1
      obtain ⟨hT, hL, hW⟩ := H4 f.val R hrep
      have h1 := P2 f.val f.property.1
      have h2 := f.property.2 (cF (aN (decode f.val))) (hcF_el _)
      rw [(hclean (decode f.val)).2.1] at h2
      have hbr : broken f.val = 0 := by omega
      have hb : ∀ i, bad f.val i = 0 := by
        intro i
        by_contra hne
        have : i ∈ Finset.univ.filter (fun i : Fin n => 0 < bad f.val i) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.pos_of_ne_zero hne
        have hbr' : (Finset.univ.filter (fun i : Fin n => 0 < bad f.val i)) = ∅ :=
          Finset.card_eq_zero.mp hbr
        rw [hbr'] at this
        exact absurd this (Finset.notMem_empty _)
      have hall := E_all n (6 * n + 1) rfl R hsym hmat
        (fun i hi s hs => (hT ⟨i, hi⟩ ⟨s, hs⟩).mp ((hbad0 f.val ⟨i, hi⟩).mp (hb ⟨i, hi⟩) ⟨s, hs⟩))
        (aN (decode f.val))
        (fun i hi => by
          have := hL ⟨i, hi⟩ true
          rw [← this]
          have h3 := aN_val (decode f.val) ⟨i, hi⟩
          simp only at h3
          rw [h3]
          simp only [decode, decide_eq_true_eq])
      exact H3 _ _ _ _ (hcF_rep _) hrep (fun u v hu hv huv => (hall u v hu hv huv).symm)
    refine ⟨⟨fun a => ⟨cF (aN a.val), hAF a⟩, fun f => ⟨decode f.val, hFA f⟩, ?_, ?_⟩, ?_⟩
    · intro a
      exact Subtype.ext (hclean a.val).1
    · intro f
      exact Subtype.ext (hright f)
    · intro a
      exact ⟨(hclean a.val).1, (hclean a.val).2.1, (hclean a.val).2.2.1⟩



open PEqualNP.MetaComplexity PEqualNP.Represents

def zOf {nr nc : ℕ} (x : Fin nr → Bool) (y : Fin nc → Bool) : ℕ → Bool :=
  fun i => if h : i < nr then x ⟨i, h⟩ else if h2 : i - nr < nc then y ⟨i - nr, h2⟩ else false

def canonR (crown : Bool) (k d : ℕ) (R : ℕ → ℕ → Prop) (z : ℕ → Bool) : Prop :=
  (crown = true ∧ z (k + 1) = true) ∨ (∃ u, u < k ∧ z u = true ∧ z (d + u) = true) ∨
  ∃ u v, u < k ∧ v < k ∧ u ≠ v ∧ R u v ∧
    ((z u = true ∧ z v = true) ∨ (z (d + u) = true ∧ z (d + v) = true))

theorem G_onehot (nr nc : ℕ) (u : Fin nr) (v : Fin nc) :
    zOf (fun i : Fin nr => decide (i = u)) (fun j : Fin nc => decide (j = v)) =
      pair u.val (nr + v.val) := by
  funext i
  unfold zOf pair
  have hu := u.isLt
  have hv := v.isLt
  by_cases h : i < nr
  · rw [dif_pos h, decide_eq_decide]
    simp only [Fin.ext_iff]
    omega
  · rw [dif_neg h]
    by_cases h2 : i - nr < nc
    · rw [dif_pos h2, decide_eq_decide]
      simp only [Fin.ext_iff]
      omega
    · rw [dif_neg h2]
      symm
      rw [decide_eq_false_iff_not]
      omega

theorem G1_ofFn (nr nc : ℕ) (x : Fin nr → Bool) (y : Fin nc → Bool) :
    (List.ofFn fun i : Fin (nr + nc) => zOf x y i.val) = List.ofFn x ++ List.ofFn y := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    unfold zOf
    by_cases h : i < nr
    · simp [h]
    · have h3 : i - nr < nc := by
        simp only [List.length_ofFn] at h1
        omega
      simp [h, h3]

theorem G_eval (nr nc : ℕ) (C : Circuit) (x : Fin nr → Bool) (y : Fin nc → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) = fn C.gates (nr + nc) C.output (zOf x y) := by
  unfold fn
  rw [G1_ofFn]
  rfl

theorem G_rep (nr nc : ℕ) (A : Fin nr → Fin nc → Bool) (C : Circuit) (h : Represents A C)
    (u : Fin nr) (v : Fin nc) :
    fn C.gates (nr + nc) C.output (pair u.val (nr + v.val)) = A u v := by
  have h1 := h u v
  unfold oneEach at h1
  rw [G_eval, G_onehot] at h1
  exact h1

theorem G1_b1 (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b <;> by_cases hp : P <;> simp_all

theorem G1_b2 (b : Bool) (P : Prop) [Decidable P] (h : b = false ↔ P) : b = decide (¬ P) := by
  cases b <;> by_cases hp : P <;> simp_all

theorem G1_partner_lt (n : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u < 6 * n) : partner a u < 6 * n := by
  have := E_partner_block a u
  omega

theorem G1_canon (n : ℕ) (a : ℕ → Bool) (crown : Bool) (d : ℕ) (z : ℕ → Bool) :
    ((crown = true ∧ z (6 * n + 2) = true) ∨
        (∃ u, u < 6 * n + 1 ∧ z u = true ∧ z (d + u) = true) ∨
        ∃ u, u < 6 * n ∧ ((z u = true ∧ z (partner a u) = true) ∨
          (z (d + u) = true ∧ z (d + partner a u) = true))) ↔
      canonR crown (6 * n + 1) d (Ra n a) z := by
  unfold canonR Ra
  constructor
  · rintro (h | h | ⟨u, hu, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have := G1_partner_lt n a u hu
      exact Or.inr (Or.inr ⟨u, partner a u, by omega, by omega, (E_partner_ne a u).symm,
        ⟨hu, rfl⟩, h⟩)
  · rintro (h | h | ⟨u, v, _, _, _, ⟨hu, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨u, hu, h⟩)

theorem G1_canon_pair (crown : Bool) (k nr : ℕ) (R : ℕ → ℕ → Prop) (u v : ℕ)
    (hc : crown = true → k + 1 < nr) (hk : k ≤ nr) (hu : u < nr) :
    canonR crown k nr R (pair u (nr + v)) ↔ (crown = true ∧ u = k + 1) ∨ (u < k ∧ u = v) := by
  unfold canonR pair
  simp only [decide_eq_true_iff]
  constructor
  · rintro (⟨hc', h⟩ | ⟨w, hw, h1, h2⟩ | ⟨w, w', hw, hw', hne, _, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩)
    · have := hc hc'
      exact Or.inl ⟨hc', by omega⟩
    · exact Or.inr (by omega)
    · exfalso; omega
    · exfalso; omega
  · rintro (⟨hc', h⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hc', Or.inl (by omega)⟩
    · exact Or.inr (Or.inl ⟨u, h1, Or.inl rfl, Or.inr (by omega)⟩)

theorem G1_repA (n : ℕ) (a : ℕ → Bool) (crown : Bool) (nr nc : ℕ)
    (hnr : nr = if crown then 6 * n + 1 + 2 else 6 * n + 1)
    (C : Circuit)
    (hfn : ∀ z, (fn C.gates (nr + nc) C.output z = !crown ↔
      canonR crown (6 * n + 1) nr (Ra n a) z))
    (u : Fin nr) (v : Fin nc) :
    C.eval (oneEach u v) = (if crown then
      decide (u.val ≠ 6 * n + 1 + 1 ∧ ¬ (u.val < 6 * n + 1 ∧ u.val = v.val))
      else decide (u.val = v.val)) := by
  unfold oneEach
  rw [G_eval, G_onehot]
  have hu := u.isLt
  have h := hfn (pair u.val (nr + v.val))
  cases crown
  · simp only [Bool.false_eq_true, if_false] at hnr ⊢
    rw [G1_canon_pair false (6 * n + 1) nr _ u.val v.val (by simp) (by omega) hu] at h
    simp only [Bool.not_false] at h
    rw [G1_b1 _ _ h, decide_eq_decide]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · cases h
      · exact h
    · intro h
      exact Or.inr ⟨by omega, h⟩
  · simp only [if_true] at hnr ⊢
    rw [G1_canon_pair true (6 * n + 1) nr _ u.val v.val (by intro _; omega) (by omega) hu] at h
    simp only [Bool.not_true] at h
    rw [G1_b2 _ _ h, decide_eq_decide]
    simp only [true_and, not_or]

theorem G1_H2gen (n : ℕ) (hn : 0 < n) (crown : Bool) (a : ℕ → Bool) (nr nc : ℕ)
    (hnr : nr = if crown then 6 * n + 1 + 2 else 6 * n + 1)
    (hnc : nc = if crown then 6 * n + 1 + 1 else 6 * n + 1) :
    ∃ C : Circuit,
      (if crown then FanInTwo C ∧ C.size ≤ 2 * (6 * n + 1) + 1
        else Monotone2 C ∧ C.size + 1 ≤ 2 * (6 * n + 1)) ∧
      ∀ z, (fn C.gates (nr + nc) C.output z = !crown ↔
        canonR crown (6 * n + 1) nr (Ra n a) z) := by
  cases crown
  · simp only [Bool.false_eq_true, if_false] at hnr hnc ⊢
    obtain ⟨gs, o, hlen, hg, hfn⟩ := C_clean n hn a false nr (nr + nc) (by omega) (by simp)
      (by omega)
    simp only [Bool.false_eq_true, if_false] at hlen
    refine ⟨⟨gs, o⟩, ⟨?_, ?_⟩, ?_⟩
    · intro g hg'
      obtain ⟨hl, hop⟩ := hg g hg'
      refine ⟨?_, hl⟩
      rcases hop with h | h | ⟨h, _⟩
      · rw [h]; simp
      · rw [h]; simp
      · cases h
    · show gs.length + 1 ≤ _
      omega
    · intro z
      show fn gs (nr + nc) o z = !false ↔ _
      rw [hfn z, ← G1_canon]
      simp only [Bool.false_xor, Bool.not_false, decide_eq_true_iff]
  · simp only [if_true] at hnr hnc ⊢
    obtain ⟨gs, o, hlen, hg, hfn⟩ := C_clean n hn a true nr (nr + nc) (by omega) (by intro _; omega)
      (by omega)
    simp only [if_true] at hlen
    refine ⟨⟨gs, o⟩, ⟨?_, ?_⟩, ?_⟩
    · intro g hg'
      obtain ⟨hl, hop⟩ := hg g hg'
      refine ⟨?_, hl⟩
      rcases hop with h | h | ⟨_, h⟩
      · rw [h]; simp
      · rw [h]; simp
      · rw [h]; simp
    · show gs.length ≤ _
      omega
    · intro z
      show fn gs (nr + nc) o z = !true ↔ _
      rw [hfn z, ← G1_canon]
      simp only [Bool.true_xor, Bool.not_true, Bool.not_eq_eq_eq_not, Bool.not_false,
        decide_eq_true_iff]

theorem G_H2 (n : ℕ) (hn : 0 < n) (crown : Bool) :
    let k := 6*n+1
    let nr := if crown then k+2 else k
    let nc := if crown then k+1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
    let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
       else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧ PEqualNP.Represents.Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
    ∀ a : ℕ → Bool, ∃ f : Fn, eligible f ∧
      ∀ x y, (f x y = !crown ↔ canonR crown k nr (Ra n a) (zOf x y)) := by
  intro k nr nc A Fn eligible a
  obtain ⟨C, hgate, hfn⟩ := G1_H2gen n hn crown a nr nc rfl rfl
  refine ⟨fun x y => C.eval (List.ofFn x ++ List.ofFn y), ⟨C, hgate, ?_, fun _ _ => rfl⟩, ?_⟩
  · intro u v
    exact G1_repA n a crown nr nc rfl C hfn u v
  · intro x y
    show C.eval (List.ofFn x ++ List.ofFn y) = !crown ↔ _
    rw [G_eval]
    exact hfn _

theorem G_H3 (crown : Bool) (k nr nc : ℕ) (f f' : (Fin nr → Bool) → (Fin nc → Bool) → Bool)
    (R R' : ℕ → ℕ → Prop)
    (h : ∀ x y, (f x y = !crown ↔ canonR crown k nr R (zOf x y)))
    (h' : ∀ x y, (f' x y = !crown ↔ canonR crown k nr R' (zOf x y)))
    (hR : ∀ u v, u < k → v < k → u ≠ v → (R u v ↔ R' u v)) : f = f' := by
  funext x y
  have e : canonR crown k nr R (zOf x y) ↔ canonR crown k nr R' (zOf x y) := by
    unfold canonR
    constructor
    · rintro (h1 | h1 | ⟨u, v, hu, hv, huv, hr, hz⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨u, v, hu, hv, huv, (hR u v hu hv huv).mp hr, hz⟩)
    · rintro (h1 | h1 | ⟨u, v, hu, hv, huv, hr, hz⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨u, v, hu, hv, huv, (hR u v hu hv huv).mpr hr, hz⟩)
  have a := h x y
  have b := h' x y
  rw [e] at a
  have t : (f x y = !crown) ↔ (f' x y = !crown) := a.trans b.symm
  revert t
  cases f x y <;> cases f' x y <;> cases crown <;> simp

theorem G1_test (n : ℕ) (crown : Bool) (nr nc : ℕ) (hnr : 6 * n + 1 ≤ nr) (R : ℕ → ℕ → Prop)
    (w : Fin nr → Bool) (P : ℕ → Prop)
    (hw : ∀ u : Fin nr, w u = true ↔ P u.val) (hP : ∀ u, P u → u < 6 * n) :
    canonR crown (6 * n + 1) nr R (zOf w (fun _ : Fin nc => false)) ↔ TR (6 * n + 1) R P := by
  have hz1 : ∀ u, zOf w (fun _ : Fin nc => false) (nr + u) = false := by
    intro u
    unfold zOf
    rw [dif_neg (by omega)]
    split_ifs <;> rfl
  have hz2 : ∀ u, zOf w (fun _ : Fin nc => false) u = true → P u := by
    intro u hu
    unfold zOf at hu
    by_cases h : u < nr
    · rw [dif_pos h] at hu
      exact (hw ⟨u, h⟩).mp hu
    · rw [dif_neg h] at hu
      split_ifs at hu
  have hz3 : ∀ u, P u → zOf w (fun _ : Fin nc => false) u = true := by
    intro u hu
    have h : u < nr := by have := hP u hu; omega
    unfold zOf
    rw [dif_pos h]
    exact (hw ⟨u, h⟩).mpr hu
  unfold canonR TR
  constructor
  · rintro (⟨_, h1⟩ | ⟨u, hu, h1, h2⟩ | ⟨u, v, hu, hv, huv, hr, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩)
    · have := hP _ (hz2 _ h1)
      omega
    · rw [hz1] at h2
      cases h2
    · exact ⟨u, v, hu, hv, huv, hr, hz2 u h1, hz2 v h2⟩
    · rw [hz1] at h2
      cases h2
  · rintro ⟨u, v, hu, hv, huv, hr, pu, pv⟩
    exact Or.inr (Or.inr ⟨u, v, hu, hv, huv, hr, Or.inl ⟨hz3 u pu, hz3 v pv⟩⟩)

theorem G_H4 (n m : ℕ) (clauses : Fin m → Finset (Fin n × Bool)) (crown : Bool) (nr nc : ℕ)
    (hnr : 6 * n + 1 ≤ nr) (f : (Fin nr → Bool) → (Fin nc → Bool) → Bool) (R : ℕ → ℕ → Prop)
    (h : ∀ x y, (f x y = !crown ↔ canonR crown (6 * n + 1) nr R (zOf x y))) :
    (∀ (i : Fin n) (s : Fin 6), (f (fun (u : Fin nr) =>
        decide (u.val = 6*i.val+s.val ∨ u.val = 6*i.val+(s.val+1)%6 ∨ u.val = 6*i.val+(s.val+2)%6))
        (fun _ => false) = !crown) ↔ TR (6 * n + 1) R (tripleP i.val s.val)) ∧
    (∀ (i : Fin n) (b : Bool), (f (fun (u : Fin nr) =>
        decide (u.val = 6*i.val ∨ u.val = 6*i.val+(if b then 1 else 5)))
        (fun _ => false) = !crown) ↔ TR (6 * n + 1) R (litP i.val b)) ∧
    (∀ j : Fin m, (f (fun (u : Fin nr) => decide (∃ lit ∈ clauses j,
        decide (u.val = 6*lit.1.val ∨ u.val = 6*lit.1.val+(if lit.2 then 1 else 5)) = true))
        (fun _ => false) = !crown) ↔ TR (6 * n + 1) R (wordP clauses j)) := by
  have hlit : ∀ (i : Fin n) (b : Bool) (u : ℕ), litP i.val b u → u < 6 * n := by
    intro i b u hu
    have hi := i.isLt
    unfold litP at hu
    rcases hu with hu | hu
    · omega
    · cases b
      · simp only [Bool.false_eq_true, if_false] at hu
        omega
      · simp only [if_true] at hu
        omega
  refine ⟨fun i s => ?_, fun i b => ?_, fun j => ?_⟩
  · rw [h]
    apply G1_test n crown nr nc hnr R
    · intro u
      simp only [decide_eq_true_iff, tripleP]
    · intro u hu
      have hi := i.isLt
      have hs := s.isLt
      unfold tripleP at hu
      omega
  · rw [h]
    apply G1_test n crown nr nc hnr R
    · intro u
      simp only [decide_eq_true_iff, litP]
    · exact hlit i b
  · rw [h]
    apply G1_test n crown nr nc hnr R
    · intro u
      simp only [decide_eq_true_iff, wordP, litP]
    · rintro u ⟨lit, _, hl⟩
      exact hlit lit.1 lit.2 u hl

theorem G2_single_le_left (a b : ℕ) : ∀ i, single a i = true → pair a b i = true := by
  intro i h
  simp only [single, pair, decide_eq_true_eq] at h ⊢
  exact Or.inl h

theorem G2_single_le_right (a b : ℕ) : ∀ i, single b i = true → pair a b i = true := by
  intro i h
  simp only [single, pair, decide_eq_true_eq] at h ⊢
  exact Or.inr h

theorem G_H1_mono (k : ℕ) (hk : 3 ≤ k) (C : Circuit) (hmon : Monotone2 C) (hsz : C.size + 1 ≤ 2 * k)
    (hrep : Represents (fun (i : Fin k) (j : Fin k) => decide (i.val = j.val)) C) :
    ∃ R : ℕ → ℕ → Prop, (∀ u v, R u v → R v u) ∧
      (∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w) ∧
      ∀ z : ℕ → Bool, (fn C.gates (k + k) C.output z = true ↔ canonR false k k R z) := by
  have hF : ∀ u v, u < k → v < k →
      fn C.gates (k + k) C.output (pair u (k + v)) = decide (u = v) := by
    intro u v hu hv
    exact G_rep k k _ C hrep ⟨u, hu⟩ ⟨v, hv⟩
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hmon g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) := by
    intro g hg
    refine ⟨(hmon g hg).2, ?_⟩
    rcases hops g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hmo := A_mono (k + k) C.gates hops C.output
  obtain ⟨S, hSsub, hdep, hcard, htight⟩ := A_tight (k + k) C.gates hfan C.output
  have hother : ∀ u, u < k → ∃ u2, u2 < k ∧ u2 ≠ u := by
    intro u hu
    by_cases h0 : u = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  have hxS : ∀ u, u < k → u ∈ S := by
    intro u hu
    by_contra hns
    have h1 := B1_pair_right hdep u (k + u) hns
    rw [hF u u hu hu] at h1
    obtain ⟨u2, hu2, hne⟩ := hother u hu
    have h2 := hmo (single (k + u)) (pair u2 (k + u)) (G2_single_le_right u2 (k + u))
      (by rw [← h1]; simp)
    rw [hF u2 u hu2 hu] at h2
    simp [hne] at h2
  have hyS : ∀ u, u < k → k + u ∈ S := by
    intro u hu
    by_contra hns
    have h1 := B1_pair_left hdep u (k + u) hns
    rw [hF u u hu hu] at h1
    obtain ⟨u2, hu2, hne⟩ := hother u hu
    have h2 := hmo (single u) (pair u (k + u2)) (G2_single_le_left u (k + u2))
      (by rw [← h1]; simp)
    rw [hF u u2 hu hu2] at h2
    simp [Ne.symm hne] at h2
  have hSeq : S = Finset.range (k + k) := by
    apply Finset.Subset.antisymm hSsub
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h : i < k
    · exact hxS i h
    · have := hyS (i - k) (by omega)
      have e : k + (i - k) = i := by omega
      rw [e] at this
      exact this
  have hb2 : b2 C.gates ≤ C.gates.length := List.countP_le_length
  have hsize : C.size = C.gates.length := rfl
  have hcardS : S.card = k + k := by rw [hSeq, Finset.card_range]
  have hte : S.card = 1 + b2 C.gates := by omega
  have hnots : nots C.gates = 0 := by
    unfold nots
    rw [List.countP_eq_zero]
    intro g hg
    rcases hops g hg with h | h <;> simp [h, isNot]
  have hRO : ROx false S (fn C.gates (k + k) C.output) := (htight hte).1 hnots
  have hsx : ∀ u, u < k → fn C.gates (k + k) C.output (single u) = false := by
    intro u hu
    by_contra hne
    have ht : fn C.gates (k + k) C.output (single u) = true := by
      simpa using hne
    obtain ⟨u2, hu2, hne2⟩ := hother u hu
    have h2 := hmo (single u) (pair u (k + u2)) (G2_single_le_left u (k + u2)) ht
    rw [hF u u2 hu hu2] at h2
    simp [Ne.symm hne2] at h2
  have hsy : ∀ u, u < k → fn C.gates (k + k) C.output (single (k + u)) = false := by
    intro u hu
    by_contra hne
    have ht : fn C.gates (k + k) C.output (single (k + u)) = true := by
      simpa using hne
    obtain ⟨u2, hu2, hne2⟩ := hother u hu
    have h2 := hmo (single (k + u)) (pair u2 (k + u)) (G2_single_le_right u2 (k + u)) ht
    rw [hF u2 u hu2 hu] at h2
    simp [hne2] at h2
  have hSU : S = Finset.range k ∪ (Finset.range k).image (fun u => k + u) ∪ ∅ := by
    rw [hSeq]
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image, Finset.notMem_empty, or_false]
    constructor
    · intro hi
      by_cases h : i < k
      · exact Or.inl h
      · exact Or.inr ⟨i - k, by omega, by omega⟩
    · rintro (h | ⟨u, hu, rfl⟩) <;> omega
  obtain ⟨hform, hmat⟩ := B_matching k S (fn C.gates (k + k) C.output) hRO (Finset.range k) ∅
    (fun u hu => Finset.mem_range.mp hu)
    (fun p hp => absurd hp (Finset.notMem_empty p))
    hSU
    (fun p hp => absurd hp (Finset.notMem_empty p))
    (fun u hu => ⟨hsx u (Finset.mem_range.mp hu), hsy u (Finset.mem_range.mp hu)⟩)
    (fun u hu v hv => hF u v (Finset.mem_range.mp hu) (Finset.mem_range.mp hv))
  refine ⟨fun u v => fn C.gates (k + k) C.output (pair u v) = true, ?_, ?_, ?_⟩
  · intro u v h
    rw [B1_pair_comm]; exact h
  · intro u v w hu hv hw huv huw h1 h2
    exact hmat u (Finset.mem_range.mpr hu) v (Finset.mem_range.mpr hv) w (Finset.mem_range.mpr hw)
      huv huw h1 h2
  · intro z
    rw [hform z]
    unfold canonR
    constructor
    · rintro (⟨p, hp, _⟩ | ⟨u, hu, h⟩ | ⟨u, hu, v, hv, huv, hR, h⟩)
      · exact absurd hp (Finset.notMem_empty p)
      · exact Or.inr (Or.inl ⟨u, Finset.mem_range.mp hu, h⟩)
      · exact Or.inr (Or.inr ⟨u, v, Finset.mem_range.mp hu, Finset.mem_range.mp hv, huv, hR, h⟩)
    · rintro (⟨hc, _⟩ | ⟨u, hu, h⟩ | ⟨u, v, hu, hv, huv, hR, h⟩)
      · exact absurd hc (by simp)
      · exact Or.inr (Or.inl ⟨u, Finset.mem_range.mpr hu, h⟩)
      · exact Or.inr (Or.inr ⟨u, Finset.mem_range.mpr hu, v, Finset.mem_range.mpr hv, huv, hR, h⟩)

theorem G3_vt {k : ℕ} {F : (ℕ → Bool) → Bool}
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (u v : ℕ) (hu : u < k + 2) (hv : v < k + 1) (h : u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)) :
    F (pair u (k + 2 + v)) = true := by
  rw [hF u v hu hv]; exact decide_eq_true h

theorem G3_vf {k : ℕ} {F : (ℕ → Bool) → Bool}
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (u v : ℕ) (hu : u < k + 2) (hv : v < k + 1) (h : ¬ (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v))) :
    F (pair u (k + 2 + v)) = false := by
  rw [hF u v hu hv]; exact decide_eq_false h

theorem G3_rows {k : ℕ} (hk : 2 ≤ k) {F : (ℕ → Bool) → Bool} {S : Finset ℕ} (hd : DepOn S F)
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (u u' : ℕ) (hu : u < k + 2) (hu' : u' < k + 2) (hne : u ≠ u') (h1 : u ∉ S) (h2 : u' ∉ S) :
    False := by
  have key2 : ∀ v, v < k + 1 →
      ((u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)) ↔ (u' ≠ k + 1 ∧ ¬ (u' < k ∧ u' = v))) := by
    intro v hv
    have key : F (pair u (k + 2 + v)) = F (pair u' (k + 2 + v)) := by
      rw [B1_pair_right hd u _ h1, B1_pair_right hd u' _ h2]
    rw [hF u v hu hv, hF u' v hu' hv] at key
    exact decide_eq_decide.mp key
  have a0 := key2 0 (by omega)
  have a1 := key2 1 (by omega)
  by_cases c1 : u < k
  · have a2 := key2 u (by omega)
    omega
  · by_cases c2 : u' < k
    · have a3 := key2 u' (by omega)
      omega
    · omega

theorem G3_cols {k : ℕ} (hk : 2 ≤ k) {F : (ℕ → Bool) → Bool} {S : Finset ℕ} (hd : DepOn S F)
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (v v' : ℕ) (hv : v < k + 1) (hv' : v' < k + 1) (hne : v ≠ v') (h1 : k + 2 + v ∉ S)
    (h2 : k + 2 + v' ∉ S) : False := by
  have key2 : ∀ u, u < k + 2 →
      ((u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)) ↔ (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v'))) := by
    intro u hu
    have key : F (pair u (k + 2 + v)) = F (pair u (k + 2 + v')) := by
      rw [B1_pair_left hd u _ h1, B1_pair_left hd u _ h2]
    rw [hF u v hu hv, hF u v' hu hv'] at key
    exact decide_eq_decide.mp key
  by_cases c1 : v < k
  · have a := key2 v (by omega)
    omega
  · have a := key2 v' (by omega)
    omega

theorem G3_card {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range (k + 2 + (k + 1)))
    (hr : ∀ u u', u < k + 2 → u' < k + 2 → u ≠ u' → u ∉ S → u' ∉ S → False)
    (hc : ∀ v v', v < k + 1 → v' < k + 1 → v ≠ v' → k + 2 + v ∉ S → k + 2 + v' ∉ S → False) :
    2 * k + 1 ≤ S.card ∧
      (S.card = 2 * k + 1 → ∃ r0 c0, r0 < k + 2 ∧ c0 < k + 1 ∧ r0 ∉ S ∧ k + 2 + c0 ∉ S) := by
  have hM := Finset.card_sdiff_add_card_eq_card hS
  rw [Finset.card_range] at hM
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range (k + 2 + (k + 1)) \ S) (fun i => i < k + 2)
  have h1 : ((Finset.range (k + 2 + (k + 1)) \ S).filter (fun i => i < k + 2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range] at ha hb
    by_contra hne
    exact hr a b ha.2 hb.2 hne ha.1.2 hb.1.2
  have h2 : ((Finset.range (k + 2 + (k + 1)) \ S).filter (fun i => ¬ i < k + 2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range] at ha hb
    by_contra hne
    have ea : k + 2 + (a - (k + 2)) = a := by omega
    have eb : k + 2 + (b - (k + 2)) = b := by omega
    exact hc (a - (k + 2)) (b - (k + 2)) (by omega) (by omega) (by omega)
      (by rw [ea]; exact ha.1.2) (by rw [eb]; exact hb.1.2)
  refine ⟨by omega, ?_⟩
  intro hcard
  have c1 : 0 < ((Finset.range (k + 2 + (k + 1)) \ S).filter (fun i => i < k + 2)).card := by omega
  have c2 : 0 < ((Finset.range (k + 2 + (k + 1)) \ S).filter (fun i => ¬ i < k + 2)).card := by omega
  obtain ⟨r0, hr0⟩ := Finset.card_pos.mp c1
  obtain ⟨c0, hc0⟩ := Finset.card_pos.mp c2
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range] at hr0 hc0
  have ec : k + 2 + (c0 - (k + 2)) = c0 := by omega
  exact ⟨r0, c0 - (k + 2), hr0.2, by omega, hr0.1.2, by rw [ec]; exact hc0.1.2⟩

theorem G3_single_le_pair_l (u w : ℕ) : ∀ i, single u i = true → pair u w i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  simp [pair, hi]

theorem G3_single_le_pair_r (u w : ℕ) : ∀ i, single w i = true → pair u w i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  simp [pair, hi]

theorem G3_mono_mem {k : ℕ} (hk : 2 ≤ k) {F : (ℕ → Bool) → Bool} {S : Finset ℕ} (hd : DepOn S F)
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (hm : ∀ z z' : ℕ → Bool, (∀ i, z i = true → z' i = true) → F z = true → F z' = true) :
    (∀ u, u ≤ k → u ∈ S) ∧ (∀ v, v ≤ k → k + 2 + v ∈ S) ∧
    (∀ u, u < k → F (single u) = false) ∧ (∀ v, v < k → F (single (k + 2 + v)) = false) := by
  have hsx : ∀ u, u < k → F (single u) = false := by
    intro u hu
    by_contra h
    have h' : F (single u) = true := by simpa using h
    have a := hm _ _ (G3_single_le_pair_l u (k + 2 + u)) h'
    rw [G3_vf hF u u (by omega) (by omega) (by omega)] at a
    exact Bool.false_ne_true a
  have hsy : ∀ v, v < k → F (single (k + 2 + v)) = false := by
    intro v hv
    by_contra h
    have h' : F (single (k + 2 + v)) = true := by simpa using h
    have a := hm _ _ (G3_single_le_pair_r v (k + 2 + v)) h'
    rw [G3_vf hF v v (by omega) (by omega) (by omega)] at a
    exact Bool.false_ne_true a
  have hother : ∀ u, ∃ v, v < k ∧ v ≠ u := by
    intro u
    by_cases h : u = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  refine ⟨?_, ?_, hsx, hsy⟩
  · intro u hu
    by_contra hn
    by_cases huk : u < k
    · obtain ⟨v, hv, hvu⟩ := hother u
      have a := G3_vt hF u v (by omega) (by omega) (by omega)
      rw [B1_pair_right hd u _ hn, hsy v hv] at a
      exact Bool.false_ne_true a
    · have a := G3_vt hF u 0 (by omega) (by omega) (by omega)
      rw [B1_pair_right hd u _ hn, hsy 0 (by omega)] at a
      exact Bool.false_ne_true a
  · intro v hv
    by_contra hn
    by_cases hvk : v < k
    · obtain ⟨u, hu, huv⟩ := hother v
      have a := G3_vt hF u v (by omega) (by omega) (by omega)
      rw [B1_pair_left hd u _ hn, hsx u hu] at a
      exact Bool.false_ne_true a
    · have a := G3_vt hF 0 v (by omega) (by omega) (by omega)
      rw [B1_pair_left hd 0 _ hn, hsx 0 (by omega)] at a
      exact Bool.false_ne_true a

theorem G3_mono_false {k : ℕ} (hk : 3 ≤ k) {F : (ℕ → Bool) → Bool} {S : Finset ℕ}
    (hro : ROx false S F)
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v))) : False := by
  obtain ⟨hx, hy, hsx, hsy⟩ := G3_mono_mem (by omega) (B_dep hro) hF (B_mono hro)
  refine B_crown_mono_impossible (k + 2) (by omega) S F hro
    (fun u hu => ⟨hx u (by omega), hy u (by omega)⟩)
    (fun u hu => ⟨hsx u (by omega), hsy u (by omega)⟩) ?_
  intro u hu v hv
  rw [hF u v (by omega) (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem G3_pos {S1 S2 : Finset ℕ} {s : (ℕ → Bool) → Bool} {T : Bool → (ℕ → Bool) → Bool}
    {F : (ℕ → Bool) → Bool} (hdis : Disjoint S1 S2) (hs : ROx false S2 s)
    (hTm : ∀ b (z z' : ℕ → Bool), (∀ i, z i = true → z' i = true) → T b z = true → T b z' = true)
    (hFT : ∀ z, F z = T (!s z) z) (i : ℕ) (hi : i ∈ S1) (z z' : ℕ → Bool)
    (he : ∀ j, j ≠ i → z j = z' j) (hz : z i = false) : F z = true → F z' = true := by
  intro h
  have hi2 : i ∉ S2 := Finset.disjoint_left.mp hdis hi
  have es : s z = s z' := B_dep hs z z' (fun j hj => he j (fun e => hi2 (e ▸ hj)))
  rw [hFT] at h ⊢
  rw [← es]
  refine hTm _ z z' ?_ h
  intro j hj
  by_cases e : j = i
  · subst e; rw [hz] at hj; exact absurd hj Bool.false_ne_true
  · rw [← he j e]; exact hj

theorem G3_neg {S1 S2 : Finset ℕ} {s : (ℕ → Bool) → Bool} {T : Bool → (ℕ → Bool) → Bool}
    {F : (ℕ → Bool) → Bool} (hdis : Disjoint S1 S2) (hs : ROx false S2 s)
    (hTd : ∀ b, DepOn S1 (T b)) (hT01 : ∀ z, T false z = true → T true z = true)
    (hFT : ∀ z, F z = T (!s z) z) (i : ℕ) (hi : i ∈ S2) (z z' : ℕ → Bool)
    (he : ∀ j, j ≠ i → z j = z' j) (hz : z i = false) : F z' = true → F z = true := by
  intro h
  have hi1 : i ∉ S1 := Finset.disjoint_right.mp hdis hi
  have eT : ∀ b, T b z = T b z' := fun b => hTd b z z' (fun j hj => he j (fun e => hi1 (e ▸ hj)))
  have hle : ∀ j, z j = true → z' j = true := by
    intro j hj
    by_cases e : j = i
    · subst e; rw [hz] at hj; exact absurd hj Bool.false_ne_true
    · rw [← he j e]; exact hj
  have hsm := B_mono hs z z' hle
  rw [hFT] at h ⊢
  rw [eT]
  cases h1 : s z' with
  | false =>
    have h0 : s z = false := by
      cases h2 : s z with
      | false => rfl
      | true => rw [hsm h2] at h1; exact absurd h1 (by simp)
    rw [h1] at h; rw [h0]; exact h
  | true =>
    rw [h1] at h
    cases h2 : s z with
    | false => exact hT01 _ h
    | true => exact h

theorem G3_posR {F : (ℕ → Bool) → Bool} {i : ℕ}
    (hpos : ∀ z z' : ℕ → Bool, (∀ j, j ≠ i → z j = z' j) → z i = false → F z = true → F z' = true)
    (u : ℕ) (hne : u ≠ i) : F (single u) = true → F (pair u i) = true :=
  hpos _ _ (by intro j hj; simp [single, pair, hj]) (by simp [single, Ne.symm hne])

theorem G3_posL {F : (ℕ → Bool) → Bool} {i : ℕ}
    (hpos : ∀ z z' : ℕ → Bool, (∀ j, j ≠ i → z j = z' j) → z i = false → F z = true → F z' = true)
    (w : ℕ) (hne : i ≠ w) : F (single w) = true → F (pair i w) = true :=
  hpos _ _ (by intro j hj; simp [single, pair, hj]) (by simp [single, hne])

theorem G3_negR {F : (ℕ → Bool) → Bool} {i : ℕ}
    (hneg : ∀ z z' : ℕ → Bool, (∀ j, j ≠ i → z j = z' j) → z i = false → F z' = true → F z = true)
    (u : ℕ) (hne : u ≠ i) : F (pair u i) = true → F (single u) = true :=
  hneg _ _ (by intro j hj; simp [single, pair, hj]) (by simp [single, Ne.symm hne])

theorem G3_negL {F : (ℕ → Bool) → Bool} {i : ℕ}
    (hneg : ∀ z z' : ℕ → Bool, (∀ j, j ≠ i → z j = z' j) → z i = false → F z' = true → F z = true)
    (w : ℕ) (hne : i ≠ w) : F (pair i w) = true → F (single w) = true :=
  hneg _ _ (by intro j hj; simp [single, pair, hj]) (by simp [single, hne])

theorem G3_count (gs : List Gate) : b2 gs + nots gs ≤ gs.length := by
  induction gs with
  | nil => simp [b2, nots]
  | cons g t ih =>
    unfold b2 nots at *
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    cases h : isNot g.op <;> simp <;> (try split_ifs) <;> omega

theorem G3_crown_true {k : ℕ} (hk : 3 ≤ k) {F : (ℕ → Bool) → Bool} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (k + 2 + (k + 1))) (hd : DepOn S F)
    (hF : ∀ u v, u < k + 2 → v < k + 1 →
      F (pair u (k + 2 + v)) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)))
    (hcard : S.card = 2 * k + 1) (hro : ROx true S F) :
    ∃ R : ℕ → ℕ → Prop, (∀ u v, R u v → R v u) ∧
      (∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w) ∧
      ∀ z : ℕ → Bool, (F z = false ↔ canonR true k (k + 2) R z) := by
  obtain ⟨S1, S2, s, T, hdis, hSeq, hs, hTd, hTm, hT01, hFT, hemp⟩ := B_decomp hro
  have hrows := fun u u' hu hu' hne h1 h2 => G3_rows (by omega) hd hF u u' hu hu' hne h1 h2
  have hcols := fun v v' hv hv' hne h1 h2 => G3_cols (by omega) hd hF v v' hv hv' hne h1 h2
  obtain ⟨r0, c0, hr0, hc0, hr0S, hc0S⟩ := (G3_card hS hrows hcols).2 hcard
  have hrowS : ∀ u, u < k + 2 → u ≠ r0 → u ∈ S := by
    intro u hu hne
    by_contra h
    exact hrows u r0 hu hr0 hne h hr0S
  have hcolS : ∀ v, v < k + 1 → v ≠ c0 → k + 2 + v ∈ S := by
    intro v hv hne
    by_contra h
    exact hcols v c0 hv hc0 hne h hc0S
  have hsx : ∀ u, u < k + 2 → F (single u) = decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = c0)) := by
    intro u hu
    rw [← hF u c0 hu hc0, B1_pair_left hd u _ hc0S]
  have hsy : ∀ v, v < k + 1 → F (single (k + 2 + v)) = decide (r0 ≠ k + 1 ∧ ¬ (r0 < k ∧ r0 = v)) := by
    intro v hv
    rw [← hF r0 v hr0 hv, B1_pair_right hd r0 _ hr0S]
  have hpos := fun i hi => G3_pos (F := F) hdis hs hTm hFT i hi
  have hneg := fun i hi => G3_neg (F := F) hdis hs hTd hT01 hFT i hi
  have hmemS : ∀ i ∈ S, i ∈ S1 ∨ i ∈ S2 := by
    intro i hi
    rw [hSeq] at hi
    exact Finset.mem_union.mp hi
  have hother : ∀ u, ∃ v, v < k ∧ v ≠ u := by
    intro u
    by_cases h : u = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  have hc0k : c0 = k := by
    by_contra hne
    obtain ⟨v, hv, hvne⟩ := hother c0
    rcases hmemS _ (hcolS v (by omega) hvne) with h1 | h2
    · have a := G3_posR (hpos _ h1) v (by omega)
        (by rw [hsx v (by omega)]; exact decide_eq_true (by omega))
      rw [G3_vf hF v v (by omega) (by omega) (by omega)] at a
      exact Bool.false_ne_true a
    · have a := G3_negR (hneg _ h2) c0 (by omega) (G3_vt hF c0 v (by omega) (by omega) (by omega))
      rw [hsx c0 (by omega)] at a
      have := of_decide_eq_true a
      omega
  have hy2 : ∀ v, v < k → k + 2 + v ∈ S2 := by
    intro v hv
    rcases hmemS _ (hcolS v (by omega) (by omega)) with h1 | h2
    · have a := G3_posR (hpos _ h1) v (by omega)
        (by rw [hsx v (by omega)]; exact decide_eq_true (by omega))
      rw [G3_vf hF v v (by omega) (by omega) (by omega)] at a
      exact absurd a Bool.false_ne_true
    · exact h2
  have hr0k : k ≤ r0 := by
    by_contra hlt
    obtain ⟨u, hu, hune⟩ := hother r0
    rcases hmemS _ (hrowS u (by omega) hune) with h1 | h2
    · have a := G3_posL (hpos _ h1) (k + 2 + u) (by omega)
        (by rw [hsy u (by omega)]; exact decide_eq_true (by omega))
      rw [G3_vf hF u u (by omega) (by omega) (by omega)] at a
      exact Bool.false_ne_true a
    · have a := G3_negL (hneg _ h2) (k + 2 + r0) (by omega)
        (G3_vt hF u r0 (by omega) (by omega) (by omega))
      rw [hsy r0 (by omega)] at a
      have := of_decide_eq_true a
      omega
  have hds := B_dep hs
  by_cases hr0e : r0 = k + 1
  · exfalso
    have hx1 : ∀ u, u ≤ k → u ∈ S1 := by
      intro u hu
      rcases hmemS _ (hrowS u (by omega) (by omega)) with h1 | h2
      · exact h1
      · obtain ⟨v, hv, hvu⟩ := hother u
        have a := G3_negL (hneg _ h2) (k + 2 + v) (by omega)
          (G3_vt hF u v (by omega) (by omega) (by omega))
        rw [hsy v (by omega)] at a
        have := of_decide_eq_true a
        omega
    have e1 : ∀ u v, u ≤ k → v < k →
        F (pair u (k + 2 + v)) = T (!s (single (k + 2 + v))) (single u) := by
      intro u v hu hv
      have hu2 : u ∉ S2 := Finset.disjoint_left.mp hdis (hx1 u hu)
      have hv1 : k + 2 + v ∉ S1 := Finset.disjoint_right.mp hdis (hy2 v hv)
      rw [hFT, B1_pair_right hds u _ hu2, B1_pair_left (hTd _) u _ hv1]
    have e2 : ∀ u, u ≤ k → T true (single u) = true := by
      intro u hu
      have hu2 : u ∉ S2 := Finset.disjoint_left.mp hdis (hx1 u hu)
      have a := hsx u (by omega)
      rw [hFT, B1_single_off hds (B_zero hs) u hu2] at a
      rw [Bool.not_false] at a
      rw [a]
      exact decide_eq_true (by omega)
    have s0 : s (single (k + 2 + 0)) = true := by
      by_contra h
      have h' : s (single (k + 2 + 0)) = false := Bool.eq_false_iff.mpr h
      have a := e1 0 0 (by omega) (by omega)
      rw [h', Bool.not_false, e2 0 (by omega), G3_vf hF 0 0 (by omega) (by omega) (by omega)] at a
      exact Bool.false_ne_true a
    have s1 : s (single (k + 2 + 1)) = true := by
      by_contra h
      have h' : s (single (k + 2 + 1)) = false := Bool.eq_false_iff.mpr h
      have a := e1 1 1 (by omega) (by omega)
      rw [h', Bool.not_false, e2 1 (by omega), G3_vf hF 1 1 (by omega) (by omega) (by omega)] at a
      exact Bool.false_ne_true a
    have a0 := e1 0 0 (by omega) (by omega)
    have a1 := e1 0 1 (by omega) (by omega)
    rw [s0] at a0
    rw [s1] at a1
    have a2 := a0.trans a1.symm
    rw [G3_vf hF 0 0 (by omega) (by omega) (by omega),
      G3_vt hF 0 1 (by omega) (by omega) (by omega)] at a2
    exact Bool.false_ne_true a2
  · have hr0e' : r0 = k := by omega
    have hx2 : ∀ u, u < k → u ∈ S2 := by
      intro u hu
      rcases hmemS _ (hrowS u (by omega) (by omega)) with h1 | h2
      · have a := G3_posL (hpos _ h1) (k + 2 + u) (by omega)
          (by rw [hsy u (by omega)]; exact decide_eq_true (by omega))
        rw [G3_vf hF u u (by omega) (by omega) (by omega)] at a
        exact absurd a Bool.false_ne_true
      · exact h2
    have hk1 : k + 1 ∈ S2 := by
      rcases hmemS _ (hrowS (k + 1) (by omega) (by omega)) with h1 | h2
      · have a := G3_posL (hpos _ h1) (k + 2 + 0) (by omega)
          (by rw [hsy 0 (by omega)]; exact decide_eq_true (by omega))
        rw [G3_vf hF (k + 1) 0 (by omega) (by omega) (by omega)] at a
        exact absurd a Bool.false_ne_true
      · exact h2
    have hS1 : S1 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have hiS : i ∈ S := by rw [hSeq]; exact Finset.mem_union_left _ hi
      have hlt := Finset.mem_range.mp (hS hiS)
      have hn2 : i ∉ S2 := Finset.disjoint_left.mp hdis hi
      by_cases c1 : i < k
      · exact hn2 (hx2 i c1)
      · by_cases c2 : i = k
        · rw [c2, ← hr0e'] at hiS; exact hr0S hiS
        · by_cases c3 : i = k + 1
          · rw [c3] at hn2; exact hn2 hk1
          · have e : k + 2 + (i - (k + 2)) = i := by omega
            by_cases c4 : i - (k + 2) < k
            · have := hy2 _ c4
              rw [e] at this
              exact hn2 this
            · have e' : i = k + 2 + c0 := by omega
              rw [e'] at hiS
              exact hc0S hiS
    have hS2 : S = S2 := by rw [hSeq, hS1, Finset.empty_union]
    have hFs : ∀ z, F z = !s z := fun z => by rw [hFT, hemp hS1]
    have hsF : ∀ z, s z = !F z := by intro z; rw [hFs, Bool.not_not]
    have hSform : S = Finset.range k ∪ (Finset.range k).image (fun u => k + 2 + u) ∪ {k + 1} := by
      ext i
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_singleton]
      constructor
      · intro hiS
        have hlt := Finset.mem_range.mp (hS hiS)
        by_cases c1 : i < k
        · exact Or.inl (Or.inl c1)
        · by_cases c2 : i = k
          · rw [c2, ← hr0e'] at hiS; exact absurd hiS hr0S
          · by_cases c3 : i = k + 1
            · exact Or.inr c3
            · by_cases c4 : i - (k + 2) < k
              · exact Or.inl (Or.inr ⟨i - (k + 2), c4, by omega⟩)
              · have e' : i = k + 2 + c0 := by omega
                rw [e'] at hiS
                exact absurd hiS hc0S
      · rintro ((h | ⟨v, hv, rfl⟩) | rfl)
        · rw [hS2]; exact hx2 i h
        · rw [hS2]; exact hy2 v hv
        · rw [hS2]; exact hk1
    have hs' : ROx false S s := by rw [hS2]; exact hs
    have hm := B_matching (k + 2) S s hs' (Finset.range k) {k + 1}
      (by intro u hu; have := Finset.mem_range.mp hu; omega)
      (by
        intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        refine ⟨by simp, ?_⟩
        intro u hu
        have := Finset.mem_range.mp hu
        omega)
      hSform
      (by
        intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        rw [hsF, hsx (k + 1) (by omega),
          decide_eq_false (p := (k + 1 ≠ k + 1 ∧ ¬ (k + 1 < k ∧ k + 1 = c0))) (by omega)]
        rfl)
      (by
        intro u hu
        have hu' := Finset.mem_range.mp hu
        have t1 : F (single u) = true := by
          rw [hsx u (by omega)]; exact decide_eq_true (by omega)
        have t2 : F (single (k + 2 + u)) = true := by
          rw [hsy u (by omega)]; exact decide_eq_true (by omega)
        rw [hsF, hsF, t1, t2]
        exact ⟨rfl, rfl⟩)
      (by
        intro u hu v hv
        have hu' := Finset.mem_range.mp hu
        have hv' := Finset.mem_range.mp hv
        rw [hsF, hF u v (by omega) (by omega)]
        by_cases e : u = v
        · rw [decide_eq_false (p := (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v))) (by omega), decide_eq_true e]
          rfl
        · rw [decide_eq_true (p := (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v))) (by omega), decide_eq_false e]
          rfl)
    obtain ⟨hform, hmatch⟩ := hm
    refine ⟨fun u v => s (pair u v) = true, ?_, ?_, ?_⟩
    · intro u v h
      show s (pair v u) = true
      rw [B1_pair_comm]; exact h
    · intro u v w hu hv hw huv huw h1 h2
      exact hmatch u (Finset.mem_range.mpr hu) v (Finset.mem_range.mpr hv) w (Finset.mem_range.mpr hw)
        huv huw h1 h2
    · intro z
      have hz : F z = false ↔ s z = true := by
        rw [hFs]; cases s z <;> simp
      rw [hz, hform z]
      unfold canonR
      constructor
      · rintro (⟨p, hp, hzp⟩ | ⟨u, hu, hzu⟩ | ⟨u, hu, v, hv, hne, hR, hzz⟩)
        · left
          rw [Finset.mem_singleton] at hp
          subst hp
          exact ⟨rfl, hzp⟩
        · right; left
          exact ⟨u, Finset.mem_range.mp hu, hzu⟩
        · right; right
          exact ⟨u, v, Finset.mem_range.mp hu, Finset.mem_range.mp hv, hne, hR, hzz⟩
      · rintro (⟨_, hzp⟩ | ⟨u, hu, hzu⟩ | ⟨u, v, hu, hv, hne, hR, hzz⟩)
        · left
          exact ⟨k + 1, Finset.mem_singleton_self _, hzp⟩
        · right; left
          exact ⟨u, Finset.mem_range.mpr hu, hzu⟩
        · right; right
          exact ⟨u, Finset.mem_range.mpr hu, v, Finset.mem_range.mpr hv, hne, hR, hzz⟩

theorem G_H1_crown (k : ℕ) (hk : 3 ≤ k) (C : Circuit) (hfan : FanInTwo C) (hsz : C.size ≤ 2 * k + 1)
    (hrep : Represents (fun (i : Fin (k + 2)) (j : Fin (k + 1)) =>
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val))) C) :
    ∃ R : ℕ → ℕ → Prop, (∀ u v, R u v → R v u) ∧
      (∀ u v w, u < k → v < k → w < k → u ≠ v → u ≠ w → R u v → R u w → v = w) ∧
      ∀ z : ℕ → Bool, (fn C.gates (k + 2 + (k + 1)) C.output z = false ↔ canonR true k (k + 2) R z) := by
  have hF : ∀ u v, u < k + 2 → v < k + 1 →
      fn C.gates (k + 2 + (k + 1)) C.output (pair u (k + 2 + v)) =
        decide (u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)) := by
    intro u v hu hv
    exact G_rep (k + 2) (k + 1) _ C hrep ⟨u, hu⟩ ⟨v, hv⟩
  have hfan' : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) := by
    intro g hg
    have := hfan g hg
    exact ⟨this.2, this.1⟩
  obtain ⟨S, hS, hd, hcard, htight⟩ := A_tight (k + 2 + (k + 1)) C.gates hfan' C.output
  have hcnt := G3_count C.gates
  have hsz' : C.gates.length ≤ 2 * k + 1 := hsz
  have hrows := fun u u' hu hu' hne h1 h2 => G3_rows (by omega) hd hF u u' hu hu' hne h1 h2
  have hcols := fun v v' hv hv' hne h1 h2 => G3_cols (by omega) hd hF v v' hv hv' hne h1 h2
  obtain ⟨hlow, _⟩ := G3_card hS hrows hcols
  by_cases hn : nots C.gates = 0
  · exfalso
    have hn' : List.countP (fun g => isNot g.op) C.gates = 0 := hn
    have hmonF := A_mono (k + 2 + (k + 1)) C.gates (by
      intro g hg
      have h0 := List.countP_eq_zero.mp hn' g hg
      rcases (hfan' g hg).2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; apply h0; rw [h]; rfl) C.output
    obtain ⟨hx, hy, _, _⟩ := G3_mono_mem (by omega) hd hF hmonF
    have hsub : (Finset.range (k + 2 + (k + 1))).erase (k + 1) ⊆ S := by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      by_cases h : i ≤ k
      · exact hx i h
      · have e : k + 2 + (i - (k + 2)) = i := by omega
        rw [← e]
        exact hy _ (by omega)
    have hbig := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hbig
    have hro := (htight (by omega)).1 hn
    exact G3_mono_false hk hro hF
  · have hc : S.card = 2 * k + 1 := by omega
    obtain ⟨c, hro⟩ := (htight (by omega)).2 (by omega)
    cases c with
    | false => exact (G3_mono_false hk hro hF).elim
    | true => exact G3_crown_true hk hS hd hF hc hro

theorem G_H1 (n : ℕ) (hn : 0 < n) (crown : Bool) :
    let k := 6*n+1
    let nr := if crown then k+2 else k
    let nc := if crown then k+1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
    let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
       else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧ PEqualNP.Represents.Represents A C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
    ∀ f : Fn, eligible f → ∃ R : ℕ → ℕ → Prop, (∀ u v, R u v → R v u) ∧
      (∀ u v w, u < 6*n+1 → v < 6*n+1 → w < 6*n+1 → u ≠ v → u ≠ w → R u v → R u w → v = w) ∧
      (∀ x y, (f x y = !crown ↔ canonR crown k nr R (zOf x y))) := by
  cases crown
  · intro k nr nc A Fn eligible f hf
    obtain ⟨C, hg, hrep, hfe⟩ := hf
    have hg' : Monotone2 C ∧ C.size + 1 ≤ 2 * k := hg
    have hrep' : Represents (fun (i : Fin k) (j : Fin k) => decide (i.val = j.val)) C := hrep
    obtain ⟨R, hs, hm, hF⟩ := G_H1_mono k (by omega) C hg'.1 hg'.2 hrep'
    refine ⟨R, hs, hm, ?_⟩
    intro x y
    rw [hfe x y, G_eval nr nc C x y]
    exact hF (zOf x y)
  · intro k nr nc A Fn eligible f hf
    obtain ⟨C, hg, hrep, hfe⟩ := hf
    have hg' : FanInTwo C ∧ C.size ≤ 2 * k + 1 := hg
    have hrep' : Represents (fun (i : Fin (k + 2)) (j : Fin (k + 1)) =>
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val))) C := hrep
    obtain ⟨R, hs, hm, hF⟩ := G_H1_crown k (by omega) C hg'.1 hg'.2 hrep'
    refine ⟨R, hs, hm, ?_⟩
    intro x y
    rw [hfe x y, G_eval nr nc C x y]
    exact hF (zOf x y)

end PEqualNP.Outside.L_meta_29950

theorem PEqualNP.Outside.L_meta_29950 : (∀ (n m : Nat), 0 < n → ∀ (clauses : Fin m → Finset (Fin n × Bool)),
  (∀ j, (clauses j).card ≤ 3) → ∀ crown : Bool,
  let k := 6*n+1
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
     else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧ PEqualNP.Represents.Represents A C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  let test := fun (f : Fn) (w : Fin nr → Bool) => f w (fun _ => false) = !crown
  let triple := fun (i : Fin n) (s : Fin 6) (u : Fin nr) =>
    decide (u.val = 6*i.val+s.val ∨ u.val = 6*i.val+(s.val+1)%6 ∨ u.val = 6*i.val+(s.val+2)%6)
  let litWord := fun (i : Fin n) (sgn : Bool) (u : Fin nr) =>
    decide (u.val = 6*i.val ∨ u.val = 6*i.val+(if sgn then 1 else 5))
  let word := fun (j : Fin m) (u : Fin nr) =>
    decide (∃ lit ∈ clauses j, litWord lit.1 lit.2 u = true)
  let decode := fun (f : Fn) (i : Fin n) => decide (test f (litWord i true))
  let satisfied := fun (a : Fin n → Bool) (j : Fin m) => ∃ lit ∈ clauses j, a lit.1 = lit.2
  let occ := fun (i : Fin n) =>
    (Finset.univ.filter (fun j : Fin m => ∃ b : Bool, (i,b) ∈ clauses j)).card
  let bad := fun (f : Fn) (i : Fin n) =>
    (Finset.univ.filter (fun s : Fin 6 => ¬ test f (triple i s))).card
  let broken := fun (f : Fn) => (Finset.univ.filter (fun i : Fin n => 0 < bad f i)).card
  let loss := fun (a : Fin n → Bool) => (Finset.univ.filter (fun j => ¬ satisfied a j)).card
  let errs := fun (f : Fn) => (Finset.univ.filter (fun j : Fin m => ¬ test f (word j))).card +
    ∑ i : Fin n, (1+occ i)*bad f i
  let BestA := { a : Fin n → Bool // ∀ z : Fin n → Bool, loss a ≤ loss z }
  let BestF := { f : Fn // eligible f ∧ ∀ g : Fn, eligible g → errs f ≤ errs g }
  (m + (∑ i : Fin n, 6*(1+occ i)) ≤ 6*n+19*m) ∧
  (∀ f : Fn, eligible f → loss (decode f) + broken f ≤ errs f) ∧
  ∃ e : BestA ≃ BestF, ∀ a : BestA,
    decode (e a).val = a.val ∧ errs (e a).val = loss a.val ∧ broken (e a).val = 0) := by
  intro n m hn clauses hcl crown k nr nc A Fn eligible test triple litWord word
  have hnr : 6 * n + 1 ≤ nr := by
    show 6 * n + 1 ≤ (if crown = true then 6 * n + 1 + 2 else 6 * n + 1)
    split <;> omega
  exact PEqualNP.Outside.L_meta_29950.F_abstract n m clauses hcl Fn (Fin nr → Bool) eligible test
    (inst := fun f w => inferInstanceAs (Decidable (f w (fun _ => false) = !crown)))
    triple litWord word
    (fun f R => ∀ x y, (f x y = !crown ↔
      PEqualNP.Outside.L_meta_29950.canonR crown k nr R (PEqualNP.Outside.L_meta_29950.zOf x y)))
    (PEqualNP.Outside.L_meta_29950.G_H1 n hn crown)
    (PEqualNP.Outside.L_meta_29950.G_H2 n hn crown)
    (fun f f' R R' h h' hR => PEqualNP.Outside.L_meta_29950.G_H3 crown k nr nc f f' R R' h h' hR)
    (fun f R h => PEqualNP.Outside.L_meta_29950.G_H4 n m clauses crown nr nc hnr f R h)
