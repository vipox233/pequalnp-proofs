import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1379

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical

private noncomputable def effective (g : Gate) : List Nat := by
  classical
  exact if g.op = .not then g.inputs.take 1 else g.inputs

private theorem effective_mem_inputs {g : Gate} {u : Nat} (hu : u ∈ effective g) :
    u ∈ g.inputs := by
  classical
  by_cases h : g.op = .not
  · exact List.mem_of_mem_take (by simpa [effective, h] using hu)
  · simpa [effective, h] using hu

private theorem effective_length (g : Gate) : (effective g).length ≤ g.inputs.length := by
  classical
  by_cases h : g.op = .not
  · simpa [effective, h] using List.length_take_le' 1 g.inputs
  · simp [effective, h]

private theorem copy_eval_effective (g : Gate) (v : Nat → Bool) :
    g.op.eval (g.inputs.map v) = g.op.eval ((effective g).map v) := by
  classical
  rcases g with ⟨op, ins⟩
  cases op with
  | not => cases ins <;> simp [effective, GateOp.eval]
  | and => simp [effective]
  | or => simp [effective]
  | mod a => simp [effective]
  | maj => simp [effective]

-- The fold evaluation lemmas below are adapted from
-- lean/PEqualNP/Outside/L_lib_1324.lean at 6a82872f145f33551b94b8f483dee786f14824f2.
-- Names are prefixed, and the last two wrappers expose the reads-back and effective forms.
private def copyRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem copy_run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    copyRun (gs ++ [g]) x =
      copyRun gs x ++ [g.op.eval (g.inputs.map fun i => (copyRun gs x).getD i false)] := by
  simp only [copyRun, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem copy_run_length (gs : List Gate) (x : List Bool) :
    (copyRun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [copyRun]
  | append_singleton gs g ih =>
    rw [copy_run_snoc, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton]
    omega

private theorem copy_getD_lt (l : List Bool) (b : Bool) (t : Nat) (ht : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem copy_getD_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

private theorem copy_run_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (w : Nat)
    (hw : w < x.length + gs₁.length) :
    (copyRun (gs₁ ++ gs₂) x).getD w false = (copyRun gs₁ x).getD w false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc, copy_run_snoc, copy_getD_lt]
    · exact ih
    · rw [copy_run_length, List.length_append]; omega

private theorem copy_wires_input (C : Circuit) (x : List Bool) (u : Nat)
    (hu : u < x.length) : (C.wires x).getD u false = x.getD u false := by
  change (copyRun C.gates x).getD u false = _
  simpa [copyRun] using copy_run_prefix [] C.gates x u (by simpa using hu)

private theorem copy_run_gate (gs : List Gate) (x : List Bool) (j : Nat) (hj : j < gs.length) :
    (copyRun gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (copyRun gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h₁ := (List.take_append_drop j gs).symm
    have h₂ : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h₂] at h₁
    simpa [List.append_assoc] using h₁
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hp₁ : (copyRun gs x).getD (x.length + j) false =
      (copyRun (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact copy_run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by rw [List.length_append, List.length_singleton, hlen]; omega)
  rw [hp₁, copy_run_snoc]
  have hrlen : (copyRun (gs.take j) x).length = x.length + j := by rw [copy_run_length, hlen]
  rw [← hrlen, copy_getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hrlen]
  by_cases hi : i < x.length + j
  · rw [if_pos hi]
    have htake : (copyRun gs x).getD i false = (copyRun (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact copy_run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i
        (by rw [hlen]; exact hi)
    exact htake.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private theorem copy_wires_gate_full (C : Circuit) (x : List Bool) (j : Nat)
    (hj : j < C.size) (hback : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hj' : j < C.gates.length := hj
  have hjg : gateAt C j = C.gates[j] := by
    unfold gateAt
    exact List.getD_eq_getElem _ _ hj'
  change (copyRun C.gates x).getD (x.length + j) false = _
  rw [copy_run_gate C.gates x j hj', ← hjg]
  apply congrArg ((gateAt C j).op.eval)
  apply List.map_congr_left
  intro i hi
  exact if_pos (hback j hj' i hi)

private theorem copy_wires_gate (C : Circuit) (x : List Bool) (j : Nat)
    (hj : j < C.size) (hback : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((effective (gateAt C j)).map fun i => (C.wires x).getD i false) :=
  (copy_wires_gate_full C x j hj hback).trans (copy_eval_effective _ _)

-- Reindex a dependency-closed list of selected gates into a circuit on the new raw wires.
-- The wire map works simultaneously for every pair of inputs agreeing on the used raw wires.
private theorem copyCircuit (C : Circuit) (m b : Nat) (hb : 0 < b) (S : Finset Nat)
    (hS : ∀ i ∈ S, i < C.size) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hback : ReadsBack m C)
    (hclosed : ∀ i ∈ S, ∀ u ∈ effective (gateAt C i), m ≤ u → u - m ∈ S)
    (f : Nat → Nat) (hf : ∀ i < m, f i < b) :
    ∃ (D : Circuit) (ρ : Nat → Nat),
      PEqualNP.MetaComplexity.FanInTwo D ∧ ReadsBack b D ∧ D.output < b + D.size ∧
      D.size - PEqualNP.NotBracket.notCount D = (S.filter fun i => (gateAt C i).op ≠ .not).card ∧
      PEqualNP.NotBracket.notCount D = (S.filter fun i => (gateAt C i).op = .not).card ∧
      (∀ i < m, ρ i = f i) ∧ (∀ i ∈ S, ρ (m + i) < b + D.size) ∧
      ∀ (x y : List Bool), x.length = m → y.length = b →
        (∀ i ∈ S, ∀ u ∈ effective (gateAt C i), u < m → x.getD u false = y.getD (f u) false) →
        ∀ i ∈ S, (C.wires x).getD (m + i) false = (D.wires y).getD (ρ (m + i)) false := by
  classical
  let A := S.sort (· ≤ ·)
  let ρ : Nat → Nat := fun u => if u < m then f u else b + A.idxOf (u - m)
  let G : Nat → Gate := fun i => ⟨(gateAt C i).op, (effective (gateAt C i)).map ρ⟩
  let D : Circuit := ⟨A.map G, 0⟩
  have hMem (i : Nat) : i ∈ A ↔ i ∈ S := S.mem_sort _
  have hNodup : A.Nodup := S.sort_nodup _
  have hRank (i : Nat) (hi : i ∈ S) : A.idxOf i < A.length :=
    List.idxOf_lt_length_of_mem ((hMem i).2 hi)
  have hRankLt {i j : Nat} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) :
      A.idxOf i < A.idxOf j := by
    by_contra! hji
    have hordered : A.Pairwise (· ≤ ·) := S.pairwise_sort _
    have hle := hordered.rel_get_of_le
      (a := ⟨A.idxOf j, hRank j hj⟩) (b := ⟨A.idxOf i, hRank i hi⟩) hji
    change A[A.idxOf j]'(hRank j hj) ≤ A[A.idxOf i]'(hRank i hi) at hle
    rw [List.getElem_idxOf (hRank j hj), List.getElem_idxOf (hRank i hi)] at hle
    omega
  have hρRaw (i : Nat) (hi : i < m) : ρ i = f i := if_pos hi
  have hρGate (i : Nat) : ρ (m + i) = b + A.idxOf i := by
    simp [ρ, show ¬ m + i < m by omega]
  have hAt (k : Nat) (hk : k < A.length) : gateAt D k = G A[k] := by
    have hk' : k < D.gates.length := by simpa [D] using hk
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk']
    change (A.map G)[k]'hk' = _
    exact List.getElem_map _
  have hDlen : D.size = A.length := by simp [D, Circuit.size]
  have hDback : ReadsBack b D := by
    intro k hk u hu
    have hk' : k < A.length := by simpa [D] using hk
    rw [hAt k hk'] at hu
    change u ∈ (effective (gateAt C A[k])).map ρ at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    by_cases hvm : v < m
    · rw [hρRaw v hvm]
      have := hf v hvm
      omega
    · have hkS : A[k] ∈ S := (hMem _).1 (List.getElem_mem hk')
      have hvl := hback A[k] (hS _ hkS) v (effective_mem_inputs hv)
      have hvS := hclosed _ hkS v hv (by omega)
      have hvk := hRankLt hvS hkS (show v - m < A[k] by omega)
      rw [hNodup.idxOf_getElem k hk'] at hvk
      have hρv : ρ v = b + A.idxOf (v - m) := if_neg hvm
      rw [hρv]
      omega
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    change g ∈ A.map G at hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    have hiC : i < C.gates.length := hS i ((hMem i).1 hi)
    have hgi : gateAt C i ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hiC]
      exact List.getElem_mem hiC
    obtain ⟨hop, hin⟩ := hfan _ hgi
    refine ⟨hop, ?_⟩
    change ((effective (gateAt C i)).map ρ).length ≤ 2
    rw [List.length_map]
    exact (effective_length _).trans hin
  have hNeg : PEqualNP.NotBracket.notCount D = (S.filter fun i => (gateAt C i).op = .not).card := by
    unfold PEqualNP.NotBracket.notCount
    let p : Gate → Bool := fun g => @decide (g.op = .not) (lineDegreeGateOpDecEq _ _)
    change ((A.map G).filter p).length = _
    have hnd : (A.filter (p ∘ G)).Nodup := List.Nodup.filter _ hNodup
    have hA : A.toFinset = S := S.sort_toFinset _
    rw [List.filter_map, List.length_map, ← List.toFinset_card_of_nodup hnd,
      List.toFinset_filter, hA]
    apply congrArg Finset.card
    ext i
    simp [p, G, Function.comp_apply]
  have hPos : D.size - PEqualNP.NotBracket.notCount D =
      (S.filter fun i => (gateAt C i).op ≠ .not).card := by
    have hpartition := Finset.card_filter_add_card_filter_not (s := S)
      (fun i => (gateAt C i).op = .not)
    change (S.filter fun i => (gateAt C i).op = .not).card +
      (S.filter fun i => (gateAt C i).op ≠ .not).card = S.card at hpartition
    rw [hNeg, hDlen, show A.length = S.card from S.length_sort _]
    omega
  refine ⟨D, ρ, hDfan, hDback, ?_, hPos, hNeg, hρRaw, ?_, ?_⟩
  · change 0 < b + D.size
    omega
  · intro i hi
    rw [hρGate, hDlen]
    exact Nat.add_lt_add_left (hRank i hi) b
  · intro x y hx hy hagree i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      let k := A.idxOf i
      have hk : k < A.length := hRank i hi
      have hkD : k < D.size := hDlen.symm ▸ hk
      have hki : A[k] = i := List.getElem_idxOf hk
      have hs := copy_wires_gate C x i (hS i hi) (by rwa [hx])
      have ht := copy_wires_gate_full D y k hkD (by rwa [hy])
      rw [hx] at hs
      rw [hy, hAt k hk, hki] at ht
      rw [hs, hρGate i, ht]
      change (gateAt C i).op.eval ((effective (gateAt C i)).map _) =
        (gateAt C i).op.eval (((effective (gateAt C i)).map ρ).map _)
      rw [List.map_map]
      apply congrArg ((gateAt C i).op.eval)
      apply List.map_congr_left
      intro u hu
      change (C.wires x).getD u false = (D.wires y).getD (ρ u) false
      by_cases hum : u < m
      · rw [hρRaw u hum, copy_wires_input C x u (by omega),
          copy_wires_input D y (f u) (by rw [hy]; exact hf u hum)]
        exact hagree i hi u hu hum
      · have hu_back := hback i (hS i hi) u (effective_mem_inputs hu)
        have hu_sel := hclosed i hi u hu (by omega)
        have hu_eq : m + (u - m) = u := by omega
        simpa only [hu_eq] using ih (u - m) (by omega) hu_sel

private def depGraph {N : ℕ} (pins : Fin N → List (Fin N))
    (before : ∀ v u, u ∈ pins v → u.val < v.val) : SimpleGraph (Fin N) where
  Adj u v := u ∈ pins v ∨ v ∈ pins u
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨fun v h => Nat.lt_irrefl v.val (before v v (h.elim id id))⟩

private theorem depGraph_card {N : ℕ} (pins : Fin N → List (Fin N))
    (before : ∀ v u, u ∈ pins v → u.val < v.val)
    (c : (depGraph pins before).ConnectedComponent) :
    let S : Finset (Fin N) := by
      classical
      exact Finset.univ.filter (fun v => (depGraph pins before).connectedComponentMk v = c)
    S.card ≤ S.sum (fun v => (pins v).length) + 1 := by
  classical
  intro S
  have hS (v : Fin N) : v ∈ S ↔ v ∈ c.supp := by
    change v ∈ Finset.univ.filter (fun w => (depGraph pins before).connectedComponentMk w = c) ↔
      v ∈ c.supp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
  letI : Fintype c := Fintype.ofFinset S hS
  let Slots := Σ v : c, Fin (pins v.val).length
  let operand (q : Slots) : c :=
    ⟨(pins q.1.val).get q.2,
      c.mem_supp_of_adj_mem_supp q.1.property (Or.inr (List.get_mem _ _))⟩
  let edge (q : Slots) : c.toSimpleGraph.edgeSet := by
    refine ⟨Sym2.mk (operand q) q.1, (SimpleGraph.mem_edgeSet c.toSimpleGraph).mpr ?_⟩
    change (pins q.1.val).get q.2 ∈ pins q.1.val ∨ q.1.val ∈ pins ((pins q.1.val).get q.2)
    exact Or.inl (List.get_mem _ _)
  have hSurj : Function.Surjective edge := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    have hadj : u.val ∈ pins v.val ∨ v.val ∈ pins u.val :=
      (SimpleGraph.mem_edgeSet c.toSimpleGraph).mp he
    rcases hadj with huv | hvu
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp huv
      have hget : operand ⟨v, i⟩ = u := Subtype.ext hi
      refine ⟨⟨v, i⟩, Subtype.ext ?_⟩
      change Sym2.mk (operand ⟨v, i⟩) v = Sym2.mk u v
      rw [hget]
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvu
      have hget : operand ⟨u, i⟩ = v := Subtype.ext hi
      refine ⟨⟨u, i⟩, Subtype.ext ?_⟩
      change Sym2.mk (operand ⟨u, i⟩) u = Sym2.mk u v
      rw [hget]
      exact Sym2.eq_swap
  have hEdges := Nat.card_le_card_of_surjective edge hSurj
  have hSlots : Nat.card Slots = S.sum (fun v => (pins v).length) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact (Finset.sum_subtype (p := (· ∈ c.supp)) S hS (fun v => (pins v).length)).symm
  have hComponent : Nat.card c = S.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_finset' (p := c.supp) S hS
  have hConnected := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  rw [hComponent] at hConnected
  rw [hSlots] at hEdges
  exact hConnected.trans (Nat.add_le_add_right hEdges 1)
private theorem locInput (C : Circuit) (x : List Bool) (v : ℕ) (hv : v < x.length) :
    (C.wires x).getD v false = x.getD v false :=
  copy_wires_input C x v hv

private theorem locGate (C : Circuit) (m : ℕ) (x : List Bool) (hx : x.length = m)
    (back : ReadsBack m C) (i : ℕ) (hi : i < C.size) :
    (C.wires x).getD (m+i) false = (gateAt C i).op.eval
      ((effective (gateAt C i)).map fun u => (C.wires x).getD u false) := by
  subst m
  exact copy_wires_gate C x i hi back

private noncomputable def cuts (n : ℕ) (C : Circuit) (v : ℕ) : List ℕ :=
  if n+2 ≤ v then effective (gateAt C (v-(n+2))) else []

private theorem cuts_lt (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    {v u : ℕ} (hv : v < n+2+C.size) (hu : u ∈ cuts n C v) : u < v := by
  by_cases h : n+2 ≤ v
  · have hi : v-(n+2) < C.size := by omega
    rw [cuts, ite_eq_left h] at hu
    have hb := back _ hi u (effective_mem_inputs hu)
    omega
  · simp [cuts, h] at hu

private theorem locality {α : Type*} (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    (label : ℕ → α)
    (edge : ∀ v < n+2+C.size, ∀ u ∈ cuts n C v, label u = label v)
    (x y : List Bool) (hx : x.length = n+2) (hy : y.length = n+2)
    (v : ℕ) (hv : v < n+2+C.size)
    (hraw : ∀ u < n+2, label u = label v → x.getD u false = y.getD u false) :
    (C.wires x).getD v false = (C.wires y).getD v false := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases hb : v < n+2
    · rw [locInput _ _ _ (by simpa only [hx] using hb),
        locInput _ _ _ (by simpa only [hy] using hb)]
      exact hraw v hb rfl
    · let i := v-(n+2)
      have hi : i < C.size := by dsimp [i]; omega
      have he : v = n+2+i := by dsimp [i]; omega
      conv_lhs => rw [he, locGate C (n+2) x hx back i hi]
      conv_rhs => rw [he, locGate C (n+2) y hy back i hi]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hm : u ∈ cuts n C v := by
        simpa only [cuts, ite_eq_left (by omega : n+2 ≤ v)] using hu
      have hlt := cuts_lt n C back hv hm
      have hcl := edge v hv u hm
      exact ih u hlt (by omega) (fun z hz hzu => hraw z hz (hzu.trans hcl))

private def thresholdRaw (n t : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < t)) ++ [false,true]

private theorem rawLen (n t : ℕ) : (thresholdRaw n t).length = n+2 := by
  simp [thresholdRaw]

private theorem rawSwitch (n t v : ℕ) (hv : v < n) :
    (thresholdRaw n t).getD v false = decide (v < t) := by
  dsimp only [thresholdRaw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hv), List.getElem?_ofFn]
  simp [hv]

private theorem rawFalse (n t : ℕ) : (thresholdRaw n t).getD n false = false := by
  dsimp only [thresholdRaw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

private theorem rawTrue (n t : ℕ) : (thresholdRaw n t).getD (n+1) false = true := by
  dsimp only [thresholdRaw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

private theorem rawStable (n s t u : ℕ) (hu : u < n+2)
    (h : u < s ∨ t ≤ u) (hst : s ≤ t) :
    (thresholdRaw n s).getD u false = (thresholdRaw n t).getD u false := by
  by_cases hs : u < n
  · rw [rawSwitch _ _ _ hs, rawSwitch _ _ _ hs]
    rcases h with h | h
    · simp [h, show u < t by omega]
    · simp [show ¬u < s by omega, show ¬u < t by omega]
  · have he : u = n ∨ u = n+1 := by omega
    rcases he with rfl | rfl
    · rw [rawFalse, rawFalse]
    · rw [rawTrue, rawTrue]

private def total {d : ℕ} (w : Fin d → ℕ) : ℕ := ∑ j, w j

private def startAt {d : ℕ} (w : Fin d → ℕ) (j : Fin d) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin d => i.val < j.val), w i

private theorem startMono {d : ℕ} (w : Fin d → ℕ) {j k : Fin d} (h : j.val < k.val) :
    startAt w j + w j ≤ startAt w k := by
  classical
  have hn : j ∉ Finset.univ.filter (fun i : Fin d => i.val < j.val) := by simp
  have hi : insert j (Finset.univ.filter (fun i : Fin d => i.val < j.val)) ⊆
      Finset.univ.filter (fun i : Fin d => i.val < k.val) := by
    intro a ha
    have h' : a.val < k.val := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact h
      · exact Nat.lt_trans (Finset.mem_filter.mp ha).2 h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩
  have hsum := Finset.sum_le_sum_of_subset hi (f := w)
  rw [Finset.sum_insert hn] at hsum
  simpa [startAt, Nat.add_comm] using hsum

private theorem startBound {d : ℕ} (w : Fin d → ℕ) (j : Fin d) :
    startAt w j + w j ≤ total w := by
  classical
  have hn : j ∉ Finset.univ.filter (fun i : Fin d => i.val < j.val) := by simp
  have hi : insert j (Finset.univ.filter (fun i : Fin d => i.val < j.val)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset hi (f := w)
  rw [Finset.sum_insert hn] at hsum
  simpa [startAt, total, Nat.add_comm] using hsum

private def switchIndex {d : ℕ} (w : Fin d → ℕ) (a : Σ j, Fin (w j)) : Fin (total w) :=
  ⟨startAt w a.1 + a.2.val, by have := startBound w a.1; have := a.2.isLt; omega⟩

private theorem switchInj {d : ℕ} (w : Fin d → ℕ) : Function.Injective (switchIndex w) := by
  rintro ⟨j, a⟩ ⟨k, b⟩ he
  have he' : startAt w j + a.val = startAt w k + b.val := congrArg Fin.val he
  have hjk : j.val = k.val := by
    rcases lt_trichotomy j.val k.val with h | h | h
    · have := startMono w h
      have := a.isLt
      omega
    · exact h
    · have := startMono w h
      have := b.isLt
      omega
  obtain rfl : j = k := Fin.ext hjk
  obtain rfl : a = b := Fin.ext (by omega)
  rfl

private theorem switchSurj {d : ℕ} (w : Fin d → ℕ) : Function.Surjective (switchIndex w) := by
  have hc : Fintype.card (Σ j, Fin (w j)) = Fintype.card (Fin (total w)) := by
    calc
      _ = total w := by simp only [Fintype.card_sigma, Fintype.card_fin, total]
      _ = Fintype.card (Fin (total w)) := (Fintype.card_fin (total w)).symm
  exact ((Fintype.bijective_iff_injective_and_card (switchIndex w)).2 ⟨switchInj w, hc⟩).2

private theorem switchLink {d : ℕ} (w : Fin d → ℕ) (C : Circuit)
    (back : ReadsBack (total w+2) C) {α : Type*} (label : ℕ → α)
    (edge : ∀ v < total w+2+C.size, ∀ u ∈ cuts (total w) C v, label u = label v)
    {j : Fin d} (i : Fin (w j)) {r : ℕ} (hr : r < total w+2+C.size)
    (hne : (C.wires (thresholdRaw (total w) (startAt w j+i.val))).getD r false ≠
      (C.wires (thresholdRaw (total w) (startAt w j+i.val+1))).getD r false) :
    label (startAt w j+i.val) = label r := by
  by_contra hn
  apply hne
  refine locality (total w) C back label edge _ _ (rawLen ..) (rawLen ..) r hr ?_
  intro u hu hclass
  have hne' : u ≠ startAt w j+i.val := fun he => hn (he ▸ hclass)
  exact rawStable _ _ _ _ hu (by omega) (by omega)

private theorem offBlockConstant {d : ℕ} (w : Fin d → ℕ) (C : Circuit)
    (back : ReadsBack (total w+2) C) {α : Type*} (label : ℕ → α)
    (edge : ∀ v < total w+2+C.size, ∀ u ∈ cuts (total w) C v, label u = label v)
    {j : Fin d} (c : α) (link : ∀ i : Fin (w j), label (startAt w j+i.val) = c)
    {v : ℕ} (hv : v < total w+2+C.size) (hvc : label v ≠ c) (t : Fin (w j+1)) :
    (C.wires (thresholdRaw (total w) (startAt w j+t.val))).getD v false =
      (C.wires (thresholdRaw (total w) (startAt w j))).getD v false := by
  symm
  refine locality (total w) C back label edge _ _ (rawLen ..) (rawLen ..) v hv ?_
  intro u hu hclass
  have houtside : u < startAt w j ∨ startAt w j+t.val ≤ u := by
    by_contra! h
    let a : Fin (w j) := ⟨u-startAt w j, by have := t.isLt; omega⟩
    have he : startAt w j+a.val = u := by dsimp [a]; omega
    exact hvc (hclass.symm.trans (he ▸ link a))
  exact rawStable _ _ _ _ hu houtside (by omega)
private noncomputable def fiber {ι α : Type*} (A : Finset ι) (f : ι → α) (c : α) : Finset ι :=
  A.filter fun a => f a = c

private theorem memFiber {ι α : Type*} {A : Finset ι} {f : ι → α} {a : ι} {c : α} :
    a ∈ fiber A f c ↔ a ∈ A ∧ f a = c := by
  simp [fiber]

private noncomputable def blocks {d : ℕ} {α : Type*} (r : Fin d → α) (c : α) : Finset (Fin d) :=
  fiber Finset.univ r c

private noncomputable def need {d : ℕ} {α : Type*} (w : Fin d → ℕ) (r : Fin d → α) (c : α) : ℕ :=
  (blocks r c).sum w

private theorem memBlocks {d : ℕ} {α : Type*} {r : Fin d → α} {c : α} {j : Fin d} :
    j ∈ blocks r c ↔ r j = c := by
  simp [blocks, memFiber]

private def goodClass {d : ℕ} {α : Type*} (w : Fin d → ℕ) (r : Fin d → α)
    (P : α → ℕ) (c : α) : Prop := (blocks r c).card = 1 ∧ P c+1 = need w r c

private theorem budgets {d p q : ℕ} {α : Type*} (w : Fin d → ℕ) (r : Fin d → α) (P Q : α → ℕ)
    (hp : ∑ c ∈ Finset.univ.image r, P c ≤ p)
    (hq : ∑ c ∈ Finset.univ.image r, Q c ≤ q)
    (hb : ∀ c ∈ Finset.univ.image r, need w r c ≤ P c+1) :
    let G : Finset (Fin d) := Finset.univ.filter (fun j => goodClass w r P (r j))
    total w ≤ p+d ∧ d-G.card ≤ 2*(p+d-total w) ∧ G.sum (fun j => Q (r j)) ≤ q := by
  classical
  intro G
  let K := Finset.univ.image r
  let B : Finset (Fin d) := Finset.univ \ G
  have hB : B.card = d-G.card := by
    simp [B, Finset.card_sdiff_of_subset (Finset.subset_univ G), Fintype.card_fin]
  have maps (j : Fin d) : r j ∈ K := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hs : ∑ c ∈ K, need w r c = total w := by
    exact Finset.sum_fiberwise_of_maps_to (fun j _ => maps j) w
  have hc : ∑ c ∈ K, (blocks r c).card = d := by
    simpa only [blocks, fiber, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := r) (t := K)
        (fun j _ => maps j)).symm
  have hbc : ∑ c ∈ K, (fiber B r c).card = B.card :=
    (Finset.card_eq_sum_card_fiberwise (s := B) (f := r) (t := K) (fun j _ => maps j)).symm
  have loss : ∀ c ∈ K, 2 * need w r c + (fiber B r c).card ≤ 2 * (P c + (blocks r c).card) := by
    intro c hck
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hck
    have hm : j ∈ blocks r (r j) := memBlocks.mpr rfl
    have hn : 0 < (blocks r (r j)).card := Finset.card_pos.mpr ⟨j, hm⟩
    have hbf : (fiber B r (r j)).card ≤ (blocks r (r j)).card := by
      apply Finset.card_le_card
      intro i hi
      exact memBlocks.mpr (memFiber.mp hi).2
    have hbound := hb (r j) (maps j)
    by_cases heq : (blocks r (r j)).card = 1
    · by_cases hmin : P (r j)+1 = need w r (r j)
      · have hz : fiber B r (r j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          obtain ⟨hib, hr⟩ := memFiber.mp hi
          have hiG : i ∈ G := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, by rw [hr]; exact ⟨heq, hmin⟩⟩
          exact (Finset.mem_sdiff.mp hib).2 hiG
        rw [hz, Finset.card_empty]
        omega
      · omega
    · omega
  have htotal :
      2 * (∑ c ∈ K, need w r c) + (∑ c ∈ K, (fiber B r c).card) ≤
        2 * ((∑ c ∈ K, P c) + (∑ c ∈ K, (blocks r c).card)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using Finset.sum_le_sum loss
  rw [hs, hbc, hc, hB] at htotal
  change (∑ c ∈ K, P c) ≤ p at hp
  have hbgt : ∑ j ∈ G, Q (r j) ≤ ∑ c ∈ K, Q c := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := G) (t := K) (fun j _ => maps j) Q]
    apply Finset.sum_le_sum
    intro c _
    by_cases he : (fiber G r c).Nonempty
    · obtain ⟨j, hj⟩ := he
      obtain ⟨hjG, hr⟩ := memFiber.mp hj
      have hgood : goodClass w r P (r j) := (Finset.mem_filter.mp hjG).2
      have hcard : (fiber G r c).card = 1 := by
        have hh : (fiber G r c).card ≤ (blocks r (r j)).card := by
          apply Finset.card_le_card
          intro i hi
          exact memBlocks.mpr ((memFiber.mp hi).2.trans hr.symm)
        have hpos := Finset.card_pos.mpr ⟨j, hj⟩
        have hone := hgood.1
        omega
      change (fiber G r c).sum (fun _ => Q c) ≤ Q c
      simp [Finset.sum_const, hcard]
    · have hzero : fiber G r c = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      change (fiber G r c).sum (fun _ => Q c) ≤ Q c
      simp [hzero]
  refine ⟨?_, ?_, hbgt.trans hq⟩ <;> omega

private noncomputable def posSet (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun i => (gateAt C i).op ≠ .not)

private noncomputable def negSet (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun i => (gateAt C i).op = .not)

private theorem gateAtGet (C : Circuit) (i : ℕ) (hi : i < C.size) :
    gateAt C i = C.gates[i]'hi := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem allNeg (C : Circuit) :
    (negSet C (Finset.range C.size)).card = PEqualNP.NotBracket.notCount C := by
  classical
  let A := (Finset.univ : Finset (Fin C.size)).filter (fun i => (gateAt C i.val).op = .not)
  have hc : (negSet C (Finset.range C.size)).card = A.card := by
    apply Finset.card_bij (fun i hi => ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ he
      exact congrArg Fin.val he
    · intro j hj
      exact ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, (Finset.mem_filter.mp hj).2⟩,
        Fin.ext rfl⟩
  rw [hc]
  unfold PEqualNP.NotBracket.notCount
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← List.ofFn_getElem (xs := C.gates)]
  rw [List.countP_ofFn]
  apply congrArg Finset.card
  ext i
  let p : Gate → Bool := fun g => @decide (g.op = .not) (lineDegreeGateOpDecEq _ _)
  change i ∈ (Finset.univ : Finset (Fin C.size)).filter (fun a => (gateAt C a.val).op = .not) ↔
    i ∈ (Finset.univ : Finset (Fin C.size)).filter (fun a => p (C.gates[a.val]'a.isLt) = true)
  simp only [Finset.mem_filter, gateAtGet C i.val i.isLt, p, decide_eq_true_eq]

private theorem allPos (C : Circuit) :
    (posSet C (Finset.range C.size)).card = C.size-PEqualNP.NotBracket.notCount C := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range C.size)
    (p := fun i => (gateAt C i).op = .not)
  rw [Finset.card_range] at h
  change (negSet C (Finset.range C.size)).card + (posSet C (Finset.range C.size)).card = _ at h
  rw [allNeg] at h
  omega

private noncomputable def gateFiber {α : Type*} (n : ℕ) (C : Circuit) (l : ℕ → α) (c : α) : Finset ℕ :=
  fiber (Finset.range C.size) (fun i => l (n+2+i)) c

private theorem memGateFiber {α : Type*} {n : ℕ} {C : Circuit} {l : ℕ → α} {c : α} {i : ℕ} :
    i ∈ gateFiber n C l c ↔ i < C.size ∧ l (n+2+i) = c := by
  simp [gateFiber, memFiber]

private theorem posFiber {α : Type*} (n : ℕ) (C : Circuit) (l : ℕ → α) (c : α) :
    posSet C (gateFiber n C l c) = fiber (posSet C (Finset.range C.size)) (fun i => l (n+2+i)) c := by
  classical
  ext i
  simp only [posSet, Finset.mem_filter, memGateFiber, memFiber, Finset.mem_range]
  tauto

private theorem negFiber {α : Type*} (n : ℕ) (C : Circuit) (l : ℕ → α) (c : α) :
    negSet C (gateFiber n C l c) = fiber (negSet C (Finset.range C.size)) (fun i => l (n+2+i)) c := by
  classical
  ext i
  simp only [negSet, Finset.mem_filter, memGateFiber, memFiber, Finset.mem_range]
  tauto

private theorem sumFiberCardLe {α β : Type*} (A : Finset α) (K : Finset β) (f : α → β) :
    ∑ c ∈ K, (fiber A f c).card ≤ A.card := by
  classical
  calc
    _ = (A.filter (fun a => f a ∈ K)).card := Finset.sum_card_fiberwise_eq_card_filter A K f
    _ ≤ _ := Finset.card_filter_le A (fun a => f a ∈ K)
private noncomputable def wirePins (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    (v : Fin (n+2+C.size)) : List (Fin (n+2+C.size)) :=
  (cuts n C v.val).attach.map fun u => ⟨u.val, (cuts_lt n C back v.isLt u.property).trans v.isLt⟩

private theorem wirePinsBefore (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    (v u : Fin (n+2+C.size)) (hu : u ∈ wirePins n C back v) : u.val < v.val := by
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hu
  have he : a.val = u.val := congrArg Fin.val ha
  rw [← he]
  exact cuts_lt n C back v.isLt a.property

private noncomputable def wireGraph (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C) :
    SimpleGraph (Fin (n+2+C.size)) := depGraph (wirePins n C back) (wirePinsBefore n C back)

private noncomputable def wireLabel (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C) (v : ℕ) :
    (wireGraph n C back).ConnectedComponent :=
  (wireGraph n C back).connectedComponentMk
    (if h : v < n+2+C.size then ⟨v,h⟩ else ⟨0, by omega⟩)

private theorem wireLabelAt (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    (v : Fin (n+2+C.size)) : wireLabel n C back v.val = (wireGraph n C back).connectedComponentMk v := by
  simp [wireLabel, v.isLt]

private theorem wireEdge (n : ℕ) (C : Circuit) (back : ReadsBack (n+2) C)
    (v : ℕ) (hv : v < n+2+C.size) (u : ℕ) (hu : u ∈ cuts n C v) :
    wireLabel n C back u = wireLabel n C back v := by
  have h := cuts_lt n C back hv hu
  let u' : Fin (n+2+C.size) := ⟨u,h.trans hv⟩
  let v' : Fin (n+2+C.size) := ⟨v,hv⟩
  change wireLabel n C back u'.val = wireLabel n C back v'.val
  rw [wireLabelAt, wireLabelAt]
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  apply Or.inl
  apply List.mem_map.mpr
  exact ⟨⟨u, hu⟩, List.mem_attach _ _, rfl⟩

private theorem widthCard {d N : ℕ} {α : Type*} (w : Fin d → ℕ) (r : Fin d → α)
    (l : ℕ → α) (c : α) (hN : total w ≤ N)
    (link : ∀ j (i : Fin (w j)), l (startAt w j+i.val) = r j) :
    ((fiber (Finset.univ : Finset (Fin N)) (fun v => l v.val) c).filter
      (fun v => v.val < total w)).card = need w r c := by
  classical
  let B := (blocks r c).sigma (fun j => (Finset.univ : Finset (Fin (w j))))
  have hB : B.card = need w r c := by
    simp [B, Finset.card_sigma, need, Fintype.card_fin]
  rw [← hB]
  symm
  apply Finset.card_bij (fun a _ => ⟨(switchIndex w a).val, (switchIndex w a).isLt.trans_le hN⟩)
  · intro a ha
    have hja : r a.1 = c := memBlocks.mp (Finset.mem_sigma.mp ha).1
    exact Finset.mem_filter.mpr ⟨memFiber.mpr ⟨Finset.mem_univ _,
      (link a.1 a.2).trans hja⟩, (switchIndex w a).isLt⟩
  · intro a _ b _ hab
    apply switchInj w
    exact Fin.ext (congrArg (fun v : Fin N => v.val) hab)
  · intro v hv
    obtain ⟨hm, hvn⟩ := Finset.mem_filter.mp hv
    let v' : Fin (total w) := ⟨v.val,hvn⟩
    obtain ⟨a, ha⟩ := switchSurj w v'
    have hval : startAt w a.1 + a.2.val = v.val := congrArg Fin.val ha
    refine ⟨a, Finset.mem_sigma.mpr ⟨memBlocks.mpr ?_, Finset.mem_univ _⟩, Fin.ext hval⟩
    rw [← link a.1 a.2, hval]
    exact (memFiber.mp hm).2

private theorem posCard {α : Type*} (n : ℕ) (C : Circuit) (l : ℕ → α) (c : α) :
    (((fiber (Finset.univ : Finset (Fin (n+2+C.size))) (fun v => l v.val) c).filter
      (fun v => n+2 ≤ v.val ∧ (gateAt C (v.val-(n+2))).op ≠ .not))).card =
        (posSet C (gateFiber n C l c)).card := by
  classical
  symm
  apply Finset.card_bij (fun i hi => ⟨n+2+i, Nat.add_lt_add_left
    (memGateFiber.mp (Finset.mem_filter.mp hi).1).1 _⟩)
  · intro i hi
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hc⟩ := memGateFiber.mp hm
    exact Finset.mem_filter.mpr ⟨memFiber.mpr ⟨Finset.mem_univ _,hc⟩,
      Nat.le_add_right _ _, by simpa only [Nat.add_sub_cancel_left] using hn⟩
  · intro i _ j _ he
    have hh : n+2+i = n+2+j := congrArg Fin.val he
    omega
  · intro v hv
    obtain ⟨hm, hle, hn⟩ := Finset.mem_filter.mp hv
    have hc := (memFiber.mp hm).2
    have hval : n+2+(v.val-(n+2)) = v.val := by omega
    refine ⟨v.val-(n+2), Finset.mem_filter.mpr ⟨memGateFiber.mpr ⟨?_,?_⟩, hn⟩, Fin.ext hval⟩
    · have := v.isLt
      omega
    · rw [hval]
      exact hc

private theorem componentWidth {d : ℕ} (w : Fin d → ℕ) (C : Circuit)
    (fan : FanInTwo C) (back : ReadsBack (total w+2) C)
    (r : Fin d → (wireGraph (total w) C back).ConnectedComponent)
    (link : ∀ j (i : Fin (w j)), wireLabel (total w) C back (startAt w j+i.val) = r j)
    (c : (wireGraph (total w) C back).ConnectedComponent) :
    need w r c ≤ (posSet C (gateFiber (total w) C (wireLabel (total w) C back) c)).card + 1 := by
  classical
  let n := total w
  let l := wireLabel n C back
  let S := fiber (Finset.univ : Finset (Fin (n+2+C.size))) (fun v => l v.val) c
  have hG : S.card ≤ S.sum (fun v => (cuts n C v.val).length) + 1 := by
    have hh := depGraph_card (wirePins n C back) (wirePinsBefore n C back) c
    dsimp only at hh
    simpa only [S, fiber, l, wireLabelAt, wireGraph, wirePins, List.length_map, List.length_attach] using hh
  let rawFlag : Fin (n+2+C.size) → ℕ := fun v => if v.val < n then 1 else 0
  let posFlag : Fin (n+2+C.size) → ℕ := fun v =>
    if n+2 ≤ v.val ∧ (gateAt C (v.val-(n+2))).op ≠ .not then 1 else 0
  have hR : S.sum rawFlag = need w r c := by
    rw [show S.sum rawFlag = (S.filter (fun v => v.val < n)).card by simp [rawFlag]]
    exact widthCard w r l c (by dsimp [n]; omega) link
  have hP : S.sum posFlag = (posSet C (gateFiber n C l c)).card := by
    rw [show S.sum posFlag = (S.filter (fun v => n+2 ≤ v.val ∧
      (gateAt C (v.val-(n+2))).op ≠ .not)).card by simp [posFlag]]
    exact posCard n C l c
  have hpoint : ∀ v ∈ S, (cuts n C v.val).length + rawFlag v ≤ 1 + posFlag v := by
    intro v _
    by_cases hv : n+2 ≤ v.val
    · have hn : ¬v.val < n := by omega
      let i := v.val-(n+2)
      have hi : i < C.size := by have := v.isLt; dsimp [i]; omega
      have hfan := (fan (gateAt C i) (by rw [gateAtGet C i hi]; exact List.getElem_mem _)).2
      by_cases ht : (gateAt C i).op = .not
      · simp only [cuts, hv, ite_true, rawFlag, hn, ite_false, Nat.add_zero,
          posFlag, true_and, ← show i = v.val-(n+2) by rfl, ht, not_true_eq_false, Nat.add_zero,
          effective, List.length_take]
        omega
      · simpa [cuts, hv, rawFlag, hn, posFlag, ← show i = v.val-(n+2) by rfl, effective, ht] using hfan
    · by_cases hr : v.val < n <;> simp [cuts, posFlag, rawFlag, hv, hr]
  have hh := Finset.sum_le_sum hpoint
  have hOne : (∑ _ ∈ S, (1 : ℕ)) = S.card := (Finset.card_eq_sum_ones S).symm
  simp only [Finset.sum_add_distrib, hOne, hR, hP] at hh
  change need w r c ≤ (posSet C (gateFiber n C l c)).card + 1
  omega
private def localInputIndex (n s w u : ℕ) : ℕ :=
  if s ≤ u ∧ u < s+w then u-s else if u = n+1 then w+1 else w

private theorem localInputIndexBound (n s w u : ℕ) : localInputIndex n s w u < w+2 := by
  unfold localInputIndex
  split
  · omega
  · split <;> omega

private theorem singleBlockInputs {d : ℕ} (w : Fin d → ℕ) {α : Type*}
    (l : ℕ → α) (r : Fin d → α) (j : Fin d) (hs : (blocks r (r j)).card = 1)
    (link : ∀ a (i : Fin (w a)), l (startAt w a+i.val) = r a)
    (u : ℕ) (hu : u < total w) (hc : l u = r j) : startAt w j ≤ u ∧ u < startAt w j+w j := by
  obtain ⟨⟨a, i⟩, e⟩ := switchSurj w ⟨u,hu⟩
  have he : startAt w a+i.val = u := congrArg Fin.val e
  have ha : r a = r j := by rw [← link a i, he]; exact hc
  have heq := Finset.card_le_one.mp (Nat.le_of_eq hs) a (memBlocks.mpr ha) j (memBlocks.mpr rfl)
  subst a
  have := i.isLt
  omega

private theorem localInputAgreement (n s w : ℕ) (hs : s+w ≤ n) (t u : ℕ) (hu : u < n+2)
    (hinterval : u < n → s ≤ u ∧ u < s+w) :
    (thresholdRaw n (s+t)).getD u false =
      (thresholdRaw w t).getD (localInputIndex n s w u) false := by
  by_cases hvar : u < n
  · obtain ⟨hlo,hhi⟩ := hinterval hvar
    have hn : u-s < w := by omega
    rw [localInputIndex, ite_eq_left (And.intro hlo hhi), rawSwitch _ _ _ hvar, rawSwitch _ _ _ hn]
    have he : (u < s+t) = (u-s < t) := propext (by omega)
    simp only [he]
  · have he : u = n ∨ u = n+1 := by omega
    rcases he with he | he
    · subst u
      have hm : localInputIndex n s w n = w := by
        unfold localInputIndex
        rw [ite_eq_right (by omega : ¬ (s ≤ n ∧ n < s+w)),
          ite_eq_right (by omega : ¬ n = n+1)]
      rw [hm, rawFalse, rawFalse]
    · subst u
      have hm : localInputIndex n s w (n+1) = w+1 := by
        unfold localInputIndex
        rw [ite_eq_right (by omega : ¬ (s ≤ n+1 ∧ n+1 < s+w)), ite_eq_left rfl]
      rw [hm, rawTrue, rawTrue]

private theorem copyBlock {d q : ℕ} (w : Fin d → ℕ) (C : Circuit)
    (fan : FanInTwo C) (back : ReadsBack (total w+2) C)
    {α : Type*} (l : ℕ → α) (r : Fin d → α)
    (edge : ∀ v < total w+2+C.size, ∀ u ∈ cuts (total w) C v, l u = l v)
    (link : ∀ j (i : Fin (w j)), l (startAt w j+i.val) = r j)
    (j : Fin d) (tap : Fin (q+1) → ℕ) (out : Fin (q+1) → Fin (w j+1) → Bool)
    (htap : ∀ k, tap k < total w+2+C.size)
    (hout : ∀ k t, (C.wires (thresholdRaw (total w) (startAt w j+t.val))).getD (tap k) false = out k t)
    (hg : goodClass w r (fun c => (posSet C (gateFiber (total w) C l c)).card) (r j)) :
    ∃ (D : Circuit) (T : Fin (q+1) → ℕ),
      FanInTwo D ∧ ReadsBack (w j+2) D ∧ D.output < w j+2+D.size ∧
      (∀ k, T k < w j+2+D.size) ∧ D.size-PEqualNP.NotBracket.notCount D = w j-1 ∧
      PEqualNP.NotBracket.notCount D ≤ (negSet C (gateFiber (total w) C l (r j))).card ∧
      ∀ k t, (D.wires (thresholdRaw (w j) t.val)).getD (T k) false = out k t := by
  classical
  let n := total w
  let s := startAt w j
  let S := gateFiber n C l (r j)
  let F := localInputIndex n s (w j)
  have hS (i : ℕ) (hi : i ∈ S) : i < C.size := (memGateFiber.mp hi).1
  have hcomp (i : ℕ) (hi : i ∈ S) : l (n+2+i) = r j := (memGateFiber.mp hi).2
  have hclosed (i : ℕ) (hi : i ∈ S) (u : ℕ) (hu : u ∈ effective (gateAt C i)) (hm : n+2 ≤ u) :
      u-(n+2) ∈ S := by
    have him := hS i hi
    have hlt : u < n+2+i := back i him u (effective_mem_inputs hu)
    have hh : u ∈ cuts n C (n+2+i) := by simpa [cuts] using hu
    have he := (edge (n+2+i) (by have := hS i hi; omega) u hh).trans (hcomp i hi)
    exact memGateFiber.mpr ⟨by omega, by rwa [show n+2+(u-(n+2)) = u by omega]⟩
  obtain ⟨D, ρ, hfan, hback, hDout, hp, hn, hρRaw, hρGate, hsim⟩ :=
    copyCircuit C (n+2) (w j+2) (by omega) S hS fan back hclosed F
      (fun u _ => localInputIndexBound n s (w j) u)
  have hagree (u : ℕ) (hu : u < n+2) (hc : l u = r j) (t : Fin (w j+1)) :
      (thresholdRaw n (s+t.val)).getD u false = (thresholdRaw (w j) t.val).getD (F u) false :=
    localInputAgreement n s (w j) (startBound w j) t.val u hu
      (fun hv => singleBlockInputs w l r j hg.1 link u hv hc)
  let T : Fin (q+1) → ℕ := fun k => if l (tap k) = r j then ρ (tap k)
    else if out k 0 then w j+1 else w j
  have hsingle : blocks r (r j) = {j} := by
    ext a
    simp only [Finset.mem_singleton]
    constructor
    · intro ha
      exact Finset.card_le_one.mp (Nat.le_of_eq hg.1) a ha j (memBlocks.mpr rfl)
    · rintro rfl
      exact memBlocks.mpr rfl
  have hp' : (posSet C S).card + 1 = w j := by
    have h := hg.2
    simpa [need, hsingle, S, n] using h
  change D.size-PEqualNP.NotBracket.notCount D = (posSet C S).card at hp
  change PEqualNP.NotBracket.notCount D = (negSet C S).card at hn
  refine ⟨D, T, hfan, hback, hDout, ?_, by omega, hn.le, ?_⟩
  · intro k
    by_cases hc : l (tap k) = r j
    · simp only [T, hc, ite_true]
      by_cases hraw : tap k < n+2
      · rw [hρRaw _ hraw]
        exact (localInputIndexBound n s (w j) (tap k)).trans_le (Nat.le_add_right _ _)
      · let i := tap k-(n+2)
        have he : n+2+i = tap k := by dsimp [i]; omega
        have hi : i < C.size := by have := htap k; dsimp [i]; omega
        have hmem : i ∈ S := memGateFiber.mpr ⟨hi, by rwa [he]⟩
        simpa only [he] using hρGate i hmem
    · simp only [T, hc, ite_false]
      split <;> omega
  · intro k t
    by_cases hc : l (tap k) = r j
    · simp only [T, hc, ite_true]
      rw [← hout k t]
      by_cases hraw : tap k < n+2
      · rw [hρRaw _ hraw, locInput C _ _ (by rw [rawLen]; exact hraw),
          locInput D _ _ (by rw [rawLen]; exact localInputIndexBound n s (w j) (tap k))]
        exact (hagree (tap k) hraw hc t).symm
      · let i := tap k-(n+2)
        have he : n+2+i = tap k := by dsimp [i]; omega
        have hi : i < C.size := by have := htap k; dsimp [i]; omega
        have hmem : i ∈ S := memGateFiber.mpr ⟨hi, by rwa [he]⟩
        have hr := hsim (thresholdRaw n (s+t.val)) (thresholdRaw (w j) t.val)
          (rawLen ..) (rawLen ..) (fun a ha u hu h => hagree u h
            ((edge (n+2+a) (Nat.add_lt_add_left (hS a ha) (n+2)) u
              (by change u ∈ cuts n C (n+2+a); simpa [cuts] using hu)).trans (hcomp a ha)) t)
          i hmem
        simpa only [he] using hr.symm
    · have hconst := offBlockConstant w C back l edge (r j) (link j) (htap k) hc t
      have h0 := hout k 0
      simp only [Fin.val_zero, Nat.add_zero] at h0
      rw [← hout k t, hconst, h0]
      simp only [T, hc, ite_false]
      cases hb : out k 0
      · simp only [hb, Bool.false_eq_true, ite_false]
        rw [locInput D _ _ (by rw [rawLen]; omega), rawFalse]
      · simp only [hb, ite_true]
        rw [locInput D _ _ (by rw [rawLen]; omega), rawTrue]
private theorem solve {d : ℕ} (width count : Fin d → ℕ)
    (W : ∀ j : Fin d, Fin (count j+1) → Fin (width j+1) → Bool)
    (halt : ∀ j (i : Fin (width j)), W j 0 i.castSucc ≠ W j 0 i.succ)
    (C : Circuit) (tap : ∀ j : Fin d, Fin (count j+1) → ℕ)
    (fan : FanInTwo C) (back : ReadsBack (total width+2) C)
    (htap : ∀ j k, tap j k < total width+2+C.size)
    (hout : ∀ j k (t : Fin (width j+1)),
      (C.wires (thresholdRaw (total width) (startAt width j+t.val))).getD (tap j k) false = W j k t) :
    total width ≤ (C.size-PEqualNP.NotBracket.notCount C)+d ∧
    ∃ (G : Finset (Fin d)) (budget : Fin d → ℕ),
      d-G.card ≤ 2*((C.size-PEqualNP.NotBracket.notCount C)+d-total width) ∧
      G.sum budget ≤ PEqualNP.NotBracket.notCount C ∧
      ∀ j ∈ G, ∃ (D : Circuit) (T : Fin (count j+1) → ℕ),
        FanInTwo D ∧ ReadsBack (width j+2) D ∧ D.output < width j+2+D.size ∧
        (∀ k, T k < width j+2+D.size) ∧ D.size-PEqualNP.NotBracket.notCount D = width j-1 ∧
        PEqualNP.NotBracket.notCount D ≤ budget j ∧
        ∀ k t, (D.wires (thresholdRaw (width j) t.val)).getD (T k) false = W j k t := by
  classical
  let n := total width
  let l := wireLabel n C back
  let r : Fin d → (wireGraph n C back).ConnectedComponent := fun j => l (tap j 0)
  let P : (wireGraph n C back).ConnectedComponent → ℕ := fun c => (posSet C (gateFiber n C l c)).card
  let Q : (wireGraph n C back).ConnectedComponent → ℕ := fun c => (negSet C (gateFiber n C l c)).card
  let K := Finset.univ.image r
  have link (j : Fin d) (i : Fin (width j)) : l (startAt width j+i.val) = r j := by
    apply switchLink width C back l (wireEdge n C back) i (htap j 0)
    have h0 := hout j 0 i.castSucc
    have h1 := hout j 0 i.succ
    simp only [Fin.val_castSucc, Fin.val_succ, ← Nat.add_assoc] at h0 h1
    rw [h0, h1]
    exact halt j i
  have hp : ∑ c ∈ K, P c ≤ C.size-PEqualNP.NotBracket.notCount C := by
    simp only [P, posFiber, ← allPos C]
    exact sumFiberCardLe _ _ _
  have hq : ∑ c ∈ K, Q c ≤ PEqualNP.NotBracket.notCount C := by
    simp only [Q, negFiber, ← allNeg C]
    exact sumFiberCardLe _ _ _
  have hb (c : (wireGraph n C back).ConnectedComponent) (_ : c ∈ K) : need width r c ≤ P c+1 :=
    componentWidth width C fan back r link c
  let G : Finset (Fin d) := Finset.univ.filter (fun j => goodClass width r P (r j))
  have h := budgets width r P Q hp hq hb
  change n ≤ _ ∧ d-G.card ≤ _ ∧ G.sum (fun j => Q (r j)) ≤ _ at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, G, (fun j => Q (r j)), h₂, h₃, ?_⟩
  intro j hj
  exact copyBlock width C fan back l r (wireEdge n C back) link j (tap j) (W j) (htap j) (hout j)
    (Finset.mem_filter.mp hj).2

end PEqualNP.Outside.L_lib_1379

theorem PEqualNP.Outside.L_lib_1379 :
∀ (d : Nat) (width count : Fin d → Nat)
    (W : ∀ j : Fin d, Fin (count j+1) → Fin (width j+1) → Bool),
  (∀ j, 0 < width j) → (∀ j (i : Fin (width j)), W j 0 i.castSucc ≠ W j 0 i.succ) →
  let groups : Finset (Fin d) := Finset.univ
  let n := groups.sum width
  let start := fun (j : Fin d) => (groups.filter (fun i => i.val < j.val)).sum width
  let raw := fun (k t : Nat) => List.ofFn (fun i : Fin k => decide (i.val < t)) ++ [false,true]
  let neg := PEqualNP.NotBracket.notCount
  let pos := fun C => PEqualNP.CircuitLowerBounds.Circuit.size C - neg C
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : ∀ j : Fin d, Fin (count j+1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
    (∀ j k, tap j k < n+2+C.size) →
    (∀ j k (t : Fin (width j+1)), (C.wires (raw n (start j+t.val))).getD (tap j k) false = W j k t) →
    n ≤ pos C + d ∧
    ∃ (G : Finset (Fin d)) (budget : Fin d → Nat),
      d-G.card ≤ 2*(pos C + d - n) ∧ G.sum budget ≤ neg C ∧
      ∀ j ∈ G, ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (T : Fin (count j+1) → Nat),
        PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (width j+2) D ∧
        D.output < width j+2+D.size ∧ (∀ k, T k < width j+2+D.size) ∧
        pos D = width j-1 ∧ neg D ≤ budget j ∧
        ∀ k t, (D.wires (raw (width j) t.val)).getD (T k) false = W j k t := by
  intro _ width count W _ halt
  exact PEqualNP.Outside.L_lib_1379.solve width count W halt
