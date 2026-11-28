import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_820

open PEqualNP.CircuitLowerBounds

def Dg (old : List ℕ) (G : ℕ → Gate) (i : ℕ) : Gate :=
  ⟨(G i).op, (G i).inputs.map old.idxOf⟩

theorem getD_lt {α : Type} (l : List α) (d : α) (j : ℕ) (h : j < l.length) :
    l.getD j d = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem fold_wires (old : List ℕ) (k s : ℕ) (hl : old.length = k + s) (G : ℕ → Gate)
    (v : ℕ → Bool)
    (hin : ∀ i < s, ∀ w ∈ (G i).inputs, w ∈ old ∧ old.idxOf w < k + i)
    (heq : ∀ i (h : i < s), v (old[k+i]'(by omega)) = (G i).op.eval ((G i).inputs.map v)) :
    ∀ m ≤ s, ((List.range m).map (Dg old G)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      ((old.map v).take k) = (old.map v).take (k+m) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [show k + (m+1) = (k+m)+1 by omega, List.take_add_one]
    have hlt : k + m < old.length := by omega
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.toList_some]
    congr 2
    rw [heq m (by omega)]
    simp only [Dg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    obtain ⟨hmem, hidx⟩ := hin m (by omega) w hw
    have hil : old.idxOf w < old.length := List.idxOf_lt_length_of_mem hmem
    simp only [Function.comp]
    rw [getD_lt _ _ _ (by simp; omega)]
    rw [List.getElem_take, List.getElem_map, List.getElem_idxOf hil]

end PEqualNP.Outside.L_lib_820

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_820 in
theorem PEqualNP.Outside.L_lib_820 : ∀ (N k s : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (J : Fin s ↪ Fin C.size)
    (port : Fin k ↪ Fin (N+C.size)) (o : Fin (N+C.size)),
  let old := List.ofFn (fun b : Fin k => (port b).val) ++
    List.ofFn (fun i : Fin s => N+(J i).val)
  StrictMono J → (∀ b i, (port b).val ≠ N+(J i).val) →
  (∀ i (w : Nat), w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (J i).val).inputs →
    w < N+(J i).val ∧ ((∃ b, (port b).val = w) ∨ ∃ j, j < i ∧ N+(J j).val = w)) →
  o.val ∈ old →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = s ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack k D ∧
    old.getD D.output (N+C.size) = o.val ∧
    (∀ i : Fin s,
      let d := PEqualNP.MetaComplexity.NestedCover.gateAt D i.val
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C (J i).val
      d.op = g.op ∧ d.inputs.map (fun w => old.getD w (N+C.size)) = g.inputs) ∧
    ∀ v : Nat → Bool,
      (∀ i : Fin s, let g := PEqualNP.MetaComplexity.NestedCover.gateAt C (J i).val
        v (N+(J i).val) = g.op.eval (g.inputs.map v)) →
      let z := List.ofFn (fun b : Fin k => v (port b).val)
      D.wires z = z ++ List.ofFn (fun i : Fin s => v (N+(J i).val)) ∧ D.eval z = v o.val := by
  intro N k s C J port o old hJ hdis hin ho
  have hlen : old.length = k + s := by simp [old]
  have hA : ∀ b (h : b < k), old[b]'(by omega) = (port ⟨b, h⟩).val := by
    intro b h
    simp only [old]
    rw [List.getElem_append_left (by simp; omega)]
    simp
  have hB : ∀ i (h : i < s), old[k+i]'(by omega) = N + (J ⟨i, h⟩).val := by
    intro i h
    simp only [old]
    rw [List.getElem_append_right (by simp)]
    simp
  have hnd : old.Nodup := by
    simp only [old]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_ofFn]
      intro a b hab
      exact port.injective (Fin.val_injective hab)
    · rw [List.nodup_ofFn]
      intro a b hab
      exact J.injective (Fin.val_injective (by simpa using hab))
    · intro a ha b hb
      simp only [List.mem_ofFn] at ha hb
      obtain ⟨b', rfl⟩ := ha
      obtain ⟨i', rfl⟩ := hb
      exact hdis b' i'
  let G : ℕ → Gate := fun i =>
    if h : i < s then PEqualNP.MetaComplexity.NestedCover.gateAt C (J ⟨i, h⟩).val
    else ⟨GateOp.or, []⟩
  have hG : ∀ i : Fin s, G i.val = PEqualNP.MetaComplexity.NestedCover.gateAt C (J i).val := by
    intro i
    simp [G, i.isLt]
  have hin2 : ∀ i < s, ∀ w ∈ (G i).inputs, w ∈ old ∧ old.idxOf w < k + i := by
    intro i hi w hw
    rw [hG ⟨i, hi⟩] at hw
    obtain ⟨_, hw2⟩ := hin ⟨i, hi⟩ w hw
    rcases hw2 with ⟨b, hb⟩ | ⟨j, hj, hjw⟩
    · have e := hA b.val b.isLt
      rw [hb] at e
      rw [← e]
      refine ⟨List.getElem_mem _, ?_⟩
      rw [hnd.idxOf_getElem]
      omega
    · have e := hB j.val j.isLt
      rw [hjw] at e
      rw [← e]
      refine ⟨List.getElem_mem _, ?_⟩
      rw [hnd.idxOf_getElem]
      have : j.val < i := hj
      omega
  let D : Circuit := ⟨(List.range s).map (Dg old G), old.idxOf o.val⟩
  have hgD : ∀ j < s, PEqualNP.MetaComplexity.NestedCover.gateAt D j = Dg old G j := by
    intro j hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
    rw [getD_lt _ _ _ (by simp; omega)]
    simp
  have hback : ∀ w ∈ old, old.getD (old.idxOf w) (N + C.size) = w := by
    intro w hw
    have hil : old.idxOf w < old.length := List.idxOf_lt_length_of_mem hw
    rw [getD_lt _ _ _ hil, List.getElem_idxOf hil]
  refine ⟨D, by simp [D, Circuit.size], ?_, hback _ ho, ?_, ?_⟩
  · intro j hj w hw
    have hj' : j < s := by simpa [D] using hj
    rw [hgD j hj'] at hw
    simp only [Dg, List.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact (hin2 j hj' u hu).2
  · intro i
    simp only []
    rw [hgD i.val i.isLt]
    simp only [Dg]
    rw [← hG i]
    refine ⟨rfl, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (G i.val).inputs]
    apply List.map_congr_left
    intro w hw
    exact hback w (hin2 i.val i.isLt w hw).1
  · intro v hv
    have heq : ∀ i (h : i < s), v (old[k+i]'(by omega)) = (G i).op.eval ((G i).inputs.map v) := by
      intro i h
      rw [hB i h, hG ⟨i, h⟩]
      exact hv ⟨i, h⟩
    have hz : (old.map v).take k = List.ofFn (fun b : Fin k => v (port b).val) := by
      simp only [old, List.map_append, List.map_ofFn]
      rw [List.take_left' (by simp)]
      rfl
    have hall : old.map v = List.ofFn (fun b : Fin k => v (port b).val) ++
        List.ofFn (fun i : Fin s => v (N + (J i).val)) := by
      simp only [old, List.map_append, List.map_ofFn]
      rfl
    have hw : D.wires (List.ofFn (fun b : Fin k => v (port b).val)) = old.map v := by
      have := fold_wires old k s hlen G v hin2 heq s le_rfl
      rw [hz, ← hlen, List.take_of_length_le (by simp)] at this
      simp only [Circuit.wires, D]
      exact this
    refine ⟨by rw [hw, hall], ?_⟩
    simp only [Circuit.eval]
    rw [hw]
    have hil : old.idxOf o.val < old.length := List.idxOf_lt_length_of_mem ho
    rw [getD_lt _ _ _ (by simpa using hil)]
    simp only [List.getElem_map]
    exact congrArg v (List.getElem_idxOf hil)
