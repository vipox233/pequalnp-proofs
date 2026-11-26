import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19454

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.Represents

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_prefix hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_prefix pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

theorem child (N : ℕ) (C : Circuit) {i w j : ℕ} (hj : j < C.gates.length)
    (read : w ∈ C.gates[j].inputs) (lo : N ≤ w) (hi : w < N+j)
    (inside : i = w-N ∨ InCone N C i (w-N)) : InCone N C i j := by
  let F (cs : List (List ℕ)) (g : Gate) := (g.inputs.filter (fun t => decide (N≤t ∧ t<N+cs.length))).flatMap
    (fun t => (t-N) :: cs.getD (t-N) [])
  obtain ⟨v,pre,len⟩ := foldl_snoc_split F C.gates [] j hj []
  simp only [List.length_nil,Nat.zero_add] at v len
  change i ∈ (C.gates.foldl (fun cs g => cs ++ [F cs g]) []).getD j []
  rw [v]
  apply List.mem_flatMap.mpr
  refine ⟨w,List.mem_filter.mpr ⟨read,decide_eq_true ⟨lo,by omega⟩⟩,?_⟩
  apply List.mem_cons.mpr
  rcases inside with eq | anc
  · exact Or.inl eq
  · right
    exact (getD_of_prefix pre (i := w-N) (by omega) []).symm ▸ anc

theorem follows (C : Circuit) (N u : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i ≠ u → x.getD i false = true → y.getD i false = true) (mono : Monotone2 C) :
    ∀ w, w ≠ u → (∀ i (hi : i < C.gates.length),
      (w = N+i ∨ (N ≤ w ∧ InCone N C i (w-N))) → u ∉ C.gates[i].inputs) →
      (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro wu silent
    by_cases input : w < N
    · have raw (z : List Bool) (h : w<z.length) : (C.wires z).getD w false = z.getD w false :=
        getD_of_prefix (foldl_snoc_prefix readGate C.gates z) h false
      rw [raw x (by omega), raw y (by omega)]
      exact hxy w wu
    by_cases past : N+C.gates.length ≤ w
    · have len : (C.wires x).length = N+C.gates.length := (foldl_snoc_length readGate C.gates x).trans (by rw [hx])
      have off : (C.wires x).getD w false = false := List.getD_eq_default _ _ (by omega)
      rw [off]
      simp
    obtain ⟨j,rfl⟩ : ∃ j, w=N+j := ⟨w-N,by omega⟩
    have hj : j<C.gates.length := by omega
    have vx := wireAt C x j hj
    have vy := wireAt C y j hj
    rw [hx] at vx
    rw [hy] at vy
    rw [vx,vy]
    let X (t : ℕ) := if t<N+j then (C.wires x).getD t false else false
    let Y (t : ℕ) := if t<N+j then (C.wires y).getD t false else false
    have move (t : ℕ) (read : t∈C.gates[j].inputs) : X t = true → Y t = true := by
      by_cases ht : t<N+j
      · simp only [X, Y, ht, ↓reduceIte]
        apply ih t ht
        · rintro rfl
          exact silent j hj (Or.inl rfl) read
        · intro i hi anc
          apply silent i hi
          right
          refine ⟨by omega,?_⟩
          rw [Nat.add_sub_cancel_left]
          rcases anc with rfl | ⟨lo,anc⟩
          · exact child N C hj read (by omega) ht (Or.inl (by omega))
          · exact child N C hj read lo ht (Or.inr anc)
      · simp [X,Y,ht]
    have op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := (mono _ (List.getElem_mem hj)).1
    change C.gates[j].op.eval (C.gates[j].inputs.map X) = true → C.gates[j].op.eval (C.gates[j].inputs.map Y) = true
    rcases op with h | h
    · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
      exact fun pos i hi => move i hi (pos i hi)
    · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      rintro ⟨i,hi,pos⟩
      exact ⟨i,hi,move i hi pos⟩

theorem otherRow {n m : ℕ} (u u' : Fin n) (v : Fin m) (i : ℕ) (ne : i ≠ u.val) :
    (oneEach u v).getD i false = true → (oneEach u' v).getD i false = true := by
  let left (p : Fin n) := List.ofFn fun j : Fin n => decide (j=p)
  let rightBits := List.ofFn fun j : Fin m => decide (j=v)
  have len (p : Fin n) : (left p).length=n := by simp [left]
  change (left u ++ rightBits).getD i false = true → (left u' ++ rightBits).getD i false = true
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i<n
  · have hi : i<(left u).length := by rw [len]; exact h
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    simp [left,Fin.ext_iff,ne]
  · have hu : (left u).length ≤ i := by rw [len]; omega
    have hu' : (left u').length ≤ i := by rw [len]; omega
    rw [List.getElem?_append_right hu, List.getElem?_append_right hu', len, len]
    exact id

end PEqualNP.Outside.L_meta_19454

open PEqualNP.Outside.L_meta_19454 PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19454 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin n), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ (u' : Fin n) (v : Fin m), A u v = true → A u' v = true) := by
  intro n m A C u mono rep quiet u' v pos
  rw [← rep u v] at pos
  rw [← rep u' v]
  apply follows C (n+m) u.val (oneEach u v) (oneEach u' v) (by simp [oneEach]) (by simp [oneEach])
    (otherRow u u' v) mono C.output quiet.1 _ pos
  intro i hi h
  simpa [List.getD_eq_getElem?_getD,hi] using quiet.2 i hi h
