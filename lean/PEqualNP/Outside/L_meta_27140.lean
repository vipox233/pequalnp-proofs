import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27140_aux

open PEqualNP.CircuitLowerBounds

def tgt (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def ga : Gate := ⟨GateOp.and, [0, 1]⟩
def gb : Gate := ⟨GateOp.and, [0, 5]⟩

def st (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rd (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

def bx (m : Nat) (j : Fin 9) : Bool := m.testBit j.val

def pf (x : Fin 9 → Bool) : List Bool := st (st (List.ofFn x) ga) gb

def wl : List Nat := [272, 96, 80, 132, 68, 66, 20, 12, 10]

def wa (i : Fin 9) : Fin 9 → Bool := bx (wl.getD i.val 0)

def wb (i : Fin 9) : Fin 9 → Bool := bx (wl.getD i.val 0 ^^^ 2 ^ i.val)

theorem wit_ok : ∀ i : Fin 9, tgt (wa i) ≠ tgt (wb i) ∧
    ∀ j : Fin 11, j.val ≠ i.val → (pf (wa i)).getD j.val false = (pf (wb i)).getD j.val false := by
  decide +kernel

theorem fold_agree (gs : List Gate) (i : Nat) (hi : i ∉ rd gs) :
    ∀ a b : List Bool, a.length = b.length → (∀ j, j ≠ i → a.getD j false = b.getD j false) →
      ∀ j, j ≠ i → (gs.foldl st a).getD j false = (gs.foldl st b).getD j false := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    have hn : i ∉ g.inputs ∧ i ∉ rd gs := by simpa [rd] using hi
    have hm : g.inputs.map (fun j => a.getD j false) = g.inputs.map (fun j => b.getD j false) :=
      List.map_congr_left (fun j hj => h j (fun he => hn.1 (he ▸ hj)))
    apply ih hn.2 (st a g) (st b g) (by simp [st, hl])
    intro j hj
    by_cases hk : j < a.length
    · rw [st, st, List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (hl ▸ hk)]
      exact h j hj
    · rw [st, st, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hk),
        List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hk), hm, hl]

theorem pf_len (x : Fin 9 → Bool) : (pf x).length = 11 := by simp [pf, st]

theorem in_suffix (C : Circuit) (gs : List Gate) (hg : C.gates = ga :: gb :: gs)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = tgt x)
    (ho : C.output + 1 = 9 + C.size) (i : Fin 9) : i.val ∈ rd gs := by
  by_contra hn
  have hw := wit_ok i
  have hag : ∀ j, j ≠ i.val → (pf (wa i)).getD j false = (pf (wb i)).getD j false := by
    intro j hj
    by_cases hj' : j < 11
    · exact hw.2 ⟨j, hj'⟩ hj
    · have h1 : (pf (wa i)).length ≤ j := by rw [pf_len]; omega
      have h2 : (pf (wb i)).length ≤ j := by rw [pf_len]; omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
  have hout : C.output ≠ i.val := by
    simp [Circuit.size, hg] at ho
    omega
  have hev (x : Fin 9 → Bool) : C.eval (List.ofFn x) = (gs.foldl st (pf x)).getD C.output false := by
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_cons]
    rfl
  have h := fold_agree gs i.val hn _ _ (by rw [pf_len, pf_len]) hag C.output hout
  rw [← hev, ← hev, he, he] at h
  exact hw.1 h

theorem rd_len (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (rd gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [rd]
  | cons g gs ih =>
    have h1 := h g (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    simp only [rd, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
    omega

theorem subset_len_le : ∀ {l1 l2 : List Nat}, l1.Nodup → (∀ x, x ∈ l1 → x ∈ l2) → l1.length ≤ l2.length := by
  intro l1
  induction l1 with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro l2 hnd hsub
    have hnd' := List.nodup_cons.mp hnd
    have ha : a ∈ l2 := hsub a (by simp)
    have h1 := ih hnd'.2 (l2 := l2.erase a) (fun x hx => by
      have hne : x ≠ a := fun h => hnd'.1 (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.mpr (hsub x (by simp [hx])))
    have hlen : (l2.erase a).length + 1 = l2.length := by
      rw [List.length_erase_of_mem ha]
      have : 0 < l2.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

theorem main (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = tgt x)
    (ho : C.output + 1 = 9 + C.size)
    (hu : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some ga) (h1 : C.gates.tail.head? = some gb) : 12 ≤ C.size := by
  obtain ⟨gl, out⟩ := C
  match gl, h0, h1 with
  | a :: b :: gs, h0, h1 =>
    have ha : a = ga := Option.some.inj h0
    have hb : b = gb := Option.some.inj h1
    subst ha hb
    have hg : (Circuit.mk (ga :: gb :: gs) out).gates = ga :: gb :: gs := rfl
    have hsub : ∀ z, z ∈ List.range (10 + gs.length) → z ∈ rd gs := by
      intro z hz
      have hz' := List.mem_range.mp hz
      by_cases h9 : z < 9
      · exact in_suffix _ gs hg he ho ⟨z, h9⟩
      · obtain ⟨k, _, hk⟩ := hu ⟨z - 9, by simp; omega⟩ (by simp; omega)
        have hz9 : 9 + (z - 9) = z := by omega
        simp only [hz9] at hk
        have hm : (ga :: gb :: gs).get k ∈ ga :: gb :: gs := List.get_mem _ _
        rcases List.mem_cons.mp hm with e | hm
        · rw [e] at hk; simp [ga] at hk <;> omega
        rcases List.mem_cons.mp hm with e | hm
        · rw [e] at hk; simp [gb] at hk <;> omega
        exact List.mem_flatMap.mpr ⟨_, hm, hk⟩
    have hc := subset_len_le List.nodup_range hsub
    rw [List.length_range] at hc
    have hl := rd_len gs (fun g hg => (hfan g (by simp [hg])).2)
    simp only [Circuit.size, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_27140_aux

theorem PEqualNP.Outside.L_meta_27140 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩) := by
  rintro ⟨C, hfan, hsize, hf, hout, -, -, hused, h0, h1⟩
  have := PEqualNP.Outside.L_meta_27140_aux.main C hfan hf hout hused h0 h1
  omega
