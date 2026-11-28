import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33663_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-! ### Section 1: `ZMod 2` Helpers, 2-Bit Colors, and Disjoint Error Counting -/

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma b2z_injective : Function.Injective b2z := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private lemma b2z_not (b : Bool) : b2z (!b) = 1 + b2z b := by cases b <;> decide
private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by cases a <;> cases b <;> decide
private lemma b2z_or (a b : Bool) : b2z (a || b) = b2z a + b2z b + b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide
private lemma z2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

private def det2 (p q : ZMod 2 × ZMod 2) : ZMod 2 :=
  p.1 * q.2 + p.2 * q.1

private lemma det2_self (p : ZMod 2 × ZMod 2) : det2 p p = 0 := by
  rcases p with ⟨a, b⟩
  unfold det2
  fin_cases a <;> fin_cases b <;> decide

private lemma det2_comm (p q : ZMod 2 × ZMod 2) : det2 p q = det2 q p := by
  unfold det2; ring

private lemma det2_zero_left (p : ZMod 2 × ZMod 2) : det2 (0, 0) p = 0 := by
  simp [det2]

private lemma det2_zero_right (p : ZMod 2 × ZMod 2) : det2 p (0, 0) = 0 := by
  simp [det2]

private lemma det2_eq_one_of_ne {p q : ZMod 2 × ZMod 2}
    (hp : p ≠ (0, 0)) (hq : q ≠ (0, 0)) (hne : p ≠ q) : det2 p q = 1 := by
  rcases p with ⟨a1, a2⟩
  rcases q with ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    first | decide | (exfalso; apply hp; decide) | (exfalso; apply hq; decide) | (exfalso; apply hne; decide)

private def colorVec : Fin 3 → ZMod 2 × ZMod 2
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (1, 1)

private def otherColor : Fin 3 → ZMod 2 × ZMod 2
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (1, 1)
  | ⟨2, _⟩ => (1, 0)

private def pairToFin3 (p : ZMod 2 × ZMod 2) : Fin 3 :=
  if p = (1, 0) then ⟨0, by decide⟩
  else if p = (0, 1) then ⟨1, by decide⟩
  else ⟨2, by decide⟩

private lemma colorVec_pairToFin3 {p : ZMod 2 × ZMod 2} (hp : p ≠ (0, 0)) :
    colorVec (pairToFin3 p) = p := by
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact absurd rfl hp
  · decide
  · decide
  · decide

private lemma det2_colorVec_otherColor (c : Fin 3) : det2 (colorVec c) (otherColor c) = 1 := by
  fin_cases c <;> decide

private lemma det2_colorVec_eq_decide (a b : Fin 3) :
    det2 (colorVec a) (colorVec b) = if a = b then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> decide

private lemma four_sum_err_pos {α : Type*} [DecidableEq α]
    (s : Finset α) (f l : α → Bool)
    (hpar : (∑ t ∈ s, b2z (f t)) ≠ (∑ t ∈ s, b2z (l t))) :
    1 ≤ (s.filter (fun t => f t ≠ l t)).card := by
  refine Finset.card_pos.mpr ?_
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hpar
  refine Finset.sum_congr rfl fun t ht => ?_
  have hnot : t ∉ s.filter (fun t => f t ≠ l t) := by rw [h]; exact Finset.notMem_empty t
  have heq : f t = l t := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨ht, hne⟩)
  rw [heq]

private lemma finset_card_disjoint_union_ge {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (B : ι → Finset α) (E : Finset α)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) :
    ∑ i ∈ I, (E ∩ B i).card ≤ E.card := by
  have hsub : I.biUnion (fun i => E ∩ B i) ⊆ E := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxi).1
  calc ∑ i ∈ I, (E ∩ B i).card
      = (I.biUnion (fun i => E ∩ B i)).card := by
        symm
        refine Finset.card_biUnion fun i hi j hj hij => ?_
        exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj i hi j hj hij)
    _ ≤ E.card := Finset.card_le_card hsub

private lemma exists_adj_ne {α : Type*} {s : ℕ} (f : Fin (s + 1) → α)
    {a b : Fin (s + 1)} (hab : f a ≠ f b) :
    ∃ r : Fin s, f r.castSucc ≠ f r.succ := by
  have hconst : (∀ r : Fin s, f r.castSucc = f r.succ) → ∀ i : Fin (s + 1), f i = f 0 := by
    intro hall i
    rcases i with ⟨v, hv⟩
    induction v with
    | zero => rfl
    | succ v ih =>
      have hv' : v < s := by omega
      have h1 : f ⟨v, by omega⟩ = f ⟨v + 1, hv⟩ := hall ⟨v, hv'⟩
      rw [← h1, ih (by omega)]
  by_contra h
  push Not at h
  apply hab
  rw [hconst h a, hconst h b]

/-! ### Section 2: Circuit Algebra (`fits n 0`, `fits n 1`) and Circuit Builders -/

private noncomputable def isNL (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

private def fitsAux (n b : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧
  (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) ∧
  C.gates.countP isNL ≤ b

private lemma gate_eval_mod2_len0 : b2z (GateOp.eval (.mod 2) []) = 1 := rfl
private lemma gate_eval_mod2_len1 (a : Bool) : b2z (GateOp.eval (.mod 2) [a]) = 1 + b2z a := by
  cases a <;> decide
private lemma gate_eval_mod2_len2 (a b : Bool) :
    b2z (GateOp.eval (.mod 2) [a, b]) = 1 + b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma wires_append_gate (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp [Circuit.wires]

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  generalize C.gates = gs
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp; omega

private lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_of_ge {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_ofFn_fin {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    b2z ((List.ofFn x).getD i false) =
      if h : i < n then b2z (x ⟨i, h⟩) else 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [getD_of_ge _ _ _ (by simp; omega)]; rfl

private lemma wires_input_eq {n : ℕ} (gs : List Gate) (q : Fin n) (x : Fin n → Bool) :
    ((Circuit.mk gs 0).wires (List.ofFn x)).getD q.1 false = x q := by
  induction gs using List.reverseRecOn with
  | nil =>
    simp [Circuit.wires, List.getD_eq_getElem?_getD, q.2]
  | append_singleton gs g ih =>
    rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; omega)]
    exact ih

private lemma wires_zero_affine {n : ℕ} (gs : List Gate)
    (hallow : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
    (hnl : gs.countP isNL = 0) :
    ∀ i : ℕ, ∃ (c : ZMod 2) (u : Fin n → ZMod 2), ∀ x : Fin n → Bool,
      b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
        c + ∑ q : Fin n, u q * b2z (x q) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases hi : i < n
    · refine ⟨0, fun q => if q.1 = i then 1 else 0, fun x => ?_⟩
      simp only [Circuit.wires, List.foldl_nil, getD_ofFn_fin, hi, ↓reduceDIte, zero_add]
      rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro q _ hq
        have hne : q.1 ≠ i := fun h => hq (Fin.ext h)
        simp [hne]
      · intro hnm; exact absurd (Finset.mem_univ _) hnm
    · refine ⟨0, fun _ => 0, fun x => ?_⟩
      simp only [Circuit.wires, List.foldl_nil, getD_ofFn_fin, hi, ↓reduceDIte, zero_mul,
        Finset.sum_const_zero, add_zero]
  | append_singleton gs g ih =>
    have hallow_gs : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)) :=
      fun h hh => hallow h (List.mem_append_left _ hh)
    have hallow_g := hallow g (List.mem_append_right _ (List.mem_singleton_self g))
    have hcount_split : (gs ++ [g]).countP isNL = gs.countP isNL + (if isNL g then 1 else 0) := by
      simp only [List.countP_append, List.countP_cons, List.countP_nil]
      split_ifs <;> omega
    have hnl_gs : gs.countP isNL = 0 := by split_ifs at hcount_split <;> omega
    have hnl_g : isNL g = false := by
      cases h : isNL g
      · rfl
      · rw [h] at hcount_split; simp only [↓reduceIte] at hcount_split; omega
    have ih' := ih hallow_gs hnl_gs
    have hg_aff : ∃ (c : ZMod 2) (u : Fin n → ZMod 2), ∀ x : Fin n → Bool,
        b2z (g.op.eval (g.inputs.map fun idx => ((Circuit.mk gs 0).wires (List.ofFn x)).getD idx false)) =
          c + ∑ q : Fin n, u q * b2z (x q) := by
      rcases hallow_g with ⟨hlen, hop⟩
      cases h_in : g.inputs with
      | nil =>
        rcases hop with hop | hop | hop | ⟨_, h1⟩
        · refine ⟨1, fun _ => 0, fun _ => by simp [hop, GateOp.eval, b2z]⟩
        · refine ⟨0, fun _ => 0, fun _ => by simp [hop, GateOp.eval, b2z]⟩
        · refine ⟨1, fun _ => 0, fun _ => by simp [hop, gate_eval_mod2_len0]⟩
        · rw [h_in] at h1; simp at h1
      | cons i1 rest =>
        cases rest with
        | nil =>
          obtain ⟨c1, u1, hu1⟩ := ih' i1
          rcases hop with hop | hop | hop | ⟨hop, _⟩
          · refine ⟨c1, u1, fun x => by rw [← hu1 x]; simp [hop, GateOp.eval]⟩
          · refine ⟨c1, u1, fun x => by rw [← hu1 x]; simp [hop, GateOp.eval]⟩
          · refine ⟨1 + c1, u1, fun x => by simp only [hop, List.map_cons, List.map_nil, gate_eval_mod2_len1, hu1 x]; ring⟩
          · refine ⟨1 + c1, u1, fun x => by simp only [hop, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not, hu1 x]; ring⟩
        | cons i2 rest2 =>
          cases rest2 with
          | nil =>
            obtain ⟨c1, u1, hu1⟩ := ih' i1
            obtain ⟨c2, u2, hu2⟩ := ih' i2
            rcases hop with hop | hop | hop | ⟨_, h1⟩
            · exfalso
              have ht : isNL g = true := by
                simp only [isNL, decide_eq_true_eq]
                exact ⟨Or.inl hop, by simp [h_in]⟩
              rw [hnl_g] at ht; exact Bool.false_ne_true ht
            · exfalso
              have ht : isNL g = true := by
                simp only [isNL, decide_eq_true_eq]
                exact ⟨Or.inr hop, by simp [h_in]⟩
              rw [hnl_g] at ht; exact Bool.false_ne_true ht
            · refine ⟨1 + c1 + c2, fun q => u1 q + u2 q, fun x => ?_⟩
              simp only [hop, List.map_cons, List.map_nil, gate_eval_mod2_len2, hu1 x, hu2 x, Finset.sum_add_distrib, add_mul]
              ring
            · rw [h_in] at h1; simp at h1
          | cons _ _ =>
            rw [h_in] at hlen; simp at hlen
    intro i
    by_cases hlt : i < n + gs.length
    · obtain ⟨c, u, hu⟩ := ih' i
      refine ⟨c, u, fun x => ?_⟩
      rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; exact hlt)]
      exact hu x
    · by_cases heq : i = n + gs.length
      · subst heq
        obtain ⟨c, u, hu⟩ := hg_aff
        refine ⟨c, u, fun x => ?_⟩
        rw [wires_append_gate]
        have hlen_w : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
          rw [wires_length]; simp
        rw [← hlen_w, getD_append_last]
        exact hu x
      · refine ⟨0, fun _ => 0, fun x => ?_⟩
        rw [getD_of_ge _ _ _ (by rw [wires_length]; simp; omega)]
        simp [b2z]

private lemma fits_zero_affine {n : ℕ} {C : Circuit} (hC : fitsAux n 0 C) :
    ∃ (c : ZMod 2) (u : Fin n → ZMod 2), ∀ x : Fin n → Bool,
      b2z (C.eval (List.ofFn x)) = c + ∑ q : Fin n, u q * b2z (x q) := by
  have hnl : C.gates.countP isNL = 0 := Nat.eq_zero_of_le_zero hC.2.2
  obtain ⟨c, u, hu⟩ := wires_zero_affine (n := n) C.gates hC.2.1 hnl C.output
  exact ⟨c, u, hu⟩

private lemma wires_one_quad {n : ℕ} (gs : List Gate)
    (hallow : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
    (hnl : gs.countP isNL ≤ 1) :
    ∃ (a0 b0 : ZMod 2) (v w : Fin n → ZMod 2),
      ∀ i : ℕ, ∃ (c lam : ZMod 2) (u : Fin n → ZMod 2), ∀ x : Fin n → Bool,
        b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          c + ∑ q : Fin n, u q * b2z (x q) +
            lam * ((a0 + ∑ q : Fin n, v q * b2z (x q)) * (b0 + ∑ q : Fin n, w q * b2z (x q))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, 0, fun _ => 0, fun _ => 0, fun i => ?_⟩
    obtain ⟨c, u, hu⟩ := wires_zero_affine (n := n) [] (by simp) (by simp) i
    exact ⟨c, 0, u, fun x => by simpa using hu x⟩
  | append_singleton gs g ih =>
    have hallow_gs : ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)) :=
      fun h hh => hallow h (List.mem_append_left _ hh)
    have hallow_g := hallow g (List.mem_append_right _ (List.mem_singleton_self g))
    have hcount_split : (gs ++ [g]).countP isNL = gs.countP isNL + (if isNL g then 1 else 0) := by
      simp only [List.countP_append, List.countP_cons, List.countP_nil]
      split_ifs <;> omega
    by_cases hgnl : isNL g = true
    · have hnl_gs : gs.countP isNL = 0 := by
        rw [hgnl] at hcount_split; simp only [↓reduceIte] at hcount_split; omega
      have hgs_aff := wires_zero_affine (n := n) gs hallow_gs hnl_gs
      have hgnl_prop : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
        simpa [isNL] using hgnl
      rcases hgnl_prop with ⟨hop, hlen2⟩
      cases h_in : g.inputs with
      | nil => rw [h_in] at hlen2; simp at hlen2
      | cons i1 rest =>
        cases rest with
        | nil => rw [h_in] at hlen2; simp at hlen2
        | cons i2 rest2 =>
          cases rest2 with
          | cons _ _ => rw [h_in] at hlen2; simp at hlen2
          | nil =>
            obtain ⟨a0, v, hv⟩ := hgs_aff i1
            obtain ⟨b0, w, hw⟩ := hgs_aff i2
            refine ⟨a0, b0, v, w, fun i => ?_⟩
            by_cases hlt : i < n + gs.length
            · obtain ⟨c, u, hu⟩ := hgs_aff i
              refine ⟨c, 0, u, fun x => ?_⟩
              rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; exact hlt)]
              simpa using hu x
            · by_cases heq : i = n + gs.length
              · subst heq
                rcases hop with hop | hop
                · refine ⟨0, 1, fun _ => 0, fun x => ?_⟩
                  rw [wires_append_gate]
                  have hlen_w : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
                    rw [wires_length]; simp
                  rw [← hlen_w, getD_append_last]
                  simp only [hop, h_in, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, b2z_and, hv x, hw x, zero_mul,
                    Finset.sum_const_zero, zero_add, one_mul]
                · refine ⟨a0 + b0, 1, fun q => v q + w q, fun x => ?_⟩
                  rw [wires_append_gate]
                  have hlen_w : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
                    rw [wires_length]; simp
                  rw [← hlen_w, getD_append_last]
                  simp only [hop, h_in, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
                    List.any_nil, id_eq, Bool.or_false, b2z_or, hv x, hw x, Finset.sum_add_distrib, add_mul, one_mul]
                  ring
              · refine ⟨0, 0, fun _ => 0, fun x => ?_⟩
                rw [getD_of_ge _ _ _ (by rw [wires_length]; simp; omega)]
                simp [b2z]
    · have hgnl_f : isNL g = false := Bool.eq_false_iff.mpr hgnl
      have hnl_gs : gs.countP isNL ≤ 1 := by
        rw [hgnl_f] at hcount_split; simp only [Bool.false_eq_true, ↓reduceIte] at hcount_split; omega
      obtain ⟨a0, b0, v, w, ih'⟩ := ih hallow_gs hnl_gs
      refine ⟨a0, b0, v, w, ?_⟩
      have hg_quad : ∃ (c lam : ZMod 2) (u : Fin n → ZMod 2), ∀ x : Fin n → Bool,
          b2z (g.op.eval (g.inputs.map fun idx => ((Circuit.mk gs 0).wires (List.ofFn x)).getD idx false)) =
            c + ∑ q : Fin n, u q * b2z (x q) +
              lam * ((a0 + ∑ q : Fin n, v q * b2z (x q)) * (b0 + ∑ q : Fin n, w q * b2z (x q))) := by
        rcases hallow_g with ⟨hlen, hop⟩
        cases h_in : g.inputs with
        | nil =>
          rcases hop with hop | hop | hop | ⟨_, h1⟩
          · refine ⟨1, 0, fun _ => 0, fun _ => by simp [hop, GateOp.eval, b2z]⟩
          · refine ⟨0, 0, fun _ => 0, fun _ => by simp [hop, GateOp.eval, b2z]⟩
          · refine ⟨1, 0, fun _ => 0, fun _ => by simp [hop, gate_eval_mod2_len0]⟩
          · rw [h_in] at h1; simp at h1
        | cons i1 rest =>
          cases rest with
          | nil =>
            obtain ⟨c1, lam1, u1, hu1⟩ := ih' i1
            rcases hop with hop | hop | hop | ⟨hop, _⟩
            · refine ⟨c1, lam1, u1, fun x => by rw [← hu1 x]; simp [hop, GateOp.eval]⟩
            · refine ⟨c1, lam1, u1, fun x => by rw [← hu1 x]; simp [hop, GateOp.eval]⟩
            · refine ⟨1 + c1, lam1, u1, fun x => by simp only [hop, List.map_cons, List.map_nil, gate_eval_mod2_len1, hu1 x]; ring⟩
            · refine ⟨1 + c1, lam1, u1, fun x => by simp only [hop, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not, hu1 x]; ring⟩
          | cons i2 rest2 =>
            cases rest2 with
            | nil =>
              obtain ⟨c1, lam1, u1, hu1⟩ := ih' i1
              obtain ⟨c2, lam2, u2, hu2⟩ := ih' i2
              rcases hop with hop | hop | hop | ⟨_, h1⟩
              · exfalso
                have ht : isNL g = true := by
                  simp only [isNL, decide_eq_true_eq]
                  exact ⟨Or.inl hop, by simp [h_in]⟩
                exact hgnl ht
              · exfalso
                have ht : isNL g = true := by
                  simp only [isNL, decide_eq_true_eq]
                  exact ⟨Or.inr hop, by simp [h_in]⟩
                exact hgnl ht
              · refine ⟨1 + c1 + c2, lam1 + lam2, fun q => u1 q + u2 q, fun x => ?_⟩
                simp only [hop, List.map_cons, List.map_nil, gate_eval_mod2_len2, hu1 x, hu2 x, Finset.sum_add_distrib, add_mul]
                ring
              · rw [h_in] at h1; simp at h1
            | cons _ _ =>
              rw [h_in] at hlen; simp at hlen
      intro i
      by_cases hlt : i < n + gs.length
      · obtain ⟨c, lam, u, hu⟩ := ih' i
        refine ⟨c, lam, u, fun x => ?_⟩
        rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; exact hlt)]
        exact hu x
      · by_cases heq : i = n + gs.length
        · subst heq
          obtain ⟨c, lam, u, hu⟩ := hg_quad
          refine ⟨c, lam, u, fun x => ?_⟩
          rw [wires_append_gate]
          have hlen_w : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
            rw [wires_length]; simp
          rw [← hlen_w, getD_append_last]
          exact hu x
        · refine ⟨0, 0, fun _ => 0, fun x => ?_⟩
          rw [getD_of_ge _ _ _ (by rw [wires_length]; simp; omega)]
          simp [b2z]

private lemma fits_one_quad {n : ℕ} {C : Circuit} (hC : fitsAux n 1 C) :
    ∃ (c0 a0 b0 : ZMod 2) (u v w : Fin n → ZMod 2), ∀ x : Fin n → Bool,
      b2z (C.eval (List.ofFn x)) =
        c0 + ∑ q : Fin n, u q * b2z (x q) +
          (a0 + ∑ q : Fin n, v q * b2z (x q)) * (b0 + ∑ q : Fin n, w q * b2z (x q)) := by
  obtain ⟨a0, b0, v, w, hwires⟩ := wires_one_quad (n := n) C.gates hC.2.1 hC.2.2
  obtain ⟨c0, lam, u, hu⟩ := hwires C.output
  rcases z2_cases lam with rfl | rfl
  · refine ⟨c0, 0, 0, u, fun _ => 0, fun _ => 0, fun x => ?_⟩
    have hw : C.wires (List.ofFn x) = (Circuit.mk C.gates 0).wires (List.ofFn x) := rfl
    unfold Circuit.eval
    rw [hw, hu x]; simp
  · refine ⟨c0, a0, b0, u, v, w, fun x => ?_⟩
    have hw : C.wires (List.ofFn x) = (Circuit.mk C.gates 0).wires (List.ofFn x) := rfl
    unfold Circuit.eval
    rw [hw, hu x]; simp

private def constFalseCirc (n : ℕ) : Circuit :=
  ⟨[⟨.or, []⟩], n⟩

private lemma constFalseCirc_fits (n : ℕ) : fitsAux n 0 (constFalseCirc n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    simp only [constFalseCirc, List.length_singleton] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [gateAt, constFalseCirc] at hi
  · intro h hh
    simp only [constFalseCirc, List.mem_singleton] at hh
    subst hh
    exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  · simp [constFalseCirc, isNL]

private lemma constFalseCirc_eval {n : ℕ} (x : Fin n → Bool) :
    (constFalseCirc n).eval (List.ofFn x) = false := by
  unfold Circuit.eval Circuit.wires constFalseCirc
  simp [List.getD_eq_getElem?_getD, GateOp.eval]

private def validLinPrefix (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧
  (∀ h ∈ gs, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) ∧
  gs.countP isNL = 0

private lemma readsBack_append {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : ReadsBack n ⟨gs, 0⟩) (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n ⟨gs ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hgat : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
      unfold gateAt
      exact getD_append_left gs [g] j _ hlt
    rw [hgat] at hi
    exact hgs j hlt i hi
  · have heq : j = gs.length := by omega
    subst heq
    have hgat : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
      unfold gateAt
      exact getD_append_last gs g _
    rw [hgat] at hi
    exact hg i hi

private lemma build_xor_step {n : ℕ} (gs : List Gate) (w1 w2 : ℕ)
    (hvalid : validLinPrefix n gs) (hw1 : w1 < n + gs.length) (hw2 : w2 < n + gs.length) :
    ∃ (gs' : List Gate) (wout : ℕ),
      validLinPrefix n gs' ∧
      gs.length ≤ gs'.length ∧
      wout < n + gs'.length ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool,
        ((Circuit.mk gs' 0).wires (List.ofFn x)).getD i false =
          ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) ∧
      (∀ x : Fin n → Bool,
        b2z (((Circuit.mk gs' 0).wires (List.ofFn x)).getD wout false) =
          b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD w1 false) +
          b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD w2 false)) := by
  let g1 : Gate := ⟨.mod 2, [w1, w2]⟩
  let gs1 : List Gate := gs ++ [g1]
  let t : ℕ := n + gs.length
  let g2 : Gate := ⟨.not, [t]⟩
  let gs2 : List Gate := gs1 ++ [g2]
  refine ⟨gs2, n + gs1.length, ?_, by simp [gs2, gs1], by simp [gs2, gs1], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine readsBack_append (readsBack_append hvalid.1 ?_) ?_
      · intro i hi
        simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · intro i hi
        simp only [g2, List.mem_singleton] at hi
        subst hi
        simp [gs1, t]
    · intro h hh
      simp only [gs2, gs1, List.mem_append, List.mem_singleton] at hh
      rcases hh with (hh | rfl) | rfl
      · exact hvalid.2.1 h hh
      · exact ⟨by simp [g1], Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨by simp [g2], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · simp [gs2, gs1, List.countP_append, hvalid.2.2, g1, g2, isNL]
  · intro i hi x
    have h1 : ((Circuit.mk gs1 0).wires (List.ofFn x)).getD i false =
        ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false := by
      rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; exact hi)]
    have h2 : ((Circuit.mk gs2 0).wires (List.ofFn x)).getD i false =
        ((Circuit.mk gs1 0).wires (List.ofFn x)).getD i false := by
      rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp [gs1]; omega)]
    rw [h2, h1]
  · intro x
    have hlen1 : ((Circuit.mk gs 0).wires (List.ofFn x)).length = t := by
      rw [wires_length]; simp [t]
    have hlen2 : ((Circuit.mk gs1 0).wires (List.ofFn x)).length = n + gs1.length := by
      rw [wires_length]; simp
    have ht_val : b2z (((Circuit.mk gs1 0).wires (List.ofFn x)).getD t false) =
        1 + b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD w1 false) +
          b2z (((Circuit.mk gs 0).wires (List.ofFn x)).getD w2 false) := by
      rw [wires_append_gate, ← hlen1, getD_append_last]
      simp only [g1, List.map_cons, List.map_nil, gate_eval_mod2_len2]
    rw [wires_append_gate, ← hlen2, getD_append_last]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not, ht_val]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    linear_combination h11

private lemma build_linear {n : ℕ} (gs : List Gate) (u : Fin n → ZMod 2)
    (hvalid : validLinPrefix n gs) :
    ∃ (gs' : List Gate) (wout : ℕ),
      validLinPrefix n gs' ∧
      gs.length ≤ gs'.length ∧
      wout < n + gs'.length ∧
      (∀ i < n + gs.length, ∀ x : Fin n → Bool,
        ((Circuit.mk gs' 0).wires (List.ofFn x)).getD i false =
          ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) ∧
      (∀ x : Fin n → Bool,
        b2z (((Circuit.mk gs' 0).wires (List.ofFn x)).getD wout false) =
          ∑ q : Fin n, u q * b2z (x q)) := by
  let gs0 : List Gate := gs ++ [⟨.or, []⟩]
  have hvalid0 : validLinPrefix n gs0 := by
    refine ⟨readsBack_append hvalid.1 (by simp), ?_, ?_⟩
    · intro h hh
      simp only [gs0, List.mem_append, List.mem_singleton] at hh
      rcases hh with hh | rfl
      · exact hvalid.2.1 h hh
      · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
    · simp [gs0, List.countP_append, hvalid.2.2, isNL]
  have hstep_all : ∀ (s : Finset (Fin n)),
      ∃ (gs' : List Gate) (wout : ℕ),
        validLinPrefix n gs' ∧
        gs.length ≤ gs'.length ∧
        wout < n + gs'.length ∧
        (∀ i < n + gs.length, ∀ x : Fin n → Bool,
          ((Circuit.mk gs' 0).wires (List.ofFn x)).getD i false =
            ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) ∧
        (∀ x : Fin n → Bool,
          b2z (((Circuit.mk gs' 0).wires (List.ofFn x)).getD wout false) =
            ∑ q ∈ s, u q * b2z (x q)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨gs0, n + gs.length, hvalid0, by simp [gs0], by simp [gs0], ?_, ?_⟩
      · intro i hi x
        rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; exact hi)]
      · intro x
        have hlen : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
          rw [wires_length]; simp
        rw [wires_append_gate, ← hlen, getD_append_last]
        simp [GateOp.eval, b2z]
    | insert q0 s hq0 ih =>
      obtain ⟨gs1, w1, hval1, hlen1, hw1, hpres1, heval1⟩ := ih
      rcases z2_cases (u q0) with hu0 | hu1
      · refine ⟨gs1, w1, hval1, hlen1, hw1, hpres1, fun x => ?_⟩
        rw [heval1 x, Finset.sum_insert hq0, hu0, zero_mul, zero_add]
      · obtain ⟨gs2, w2, hval2, hlen2, hw2, hpres2, heval2⟩ :=
          build_xor_step gs1 w1 q0.1 hval1 hw1 (by omega)
        refine ⟨gs2, w2, hval2, le_trans hlen1 hlen2, hw2, ?_, ?_⟩
        · intro i hi x
          rw [hpres2 i (by omega) x, hpres1 i hi x]
        · intro x
          rw [heval2 x, heval1 x, wires_input_eq gs1 q0 x, Finset.sum_insert hq0, hu1, one_mul, add_comm]
  exact hstep_all Finset.univ

private lemma build_quad_circuit {n : ℕ} (u v w : Fin n → ZMod 2) :
    ∃ C : Circuit, fitsAux n 1 C ∧ ∀ x : Fin n → Bool,
      b2z (C.eval (List.ofFn x)) =
        (∑ q : Fin n, u q * b2z (x q)) +
          (∑ q : Fin n, v q * b2z (x q)) * (∑ q : Fin n, w q * b2z (x q)) := by
  have hval0 : validLinPrefix n [] := ⟨by intro j hj; simp at hj, by simp, by simp⟩
  obtain ⟨gs1, wu, hval1, _, hwu, _, hevu⟩ := build_linear [] u hval0
  obtain ⟨gs2, wv, hval2, hlen12, hwv, hpres12, hevv⟩ := build_linear gs1 v hval1
  obtain ⟨gs3, ww, hval3, hlen23, hww, hpres23, hevw⟩ := build_linear gs2 w hval2
  let gand : Gate := ⟨.and, [wv, ww]⟩
  let gs4 : List Gate := gs3 ++ [gand]
  let wp : ℕ := n + gs3.length
  let gmod : Gate := ⟨.mod 2, [wu, wp]⟩
  let gs5 : List Gate := gs4 ++ [gmod]
  let wt : ℕ := n + gs4.length
  let gnot : Gate := ⟨.not, [wt]⟩
  let gs6 : List Gate := gs5 ++ [gnot]
  let wout : ℕ := n + gs5.length
  refine ⟨⟨gs6, wout⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine readsBack_append (readsBack_append (readsBack_append hval3.1 ?_) ?_) ?_
      · intro i hi
        simp only [gand, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro i hi
        simp only [gmod, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · simp [gs4]; omega
        · simp [gs4, wp]
      · intro i hi
        simp only [gnot, List.mem_singleton] at hi
        subst hi
        simp [gs5, wt]
    · intro h hh
      simp only [gs6, gs5, gs4, List.mem_append, List.mem_singleton] at hh
      rcases hh with ((hh | rfl) | rfl) | rfl
      · exact hval3.2.1 h hh
      · exact ⟨by simp [gand], Or.inl rfl⟩
      · exact ⟨by simp [gmod], Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨by simp [gnot], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · simp [gs6, gs5, gs4, List.countP_append, hval3.2.2, gand, gmod, gnot, isNL]
  · intro x
    have hwu_val : b2z (((Circuit.mk gs4 0).wires (List.ofFn x)).getD wu false) =
        ∑ q : Fin n, u q * b2z (x q) := by
      rw [wires_append_gate, getD_append_left _ _ _ _ (by rw [wires_length]; simp; omega)]
      rw [hpres23 wu (by omega) x, hpres12 wu hwu x, hevu x]
    have hwp_val : b2z (((Circuit.mk gs4 0).wires (List.ofFn x)).getD wp false) =
        (∑ q : Fin n, v q * b2z (x q)) * (∑ q : Fin n, w q * b2z (x q)) := by
      have hlen3 : ((Circuit.mk gs3 0).wires (List.ofFn x)).length = wp := by
        rw [wires_length]; simp [wp]
      rw [wires_append_gate, ← hlen3, getD_append_last]
      simp only [gand, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, b2z_and]
      rw [hpres23 wv hwv x, hevv x, hevw x]
    have hwt_val : b2z (((Circuit.mk gs5 0).wires (List.ofFn x)).getD wt false) =
        1 + (∑ q : Fin n, u q * b2z (x q)) +
          (∑ q : Fin n, v q * b2z (x q)) * (∑ q : Fin n, w q * b2z (x q)) := by
      have hlen4 : ((Circuit.mk gs4 0).wires (List.ofFn x)).length = wt := by
        rw [wires_length]; simp [wt]
      rw [wires_append_gate, ← hlen4, getD_append_last]
      simp only [gmod, List.map_cons, List.map_nil, gate_eval_mod2_len2, hwu_val, hwp_val]
    change b2z (((Circuit.mk gs6 0).wires (List.ofFn x)).getD wout false) = _
    have hlen5 : ((Circuit.mk gs5 0).wires (List.ofFn x)).length = wout := by
      rw [wires_length]; simp [wout]
    rw [wires_append_gate, ← hlen5, getD_append_last]
    simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not, hwt_val]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    linear_combination h11

/-! ### Section 3: Algebraic 4-Corner Identities for Quadratic Functions Over `ZMod 2` -/

private def quadEval {V : Type*} [DecidableEq V]
    (c0 a0 b0 : ZMod 2) (u v w : V → ZMod 2) (S : Finset V) : ZMod 2 :=
  c0 + (∑ q ∈ S, u q) + (a0 + ∑ q ∈ S, v q) * (b0 + ∑ q ∈ S, w q)

private lemma quad_four_anchor_alg (c0 a0 b0 ua ux uy va vx vy wa wx wy : ZMod 2) :
    (c0 + ua + (a0 + va) * (b0 + wa)) +
    (c0 + (ux + ua) + (a0 + (vx + va)) * (b0 + (wx + wa))) +
    (c0 + (uy + ua) + (a0 + (vy + va)) * (b0 + (wy + wa))) +
    (c0 + (ux + (uy + ua)) + (a0 + (vx + (vy + va))) * (b0 + (wx + (wy + wa)))) =
    vx * wy + wx * vy := by
  have h2 : (2 : ZMod 2) = 0 := z2_two_eq_zero
  linear_combination
    (2 * c0 + 2 * ua + ux + uy + 2 * a0 * b0 + 2 * a0 * wa + a0 * wx + a0 * wy +
      2 * b0 * va + b0 * vx + b0 * vy + 2 * va * wa + va * wx + va * wy +
      vx * wa + vx * wx + vy * wa + vy * wy) * h2

private lemma quad_four_triple_alg (c0 a0 b0 ux uy uz vx vy vz wx wy wz : ZMod 2) :
    (c0 + ux + (a0 + vx) * (b0 + wx)) +
    (c0 + uy + (a0 + vy) * (b0 + wy)) +
    (c0 + uz + (a0 + vz) * (b0 + wz)) +
    (c0 + (ux + (uy + uz)) + (a0 + (vx + (vy + vz))) * (b0 + (wx + (wy + wz)))) =
    (vx + vz) * (wy + wz) + (wx + wz) * (vy + vz) := by
  have h2 : (2 : ZMod 2) = 0 := z2_two_eq_zero
  linear_combination
    (2 * c0 + ux + uy + uz + 2 * a0 * b0 + a0 * wx + a0 * wy + a0 * wz +
      b0 * vx + b0 * vy + b0 * vz + vx * wx + vy * wy) * h2

private lemma quadEval_anchor_four {V : Type*} [DecidableEq V]
    (c0 a0 b0 : ZMod 2) (u v w : V → ZMod 2) {anc x y : V}
    (hax : x ≠ anc) (hay : y ≠ anc) (hxy : x ≠ y) :
    quadEval c0 a0 b0 u v w {anc} +
    quadEval c0 a0 b0 u v w {x, anc} +
    quadEval c0 a0 b0 u v w {y, anc} +
    quadEval c0 a0 b0 u v w {x, y, anc} =
    det2 (v x, w x) (v y, w y) := by
  have hx_not_ya : x ∉ ({y, anc} : Finset V) := by simp [hxy, hax]
  simp only [quadEval, det2, Finset.sum_singleton, Finset.sum_insert (Finset.notMem_singleton.mpr hax),
    Finset.sum_insert (Finset.notMem_singleton.mpr hay), Finset.sum_insert hx_not_ya]
  exact quad_four_anchor_alg c0 a0 b0 (u anc) (u x) (u y) (v anc) (v x) (v y) (w anc) (w x) (w y)

private lemma quadEval_triple_four {V : Type*} [DecidableEq V]
    (c0 a0 b0 : ZMod 2) (u v w : V → ZMod 2) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    quadEval c0 a0 b0 u v w {x} +
    quadEval c0 a0 b0 u v w {y} +
    quadEval c0 a0 b0 u v w {z} +
    quadEval c0 a0 b0 u v w {x, y, z} =
    det2 (v x + v z, w x + w z) (v y + v z, w y + w z) := by
  have hx_not_yz : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  simp only [quadEval, det2, Finset.sum_singleton, Finset.sum_insert (Finset.notMem_singleton.mpr hyz),
    Finset.sum_insert hx_not_yz]
  exact quad_four_triple_alg c0 a0 b0 (u x) (u y) (u z) (v x) (v y) (v z) (w x) (w y) (w z)

private lemma quadEval_clean_one {V : Type*} [DecidableEq V]
    (v w : V → ZMod 2) (x : V) :
    quadEval 0 0 0 (fun q => v q * w q) v w {x} = 0 := by
  simp [quadEval, z2_add_self]

private lemma quadEval_clean_two {V : Type*} [DecidableEq V]
    (v w : V → ZMod 2) {x y : V} (hxy : x ≠ y) :
    quadEval 0 0 0 (fun q => v q * w q) v w {x, y} = det2 (v x, w x) (v y, w y) := by
  simp only [quadEval, Finset.sum_insert (Finset.notMem_singleton.mpr hxy), Finset.sum_singleton,
    zero_add, det2]
  have h2 : (2 : ZMod 2) = 0 := z2_two_eq_zero
  linear_combination (v x * w x + v y * w y) * h2

private lemma quadEval_clean_three {V : Type*} [DecidableEq V]
    (v w : V → ZMod 2) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    quadEval 0 0 0 (fun q => v q * w q) v w {x, y, z} =
    det2 (v x, w x) (v y, w y) + det2 (v x, w x) (v z, w z) + det2 (v y, w y) (v z, w z) := by
  have hx_not_yz : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  simp only [quadEval, Finset.sum_insert hx_not_yz, Finset.sum_insert (Finset.notMem_singleton.mpr hyz),
    Finset.sum_singleton, zero_add, det2]
  have h2 : (2 : ZMod 2) = 0 := z2_two_eq_zero
  linear_combination (v x * w x + v y * w y + v z * w z) * h2

/-! ### Section 4: The `k × k` Grid Gadget Construction (for `k = s + 1`) -/

private abbrev PairLt (s : ℕ) := {p : Fin (s + 1) × Fin (s + 1) // p.1 < p.2}

private inductive Var (s : ℕ)
  | grid (i r c : Fin (s + 1))
  | nzAux (i r c : Fin (s + 1))
  | nzAnc (i r c : Fin (s + 1))
  | hAnc (i r : Fin (s + 1)) (c : Fin s)
  | vAnc (i : Fin (s + 1)) (r : Fin s) (c : Fin (s + 1))
  | pairSlack (p : PairLt s)
  deriving DecidableEq

private inductive Ex (s : ℕ)
  | nzEx (i r c : Fin (s + 1)) (b1 b2 : Bool)
  | hEqEx (i r : Fin (s + 1)) (c : Fin s) (b1 b2 : Bool)
  | vEqEx (i : Fin (s + 1)) (r : Fin s) (c : Fin (s + 1)) (b1 b2 : Bool)
  | pairEx (p : PairLt s) (t : Fin 4)
  deriving DecidableEq

private def varEquiv (s : ℕ) :
    Var s ≃
      ((Fin (s + 1) × Fin (s + 1) × Fin (s + 1)) ⊕ (Fin (s + 1) × Fin (s + 1) × Fin (s + 1))) ⊕
      ((Fin (s + 1) × Fin (s + 1) × Fin (s + 1)) ⊕ (Fin (s + 1) × Fin (s + 1) × Fin s)) ⊕
      ((Fin (s + 1) × Fin s × Fin (s + 1)) ⊕ PairLt s) where
  toFun
    | .grid i r c => Sum.inl (Sum.inl (i, r, c))
    | .nzAux i r c => Sum.inl (Sum.inr (i, r, c))
    | .nzAnc i r c => Sum.inr (Sum.inl (Sum.inl (i, r, c)))
    | .hAnc i r c => Sum.inr (Sum.inl (Sum.inr (i, r, c)))
    | .vAnc i r c => Sum.inr (Sum.inr (Sum.inl (i, r, c)))
    | .pairSlack p => Sum.inr (Sum.inr (Sum.inr p))
  invFun
    | Sum.inl (Sum.inl (i, r, c)) => .grid i r c
    | Sum.inl (Sum.inr (i, r, c)) => .nzAux i r c
    | Sum.inr (Sum.inl (Sum.inl (i, r, c))) => .nzAnc i r c
    | Sum.inr (Sum.inl (Sum.inr (i, r, c))) => .hAnc i r c
    | Sum.inr (Sum.inr (Sum.inl (i, r, c))) => .vAnc i r c
    | Sum.inr (Sum.inr (Sum.inr p)) => .pairSlack p
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with (⟨i, r, c⟩ | ⟨i, r, c⟩) | ((⟨i, r, c⟩ | ⟨i, r, c⟩) | (⟨i, r, c⟩ | p)) <;> rfl

private def exEquiv (s : ℕ) :
    Ex s ≃
      ((Fin (s + 1) × Fin (s + 1) × Fin (s + 1) × Bool × Bool) ⊕
       (Fin (s + 1) × Fin (s + 1) × Fin s × Bool × Bool)) ⊕
      ((Fin (s + 1) × Fin s × Fin (s + 1) × Bool × Bool) ⊕ (PairLt s × Fin 4)) where
  toFun
    | .nzEx i r c b1 b2 => Sum.inl (Sum.inl (i, r, c, b1, b2))
    | .hEqEx i r c b1 b2 => Sum.inl (Sum.inr (i, r, c, b1, b2))
    | .vEqEx i r c b1 b2 => Sum.inr (Sum.inl (i, r, c, b1, b2))
    | .pairEx p t => Sum.inr (Sum.inr (p, t))
  invFun
    | Sum.inl (Sum.inl (i, r, c, b1, b2)) => .nzEx i r c b1 b2
    | Sum.inl (Sum.inr (i, r, c, b1, b2)) => .hEqEx i r c b1 b2
    | Sum.inr (Sum.inl (i, r, c, b1, b2)) => .vEqEx i r c b1 b2
    | Sum.inr (Sum.inr (p, t)) => .pairEx p t
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with (⟨i, r, c, b1, b2⟩ | ⟨i, r, c, b1, b2⟩) | (⟨i, r, c, b1, b2⟩ | ⟨p, t⟩) <;> rfl

private instance instFintypeVar (s : ℕ) : Fintype (Var s) :=
  Fintype.ofEquiv _ (varEquiv s).symm

private instance instFintypeEx (s : ℕ) : Fintype (Ex s) :=
  Fintype.ofEquiv _ (exEquiv s).symm

private lemma card_pairLt_le (s : ℕ) : Fintype.card (PairLt s) ≤ (s + 1) * (s + 1) := by
  have h1 := Fintype.card_subtype_le (p := fun p : Fin (s + 1) × Fin (s + 1) => p.1 < p.2)
  simpa using h1

private lemma card_var_le (s : ℕ) : Fintype.card (Var s) ≤ 64 * (s + 1 + 1) ^ 3 := by
  have hcard : Fintype.card (Var s) =
      (s + 1) * ((s + 1) * (s + 1)) + (s + 1) * ((s + 1) * (s + 1)) +
      ((s + 1) * ((s + 1) * (s + 1)) + (s + 1) * ((s + 1) * s) +
      ((s + 1) * (s * (s + 1)) + Fintype.card (PairLt s))) := by
    rw [Fintype.card_congr (varEquiv s)]
    simp [Fintype.card_sum, Fintype.card_prod]
  have hp := card_pairLt_le s
  rw [hcard]
  nlinarith

private lemma card_ex_le (s : ℕ) : Fintype.card (Ex s) ≤ 128 * (s + 1 + 1) ^ 3 := by
  have hcard : Fintype.card (Ex s) =
      (s + 1) * ((s + 1) * ((s + 1) * (2 * 2))) + (s + 1) * ((s + 1) * (s * (2 * 2))) +
      ((s + 1) * (s * ((s + 1) * (2 * 2))) + Fintype.card (PairLt s) * 4) := by
    rw [Fintype.card_congr (exEquiv s)]
    simp [Fintype.card_sum, Fintype.card_prod]
  have hp := card_pairLt_le s
  rw [hcard]
  nlinarith

private def exSupp {s : ℕ} : Ex s → Finset (Var s)
  | .nzEx i r c false false => {.nzAnc i r c}
  | .nzEx i r c true false => {.grid i r c, .nzAnc i r c}
  | .nzEx i r c false true => {.nzAux i r c, .nzAnc i r c}
  | .nzEx i r c true true => {.grid i r c, .nzAux i r c, .nzAnc i r c}
  | .hEqEx i r c false false => {.hAnc i r c}
  | .hEqEx i r c true false => {.grid i r c.castSucc, .hAnc i r c}
  | .hEqEx i r c false true => {.grid i r c.succ, .hAnc i r c}
  | .hEqEx i r c true true => {.grid i r c.castSucc, .grid i r c.succ, .hAnc i r c}
  | .vEqEx i r c false false => {.vAnc i r c}
  | .vEqEx i r c true false => {.grid i r.castSucc c, .vAnc i r c}
  | .vEqEx i r c false true => {.grid i r.succ c, .vAnc i r c}
  | .vEqEx i r c true true => {.grid i r.castSucc c, .grid i r.succ c, .vAnc i r c}
  | .pairEx p ⟨0, _⟩ => {.grid p.1.1 0 p.1.2}
  | .pairEx p ⟨1, _⟩ => {.grid p.1.2 0 p.1.1}
  | .pairEx p ⟨2, _⟩ => {.pairSlack p}
  | .pairEx p ⟨3, _⟩ => {.grid p.1.1 0 p.1.2, .grid p.1.2 0 p.1.1, .pairSlack p}

private def XRaw {s : ℕ} (t : Ex s) (q : Var s) : Bool :=
  decide (q ∈ exSupp t)

private def baseRaw {s : ℕ} : Ex s → Bool
  | .nzEx _ _ _ true true => true
  | _ => false

private def askRaw {s : ℕ} : Ex s → Option (Fin (s + 1) × Fin (s + 1))
  | .pairEx p t => if t.1 = 3 then some p.1 else none
  | _ => none

private def labelRaw {s : ℕ} (g : Fin (s + 1) → Fin (s + 1) → Bool) (t : Ex s) : Bool :=
  (askRaw t).elim (baseRaw t) (fun p => g p.1 p.2)

private lemma card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _) (by simp)

private lemma card_triple_le_three {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (card_pair_le_two b c))

private lemma exSupp_card_le {s : ℕ} (t : Ex s) : (exSupp t).card ≤ 3 := by
  cases t with
  | nzEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp]
    · simp
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact card_triple_le_three _ _ _
  | hEqEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp]
    · simp
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact card_triple_le_three _ _ _
  | vEqEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp]
    · simp
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact le_trans (card_pair_le_two _ _) (by decide)
    · exact card_triple_le_three _ _ _
  | pairEx p t =>
    fin_cases t <;> simp only [exSupp]
    · simp
    · simp
    · simp
    · exact card_triple_le_three _ _ _

private lemma exSupp_injective {s : ℕ} : Function.Injective (@exSupp s) := by
  intro t1 t2 h
  have hmem : ∀ q, q ∈ exSupp t1 ↔ q ∈ exSupp t2 := fun q => by rw [h]
  cases t1 with
  | nzEx i1 r1 c1 b11 b12 =>
    have hanc : Var.nzAnc i1 r1 c1 ∈ exSupp t2 :=
      (hmem _).mp (by cases b11 <;> cases b12 <;> simp [exSupp])
    cases t2 with
    | nzEx i2 r2 c2 b21 b22 =>
      have heq : i1 = i2 ∧ r1 = r2 ∧ c1 = c2 := by
        cases b21 <;> cases b22 <;> simp [exSupp] at hanc <;> exact hanc
      rcases heq with ⟨rfl, rfl, rfl⟩
      have hb1 : b11 = b21 := by
        have hg := hmem (.grid i1 r1 c1)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp] at hg ⊢
      have hb2 : b12 = b22 := by
        have ha := hmem (.nzAux i1 r1 c1)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp] at ha ⊢
      rw [hb1, hb2]
    | hEqEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | vEqEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | pairEx _ t => fin_cases t <;> simp [exSupp] at hanc
  | hEqEx i1 r1 c1 b11 b12 =>
    have hanc : Var.hAnc i1 r1 c1 ∈ exSupp t2 :=
      (hmem _).mp (by cases b11 <;> cases b12 <;> simp [exSupp])
    cases t2 with
    | nzEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | hEqEx i2 r2 c2 b21 b22 =>
      have heq : i1 = i2 ∧ r1 = r2 ∧ c1 = c2 := by
        cases b21 <;> cases b22 <;> simp [exSupp] at hanc <;> exact hanc
      rcases heq with ⟨rfl, rfl, rfl⟩
      have hne_c : c1.castSucc ≠ c1.succ := by
        intro he; have := congrArg Fin.val he; simp at this
      have hb1 : b11 = b21 := by
        have hg := hmem (.grid i1 r1 c1.castSucc)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp, hne_c] at hg ⊢
      have hb2 : b12 = b22 := by
        have hg := hmem (.grid i1 r1 c1.succ)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp, hne_c.symm] at hg ⊢
      rw [hb1, hb2]
    | vEqEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | pairEx _ t => fin_cases t <;> simp [exSupp] at hanc
  | vEqEx i1 r1 c1 b11 b12 =>
    have hanc : Var.vAnc i1 r1 c1 ∈ exSupp t2 :=
      (hmem _).mp (by cases b11 <;> cases b12 <;> simp [exSupp])
    cases t2 with
    | nzEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | hEqEx _ _ _ b21 b22 => cases b21 <;> cases b22 <;> simp [exSupp] at hanc
    | vEqEx i2 r2 c2 b21 b22 =>
      have heq : i1 = i2 ∧ r1 = r2 ∧ c1 = c2 := by
        cases b21 <;> cases b22 <;> simp [exSupp] at hanc <;> exact hanc
      rcases heq with ⟨rfl, rfl, rfl⟩
      have hne_r : r1.castSucc ≠ r1.succ := by
        intro he; have := congrArg Fin.val he; simp at this
      have hb1 : b11 = b21 := by
        have hg := hmem (.grid i1 r1.castSucc c1)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp, hne_r] at hg ⊢
      have hb2 : b12 = b22 := by
        have hg := hmem (.grid i1 r1.succ c1)
        cases b11 <;> cases b12 <;> cases b21 <;> cases b22 <;> simp [exSupp, hne_r.symm] at hg ⊢
      rw [hb1, hb2]
    | pairEx _ t => fin_cases t <;> simp [exSupp] at hanc
  | pairEx p1 k1 =>
    cases t2 with
    | nzEx i2 r2 c2 b21 b22 =>
      have hanc : Var.nzAnc i2 r2 c2 ∈ exSupp (.pairEx p1 k1) :=
        (hmem _).mpr (by cases b21 <;> cases b22 <;> simp [exSupp])
      fin_cases k1 <;> simp [exSupp] at hanc
    | hEqEx i2 r2 c2 b21 b22 =>
      have hanc : Var.hAnc i2 r2 c2 ∈ exSupp (.pairEx p1 k1) :=
        (hmem _).mpr (by cases b21 <;> cases b22 <;> simp [exSupp])
      fin_cases k1 <;> simp [exSupp] at hanc
    | vEqEx i2 r2 c2 b21 b22 =>
      have hanc : Var.vAnc i2 r2 c2 ∈ exSupp (.pairEx p1 k1) :=
        (hmem _).mpr (by cases b21 <;> cases b22 <;> simp [exSupp])
      fin_cases k1 <;> simp [exSupp] at hanc
    | pairEx p2 k2 =>
      fin_cases k1 <;> fin_cases k2
      · have hg := (hmem (.grid p1.1.1 0 p1.1.2)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_singleton, Var.grid.injEq] at hg
        have hp : p1 = p2 := Subtype.ext (Prod.ext hg.1 hg.2.2)
        rw [hp]
      · have hg := (hmem (.grid p1.1.1 0 p1.1.2)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_singleton, Var.grid.injEq] at hg
        have hlt1 := p1.2; have hlt2 := p2.2
        rw [hg.1, hg.2.2] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · have hg := (hmem (.grid p1.1.1 0 p1.1.2)).mp (by simp [exSupp])
        simp [exSupp] at hg
      · have hs := (hmem (.pairSlack p2)).mpr (by simp [exSupp])
        simp [exSupp] at hs
      · have hg := (hmem (.grid p1.1.2 0 p1.1.1)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_singleton, Var.grid.injEq] at hg
        have hlt1 := p1.2; have hlt2 := p2.2
        rw [hg.1, hg.2.2] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · have hg := (hmem (.grid p1.1.2 0 p1.1.1)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_singleton, Var.grid.injEq] at hg
        have hp : p1 = p2 := Subtype.ext (Prod.ext hg.2.2 hg.1)
        rw [hp]
      · have hg := (hmem (.grid p1.1.2 0 p1.1.1)).mp (by simp [exSupp])
        simp [exSupp] at hg
      · have hs := (hmem (.pairSlack p2)).mpr (by simp [exSupp])
        simp [exSupp] at hs
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp [exSupp] at hs
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp [exSupp] at hs
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_singleton, Var.pairSlack.injEq] at hs
        rw [hs]
      · have hg := (hmem (.grid p2.1.1 0 p2.1.2)).mpr (by simp [exSupp])
        simp [exSupp] at hg
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp [exSupp] at hs
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp [exSupp] at hs
      · have hg := (hmem (.grid p1.1.1 0 p1.1.2)).mp (by simp [exSupp])
        simp [exSupp] at hg
      · have hs := (hmem (.pairSlack p1)).mp (by simp [exSupp])
        simp only [exSupp, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
          Var.pairSlack.injEq] at hs
        rw [hs]

private lemma XRaw_injective {s : ℕ} : Function.Injective (@XRaw s) := by
  intro t1 t2 h
  apply exSupp_injective
  ext q
  have hq : decide (q ∈ exSupp t1) = decide (q ∈ exSupp t2) := congrFun h q
  simpa using hq

private def incOf {s : ℕ} : Var s → Finset (Ex s)
  | .nzAux i r c => {.nzEx i r c false true, .nzEx i r c true true}
  | .nzAnc i r c => {.nzEx i r c false false, .nzEx i r c true false, .nzEx i r c false true, .nzEx i r c true true}
  | .hAnc i r c => {.hEqEx i r c false false, .hEqEx i r c true false, .hEqEx i r c false true, .hEqEx i r c true true}
  | .vAnc i r c => {.vEqEx i r c false false, .vEqEx i r c true false, .vEqEx i r c false true, .vEqEx i r c true true}
  | .pairSlack p => {.pairEx p 2, .pairEx p 3}
  | .grid i r c =>
      ({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s)) ∪
      (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅) ∪
      (if h : 0 < c.1 then {.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} else ∅) ∪
      (if h : r.1 < s then {.vEqEx i ⟨r.1, h⟩ c true false, .vEqEx i ⟨r.1, h⟩ c true true} else ∅) ∪
      (if h : 0 < r.1 then {.vEqEx i ⟨r.1 - 1, by omega⟩ c false true, .vEqEx i ⟨r.1 - 1, by omega⟩ c true true} else ∅) ∪
      (if h : i < c then {.pairEx ⟨(i, c), h⟩ 0, .pairEx ⟨(i, c), h⟩ 3}
       else if h' : c < i then {.pairEx ⟨(c, i), h'⟩ 1, .pairEx ⟨(c, i), h'⟩ 3}
       else ∅)

private lemma incOf_card_le {s : ℕ} (q : Var s) : (incOf q).card ≤ 36 := by
  have h2 : ∀ a b : Ex s, ({a, b} : Finset (Ex s)).card ≤ 2 := fun a b =>
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h4 : ∀ a b c d : Ex s, ({a, b, c, d} : Finset (Ex s)).card ≤ 4 := fun a b c d => by
    have := Finset.card_insert_le a {b, c, d}
    have := Finset.card_insert_le b {c, d}
    have := Finset.card_insert_le c {d}
    simp at *; omega
  cases q with
  | nzAux i r c => exact le_trans (h2 _ _) (by omega)
  | nzAnc i r c => exact le_trans (h4 _ _ _ _) (by omega)
  | hAnc i r c => exact le_trans (h4 _ _ _ _) (by omega)
  | vAnc i r c => exact le_trans (h4 _ _ _ _) (by omega)
  | pairSlack p => exact le_trans (h2 _ _) (by omega)
  | grid i r c =>
    dsimp only [incOf]
    have hc1 : (({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s))).card ≤ 2 := h2 _ _
    have hc2 : (if h : c.1 < s then ({.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} : Finset (Ex s)) else ∅).card ≤ 2 := by
      split_ifs <;> [exact h2 _ _; simp]
    have hc3 : (if h : 0 < c.1 then ({.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} : Finset (Ex s)) else ∅).card ≤ 2 := by
      split_ifs <;> [exact h2 _ _; simp]
    have hc4 : (if h : r.1 < s then ({.vEqEx i ⟨r.1, h⟩ c true false, .vEqEx i ⟨r.1, h⟩ c true true} : Finset (Ex s)) else ∅).card ≤ 2 := by
      split_ifs <;> [exact h2 _ _; simp]
    have hc5 : (if h : 0 < r.1 then ({.vEqEx i ⟨r.1 - 1, by omega⟩ c false true, .vEqEx i ⟨r.1 - 1, by omega⟩ c true true} : Finset (Ex s)) else ∅).card ≤ 2 := by
      split_ifs <;> [exact h2 _ _; simp]
    have hc6 : (if h : i < c then ({.pairEx ⟨(i, c), h⟩ 0, .pairEx ⟨(i, c), h⟩ 3} : Finset (Ex s))
        else if h' : c < i then {.pairEx ⟨(c, i), h'⟩ 1, .pairEx ⟨(c, i), h'⟩ 3} else ∅).card ≤ 2 := by
      split_ifs <;> [exact h2 _ _; exact h2 _ _; simp]
    have hu1 := Finset.card_union_le
      (({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s)) ∪
        (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅) ∪
        (if h : 0 < c.1 then {.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} else ∅) ∪
        (if h : r.1 < s then {.vEqEx i ⟨r.1, h⟩ c true false, .vEqEx i ⟨r.1, h⟩ c true true} else ∅) ∪
        (if h : 0 < r.1 then {.vEqEx i ⟨r.1 - 1, by omega⟩ c false true, .vEqEx i ⟨r.1 - 1, by omega⟩ c true true} else ∅))
      (if h : i < c then {.pairEx ⟨(i, c), h⟩ 0, .pairEx ⟨(i, c), h⟩ 3}
       else if h' : c < i then {.pairEx ⟨(c, i), h'⟩ 1, .pairEx ⟨(c, i), h'⟩ 3} else ∅)
    have hu2 := Finset.card_union_le
      (({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s)) ∪
        (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅) ∪
        (if h : 0 < c.1 then {.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} else ∅) ∪
        (if h : r.1 < s then {.vEqEx i ⟨r.1, h⟩ c true false, .vEqEx i ⟨r.1, h⟩ c true true} else ∅))
      (if h : 0 < r.1 then {.vEqEx i ⟨r.1 - 1, by omega⟩ c false true, .vEqEx i ⟨r.1 - 1, by omega⟩ c true true} else ∅)
    have hu3 := Finset.card_union_le
      (({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s)) ∪
        (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅) ∪
        (if h : 0 < c.1 then {.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} else ∅))
      (if h : r.1 < s then {.vEqEx i ⟨r.1, h⟩ c true false, .vEqEx i ⟨r.1, h⟩ c true true} else ∅)
    have hu4 := Finset.card_union_le
      (({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s)) ∪
        (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅))
      (if h : 0 < c.1 then {.hEqEx i r ⟨c.1 - 1, by omega⟩ false true, .hEqEx i r ⟨c.1 - 1, by omega⟩ true true} else ∅)
    have hu5 := Finset.card_union_le
      ({.nzEx i r c true false, .nzEx i r c true true} : Finset (Ex s))
      (if h : c.1 < s then {.hEqEx i r ⟨c.1, h⟩ true false, .hEqEx i r ⟨c.1, h⟩ true true} else ∅)
    omega

private lemma mem_incOf_of_mem_exSupp {s : ℕ} {q : Var s} {t : Ex s} (h : q ∈ exSupp t) :
    t ∈ incOf q := by
  cases t with
  | nzEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp, Finset.mem_insert, Finset.mem_singleton] at h
    · subst h; simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl | rfl <;> simp [incOf]
  | hEqEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp, Finset.mem_insert, Finset.mem_singleton] at h
    · subst h; simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl | rfl <;> simp [incOf]
  | vEqEx i r c b1 b2 =>
    cases b1 <;> cases b2 <;> simp only [exSupp, Finset.mem_insert, Finset.mem_singleton] at h
    · subst h; simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl <;> simp [incOf]
    · rcases h with rfl | rfl | rfl <;> simp [incOf]
  | pairEx p k =>
    rcases p with ⟨⟨i, j⟩, hij⟩
    have hnot : ¬ j < i := not_lt_of_gt hij
    fin_cases k <;> simp only [exSupp, Finset.mem_insert, Finset.mem_singleton] at h
    · subst h; simp [incOf, hij]
    · subst h; simp [incOf, hnot, hij]
    · subst h; simp [incOf]
    · rcases h with rfl | rfl | rfl
      · simp [incOf, hij]
      · simp [incOf, hnot, hij]
      · simp [incOf]

private lemma XRaw_deg_le {s : ℕ} (q : Var s) :
    ((Finset.univ : Finset (Ex s)).filter (fun t => XRaw t q)).card ≤ 36 := by
  have hsub : (Finset.univ : Finset (Ex s)).filter (fun t => XRaw t q) ⊆ incOf q := by
    intro t ht
    have hq : q ∈ exSupp t := by simpa [XRaw] using (Finset.mem_filter.mp ht).2
    exact mem_incOf_of_mem_exSupp hq
  exact le_trans (Finset.card_le_card hsub) (incOf_card_le q)

private lemma askRaw_lt {s : ℕ} (t : Ex s) (i j : Fin (s + 1)) (h : askRaw t = some (i, j)) :
    i < j := by
  cases t with
  | nzEx _ _ _ _ _ => simp [askRaw] at h
  | hEqEx _ _ _ _ _ => simp [askRaw] at h
  | vEqEx _ _ _ _ _ => simp [askRaw] at h
  | pairEx p k =>
    rcases k with ⟨kv, hkv⟩
    interval_cases kv
    · simp [askRaw] at h
    · simp [askRaw] at h
    · simp [askRaw] at h
    · simp only [askRaw, ↓reduceIte, Option.some.injEq] at h
      have := p.2
      rw [h] at this
      exact this

private lemma askRaw_existsUnique {s : ℕ} (i j : Fin (s + 1)) (hij : i < j) :
    ∃! t : Ex s, askRaw t = some (i, j) := by
  refine ⟨.pairEx ⟨(i, j), hij⟩ 3, rfl, fun t ht => ?_⟩
  cases t with
  | nzEx _ _ _ _ _ => simp [askRaw] at ht
  | hEqEx _ _ _ _ _ => simp [askRaw] at ht
  | vEqEx _ _ _ _ _ => simp [askRaw] at ht
  | pairEx p k =>
    rcases k with ⟨kv, hkv⟩
    interval_cases kv
    · simp [askRaw] at ht
    · simp [askRaw] at ht
    · simp [askRaw] at ht
    · simp only [askRaw, ↓reduceIte, Option.some.injEq] at ht
      have hp : p = ⟨(i, j), hij⟩ := Subtype.ext ht
      rw [hp]; rfl

/-! ### Section 5: Bucket Definitions and the Four Error Bounds on `Var s` / `Ex s` -/

private def nzBucket {s : ℕ} (i r c : Fin (s + 1)) : Finset (Ex s) :=
  {.nzEx i r c false false, .nzEx i r c true false, .nzEx i r c false true, .nzEx i r c true true}

private def hEqBucket {s : ℕ} (i r : Fin (s + 1)) (c : Fin s) : Finset (Ex s) :=
  {.hEqEx i r c false false, .hEqEx i r c true false, .hEqEx i r c false true, .hEqEx i r c true true}

private def vEqBucket {s : ℕ} (i : Fin (s + 1)) (r : Fin s) (c : Fin (s + 1)) : Finset (Ex s) :=
  {.vEqEx i r c false false, .vEqEx i r c true false, .vEqEx i r c false true, .vEqEx i r c true true}

private def pairBucket {s : ℕ} (p : PairLt s) : Finset (Ex s) :=
  {.pairEx p 0, .pairEx p 1, .pairEx p 2, .pairEx p 3}

private def gridBucket {s : ℕ} (i : Fin (s + 1)) : Finset (Ex s) :=
  (Finset.univ : Finset (Ex s)).filter fun t =>
    ((match t with
      | .nzEx i' _ _ _ _ => i' == i
      | .hEqEx i' _ _ _ _ => i' == i
      | .vEqEx i' _ _ _ _ => i' == i
      | .pairEx _ _ => false) : Bool) = true

private def colBucket {s : ℕ} (i c : Fin (s + 1)) : Finset (Ex s) :=
  (Finset.univ : Finset (Ex s)).filter fun t =>
    ((match t with
      | .nzEx i' _ c' _ _ => i' == i && c' == c
      | .vEqEx i' _ c' _ _ => i' == i && c' == c
      | _ => false) : Bool) = true

private def rowBucket {s : ℕ} (i r : Fin (s + 1)) : Finset (Ex s) :=
  (Finset.univ : Finset (Ex s)).filter fun t =>
    ((match t with
      | .nzEx i' r' _ _ _ => i' == i && r' == r
      | .hEqEx i' r' _ _ _ => i' == i && r' == r
      | _ => false) : Bool) = true

private lemma sum_four_distinct {α : Type*} [DecidableEq α] (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (f : α → ZMod 2) :
    ∑ t ∈ ({a, b, c, d} : Finset α), f t = f a + f b + f c + f d := by
  have ha : a ∉ ({b, c, d} : Finset α) := by simp [hab, hac, had]
  have hb : b ∉ ({c, d} : Finset α) := by simp [hbc, hbd]
  have hc : c ∉ ({d} : Finset α) := by simp [hcd]
  rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc, Finset.sum_singleton]
  ring

private lemma nzBucket_err_of_zero {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t))
    (i r c : Fin (s + 1)) (hcol : (v (.grid i r c), w (.grid i r c)) = (0, 0)) :
    1 ≤ ((nzBucket i r c).filter (fun t => f t ≠ labelRaw g t)).card := by
  apply four_sum_err_pos
  have hsum_f : ∑ t ∈ nzBucket i r c, b2z (f t) = 0 := by
    unfold nzBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp only [hf, exSupp]
    rw [quadEval_anchor_four c0 a0 b0 u v w (by simp) (by simp) (by simp), hcol, det2_zero_left]
  have hsum_l : ∑ t ∈ nzBucket i r c, b2z (labelRaw g t) = 1 := by
    unfold nzBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [labelRaw, askRaw, baseRaw, b2z]
  rw [hsum_f, hsum_l]
  decide

private lemma hEqBucket_err_of_det_one {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t))
    (i r : Fin (s + 1)) (c : Fin s)
    (hdet : det2 (v (.grid i r c.castSucc), w (.grid i r c.castSucc))
      (v (.grid i r c.succ), w (.grid i r c.succ)) = 1) :
    1 ≤ ((hEqBucket i r c).filter (fun t => f t ≠ labelRaw g t)).card := by
  apply four_sum_err_pos
  have hne : Var.grid i r c.castSucc ≠ Var.grid i r c.succ := by
    intro h
    have := congrArg Fin.val (Var.grid.inj h).2.2
    simp at this
  have hsum_f : ∑ t ∈ hEqBucket i r c, b2z (f t) = 1 := by
    unfold hEqBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp only [hf, exSupp]
    rw [quadEval_anchor_four c0 a0 b0 u v w (by simp) (by simp) hne, hdet]
  have hsum_l : ∑ t ∈ hEqBucket i r c, b2z (labelRaw g t) = 0 := by
    unfold hEqBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [labelRaw, askRaw, baseRaw, b2z]
  rw [hsum_f, hsum_l]
  decide

private lemma vEqBucket_err_of_det_one {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t))
    (i : Fin (s + 1)) (r : Fin s) (c : Fin (s + 1))
    (hdet : det2 (v (.grid i r.castSucc c), w (.grid i r.castSucc c))
      (v (.grid i r.succ c), w (.grid i r.succ c)) = 1) :
    1 ≤ ((vEqBucket i r c).filter (fun t => f t ≠ labelRaw g t)).card := by
  apply four_sum_err_pos
  have hne : Var.grid i r.castSucc c ≠ Var.grid i r.succ c := by
    intro h
    have := congrArg Fin.val (Var.grid.inj h).2.1
    simp at this
  have hsum_f : ∑ t ∈ vEqBucket i r c, b2z (f t) = 1 := by
    unfold vEqBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp only [hf, exSupp]
    rw [quadEval_anchor_four c0 a0 b0 u v w (by simp) (by simp) hne, hdet]
  have hsum_l : ∑ t ∈ vEqBucket i r c, b2z (labelRaw g t) = 0 := by
    unfold vEqBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [labelRaw, askRaw, baseRaw, b2z]
  rw [hsum_f, hsum_l]
  decide

private lemma pairBucket_err_of_same_col {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t))
    (p : PairLt s) (hedge : g p.1.1 p.1.2 = true)
    (hcol : (v (.grid p.1.1 0 p.1.2), w (.grid p.1.1 0 p.1.2)) =
      (v (.grid p.1.2 0 p.1.1), w (.grid p.1.2 0 p.1.1))) :
    1 ≤ ((pairBucket p).filter (fun t => f t ≠ labelRaw g t)).card := by
  apply four_sum_err_pos
  have hne_ij : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hne_xy : Var.grid p.1.1 0 p.1.2 ≠ Var.grid p.1.2 0 p.1.1 := fun h => hne_ij (Var.grid.inj h).1
  have hsum_f : ∑ t ∈ pairBucket p, b2z (f t) = 0 := by
    unfold pairBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp only [hf, exSupp]
    rw [quadEval_triple_four c0 a0 b0 u v w hne_xy (by simp) (by simp)]
    have hv : v (.grid p.1.1 0 p.1.2) = v (.grid p.1.2 0 p.1.1) := congrArg Prod.fst hcol
    have hw : w (.grid p.1.1 0 p.1.2) = w (.grid p.1.2 0 p.1.1) := congrArg Prod.snd hcol
    rw [hv, hw, det2_self]
  have hsum_l : ∑ t ∈ pairBucket p, b2z (labelRaw g t) = 1 := by
    unfold pairBucket
    rw [sum_four_distinct _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    simp [labelRaw, askRaw, baseRaw, hedge, b2z]
  rw [hsum_f, hsum_l]
  decide

private lemma card_edges_eq_pairLt {s : ℕ} (g : Fin (s + 1) → Fin (s + 1) → Bool) :
    ((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card =
    ((Finset.univ : Finset (PairLt s)).filter (fun p => g p.1.1 p.1.2 = true)).card := by
  symm
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2, (Finset.mem_filter.mp hp).2⟩
  · intro p1 _ p2 _ h; exact Subtype.ext h
  · intro q hq
    obtain ⟨_, hlt, hg⟩ := Finset.mem_filter.mp hq
    exact ⟨⟨q, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩

private lemma affine_err_lb_raw {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 : ZMod 2) (u : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 0 0 u (fun _ => 0) (fun _ => 0) (exSupp t)) :
    (s + 1) ^ 3 + ((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card ≤
    ((Finset.univ : Finset (Ex s)).filter (fun t => f t ≠ labelRaw g t)).card := by
  let E : Finset (Ex s) := Finset.univ.filter (fun t => f t ≠ labelRaw g t)
  let Idx := (Fin (s + 1) × Fin (s + 1) × Fin (s + 1)) ⊕ PairLt s
  let I1 : Finset Idx := Finset.univ.image Sum.inl
  let I2 : Finset Idx := ((Finset.univ : Finset (PairLt s)).filter (fun p => g p.1.1 p.1.2 = true)).image Sum.inr
  let B : Idx → Finset (Ex s) := fun idx =>
    match idx with
    | Sum.inl (i, r, c) => nzBucket i r c
    | Sum.inr p => pairBucket p
  have hdisj : ∀ a ∈ I1 ∪ I2, ∀ b ∈ I1 ∪ I2, a ≠ b → Disjoint (B a) (B b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro t hta htb
    rcases a with ⟨i1, r1, c1⟩ | p1 <;> rcases b with ⟨i2, r2, c2⟩ | p2
    · simp only [B, nzBucket, Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;>
        rcases htb with h | h | h | h <;> simp at h
      all_goals exact hab (by rcases h with ⟨rfl, rfl, rfl⟩; rfl)
    · simp only [B, nzBucket, pairBucket, Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;> rcases htb with h | h | h | h <;> simp at h
    · simp only [B, nzBucket, pairBucket, Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;> rcases htb with h | h | h | h <;> simp at h
    · simp only [B, pairBucket, Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;> rcases htb with h | h | h | h <;> simp at h
      all_goals exact hab (by subst h; rfl)
  have hge := finset_card_disjoint_union_ge (I1 ∪ I2) B E hdisj
  have hone : ∀ idx ∈ I1 ∪ I2, 1 ≤ (E ∩ B idx).card := by
    intro idx hidx
    have hinter : E ∩ B idx = (B idx).filter (fun t => f t ≠ labelRaw g t) := by
      ext t; simp [E, and_comm]
    rw [hinter]
    rcases Finset.mem_union.mp hidx with h1 | h2
    · obtain ⟨⟨i, r, c⟩, _, rfl⟩ := Finset.mem_image.mp h1
      exact nzBucket_err_of_zero g f c0 0 0 u (fun _ => 0) (fun _ => 0) hf i r c rfl
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h2
      exact pairBucket_err_of_same_col g f c0 0 0 u (fun _ => 0) (fun _ => 0) hf p
        (Finset.mem_filter.mp hp).2 rfl
  have hsum_ge : (I1 ∪ I2).card ≤ ∑ idx ∈ I1 ∪ I2, (E ∩ B idx).card := by
    calc (I1 ∪ I2).card = ∑ _idx ∈ I1 ∪ I2, 1 := by simp
      _ ≤ ∑ idx ∈ I1 ∪ I2, (E ∩ B idx).card := Finset.sum_le_sum hone
  have hdisjI : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
    simp at h
  have hcardI1 : I1.card = (s + 1) ^ 3 := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    simp; ring
  have hcardI2 : I2.card = ((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective, card_edges_eq_pairLt]
  rw [Finset.card_union_of_disjoint hdisjI, hcardI1, hcardI2] at hsum_ge
  exact le_trans hsum_ge hge

private lemma const_false_err_eq_raw {s : ℕ} (g : Fin (s + 1) → Fin (s + 1) → Bool) :
    ((Finset.univ : Finset (Ex s)).filter (fun t => false ≠ labelRaw g t)).card =
    (s + 1) ^ 3 + ((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card := by
  let S1 : Finset (Ex s) := Finset.univ.image (fun x : Fin (s + 1) × Fin (s + 1) × Fin (s + 1) =>
    Ex.nzEx x.1 x.2.1 x.2.2 true true)
  let S2 : Finset (Ex s) := ((Finset.univ : Finset (PairLt s)).filter (fun p => g p.1.1 p.1.2 = true)).image
    (fun p => Ex.pairEx p 3)
  have hset : (Finset.univ : Finset (Ex s)).filter (fun t => false ≠ labelRaw g t) = S1 ∪ S2 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, S1, S2,
      Finset.mem_image]
    cases t with
    | nzEx i r c b1 b2 =>
      cases b1 <;> cases b2 <;> simp [labelRaw, askRaw, baseRaw]
    | hEqEx _ _ _ _ _ => simp [labelRaw, askRaw, baseRaw]
    | vEqEx _ _ _ _ _ => simp [labelRaw, askRaw, baseRaw]
    | pairEx p k =>
      fin_cases k
      · simp [labelRaw, askRaw, baseRaw]
      · simp [labelRaw, askRaw, baseRaw]
      · simp [labelRaw, askRaw, baseRaw]
      · simp [labelRaw, askRaw, baseRaw]
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp ht1
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp ht2
    simp at h
  rw [hset, Finset.card_union_of_disjoint hdisj]
  have h1 : S1.card = (s + 1) ^ 3 := by
    rw [Finset.card_image_of_injective]
    · simp; ring
    · intro x y h
      simp only [Ex.nzEx.injEq, and_true] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  have h2 : S2.card = ((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card := by
    rw [Finset.card_image_of_injective]
    · rw [card_edges_eq_pairLt]
    · intro p1 p2 h; exact (Ex.pairEx.inj h).1
  rw [h1, h2]

-- Decoding a 3-coloring from (v, w) on Var s
private def goodRow {s : ℕ} (v w : Var s → ZMod 2) (i r : Fin (s + 1)) : Prop :=
  (v (.grid i r 0), w (.grid i r 0)) ≠ (0, 0) ∧
  ∀ c' : Fin (s + 1), (v (.grid i r c'), w (.grid i r c')) = (v (.grid i r 0), w (.grid i r 0))

private noncomputable def decodeVW {s : ℕ} (v w : Var s → ZMod 2) (i : Fin (s + 1)) : Fin 3 := by
  classical
  exact if h : ∃ r : Fin (s + 1), goodRow v w i r then
    pairToFin3 (v (.grid i (Classical.choose h) 0), w (.grid i (Classical.choose h) 0))
  else ⟨0, by decide⟩

private lemma grid_bucket_err_ge_badCols {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t))
    (i : Fin (s + 1)) :
    let E := (Finset.univ : Finset (Ex s)).filter (fun t => f t ≠ labelRaw g t)
    let badCols := (Finset.univ : Finset (Fin (s + 1))).filter
      (fun j => (v (.grid i 0 j), w (.grid i 0 j)) ≠ colorVec (decodeVW v w i))
    badCols.card ≤ (E ∩ gridBucket i).card := by
  intro E badCols
  by_cases hgr : ∃ r : Fin (s + 1), goodRow v w i r
  · -- Case 1: good row exists → charge each bad column j to colBucket i j
    let r0 := Classical.choose hgr
    have hr0 : goodRow v w i r0 := Classical.choose_spec hgr
    have hdec : colorVec (decodeVW v w i) = (v (.grid i r0 0), w (.grid i r0 0)) := by
      simp only [decodeVW, hgr, ↓reduceDIte]
      exact colorVec_pairToFin3 hr0.1
    have hdisj : ∀ j1 ∈ badCols, ∀ j2 ∈ badCols, j1 ≠ j2 → Disjoint (colBucket i j1) (colBucket i j2) := by
      intro j1 _ j2 _ hne
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [colBucket, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
      cases t with
      | nzEx i' _ c' _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht1 ht2
        exact hne (ht1.2.symm.trans ht2.2)
      | vEqEx i' _ c' _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht1 ht2
        exact hne (ht1.2.symm.trans ht2.2)
      | hEqEx _ _ _ _ _ => exact Bool.false_ne_true ht1
      | pairEx _ _ => exact Bool.false_ne_true ht1
    have hcol_sub : ∀ j, colBucket i j ⊆ gridBucket i := by
      intro j t ht
      simp only [colBucket, gridBucket, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      cases t with
      | nzEx _ _ _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht ⊢; exact ht.1
      | vEqEx _ _ _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht ⊢; exact ht.1
      | hEqEx _ _ _ _ _ => exact False.elim (Bool.false_ne_true ht)
      | pairEx _ _ => exact False.elim (Bool.false_ne_true ht)
    have hcol_err : ∀ j ∈ badCols, 1 ≤ ((E ∩ gridBucket i) ∩ colBucket i j).card := by
      intro j hj
      have hne_col : (v (.grid i 0 j), w (.grid i 0 j)) ≠ (v (.grid i r0 j), w (.grid i r0 j)) := by
        rw [hr0.2 j, ← hdec]
        exact (Finset.mem_filter.mp hj).2
      obtain ⟨r, hrne⟩ := exists_adj_ne (fun r => (v (.grid i r j), w (.grid i r j))) hne_col
      have hinter : (E ∩ gridBucket i) ∩ colBucket i j = (colBucket i j).filter (fun t => f t ≠ labelRaw g t) := by
        ext t
        simp only [E, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨hf', _⟩, hc⟩ => ⟨hc, hf'⟩, fun ⟨hc, hf'⟩ => ⟨⟨hf', hcol_sub j hc⟩, hc⟩⟩
      rw [hinter]
      by_cases hz1 : (v (.grid i r.castSucc j), w (.grid i r.castSucc j)) = (0, 0)
      · have hsub : nzBucket i r.castSucc j ⊆ colBucket i j := by
          intro t ht
          simp only [nzBucket, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl <;> simp [colBucket]
        exact le_trans (nzBucket_err_of_zero g f c0 a0 b0 u v w hf i r.castSucc j hz1)
          (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
      · by_cases hz2 : (v (.grid i r.succ j), w (.grid i r.succ j)) = (0, 0)
        · have hsub : nzBucket i r.succ j ⊆ colBucket i j := by
            intro t ht
            simp only [nzBucket, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl | rfl <;> simp [colBucket]
          exact le_trans (nzBucket_err_of_zero g f c0 a0 b0 u v w hf i r.succ j hz2)
            (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
        · have hdet := det2_eq_one_of_ne hz1 hz2 hrne
          have hsub : vEqBucket i r j ⊆ colBucket i j := by
            intro t ht
            simp only [vEqBucket, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl | rfl <;> simp [colBucket]
          exact le_trans (vEqBucket_err_of_det_one g f c0 a0 b0 u v w hf i r j hdet)
            (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    calc badCols.card = ∑ _j ∈ badCols, 1 := by simp
      _ ≤ ∑ j ∈ badCols, ((E ∩ gridBucket i) ∩ colBucket i j).card := Finset.sum_le_sum hcol_err
      _ ≤ (E ∩ gridBucket i).card := finset_card_disjoint_union_ge badCols (colBucket i) (E ∩ gridBucket i) hdisj
  · -- Case 2: NO good row exists → EVERY row r has ≥ 1 error in rowBucket i r!
    have hdisj : ∀ r1 ∈ (Finset.univ : Finset (Fin (s + 1))),
        ∀ r2 ∈ (Finset.univ : Finset (Fin (s + 1))), r1 ≠ r2 → Disjoint (rowBucket i r1) (rowBucket i r2) := by
      intro r1 _ r2 _ hne
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [rowBucket, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
      cases t with
      | nzEx _ r' _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht1 ht2
        exact hne (ht1.2.symm.trans ht2.2)
      | hEqEx _ r' _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht1 ht2
        exact hne (ht1.2.symm.trans ht2.2)
      | vEqEx _ _ _ _ _ => exact Bool.false_ne_true ht1
      | pairEx _ _ => exact Bool.false_ne_true ht1
    have hrow_sub : ∀ r, rowBucket i r ⊆ gridBucket i := by
      intro r t ht
      simp only [rowBucket, gridBucket, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      cases t with
      | nzEx _ _ _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht ⊢; exact ht.1
      | hEqEx _ _ _ _ _ =>
        simp only [Bool.and_eq_true, beq_iff_eq] at ht ⊢; exact ht.1
      | vEqEx _ _ _ _ _ => exact False.elim (Bool.false_ne_true ht)
      | pairEx _ _ => exact False.elim (Bool.false_ne_true ht)
    have hrow_err : ∀ r ∈ (Finset.univ : Finset (Fin (s + 1))),
        1 ≤ ((E ∩ gridBucket i) ∩ rowBucket i r).card := by
      intro r _
      have hnot : ¬ goodRow v w i r := fun h => hgr ⟨r, h⟩
      have hinter : (E ∩ gridBucket i) ∩ rowBucket i r = (rowBucket i r).filter (fun t => f t ≠ labelRaw g t) := by
        ext t
        simp only [E, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨hf', _⟩, hr'⟩ => ⟨hr', hf'⟩, fun ⟨hr', hf'⟩ => ⟨⟨hf', hrow_sub r hr'⟩, hr'⟩⟩
      rw [hinter]
      by_cases hz0 : (v (.grid i r 0), w (.grid i r 0)) = (0, 0)
      · have hsub : nzBucket i r 0 ⊆ rowBucket i r := by
          intro t ht
          simp only [nzBucket, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl <;> simp [rowBucket]
        exact le_trans (nzBucket_err_of_zero g f c0 a0 b0 u v w hf i r 0 hz0)
          (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
      · have hex : ∃ c' : Fin (s + 1), (v (.grid i r c'), w (.grid i r c')) ≠ (v (.grid i r 0), w (.grid i r 0)) := by
          by_contra hall
          push Not at hall
          exact hnot ⟨hz0, hall⟩
        obtain ⟨c', hc'⟩ := hex
        obtain ⟨c, hcne⟩ := exists_adj_ne (fun c => (v (.grid i r c), w (.grid i r c))) hc'
        by_cases hz1 : (v (.grid i r c.castSucc), w (.grid i r c.castSucc)) = (0, 0)
        · have hsub : nzBucket i r c.castSucc ⊆ rowBucket i r := by
            intro t ht
            simp only [nzBucket, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl | rfl <;> simp [rowBucket]
          exact le_trans (nzBucket_err_of_zero g f c0 a0 b0 u v w hf i r c.castSucc hz1)
            (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
        · by_cases hz2 : (v (.grid i r c.succ), w (.grid i r c.succ)) = (0, 0)
          · have hsub : nzBucket i r c.succ ⊆ rowBucket i r := by
              intro t ht
              simp only [nzBucket, Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl | rfl | rfl <;> simp [rowBucket]
            exact le_trans (nzBucket_err_of_zero g f c0 a0 b0 u v w hf i r c.succ hz2)
              (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
          · have hdet := det2_eq_one_of_ne hz1 hz2 hcne
            have hsub : hEqBucket i r c ⊆ rowBucket i r := by
              intro t ht
              simp only [hEqBucket, Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl | rfl | rfl <;> simp [rowBucket]
            exact le_trans (hEqBucket_err_of_det_one g f c0 a0 b0 u v w hf i r c hdet)
              (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    have hle_k : badCols.card ≤ s + 1 := by
      have := Finset.card_le_univ badCols
      simpa using this
    calc badCols.card ≤ s + 1 := hle_k
      _ = ∑ _r : Fin (s + 1), 1 := by simp
      _ ≤ ∑ r : Fin (s + 1), ((E ∩ gridBucket i) ∩ rowBucket i r).card := Finset.sum_le_sum hrow_err
      _ ≤ (E ∩ gridBucket i).card := finset_card_disjoint_union_ge Finset.univ (rowBucket i) (E ∩ gridBucket i) hdisj

private lemma quad_err_lb_raw {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (f : Ex s → Bool)
    (c0 a0 b0 : ZMod 2) (u v w : Var s → ZMod 2)
    (hf : ∀ t, b2z (f t) = quadEval c0 a0 b0 u v w (exSupp t)) :
    let edges := (Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)
    let c := decodeVW v w
    (edges.filter (fun p => c p.1 = c p.2)).card ≤
    ((Finset.univ : Finset (Ex s)).filter (fun t => f t ≠ labelRaw g t)).card := by
  intro edges c
  let E : Finset (Ex s) := Finset.univ.filter (fun t => f t ≠ labelRaw g t)
  let Ebad := edges.filter (fun p => c p.1 = c p.2)
  let Eagree := Ebad.filter (fun p => (v (.grid p.1 0 p.2), w (.grid p.1 0 p.2)) =
    (v (.grid p.2 0 p.1), w (.grid p.2 0 p.1)))
  let Edis := Ebad.filter (fun p => ¬ ((v (.grid p.1 0 p.2), w (.grid p.1 0 p.2)) =
    (v (.grid p.2 0 p.1), w (.grid p.2 0 p.1))))
  have hsplit : Ebad.card = Eagree.card + Edis.card :=
    (Finset.card_filter_add_card_filter_not (s := Ebad)
      (p := fun p => (v (.grid p.1 0 p.2), w (.grid p.1 0 p.2)) =
        (v (.grid p.2 0 p.1), w (.grid p.2 0 p.1)))).symm
  -- Bound Edis.card ≤ ∑ i, (badCols i).card
  let badCols : Fin (s + 1) → Finset (Fin (s + 1)) := fun i =>
    Finset.univ.filter (fun j => (v (.grid i 0 j), w (.grid i 0 j)) ≠ colorVec (c i))
  let badPairs : Finset (Fin (s + 1) × Fin (s + 1)) :=
    Finset.univ.filter (fun q => q.2 ∈ badCols q.1)
  have hdis_le : Edis.card ≤ ∑ i : Fin (s + 1), (badCols i).card := by
    have hcard_bp : badPairs.card = ∑ i : Fin (s + 1), (badCols i).card := by
      have hbi : badPairs.card = (Finset.univ.sigma badCols).card := by
        refine Finset.card_bij (fun q _ => ⟨q.1, q.2⟩) ?_ ?_ ?_
        · intro q hq
          exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
        · intro q1 _ q2 _ h
          exact Prod.ext (congrArg Sigma.fst h) (by cases q1; cases q2; cases h; rfl)
        · intro x hx
          exact ⟨(x.1, x.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sigma.mp hx).2⟩, rfl⟩
      rw [hbi, Finset.card_sigma]
    rw [← hcard_bp]
    let φ : Fin (s + 1) × Fin (s + 1) → Fin (s + 1) × Fin (s + 1) := fun p =>
      if p.2 ∈ badCols p.1 then (p.1, p.2) else (p.2, p.1)
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro p hp
      obtain ⟨hp_bad, hne⟩ := Finset.mem_filter.mp hp
      have hceq : c p.1 = c p.2 := (Finset.mem_filter.mp hp_bad).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp only [φ]
      split_ifs with h1
      · exact h1
      · simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
        push Not at h1
        intro h2
        apply hne
        rw [h1, h2, hceq]
    · intro p1 hp1 p2 hp2 heq
      have hlt1 : p1.1 < p1.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1).2.1
      have hlt2 : p2.1 < p2.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1).2.1
      dsimp only [φ] at heq
      split_ifs at heq with h1 h2 h2
      · exact heq
      · have h1' := congrArg Prod.fst heq
        have h2' := congrArg Prod.snd heq
        dsimp only at h1' h2'
        rw [h1', h2'] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · have h1' := congrArg Prod.fst heq
        have h2' := congrArg Prod.snd heq
        dsimp only at h1' h2'
        rw [← h1', ← h2'] at hlt2
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  -- Bound Eagree + ∑ gridBucket i via disjoint buckets
  let Idx := Fin (s + 1) ⊕ PairLt s
  let I1 : Finset Idx := Finset.univ.image Sum.inl
  let P_agree : Finset (PairLt s) := Finset.univ.filter (fun p => p.1 ∈ Eagree)
  let I2 : Finset Idx := P_agree.image Sum.inr
  let B : Idx → Finset (Ex s) := fun idx =>
    match idx with
    | Sum.inl i => gridBucket i
    | Sum.inr p => pairBucket p
  have hdisj : ∀ a ∈ I1 ∪ I2, ∀ b ∈ I1 ∪ I2, a ≠ b → Disjoint (B a) (B b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro t hta htb
    rcases a with i1 | p1 <;> rcases b with i2 | p2
    · simp only [B, gridBucket, Finset.mem_filter, Finset.mem_univ, true_and] at hta htb
      cases t with
      | nzEx _ _ _ _ _ =>
        simp only [beq_iff_eq] at hta htb
        exact hab (congrArg Sum.inl (hta.symm.trans htb))
      | hEqEx _ _ _ _ _ =>
        simp only [beq_iff_eq] at hta htb
        exact hab (congrArg Sum.inl (hta.symm.trans htb))
      | vEqEx _ _ _ _ _ =>
        simp only [beq_iff_eq] at hta htb
        exact hab (congrArg Sum.inl (hta.symm.trans htb))
      | pairEx _ _ => exact Bool.false_ne_true hta
    · simp only [B, gridBucket, pairBucket, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases htb with rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true hta
    · simp only [B, gridBucket, pairBucket, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true htb
    · simp only [B, pairBucket, Finset.mem_insert, Finset.mem_singleton] at hta htb
      rcases hta with rfl | rfl | rfl | rfl <;> rcases htb with h | h | h | h <;> simp at h
      all_goals exact hab (by subst h; rfl)
  have hge := finset_card_disjoint_union_ge (I1 ∪ I2) B E hdisj
  have hdisjI : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
    simp at h
  rw [Finset.sum_union hdisjI,
    Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h),
    Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)] at hge
  have hgrid_sum : ∑ i : Fin (s + 1), (badCols i).card ≤ ∑ i : Fin (s + 1), (E ∩ gridBucket i).card :=
    Finset.sum_le_sum fun i _ => grid_bucket_err_ge_badCols g f c0 a0 b0 u v w hf i
  have hagree_card : Eagree.card = P_agree.card := by
    symm
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · intro p1 _ p2 _ h; exact Subtype.ext h
    · intro q hq
      have hlt : q.1 < q.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.1
      exact ⟨⟨q, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  have hagree_sum : P_agree.card ≤ ∑ p ∈ P_agree, (E ∩ pairBucket p).card := by
    calc P_agree.card = ∑ _p ∈ P_agree, 1 := by simp
      _ ≤ ∑ p ∈ P_agree, (E ∩ pairBucket p).card := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_ag : p.1 ∈ Eagree := (Finset.mem_filter.mp hp).2
        have hinter : E ∩ pairBucket p = (pairBucket p).filter (fun t => f t ≠ labelRaw g t) := by
          ext t; simp [E, and_comm]
        rw [hinter]
        have hedge : g p.1.1 p.1.2 = true :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp_ag).1).1).2.2
        have hcol := (Finset.mem_filter.mp hp_ag).2
        exact pairBucket_err_of_same_col g f c0 a0 b0 u v w hf p hedge hcol
  have hge' : (∑ i : Fin (s + 1), (E ∩ gridBucket i).card) + (∑ p ∈ P_agree, (E ∩ pairBucket p).card) ≤ E.card :=
    hge
  change Ebad.card ≤ E.card
  omega

private lemma quad_err_ub_raw {s : ℕ}
    (g : Fin (s + 1) → Fin (s + 1) → Bool) (c : Fin (s + 1) → Fin 3) :
    let col : Var s → ZMod 2 × ZMod 2 := fun q =>
      match q with
      | .grid i _ _ => colorVec (c i)
      | .nzAux i _ _ => otherColor (c i)
      | .nzAnc _ _ _ => (0, 0)
      | .hAnc _ _ _ => (0, 0)
      | .vAnc _ _ _ => (0, 0)
      | .pairSlack p => if g p.1.1 p.1.2 = true then (0, 0) else colorVec (c p.1.1)
    let v : Var s → ZMod 2 := fun q => (col q).1
    let w : Var s → ZMod 2 := fun q => (col q).2
    let u : Var s → ZMod 2 := fun q => v q * w q
    ∀ (f : Ex s → Bool),
      (∀ t, b2z (f t) = quadEval 0 0 0 u v w (exSupp t)) →
      ((Finset.univ : Finset (Ex s)).filter (fun t => f t ≠ labelRaw g t)).card =
      (((Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).filter
        (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).filter (fun p => c p.1 = c p.2)).card := by
  intro col v w u f hf
  have hcol_vw : ∀ q, (v q, w q) = col q := fun _ => rfl
  let S : Finset (Ex s) :=
    ((Finset.univ : Finset (PairLt s)).filter (fun p => g p.1.1 p.1.2 = true ∧ c p.1.1 = c p.1.2)).image
      (fun p => Ex.pairEx p 3)
  have hset : (Finset.univ : Finset (Ex s)).filter (fun t => f t ≠ labelRaw g t) = S := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, Finset.mem_image]
    have hiff : f t ≠ labelRaw g t ↔ b2z (f t) ≠ b2z (labelRaw g t) :=
      ⟨fun h1 h2 => h1 (b2z_injective h2), fun h1 h2 => h1 (congrArg b2z h2)⟩
    rw [hiff, hf t]
    cases t with
    | nzEx i r c' b1 b2 =>
      cases b1 <;> cases b2
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.nzAux i r c' ≠ Var.nzAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.grid i r c' ≠ Var.nzAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_three v w
          (by simp : Var.grid i r c' ≠ Var.nzAux i r c')
          (by simp : Var.grid i r c' ≠ Var.nzAnc i r c')
          (by simp : Var.nzAux i r c' ≠ Var.nzAnc i r c'),
          hcol_vw, col, det2_zero_right, det2_colorVec_otherColor, labelRaw, askRaw, baseRaw, b2z]
    | hEqEx i r c' b1 b2 =>
      have hne_c : Var.grid i r c'.castSucc ≠ Var.grid i r c'.succ := by
        intro h; have := congrArg Fin.val (Var.grid.inj h).2.2; simp at this
      cases b1 <;> cases b2
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.grid i r c'.succ ≠ Var.hAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.grid i r c'.castSucc ≠ Var.hAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_three v w hne_c
          (by simp : Var.grid i r c'.castSucc ≠ Var.hAnc i r c')
          (by simp : Var.grid i r c'.succ ≠ Var.hAnc i r c'),
          hcol_vw, col, det2_zero_right, det2_self, labelRaw, askRaw, baseRaw, b2z]
    | vEqEx i r c' b1 b2 =>
      have hne_r : Var.grid i r.castSucc c' ≠ Var.grid i r.succ c' := by
        intro h; have := congrArg Fin.val (Var.grid.inj h).2.1; simp at this
      cases b1 <;> cases b2
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.grid i r.succ c' ≠ Var.vAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_two v w (by simp : Var.grid i r.castSucc c' ≠ Var.vAnc i r c'),
          hcol_vw, col, det2_zero_right, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_three v w hne_r
          (by simp : Var.grid i r.castSucc c' ≠ Var.vAnc i r c')
          (by simp : Var.grid i r.succ c' ≠ Var.vAnc i r c'),
          hcol_vw, col, det2_zero_right, det2_self, labelRaw, askRaw, baseRaw, b2z]
    | pairEx p k =>
      rcases k with ⟨kv, hkv⟩
      interval_cases kv
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · simp [u, exSupp, quadEval_clean_one, labelRaw, askRaw, baseRaw, b2z]
      · have hne_xy : Var.grid p.1.1 0 p.1.2 ≠ Var.grid p.1.2 0 p.1.1 :=
          fun h => (ne_of_lt p.2) (Var.grid.inj h).1
        have hne_xs : Var.grid p.1.1 0 p.1.2 ≠ Var.pairSlack p := by simp
        have hne_ys : Var.grid p.1.2 0 p.1.1 ≠ Var.pairSlack p := by simp
        simp only [u, exSupp, quadEval_clean_three v w hne_xy hne_xs hne_ys,
          hcol_vw, labelRaw, askRaw, ↓reduceIte, Option.elim_some]
        cases hgp : g p.1.1 p.1.2
        · simp only [col, hgp, Bool.false_eq_true, ↓reduceIte, det2_self, add_zero, b2z]
          have h0 : det2 (colorVec (c p.1.1)) (colorVec (c p.1.2)) +
              det2 (colorVec (c p.1.2)) (colorVec (c p.1.1)) = 0 := by
            rw [det2_comm (colorVec (c p.1.2)), z2_add_self]
          simp [h0, hgp]
        · simp only [col, hgp, ↓reduceIte, det2_zero_right, add_zero, b2z,
            det2_colorVec_eq_decide]
          by_cases hceq : c p.1.1 = c p.1.2
          · simp only [hceq, ↓reduceIte]
            exact ⟨fun _ => ⟨p, ⟨hgp, hceq⟩, rfl⟩, fun _ => by decide⟩
          · simp only [hceq, ↓reduceIte, ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
            intro p' hp' heq
            have hp_eq : p' = p := (Ex.pairEx.inj heq).1
            rw [hp_eq] at hp'
            exact hceq hp'.2
  rw [hset, Finset.card_image_of_injective _ (fun p1 p2 h => (Ex.pairEx.inj h).1)]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hg, hc⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2, hg⟩, hc⟩
  · intro p1 _ p2 _ h; exact Subtype.ext h
  · intro q hq
    obtain ⟨hq1, hc⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hlt, hg⟩ := Finset.mem_filter.mp hq1
    exact ⟨⟨q, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, hc⟩, rfl⟩

/-! ### Section 6: Final Transfer to `Fin n` / `Fin m` for Any `k : ℕ` -/

private lemma main_succ (s : ℕ) :
    let k := s + 1
    let K := Fin k
    let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
      (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)
    let defect := fun (g : K → K → Bool) (c : K → Fin 3) =>
      ((edges g).filter (fun p => c p.1 = c p.2)).card
    ∃ n m B : ℕ, n ≤ 64 * (k + 1) ^ 3 ∧ m ≤ 128 * (k + 1) ^ 3 ∧
      ∃ (X : Fin m → Fin n → Bool) (base : Fin m → Bool)
        (ask : Fin m → Option (K × K)) (decode : Circuit → K → Fin 3),
        Function.Injective X ∧
        (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun j => X t j)).card ≤ 3) ∧
        (∀ j, ((Finset.univ : Finset (Fin m)).filter (fun t => X t j)).card ≤ 36) ∧
        (∀ t i j, ask t = some (i, j) → i < j) ∧
        (∀ i j : K, i < j → ∃! t, ask t = some (i, j)) ∧
        ∀ g : K → K → Bool,
          let label := fun t => (ask t).elim (base t) (fun p => g p.1 p.2)
          let err := fun (C : Circuit) => ((Finset.univ : Finset (Fin m)).filter
            (fun t => C.eval (List.ofFn (X t)) ≠ label t)).card
          (∀ C, fitsAux n 0 C → B + (edges g).card ≤ err C) ∧
          (∃ C, fitsAux n 0 C ∧ err C = B + (edges g).card) ∧
          (∀ C, fitsAux n 1 C → defect g (decode C) ≤ err C) ∧
          ∀ c : K → Fin 3, ∃ C, fitsAux n 1 C ∧ err C = defect g c := by
  intro k K edges defect
  let n := Fintype.card (Var s)
  let m := Fintype.card (Ex s)
  let B := k ^ 3
  let eV : Var s ≃ Fin n := Fintype.equivFin (Var s)
  let eE : Ex s ≃ Fin m := Fintype.equivFin (Ex s)
  let X : Fin m → Fin n → Bool := fun t j => XRaw (eE.symm t) (eV.symm j)
  let base : Fin m → Bool := fun t => baseRaw (eE.symm t)
  let ask : Fin m → Option (K × K) := fun t => askRaw (eE.symm t)
  let decode : Circuit → K → Fin 3 := fun C =>
    @dite _ (fitsAux n 1 C) (Classical.propDecidable _)
      (fun hC =>
        let hq := fits_one_quad hC
        let vFin := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hq))))
        let wFin := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hq)))))
        decodeVW (fun q => vFin (eV q)) (fun q => wFin (eV q)))
      (fun _ => fun _ => ⟨0, by decide⟩)
  refine ⟨n, m, B, card_var_le s, card_ex_le s, X, base, ask, decode, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Injective X
    intro t1 t2 h
    apply eE.symm.injective
    apply XRaw_injective
    funext q
    have hq := congrFun h (eV q)
    simpa [X] using hq
  · -- Weight ≤ 3
    intro t
    have hcard : ((Finset.univ : Finset (Fin n)).filter (fun j => X t j)).card =
        (exSupp (eE.symm t)).card := by
      refine Finset.card_bij (fun j _ => eV.symm j) ?_ ?_ ?_
      · intro j hj
        simpa [X, XRaw] using (Finset.mem_filter.mp hj).2
      · intro j1 _ j2 _ h; exact eV.symm.injective h
      · intro q hq
        exact ⟨eV q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [X, XRaw] using hq⟩, by simp⟩
    rw [hcard]
    exact exSupp_card_le (eE.symm t)
  · -- Degree ≤ 36
    intro j
    have hcard : ((Finset.univ : Finset (Fin m)).filter (fun t => X t j)).card =
        ((Finset.univ : Finset (Ex s)).filter (fun t => XRaw t (eV.symm j))).card := by
      refine Finset.card_bij (fun t _ => eE.symm t) ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
      · intro t1 _ t2 _ h; exact eE.symm.injective h
      · intro t ht
        exact ⟨eE t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [X] using (Finset.mem_filter.mp ht).2⟩, by simp⟩
    rw [hcard]
    exact XRaw_deg_le (eV.symm j)
  · -- ask t = some (i, j) → i < j
    intro t i j h
    exact askRaw_lt (eE.symm t) i j h
  · -- ∃! t, ask t = some (i, j)
    intro i j hij
    obtain ⟨t0, ht0, huniq⟩ := askRaw_existsUnique i j hij
    refine ⟨eE t0, by simpa [ask] using ht0, fun t ht => ?_⟩
    have := huniq (eE.symm t) ht
    rw [← this, Equiv.apply_symm_apply]
  · -- Error bounds for every graph g
    intro g label err
    have herr_eq : ∀ C : Circuit,
        err C = ((Finset.univ : Finset (Ex s)).filter
          (fun t => C.eval (List.ofFn (fun j : Fin n => XRaw t (eV.symm j))) ≠ labelRaw g t)).card := by
      intro C
      refine Finset.card_bij (fun t _ => eE.symm t) ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
      · intro t1 _ t2 _ h; exact eE.symm.injective h
      · intro t ht
        exact ⟨eE t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [X, label, labelRaw, ask, base] using (Finset.mem_filter.mp ht).2⟩, by simp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) 0-AND lower bound
      intro C hC
      obtain ⟨c0, uFin, hu⟩ := fits_zero_affine hC
      rw [herr_eq C]
      refine affine_err_lb_raw g (fun t => C.eval (List.ofFn (fun j => XRaw t (eV.symm j)))) c0
        (fun q => uFin (eV q)) (fun t => ?_)
      rw [hu (fun j => XRaw t (eV.symm j))]
      have hlin : ∑ j : Fin n, uFin j * b2z (XRaw t (eV.symm j)) = ∑ q ∈ exSupp t, uFin (eV q) := by
        rw [← Fintype.sum_equiv eV (fun q => uFin (eV q) * b2z (XRaw t q))
          (fun j => uFin j * b2z (XRaw t (eV.symm j))) (fun q => by simp)]
        rw [← Finset.sum_subset (Finset.subset_univ (exSupp t))]
        · refine Finset.sum_congr rfl fun q hq => by simp [XRaw, hq, b2z]
        · intro q _ hq; simp [XRaw, hq, b2z]
      simp [quadEval, hlin]
    · -- (2) 0-AND upper bound
      refine ⟨constFalseCirc n, constFalseCirc_fits n, ?_⟩
      rw [herr_eq (constFalseCirc n)]
      simp only [constFalseCirc_eval]
      exact const_false_err_eq_raw g
    · -- (3) 1-AND lower bound
      intro C hC
      rw [herr_eq C]
      have hq := fits_one_quad hC
      let c0 := Classical.choose hq
      let h1 := Classical.choose_spec hq
      let a0 := Classical.choose h1
      let h2 := Classical.choose_spec h1
      let b0 := Classical.choose h2
      let h3 := Classical.choose_spec h2
      let uFin := Classical.choose h3
      let h4 := Classical.choose_spec h3
      let vFin := Classical.choose h4
      let h5 := Classical.choose_spec h4
      let wFin := Classical.choose h5
      have hspec : ∀ x : Fin n → Bool, b2z (C.eval (List.ofFn x)) =
          c0 + ∑ j : Fin n, uFin j * b2z (x j) +
            (a0 + ∑ j : Fin n, vFin j * b2z (x j)) * (b0 + ∑ j : Fin n, wFin j * b2z (x j)) :=
        Classical.choose_spec h5
      have hdec_eq : decode C = decodeVW (fun q => vFin (eV q)) (fun q => wFin (eV q)) := by
        simp only [decode, hC, ↓reduceDIte]
        rfl
      rw [hdec_eq]
      refine quad_err_lb_raw g (fun t => C.eval (List.ofFn (fun j => XRaw t (eV.symm j))))
        c0 a0 b0 (fun q => uFin (eV q)) (fun q => vFin (eV q)) (fun q => wFin (eV q)) (fun t => ?_)
      rw [hspec (fun j => XRaw t (eV.symm j))]
      have hlin : ∀ hF : Fin n → ZMod 2,
          ∑ j : Fin n, hF j * b2z (XRaw t (eV.symm j)) = ∑ q ∈ exSupp t, hF (eV q) := fun hF => by
        rw [← Fintype.sum_equiv eV (fun q => hF (eV q) * b2z (XRaw t q))
          (fun j => hF j * b2z (XRaw t (eV.symm j))) (fun q => by simp)]
        rw [← Finset.sum_subset (Finset.subset_univ (exSupp t))]
        · refine Finset.sum_congr rfl fun q hq => by simp [XRaw, hq, b2z]
        · intro q _ hq; simp [XRaw, hq, b2z]
      simp only [quadEval, hlin uFin, hlin vFin, hlin wFin]
    · -- (4) 1-AND upper bound
      intro c
      let col : Var s → ZMod 2 × ZMod 2 := fun q =>
        match q with
        | .grid i _ _ => colorVec (c i)
        | .nzAux i _ _ => otherColor (c i)
        | .nzAnc _ _ _ => (0, 0)
        | .hAnc _ _ _ => (0, 0)
        | .vAnc _ _ _ => (0, 0)
        | .pairSlack p => if g p.1.1 p.1.2 = true then (0, 0) else colorVec (c p.1.1)
      let v : Var s → ZMod 2 := fun q => (col q).1
      let w : Var s → ZMod 2 := fun q => (col q).2
      let u : Var s → ZMod 2 := fun q => v q * w q
      obtain ⟨C, hCfits, hCeval⟩ := build_quad_circuit (fun j : Fin n => u (eV.symm j))
        (fun j : Fin n => v (eV.symm j)) (fun j : Fin n => w (eV.symm j))
      refine ⟨C, hCfits, ?_⟩
      rw [herr_eq C]
      refine quad_err_ub_raw g c (fun t => C.eval (List.ofFn (fun j => XRaw t (eV.symm j)))) (fun t => ?_)
      rw [hCeval (fun j => XRaw t (eV.symm j))]
      have hlin : ∀ hV : Var s → ZMod 2,
          ∑ j : Fin n, hV (eV.symm j) * b2z (XRaw t (eV.symm j)) = ∑ q ∈ exSupp t, hV q := fun hV => by
        rw [← Fintype.sum_equiv eV (fun q => hV q * b2z (XRaw t q))
          (fun j => hV (eV.symm j) * b2z (XRaw t (eV.symm j))) (fun q => by simp)]
        rw [← Finset.sum_subset (Finset.subset_univ (exSupp t))]
        · refine Finset.sum_congr rfl fun q hq => by simp [XRaw, hq, b2z]
        · intro q _ hq; simp [XRaw, hq, b2z]
      simp only [quadEval, zero_add, hlin u, hlin v, hlin w]
      rfl

end PEqualNP.Outside.L_meta_33663_aux

open PEqualNP.Outside.L_meta_33663_aux in
theorem PEqualNP.Outside.L_meta_33663 :
    ∀ k : ℕ,
      let K := Fin k
      let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
        (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)
      let defect := fun (g : K → K → Bool) (c : K → Fin 3) =>
        ((edges g).filter (fun p => c p.1 = c p.2)).card
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let fits := fun (n b : ℕ) (C : Circ) =>
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))) ∧
        C.gates.countP (fun h => @decide
          ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ b
      ∃ n m B : ℕ, n ≤ 64*(k+1)^3 ∧ m ≤ 128*(k+1)^3 ∧
        ∃ (X : Fin m → Fin n → Bool) (base : Fin m → Bool)
          (ask : Fin m → Option (K × K)) (decode : Circ → K → Fin 3),
          Function.Injective X ∧
          (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun j => X t j)).card ≤ 3) ∧
          (∀ j, ((Finset.univ : Finset (Fin m)).filter (fun t => X t j)).card ≤ 36) ∧
          (∀ t i j, ask t = some (i,j) → i < j) ∧
          (∀ i j : K, i < j → ∃! t, ask t = some (i,j)) ∧
          ∀ g : K → K → Bool,
            let label := fun t => (ask t).elim (base t) (fun p => g p.1 p.2)
            let err := fun (C : Circ) => ((Finset.univ : Finset (Fin m)).filter
              (fun t => C.eval (List.ofFn (X t)) ≠ label t)).card
            (∀ C, fits n 0 C → B+(edges g).card ≤ err C) ∧
            (∃ C, fits n 0 C ∧ err C = B+(edges g).card) ∧
            (∀ C, fits n 1 C → defect g (decode C) ≤ err C) ∧
            ∀ c : K → Fin 3, ∃ C, fits n 1 C ∧ err C = defect g c := by
  intro k
  cases k with
  | zero =>
    refine ⟨0, 0, 0, by decide, by decide, fun t => t.elim0, fun t => t.elim0,
      fun t => t.elim0, fun _ i => i.elim0,
      fun t => t.elim0, fun t => t.elim0, fun j => j.elim0,
      fun t => t.elim0, fun i => i.elim0, fun g => ?_⟩
    refine ⟨fun _ _ => by simp,
      ⟨constFalseCirc 0, constFalseCirc_fits 0, by simp⟩,
      fun _ _ => by simp,
      fun _ => ⟨constFalseCirc 0, ⟨(constFalseCirc_fits 0).1, (constFalseCirc_fits 0).2.1,
        le_trans (constFalseCirc_fits 0).2.2 (by decide)⟩, by simp⟩⟩
  | succ s =>
    exact main_succ s
