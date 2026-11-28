import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53189
open PEqualNP.CircuitLowerBounds
section Q
variable {n : ℕ}
def fl (y : Finset (Fin n)) (u : Fin n) : Finset (Fin n) := symmDiff y {u}
theorem fl_fl (y : Finset (Fin n)) (u : Fin n) : fl (fl y u) u = y := by
  simp [fl, symmDiff_symmDiff_cancel_right]
theorem dfl (y : Finset (Fin n)) (u a : Fin n) :
    decide (a ∈ fl y u) = (decide (a ∈ y) ^^ decide (a = u)) := by
  by_cases h1 : a ∈ y <;> by_cases h2 : a = u <;> simp [fl, Finset.mem_symmDiff, h1, h2]
theorem ins_fl (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s) : insert a s = fl s a := by
  ext x
  by_cases hx : x = a
  · subst hx; simp [fl, Finset.mem_symmDiff, ha]
  · simp [fl, Finset.mem_symmDiff, hx]
def d1 (h : Finset (Fin n) → Bool) (u : Fin n) (y : Finset (Fin n)) : Bool := h y ^^ h (fl y u)
def d2 (h : Finset (Fin n) → Bool) (u v : Fin n) (y : Finset (Fin n)) : Bool :=
  d1 h u y ^^ d1 h u (fl y v)
def Qp (h : Finset (Fin n) → Bool) : Prop := ∀ u v, u ≠ v → ∀ y, d2 h u v y = d2 h u v ∅
theorem x8 : ∀ a1 a2 a3 a4 b1 b2 b3 b4 : Bool,
    (((a1 ^^ b1) ^^ (a2 ^^ b2)) ^^ ((a3 ^^ b3) ^^ (a4 ^^ b4))) =
      (((a1 ^^ a2) ^^ (a3 ^^ a4)) ^^ ((b1 ^^ b2) ^^ (b3 ^^ b4))) := by decide
theorem d2_xor (f g : Finset (Fin n) → Bool) (u v : Fin n) (y : Finset (Fin n)) :
    d2 (fun z => f z ^^ g z) u v y = (d2 f u v y ^^ d2 g u v y) := by
  simp only [d2, d1]
  exact x8 _ _ _ _ _ _ _ _
theorem Qp_xor (f g : Finset (Fin n) → Bool) (hf : Qp f) (hg : Qp g) : Qp (fun z => f z ^^ g z) := by
  intro u v huv y
  rw [d2_xor, d2_xor, hf u v huv y, hg u v huv y]
theorem jun_core (φ : Bool → Bool → Bool) (p q p' q' α1 α2 β1 β2 : Bool) :
    ((φ p q ^^ φ (p ^^ α1) (q ^^ β1)) ^^ (φ (p ^^ α2) (q ^^ β2) ^^ φ ((p ^^ α2) ^^ α1) ((q ^^ β2) ^^ β1))) =
    ((φ p' q' ^^ φ (p' ^^ α1) (q' ^^ β1)) ^^ (φ (p' ^^ α2) (q' ^^ β2) ^^ φ ((p' ^^ α2) ^^ α1) ((q' ^^ β2) ^^ β1))) := by
  obtain ⟨w0, w1, w2, w3, hφ⟩ : ∃ w0 w1 w2 w3 : Bool, φ = fun p q => cond p (cond q w3 w2) (cond q w1 w0) :=
    ⟨φ false false, φ false true, φ true false, φ true true, by funext p q; cases p <;> cases q <;> rfl⟩
  subst hφ
  revert p q p' q' α1 α2 β1 β2 w0 w1 w2 w3
  decide
theorem junta_Q (φ : Bool → Bool → Bool) (a b : Fin n) :
    Qp (fun y => φ (decide (a ∈ y)) (decide (b ∈ y))) := by
  intro u v _ y
  simp only [d2, d1, dfl]
  exact jun_core φ _ _ _ _ _ _ _ _
theorem const_Q (c : Bool) : Qp (fun _ : Finset (Fin n) => c) := by
  intro u v _ y
  simp [d2, d1]
theorem count4 (h : Finset (Fin n) → Bool) (u v : Fin n)
    (key : ∀ y, h y = true ∨ h (fl y u) = true ∨ h (fl y v) = true ∨ h (fl (fl y v) u) = true) :
    Fintype.card (Finset (Fin n)) ≤ 4 * (Finset.univ.filter (fun y => h y = true)).card := by
  classical
  set D := Finset.univ.filter (fun y => h y = true)
  have hsub : (Finset.univ : Finset (Finset (Fin n))) ⊆
      ((D ∪ D.image (fun z => fl z u)) ∪ D.image (fun z => fl z v)) ∪ D.image (fun z => fl (fl z u) v) := by
    intro y _
    rcases key y with h1 | h1 | h1 | h1
    · simp [D, h1]
    · apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨fl y u, by simp [D, h1], fl_fl y u⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨fl y v, by simp [D, h1], fl_fl y v⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨fl (fl y v) u, by simp [D, h1], by rw [fl_fl, fl_fl]⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  have c1 := Finset.card_union_le (D ∪ D.image (fun z => fl z u) ∪ D.image (fun z => fl z v)) (D.image (fun z => fl (fl z u) v))
  have c2 := Finset.card_union_le (D ∪ D.image (fun z => fl z u)) (D.image (fun z => fl z v))
  have c3 := Finset.card_union_le D (D.image (fun z => fl z u))
  have i1 := Finset.card_image_le (s := D) (f := fun z => fl z u)
  have i2 := Finset.card_image_le (s := D) (f := fun z => fl z v)
  have i3 := Finset.card_image_le (s := D) (f := fun z => fl (fl z u) v)
  omega
theorem cover (h : Finset (Fin n) → Bool) (hq : Qp h) (hne : ∃ z, h z = true) :
    Fintype.card (Finset (Fin n)) ≤ 4 * (Finset.univ.filter (fun y => h y = true)).card := by
  classical
  by_cases H2 : ∃ u v, u ≠ v ∧ d2 h u v ∅ = true
  · obtain ⟨u, v, huv, hd⟩ := H2
    apply count4 h u v
    intro y
    have := hq u v huv y
    rw [hd] at this
    simp only [d2, d1] at this
    revert this
    cases h y <;> cases h (fl y u) <;> cases h (fl y v) <;> cases h (fl (fl y v) u) <;> simp
  · have H2' : ∀ u v y, d1 h u (fl y v) = d1 h u y := by
      intro u v y
      by_cases huv : u = v
      · subst huv
        simp only [d1, fl_fl]
        exact Bool.xor_comm _ _
      · have e := hq u v huv y
        have h0 : d2 h u v ∅ = false := by
          by_contra hc
          exact H2 ⟨u, v, huv, by simpa using hc⟩
        rw [h0] at e
        simp only [d2] at e
        revert e
        cases d1 h u y <;> cases d1 h u (fl y v) <;> simp
    have H1 : ∀ u y, d1 h u y = d1 h u ∅ := by
      intro u y
      induction y using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => rw [ins_fl s a ha, H2', ih]
    by_cases H1' : ∃ u, d1 h u ∅ = true
    · obtain ⟨u, hu⟩ := H1'
      apply count4 h u u
      intro y
      have := H1 u y
      rw [hu] at this
      simp only [d1] at this
      revert this
      cases h y <;> cases h (fl y u) <;> simp
    · have hc : ∀ u y, h (fl y u) = h y := by
        intro u y
        have e := H1 u y
        have h0 : d1 h u ∅ = false := by
          by_contra hc
          exact H1' ⟨u, by simpa using hc⟩
        rw [h0] at e
        simp only [d1] at e
        revert e
        cases h y <;> cases h (fl y u) <;> simp
      have hk : ∀ y, h y = h ∅ := by
        intro y
        induction y using Finset.induction_on with
        | empty => rfl
        | insert a s ha ih => rw [ins_fl s a ha, hc, ih]
      obtain ⟨z, hz⟩ := hne
      have hall : Finset.univ.filter (fun y => h y = true) = Finset.univ := by
        ext y; simp [hk y, ← hk z, hz]
      rw [hall, Finset.card_univ]
      omega
theorem exists_sep (F : Finset (Finset (Fin n) → Bool)) (r : ℕ)
    (hF : ∀ f ∈ F, ∀ g ∈ F, f ≠ g →
      Fintype.card (Finset (Fin n)) ≤ 4 * (Finset.univ.filter (fun y => (f y ^^ g y) = true)).card)
    (hr : F.card ^ 2 * 3 ^ r < 4 ^ r) :
    ∃ t : Fin r → Finset (Fin n), ∀ f ∈ F, ∀ g ∈ F, f ≠ g → ∃ k, f (t k) ≠ g (t k) := by
  classical
  by_contra H
  simp only [not_exists, not_forall, not_and, exists_prop, not_not] at H
  set N := Fintype.card (Finset (Fin n))
  have hN : 0 < N := Fintype.card_pos
  set P := (F ×ˢ F).filter (fun p => p.1 ≠ p.2)
  set ag := fun p : (Finset (Fin n) → Bool) × (Finset (Fin n) → Bool) =>
    Finset.univ.filter (fun y => p.1 y = p.2 y)
  set B := P.biUnion (fun p => Fintype.piFinset (fun _ : Fin r => ag p))
  have h1 : (Finset.univ : Finset (Fin r → Finset (Fin n))) ⊆ B := by
    intro t _
    obtain ⟨f, hf, g, hg, hfg, hk⟩ := H t
    simp only [B, Finset.mem_biUnion, Fintype.mem_piFinset]
    exact ⟨(f, g), by simp [P, hf, hg, hfg], fun k => by simp [ag, hk k]⟩
  have h1' := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1'
  have h2 : B.card ≤ ∑ p ∈ P, (ag p).card ^ r := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => ?_)
    rw [Fintype.card_piFinset]
    simp
  have h3 : ∀ p ∈ P, 4 ^ r * (ag p).card ^ r ≤ 3 ^ r * N ^ r := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_product] at hp
    have hd := hF p.1 hp.1.1 p.2 hp.1.2 hp.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Finset (Fin n)))) (fun y => p.1 y = p.2 y)
    have hdis : Finset.univ.filter (fun y => (p.1 y ^^ p.2 y) = true) =
        Finset.univ.filter (fun y => ¬ (p.1 y = p.2 y)) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases p.1 y <;> cases p.2 y <;> simp
    rw [hdis] at hd
    rw [Finset.card_univ] at hsplit
    have h4 : 4 * (ag p).card ≤ 3 * N := by simp only [ag]; omega
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left h4 r
  have h5 : 4 ^ r * B.card ≤ P.card * (3 ^ r * N ^ r) := by
    calc 4 ^ r * B.card ≤ 4 ^ r * ∑ p ∈ P, (ag p).card ^ r := Nat.mul_le_mul_left _ h2
      _ = ∑ p ∈ P, 4 ^ r * (ag p).card ^ r := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ P, 3 ^ r * N ^ r := Finset.sum_le_sum h3
      _ = P.card * (3 ^ r * N ^ r) := by rw [Finset.sum_const, smul_eq_mul]
  have h6 : P.card ≤ F.card ^ 2 := by
    calc P.card ≤ (F ×ˢ F).card := Finset.card_filter_le _ _
      _ = F.card ^ 2 := by rw [Finset.card_product, sq]
  have hNr : 0 < N ^ r := Nat.pow_pos hN
  have h7 : P.card * (3 ^ r * N ^ r) < 4 ^ r * N ^ r := by
    calc P.card * (3 ^ r * N ^ r) ≤ F.card ^ 2 * (3 ^ r * N ^ r) := Nat.mul_le_mul_right _ h6
      _ = (F.card ^ 2 * 3 ^ r) * N ^ r := by ring
      _ < 4 ^ r * N ^ r := Nat.mul_lt_mul_of_pos_right hr hNr
  have h8 : 4 ^ r * N ^ r ≤ 4 ^ r * B.card := Nat.mul_le_mul_left _ h1'
  omega
end Q
section Circ
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Wr (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : Wr (gs ++ [g]) x = stp (Wr gs x) g := by
  simp [Wr, List.foldl_append]
theorem W_len (gs : List Gate) (x : List Bool) : (Wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Wr]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega
theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]
theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (Wr gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [Wr]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih
theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (Wr (gs ++ [g]) x).getD i false = (Wr gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]
theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (Wr gs x).getD i false = (Wr (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]
theorem eval_mono (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hle : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases h with h | h <;> rw [h] at hv ⊢
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at hv ⊢
    intro i hi; exact hle i hi (hv i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨v, ⟨i, hi, rfl⟩, hv⟩ := hv
    exact ⟨true, ⟨i, hi, hle i hi hv⟩, rfl⟩
theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (X Y : List Bool)
    (hl : X.length = Y.length)
    (hle : ∀ i, X.getD i false = true → Y.getD i false = true) :
    ∀ i, (Wr gs X).getD i false = true → (Wr gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [Wr] using hle
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro i
    rw [W_snoc, W_snoc]
    unfold stp
    have e1 : (Wr gs X).length = X.length + gs.length := W_len _ _
    have e2 : (Wr gs Y).length = X.length + gs.length := by rw [W_len, hl]
    rcases lt_trichotomy i (X.length + gs.length) with h | h | h
    · rw [getD_app_l _ _ _ (by omega), getD_app_l _ _ _ (by omega)]; exact ih' i
    · subst h
      have a1 := getD_app_m (Wr gs X) (g.op.eval (g.inputs.map fun i => (Wr gs X).getD i false))
      have a2 := getD_app_m (Wr gs Y) (g.op.eval (g.inputs.map fun i => (Wr gs Y).getD i false))
      rw [e1] at a1
      rw [e2] at a2
      rw [a1, a2]
      exact eval_mono g (hm g (by simp)) _ _ (fun k _ => ih' k)
    · rw [getD_big _ _ (by simp [e1]; omega)]
      intro hf
      exact absurd hf (by decide)
def Good (N : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length),
  ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) ∧ (gs[j]).inputs.length ≤ 2 ∧
    ∀ i ∈ (gs[j]).inputs, i < N + j
theorem good_nil (N : ℕ) : Good N [] := fun j hj => absurd hj (by simp)
theorem good_snoc (N : ℕ) (gs : List Gate) (g : Gate) (hg : Good N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (hi : ∀ i ∈ g.inputs, i < N + gs.length) : Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j gs.length with h | h
  · rw [List.getElem_append_left h]; exact hg j h
  · have : j = gs.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact ⟨hop, hl, hi⟩
theorem W_ext (gs gs' : List Gate) (h : ∃ t, gs' = gs ++ t) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : (Wr gs' x).getD i false = (Wr gs x).getD i false := by
  rw [W_take gs' x gs.length i hi]
  obtain ⟨t, rfl⟩ := h
  simp
theorem len_ext (gs gs' : List Gate) (h : ∃ t, gs' = gs ++ t) : gs.length ≤ gs'.length := by
  obtain ⟨t, rfl⟩ := h
  simp
theorem ext_tr {a b c : List Gate} (h1 : ∃ t, b = a ++ t) (h2 : ∃ t, c = b ++ t) : ∃ t, c = a ++ t := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t1 ++ t2, by simp⟩
theorem W_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (Wr (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (Wr gs x).getD i false) := by
  rw [W_snoc, stp]
  have := getD_app_m (Wr gs x) (g.op.eval (g.inputs.map fun i => (Wr gs x).getD i false))
  rw [W_len] at this
  exact this
theorem good_circ (N : ℕ) (gs : List Gate) (o : ℕ) (hg : Good N gs) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs, o⟩ ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, o⟩ := by
  constructor
  · intro g hgm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
    obtain ⟨h1, h2, _⟩ := hg j hj
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> rw [h] <;> simp
  · intro j hj i hi
    rw [gateAt_eq ⟨gs, o⟩ j hj] at hi
    exact (hg j hj).2.2 i hi
end Circ
section Fns
variable {n : ℕ}
def bt (i : Fin n) (x : Finset (Fin n)) : Bool := decide (i ∈ x)
def ng (i : Fin n) (x : Finset (Fin n)) : Bool := !(decide (i ∈ x))
def sm (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := (decide (e.1 ∈ x) == decide (e.2 ∈ x))
def ns (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x) == decide (e.2 ∈ x))
def k1 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x)) && !(decide (e.2 ∈ x))
def k2 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := decide (e.1 ∈ x) && !(decide (e.2 ∈ x))
def k3 (e : Fin n × Fin n) (x : Finset (Fin n)) : Bool := !(decide (e.1 ∈ x)) && decide (e.2 ∈ x)
theorem b1 : ∀ p q : Bool, ((!p) && (p == q)) = ((!p) && !q) := by decide
theorem b2 : ∀ p q : Bool, (p && !(p == q)) = (p && !q) := by decide
theorem b3 : ∀ p q : Bool, ((!p) && !(p == q)) = ((!p) && q) := by decide
theorem b4 : ∀ p q : Bool, (((!p) && !q) || (p && !q)) = !q := by decide
theorem b5 : ∀ p q : Bool, ((!q) && (p == q)) = ((!p) && !q) := by decide
theorem b6 : ∀ p q : Bool, ((!q) && !(p == q)) = (p && !q) := by decide
theorem b7 : ∀ p q : Bool, (q && !(p == q)) = ((!p) && q) := by decide
theorem b8 : ∀ p q : Bool, (((!p) && !q) || ((!p) && q)) = !p := by decide
end Fns
section Build
variable {n : ℕ} (N : ℕ) (inp : Finset (Fin n) → List Bool)
def Av (gs : List Gate) (f : Finset (Fin n) → Bool) : Prop :=
  ∃ w < N + gs.length, ∀ x, (Wr gs (inp x)).getD w false = f x
theorem av_ext (hinp : ∀ x, (inp x).length = N) {gs gs' : List Gate} (h : ∃ t, gs' = gs ++ t)
    {f : Finset (Fin n) → Bool} (hf : Av N inp gs f) : Av N inp gs' f := by
  obtain ⟨w, hw, hv⟩ := hf
  have := len_ext gs gs' h
  refine ⟨w, by omega, fun x => ?_⟩
  rw [W_ext gs gs' h (inp x) w (by rw [hinp]; exact hw)]
  exact hv x
theorem av_congr {gs : List Gate} {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f)
    (e : ∀ x, f x = g x) : Av N inp gs g := by
  obtain ⟨w, hw, hv⟩ := hf
  exact ⟨w, hw, fun x => (hv x).trans (e x)⟩
theorem av_gate (hinp : ∀ x, (inp x).length = N) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    {gs : List Gate} (hg : Good N gs) {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f)
    (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => op.eval [f x, g x]) := by
  obtain ⟨w1, hw1, e1⟩ := hf
  obtain ⟨w2, hw2, e2⟩ := hg'
  refine ⟨gs ++ [⟨op, [w1, w2]⟩], good_snoc _ _ _ hg hop (by simp) ?_, ⟨_, rfl⟩, by simp,
    N + gs.length, by simp, fun x => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · have := W_last gs ⟨op, [w1, w2]⟩ (inp x)
    rw [hinp] at this
    rw [this]
    simp only [List.map_cons, List.map_nil, e1, e2]
theorem av_and (hinp : ∀ x, (inp x).length = N) {gs : List Gate} (hg : Good N gs)
    {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f) (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => f x && g x) := by
  obtain ⟨gs', h1, h2, h3, h4⟩ := av_gate N inp hinp GateOp.and (Or.inl rfl) hg hf hg'
  exact ⟨gs', h1, h2, h3, av_congr N inp h4 (fun x => by simp [GateOp.eval])⟩
theorem av_or (hinp : ∀ x, (inp x).length = N) {gs : List Gate} (hg : Good N gs)
    {f g : Finset (Fin n) → Bool} (hf : Av N inp gs f) (hg' : Av N inp gs g) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧
      Av N inp gs' (fun x => f x || g x) := by
  obtain ⟨gs', h1, h2, h3, h4⟩ := av_gate N inp hinp GateOp.or (Or.inr rfl) hg hf hg'
  exact ⟨gs', h1, h2, h3, av_congr N inp h4 (fun x => by simp [GateOp.eval])⟩
variable (E : Finset (Fin n × Fin n)) (hinp : ∀ x, (inp x).length = N)
  (hb : ∀ gs i, Av N inp gs (bt i)) (hs : ∀ gs, ∀ e ∈ E, Av N inp gs (sm e))
  (hns : ∀ gs, ∀ e ∈ E, Av N inp gs (ns e))
include hinp hb hs hns in
theorem three_a {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n) (he : e ∈ E)
    (hA : Av N inp gs (ng e.1)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 3 ∧
      Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_and N inp hinp G hA (hs gs e he)
  obtain ⟨g2, G2, T2, L2, A2⟩ := av_and N inp hinp G1 (hb g1 e.1) (hns g1 e he)
  obtain ⟨g3, G3, T3, L3, A3⟩ := av_and N inp hinp G2 (av_ext N inp hinp (ext_tr T1 T2) hA) (hns g2 e he)
  refine ⟨g3, G3, ext_tr (ext_tr T1 T2) T3, by omega, ?_, ?_, ?_⟩
  · exact av_congr N inp (av_ext N inp hinp (ext_tr T2 T3) A1) (fun x => b1 _ _)
  · exact av_congr N inp (av_ext N inp hinp T3 A2) (fun x => b2 _ _)
  · exact av_congr N inp A3 (fun x => b3 _ _)
include hinp hb hs hns in
theorem three_b {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n) (he : e ∈ E)
    (hA : Av N inp gs (ng e.2)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 3 ∧
      Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_and N inp hinp G hA (hs gs e he)
  obtain ⟨g2, G2, T2, L2, A2⟩ := av_and N inp hinp G1 (av_ext N inp hinp T1 hA) (hns g1 e he)
  obtain ⟨g3, G3, T3, L3, A3⟩ := av_and N inp hinp G2 (hb g2 e.2) (hns g2 e he)
  refine ⟨g3, G3, ext_tr (ext_tr T1 T2) T3, by omega, ?_, ?_, ?_⟩
  · exact av_congr N inp (av_ext N inp hinp (ext_tr T2 T3) A1) (fun x => b5 _ _)
  · exact av_congr N inp (av_ext N inp hinp T3 A2) (fun x => b6 _ _)
  · exact av_congr N inp A3 (fun x => b7 _ _)
include hinp in
theorem one_a {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n)
    (h1 : Av N inp gs (k1 e)) (h2 : Av N inp gs (k2 e)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧ Av N inp gs' (ng e.2) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_or N inp hinp G h1 h2
  exact ⟨g1, G1, T1, L1, av_congr N inp A1 (fun x => b4 _ _)⟩
include hinp in
theorem one_b {gs : List Gate} (G : Good N gs) (e : Fin n × Fin n)
    (h1 : Av N inp gs (k1 e)) (h3 : Av N inp gs (k3 e)) :
    ∃ gs', Good N gs' ∧ (∃ t, gs' = gs ++ t) ∧ gs'.length = gs.length + 1 ∧ Av N inp gs' (ng e.1) := by
  obtain ⟨g1, G1, T1, L1, A1⟩ := av_or N inp hinp G h1 h3
  exact ⟨g1, G1, T1, L1, av_congr N inp A1 (fun x => b8 _ _)⟩
include hinp hb hs hns in
theorem build {c : ℕ} (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    (S : Finset (Fin n)) (hcov : ∀ j, ∃ i ∈ S, color i = j) :
    ∀ k (gs : List Gate) (K : Finset (Fin n)) (P : Finset (Fin n × Fin n)), (E \ P).card = k →
      Good N gs → S ⊆ K → P ⊆ E → (∀ v ∈ K, Av N inp gs (ng v)) →
      (∀ e ∈ P, Av N inp gs (k1 e) ∧ Av N inp gs (k2 e) ∧ Av N inp gs (k3 e) ∧ e.1 ∈ K ∧ e.2 ∈ K) →
      gs.length + S.card = K.card + 3 * P.card →
      ∃ gs', Good N gs' ∧ gs'.length + S.card = n + 3 * E.card ∧ (∀ v, Av N inp gs' (ng v)) ∧
        ∀ e ∈ E, Av N inp gs' (k1 e) ∧ Av N inp gs' (k2 e) ∧ Av N inp gs' (k3 e) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro gs K P hk G hSK hPE hK hP hlen
    by_cases H : ∃ e ∈ E, e ∉ P ∧ (e.1 ∈ K ∨ e.2 ∈ K)
    · obtain ⟨e, he, heP, hor⟩ := H
      have hlt : (E \ insert e P).card < k := by
        rw [← hk, Finset.sdiff_insert]
        have hm : e ∈ E \ P := Finset.mem_sdiff.mpr ⟨he, heP⟩
        rw [Finset.card_erase_of_mem hm]
        have := Finset.card_pos.mpr ⟨e, hm⟩
        omega
      have hPE' : insert e P ⊆ E := Finset.insert_subset he hPE
      by_cases h1 : e.1 ∈ K
      · obtain ⟨g1, G1, T1, L1, A1, A2, A3⟩ := three_a N inp E hinp hb hs hns G e he (hK e.1 h1)
        by_cases h2 : e.2 ∈ K
        · refine ih _ hlt g1 K (insert e P) rfl G1 hSK hPE'
            (fun v hv => av_ext N inp hinp T1 (hK v hv)) (fun e' he' => ?_)
            (by rw [Finset.card_insert_of_notMem heP]; omega)
          rcases Finset.mem_insert.mp he' with rfl | he'
          · exact ⟨A1, A2, A3, h1, h2⟩
          · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
            exact ⟨av_ext N inp hinp T1 q1, av_ext N inp hinp T1 q2, av_ext N inp hinp T1 q3, q4, q5⟩
        · obtain ⟨g2, G2, T2, L2, B⟩ := one_a N inp hinp G1 e A1 A2
          refine ih _ hlt g2 (insert e.2 K) (insert e P) rfl G2 (hSK.trans (Finset.subset_insert _ _)) hPE'
            (fun v hv => ?_) (fun e' he' => ?_)
            (by rw [Finset.card_insert_of_notMem heP, Finset.card_insert_of_notMem h2]; omega)
          · rcases Finset.mem_insert.mp hv with rfl | hv
            · exact B
            · exact av_ext N inp hinp (ext_tr T1 T2) (hK v hv)
          · rcases Finset.mem_insert.mp he' with rfl | he'
            · exact ⟨av_ext N inp hinp T2 A1, av_ext N inp hinp T2 A2, av_ext N inp hinp T2 A3,
                Finset.mem_insert_of_mem h1, Finset.mem_insert_self _ _⟩
            · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
              exact ⟨av_ext N inp hinp (ext_tr T1 T2) q1, av_ext N inp hinp (ext_tr T1 T2) q2,
                av_ext N inp hinp (ext_tr T1 T2) q3, Finset.mem_insert_of_mem q4, Finset.mem_insert_of_mem q5⟩
      · have h2 : e.2 ∈ K := by rcases hor with h | h; exact absurd h h1; exact h
        obtain ⟨g1, G1, T1, L1, A1, A2, A3⟩ := three_b N inp E hinp hb hs hns G e he (hK e.2 h2)
        obtain ⟨g2, G2, T2, L2, B⟩ := one_b N inp hinp G1 e A1 A3
        refine ih _ hlt g2 (insert e.1 K) (insert e P) rfl G2 (hSK.trans (Finset.subset_insert _ _)) hPE'
          (fun v hv => ?_) (fun e' he' => ?_)
          (by rw [Finset.card_insert_of_notMem heP, Finset.card_insert_of_notMem h1]; omega)
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact B
          · exact av_ext N inp hinp (ext_tr T1 T2) (hK v hv)
        · rcases Finset.mem_insert.mp he' with rfl | he'
          · exact ⟨av_ext N inp hinp T2 A1, av_ext N inp hinp T2 A2, av_ext N inp hinp T2 A3,
              Finset.mem_insert_self _ _, Finset.mem_insert_of_mem h2⟩
          · obtain ⟨q1, q2, q3, q4, q5⟩ := hP e' he'
            exact ⟨av_ext N inp hinp (ext_tr T1 T2) q1, av_ext N inp hinp (ext_tr T1 T2) q2,
              av_ext N inp hinp (ext_tr T1 T2) q3, Finset.mem_insert_of_mem q4, Finset.mem_insert_of_mem q5⟩
    · have hcl : ∀ e ∈ E, e.1 ∈ K ↔ e.2 ∈ K := by
        intro e he
        constructor
        · intro h1
          by_cases heP : e ∈ P
          · exact (hP e heP).2.2.2.2
          · exact absurd ⟨e, he, heP, Or.inl h1⟩ H
        · intro h2
          by_cases heP : e ∈ P
          · exact (hP e heP).2.2.2.1
          · exact absurd ⟨e, he, heP, Or.inr h2⟩ H
      have hcol := (hcomp K).mp hcl
      have hKu : ∀ v, v ∈ K := by
        intro v
        obtain ⟨i, hiS, hci⟩ := hcov (color v)
        exact (hcol i v hci).mp (hSK hiS)
      have hPu : ∀ e ∈ E, e ∈ P := by
        intro e he
        by_contra heP
        exact H ⟨e, he, heP, Or.inl (hKu e.1)⟩
      have hKc : K.card = n := by
        rw [Finset.eq_univ_of_forall hKu, Finset.card_univ, Fintype.card_fin]
      have hPE2 : P = E := Finset.Subset.antisymm hPE hPu
      refine ⟨gs, G, by rw [hlen, hKc, hPE2], fun v => hK v (hKu v), fun e he => ?_⟩
      obtain ⟨q1, q2, q3, _, _⟩ := hP e (hPu e he)
      exact ⟨q1, q2, q3⟩
end Build
section Facts
variable {n : ℕ}
theorem f_ng (i j : Fin n) (h : (ng i : Finset (Fin n) → Bool) = ng j) : i = j := by
  have h1 := congrFun h {i}
  simp [ng] at h1
  exact h1.symm
theorem f_k1 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k1 e = k1 e') : e = e' := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.2}
  simp [k1] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff] at h1 h2
  omega
theorem f_k2 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = k2 e') : e = e' := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e'.2}
  simp [k2, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_k3 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k3 e = k3 e') : e = e' := by
  have h1 := congrFun h {e.2}
  have h2 := congrFun h {e.2, e'.1}
  simp [k3, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_ng_k1 (i : Fin n) (e : Fin n × Fin n) (he : e.1 < e.2) (h : ng i = k1 e) : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.2}
  simp [ng, k1] at h1 h2
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1 h2
  omega
theorem f_ng_k2 (i : Fin n) (e : Fin n × Fin n) (h : ng i = k2 e) : False := by
  have h1 := congrFun h ∅
  simp [ng, k2] at h1
theorem f_ng_k3 (i : Fin n) (e : Fin n × Fin n) (h : ng i = k3 e) : False := by
  have h1 := congrFun h ∅
  simp [ng, k3] at h1
theorem f_k1_k2 (e e' : Fin n × Fin n) (h : k1 e = k2 e') : False := by
  have h1 := congrFun h ∅
  simp [k1, k2] at h1
theorem f_k1_k3 (e e' : Fin n × Fin n) (h : k1 e = k3 e') : False := by
  have h1 := congrFun h ∅
  simp [k1, k3] at h1
theorem f_k2_k3 (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = k3 e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e'.1}
  simp [k2, k3, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2
  omega
theorem f_k2_ns (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k2 e = ns e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e.2}
  have h3 := congrFun h {e.2}
  simp [k2, ns, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2 h3
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2 h3
  try (rw [Bool.eq_iff_iff] at h1)
  try (rw [Bool.eq_iff_iff] at h2)
  try (rw [Bool.eq_iff_iff] at h3)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, iff_iff_implies_and_implies] at h1 h2 h3
  omega
theorem f_k3_ns (e e' : Fin n × Fin n) (he : e.1 < e.2) (he' : e'.1 < e'.2) (h : k3 e = ns e') : False := by
  have h1 := congrFun h {e.1}
  have h2 := congrFun h {e.1, e.2}
  have h3 := congrFun h {e.2}
  simp [k3, ns, he.ne, he.ne', he'.ne, he'.ne'] at h1 h2 h3
  rw [Fin.lt_def] at he he'
  simp only [Fin.ext_iff, iff_iff_implies_and_implies] at h1 h2 h3
  try (rw [Bool.eq_iff_iff] at h1)
  try (rw [Bool.eq_iff_iff] at h2)
  try (rw [Bool.eq_iff_iff] at h3)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, iff_iff_implies_and_implies] at h1 h2 h3
  omega
theorem f_k2_0 (e : Fin n × Fin n) (he : e.1 < e.2) (h : k2 e = fun _ => false) : False := by
  have h1 := congrFun h {e.1}
  simp [k2] at h1
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1
  omega
theorem f_k3_0 (e : Fin n × Fin n) (he : e.1 < e.2) (h : k3 e = fun _ => false) : False := by
  have h1 := congrFun h {e.2}
  simp [k3] at h1
  rw [Fin.lt_def] at he
  simp only [Fin.ext_iff] at h1
  omega
end Facts
section Main
variable {n : ℕ}
def RAW [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n) → Bool) :=
  {fun _ => false, fun _ => true} ∪ Finset.univ.image bt ∪ E.image sm ∪ E.image ns
def NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n) → Bool) :=
  Finset.univ.image ng ∪ E.image k1 ∪ E.image k2 ∪ E.image k3
theorem mem_NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (f : Finset (Fin n) → Bool) :
    f ∈ NEED E ↔ (∃ i, ng i = f) ∨ (∃ e ∈ E, k1 e = f) ∨ (∃ e ∈ E, k2 e = f) ∨ (∃ e ∈ E, k3 e = f) := by
  simp only [NEED, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, or_assoc]
theorem mem_RAW [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (f : Finset (Fin n) → Bool) :
    f ∈ RAW E ↔ f = (fun _ => false) ∨ f = (fun _ => true) ∨ (∃ i, bt i = f) ∨ (∃ e ∈ E, sm e = f) ∨
      (∃ e ∈ E, ns e = f) := by
  simp only [RAW, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and, or_assoc]
theorem card_NEED [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, e.1 < e.2) : n + 3 * E.card ≤ (NEED E).card := by
  have i0 : (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool)).card = n := by
    rw [Finset.card_image_of_injective _ (fun i j h => f_ng i j h), Finset.card_univ, Fintype.card_fin]
  have i1 : (E.image k1).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k1 e e' (hE e he) (hE e' he') h)
  have i2 : (E.image k2).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k2 e e' (hE e he) (hE e' he') h)
  have i3 : (E.image k3).card = E.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => f_k3 e e' (hE e he) (hE e' he') h)
  have d1 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool)) (E.image k1) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨i, rfl⟩ := hf
    obtain ⟨e, he, h⟩ := hf'
    exact f_ng_k1 i e (hE e he) h.symm
  have d2 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool) ∪ E.image k1) (E.image k2) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨e', he', rfl⟩ := hf'
    rcases hf with ⟨i, h⟩ | ⟨e, he, h⟩
    · exact f_ng_k2 i e' h
    · exact f_k1_k2 e e' h
  have d3 : Disjoint (Finset.univ.image (ng : Fin n → Finset (Fin n) → Bool) ∪ E.image k1 ∪ E.image k2)
      (E.image k3) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf hf'
    obtain ⟨e', he', rfl⟩ := hf'
    rcases hf with (⟨i, h⟩ | ⟨e, he, h⟩) | ⟨e, he, h⟩
    · exact f_ng_k3 i e' h
    · exact f_k1_k3 e e' h
    · exact f_k2_k3 e e' (hE e he) (hE e' he') h
  unfold NEED
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    i0, i1, i2, i3]
  omega
theorem edge_col {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) : ∀ e ∈ E, color e.1 = color e.2 := by
  intro e he
  have h := (hcomp (Finset.univ.filter (fun j => color j = color e.1))).mpr (by
    intro i j hij
    simp [hij])
  have h2 : e.2 ∈ Finset.univ.filter (fun j => color j = color e.1) := (h e he).mp (by simp)
  rw [Finset.mem_filter] at h2
  exact h2.2.symm
theorem iso_col {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) (i : Fin n) (hi : ∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i) :
    ∀ j, color j = color i → j = i := by
  intro j hj
  have h := (hcomp {i}).mp (by
    intro e he
    simp [(hi e he).1, (hi e he).2])
  have := (h i j hj.symm).mp (by simp)
  simpa using this
theorem suff [DecidableEq (Finset (Fin n) → Bool)] {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hE : ∀ e ∈ E, e.1 < e.2) (hsurj : Function.Surjective color)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    (A : Finset (Finset (Fin n)))
    (hF : ∀ κ : Fin c, ∃ y ∈ A, (∀ v ∈ y, color v ≠ κ) ∧ y ∪ Finset.univ.filter (fun v => color v = κ) ∈ A)
    (hD : ∀ f ∈ NEED E, ∀ g ∈ NEED E, f ≠ g → ∃ x ∈ A, f x ≠ g x)
    (hR : ∀ f ∈ NEED E, ∀ g ∈ RAW E, ∃ x ∈ A, f x ≠ g x)
    (S : Finset (Fin n)) (p : ℕ) :
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (RAW E ∪ S.image ng).toList.length C ∧
      C.output < (RAW E ∪ S.image ng).toList.length + C.size ∧ C.size ≤ p ∧
      ∀ f ∈ NEED E, ∃ j < (RAW E ∪ S.image ng).toList.length + C.size,
        ∀ x ∈ A, (C.wires ((RAW E ∪ S.image ng).toList.map (fun g => g x))).getD j false = f x) ↔
    ((∀ j, ∃ i ∈ S, color i = j) ∧ n + 3 * E.card - S.card ≤ p) := by
  set L := (RAW E ∪ S.image ng).toList with hL
  have memL : ∀ g, g ∈ L ↔ g ∈ RAW E ∪ S.image ng := fun g => Finset.mem_toList
  have getL : ∀ (x : Finset (Fin n)) (i : ℕ) (hi : i < L.length),
      (L.map (fun g => g x)).getD i false = (L[i]) x := by
    intro x i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  have hec := edge_col E color hcomp
  have hSN : ∀ i ∈ S, ng i ∈ NEED E := fun i _ => (mem_NEED E _).mpr (Or.inl ⟨i, rfl⟩)
  constructor
  · rintro ⟨C, hm, hrb, hout, hp, hw⟩
    have hm' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have := (hm g hg).1
      simpa using this
    refine ⟨?_, ?_⟩
    · intro κ
      by_contra hno
      have hno' : ∀ i ∈ S, color i ≠ κ := fun i hi hc => hno ⟨i, hi, hc⟩
      obtain ⟨y, hyA, hy, hzA⟩ := hF κ
      set z := y ∪ Finset.univ.filter (fun v => color v = κ) with hz
      have zin : ∀ v, color v = κ → v ∈ z := fun v hv => by simp [z, hv]
      have zout : ∀ v, color v ≠ κ → (v ∈ z ↔ v ∈ y) := fun v hv => by simp [z, hv]
      have yout : ∀ v, color v = κ → v ∉ y := fun v hv hvy => hy v hvy hv
      obtain ⟨i0, hi0⟩ := hsurj κ
      obtain ⟨j, _, hjv⟩ := hw (ng i0) ((mem_NEED E _).mpr (Or.inl ⟨i0, rfl⟩))
      have mono_inp : ∀ g ∈ RAW E ∪ S.image ng, g y = true → g z = true := by
        intro g hg hgy
        rcases Finset.mem_union.mp hg with hg | hg
        · rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
          · simp at hgy
          · rfl
          · simp only [bt, decide_eq_true_eq] at hgy ⊢
            exact Finset.mem_union_left _ hgy
          · by_cases hc : color e.1 = κ
            · have h2 : color e.2 = κ := (hec e he).symm.trans hc
              simp [sm, zin _ hc, zin _ h2]
            · have h2 : color e.2 ≠ κ := fun h => hc ((hec e he).trans h)
              simp only [sm] at hgy ⊢
              have a1 := zout _ hc
              have a2 := zout _ h2
              by_cases q1 : e.1 ∈ y <;> by_cases q2 : e.2 ∈ y <;> simp_all
          · by_cases hc : color e.1 = κ
            · have h2 : color e.2 = κ := (hec e he).symm.trans hc
              simp [ns, yout _ hc, yout _ h2] at hgy
            · have h2 : color e.2 ≠ κ := fun h => hc ((hec e he).trans h)
              simp only [ns] at hgy ⊢
              have a1 := zout _ hc
              have a2 := zout _ h2
              by_cases q1 : e.1 ∈ y <;> by_cases q2 : e.2 ∈ y <;> simp_all
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
          have hc := hno' i hi
          simp only [ng, Bool.not_eq_true', decide_eq_false_iff_not] at hgy ⊢
          rwa [zout i hc]
      have hle : ∀ i, (L.map (fun g => g y)).getD i false = true → (L.map (fun g => g z)).getD i false = true := by
        intro i hi
        by_cases hiN : i < L.length
        · rw [getL y i hiN] at hi
          rw [getL z i hiN]
          exact mono_inp _ ((memL _).mp (List.getElem_mem hiN)) hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          exact absurd hi (by decide)
      have hmono := W_mono C.gates hm' (L.map (fun g => g y)) (L.map (fun g => g z)) (by simp) hle j
      have e1 := hjv y hyA
      have e2 := hjv z hzA
      have hy0 : ng i0 y = true := by
        simp only [ng, Bool.not_eq_true', decide_eq_false_iff_not]
        exact yout i0 hi0
      have hz0 : ng i0 z = false := by
        simp only [ng, Bool.not_eq_false', decide_eq_true_eq]
        exact zin i0 hi0
      rw [hy0] at e1
      rw [hz0] at e2
      have := hmono e1
      rw [show (Wr C.gates (L.map (fun g => g z))).getD j false = false from e2] at this
      exact absurd this (by decide)
    · choose! jf hjf hjv using hw
      have h1 : ∀ f ∈ NEED E \ S.image ng, L.length ≤ jf f := by
        intro f hf
        rw [Finset.mem_sdiff] at hf
        by_contra hlt
        rw [not_le] at hlt
        have hg : L[jf f] ∈ RAW E ∪ S.image ng := (memL _).mp (List.getElem_mem hlt)
        have heq : ∀ x ∈ A, f x = (L[jf f]) x := by
          intro x hx
          rw [← hjv f hf.1 x hx, ← getL x _ hlt]
          exact W_lt C.gates _ _ (by simpa using hlt)
        rcases Finset.mem_union.mp hg with hgR | hgS
        · obtain ⟨x, hx, hne⟩ := hR f hf.1 _ hgR
          exact hne (heq x hx)
        · obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hgS
          have hgN : L[jf f] ∈ NEED E := hgi ▸ hSN i hi
          have hfg : f ≠ L[jf f] := by
            intro h
            exact hf.2 (h ▸ hgS)
          obtain ⟨x, hx, hne⟩ := hD f hf.1 _ hgN hfg
          exact hne (heq x hx)
      have h2 : Set.InjOn jf (↑(NEED E \ S.image ng) : Set (Finset (Fin n) → Bool)) := by
        intro f hf g hg hfg
        have hf' := (Finset.mem_sdiff.mp hf).1
        have hg' := (Finset.mem_sdiff.mp hg).1
        by_contra hne
        obtain ⟨x, hx, hne'⟩ := hD f hf' g hg' hne
        apply hne'
        rw [← hjv f hf' x hx, ← hjv g hg' x hx, hfg]
      have h3 : (NEED E \ S.image ng).card ≤ (Finset.Ico L.length (L.length + C.size)).card := by
        apply Finset.card_le_card_of_injOn jf _ h2
        intro f hf
        have hf' := (Finset.mem_sdiff.mp hf).1
        exact Finset.mem_Ico.mpr ⟨h1 f hf, hjf f hf'⟩
      rw [Nat.card_Ico] at h3
      have h4 : (NEED E).card - (S.image ng).card ≤ (NEED E \ S.image ng).card := Finset.le_card_sdiff _ _
      have h5 : (S.image ng).card ≤ S.card := Finset.card_image_le
      have h6 := card_NEED E hE
      omega
  · rintro ⟨hcov, hp⟩
    have hinp : ∀ x : Finset (Fin n), (L.map (fun g => g x)).length = L.length := by simp
    have avin : ∀ gs, ∀ g ∈ RAW E ∪ S.image ng, Av L.length (fun x => L.map (fun g => g x)) gs g := by
      intro gs g hg
      have hgL : g ∈ L := (memL g).mpr hg
      have hlt : L.idxOf g < L.length := List.idxOf_lt_length_iff.mpr hgL
      refine ⟨L.idxOf g, by omega, fun x => ?_⟩
      rw [W_lt _ _ _ (by simpa using hlt), getL x _ hlt, List.getElem_idxOf]
    have hb : ∀ gs i, Av L.length (fun x => L.map (fun g => g x)) gs (bt i) := fun gs i =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))
    have hs : ∀ gs, ∀ e ∈ E, Av L.length (fun x => L.map (fun g => g x)) gs (sm e) := fun gs e he =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, rfl⟩))))))
    have hns : ∀ gs, ∀ e ∈ E, Av L.length (fun x => L.map (fun g => g x)) gs (ns e) := fun gs e he =>
      avin gs _ (Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))))))
    have hsn : ∀ gs, ∀ i ∈ S, Av L.length (fun x => L.map (fun g => g x)) gs (ng i) := fun gs i hi =>
      avin gs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem ng hi))
    obtain ⟨gs, G, hlen, hv, hev⟩ := build L.length (fun x => L.map (fun g => g x)) E hinp hb hs hns color hcomp
      S hcov _ [] S ∅ rfl (good_nil _) (Finset.Subset.refl _) (Finset.empty_subset _)
      (fun v hv => hsn [] v hv) (by simp) (by simp)
    have hL0 : 0 < L.length := by
      apply List.length_pos_of_mem (a := fun _ => false)
      rw [memL]
      exact Finset.mem_union_left _ ((mem_RAW E _).mpr (Or.inl rfl))
    obtain ⟨m2, rb⟩ := good_circ L.length gs 0 G
    refine ⟨⟨gs, 0⟩, m2, rb, by simp [Circuit.size]; omega, by simp [Circuit.size]; omega, ?_⟩
    intro f hf
    rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · obtain ⟨w, hw, hval⟩ := hv i
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).1
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).2.1
      exact ⟨w, hw, fun x _ => hval x⟩
    · obtain ⟨w, hw, hval⟩ := (hev e he).2.2
      exact ⟨w, hw, fun x _ => hval x⟩
end Main
section Final
variable {n : ℕ}
def Fa [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : Finset (Finset (Fin n) → Bool) :=
  insert (fun _ => false) (insert (fun _ => true) (E.biUnion (fun e => Finset.univ.image
    (fun k : Fin 9 => (![bt e.1, bt e.2, ng e.1, ng e.2, sm e, ns e, k1 e, k2 e, k3 e] :
      Fin 9 → Finset (Fin n) → Bool) k))))
theorem memFa [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (e : Fin n × Fin n)
    (he : e ∈ E) (k : Fin 9) :
    (![bt e.1, bt e.2, ng e.1, ng e.2, sm e, ns e, k1 e, k2 e, k3 e] : Fin 9 → Finset (Fin n) → Bool) k ∈ Fa E :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨e, he, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩))
theorem Fa_card [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) :
    (Fa E).card ≤ 9 * E.card + 2 := by
  unfold Fa
  set B := E.biUnion (fun e => Finset.univ.image
    (fun k : Fin 9 => (![bt e.1, bt e.2, ng e.1, ng e.2, sm e, ns e, k1 e, k2 e, k3 e] :
      Fin 9 → Finset (Fin n) → Bool) k))
  have h1 := Finset.card_insert_le (fun _ : Finset (Fin n) => false) (insert (fun _ => true) B)
  have h2 := Finset.card_insert_le (fun _ : Finset (Fin n) => true) B
  have h3 : B.card ≤ 9 * E.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ _e ∈ E, 9 := Finset.sum_le_sum (fun e _ => Finset.card_image_le.trans (by simp))
      _ = 9 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega
theorem Fa_Q [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) : ∀ f ∈ Fa E, Qp f := by
  intro f hf
  simp only [Fa, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf
  rcases hf with rfl | rfl | ⟨e, _, k, rfl⟩
  · exact const_Q false
  · exact const_Q true
  · fin_cases k
    · exact junta_Q (fun p _ => p) e.1 e.1
    · exact junta_Q (fun p _ => p) e.2 e.2
    · exact junta_Q (fun p _ => !p) e.1 e.1
    · exact junta_Q (fun p _ => !p) e.2 e.2
    · exact junta_Q (fun p q => p == q) e.1 e.2
    · exact junta_Q (fun p q => !(p == q)) e.1 e.2
    · exact junta_Q (fun p q => !p && !q) e.1 e.2
    · exact junta_Q (fun p q => p && !q) e.1 e.2
    · exact junta_Q (fun p q => !p && q) e.1 e.2
theorem Fa_sep [DecidableEq (Finset (Fin n) → Bool)] (E : Finset (Fin n × Fin n)) (r : ℕ)
    (hr : (9 * E.card + 2) ^ 2 * 3 ^ r < 4 ^ r) :
    ∃ t : Fin r → Finset (Fin n), ∀ f ∈ Fa E, ∀ g ∈ Fa E, f ≠ g → ∃ k, f (t k) ≠ g (t k) := by
  apply exists_sep (Fa E) r
  · intro f hf g hg hfg
    apply cover _ (Qp_xor f g (Fa_Q E f hf) (Fa_Q E g hg))
    by_contra hz
    apply hfg
    funext z
    have : ¬ (f z ^^ g z) = true := fun h => hz ⟨z, h⟩
    revert this
    cases f z <;> cases g z <;> simp
  · calc (Fa E).card ^ 2 * 3 ^ r ≤ (9 * E.card + 2) ^ 2 * 3 ^ r :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Fa_card E) 2)
      _ < 4 ^ r := hr
theorem main [DecidableEq (Finset (Fin n) → Bool)] {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hE : ∀ e ∈ E, e.1 < e.2) (hsurj : Function.Surjective color)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    (r : ℕ) (hr : (9 * E.card + 2) ^ 2 * 3 ^ r < 4 ^ r) :
    ∃ A : Finset (Finset (Fin n)), (∀ (S : Finset (Fin n)) (p : ℕ),
      (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (RAW E ∪ S.image ng).toList.length C ∧
        C.output < (RAW E ∪ S.image ng).toList.length + C.size ∧ C.size ≤ p ∧
        ∀ f ∈ NEED E, ∃ j < (RAW E ∪ S.image ng).toList.length + C.size,
          ∀ x ∈ A, (C.wires ((RAW E ∪ S.image ng).toList.map (fun g => g x))).getD j false = f x) ↔
      ((∀ j, ∃ i ∈ S, color i = j) ∧ n + 3 * E.card - S.card ≤ p)) ∧ A.card ≤ c + 1 + r := by
  obtain ⟨t, ht⟩ := Fa_sep E r hr
  set row : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => (color v).val < k) with hrow
  set A := (Finset.range (c + 1)).image row ∪ Finset.univ.image t with hA
  have rowA : ∀ k ≤ c, row k ∈ A := fun k hk =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem row (Finset.mem_range.mpr (by omega)))
  have tA : ∀ k, t k ∈ A := fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem t (Finset.mem_univ k))
  have hF : ∀ κ : Fin c, ∃ y ∈ A, (∀ v ∈ y, color v ≠ κ) ∧
      y ∪ Finset.univ.filter (fun v => color v = κ) ∈ A := by
    intro κ
    refine ⟨row κ.val, rowA _ (by omega), fun v hv hc => ?_, ?_⟩
    · simp [row, hc] at hv
    · have : row κ.val ∪ Finset.univ.filter (fun v => color v = κ) = row (κ.val + 1) := by
        ext v
        simp only [row, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.ext_iff]
        omega
      rw [this]
      exact rowA _ (by omega)
  have cls : ∀ f ∈ NEED E ∪ RAW E, f ∈ Fa E ∨ ∃ i, (∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i) ∧ (f = bt i ∨ f = ng i) := by
    intro f hf
    rcases Finset.mem_union.mp hf with hN | hR
    · rcases (mem_NEED E f).mp hN with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · by_cases h : ∃ e ∈ E, e.1 = i ∨ e.2 = i
        · obtain ⟨e, he, h1 | h2⟩ := h
          · left; subst h1; exact memFa E e he 2
          · left; subst h2; exact memFa E e he 3
        · right
          refine ⟨i, fun e he => ⟨fun h1 => h ⟨e, he, Or.inl h1⟩, fun h2 => h ⟨e, he, Or.inr h2⟩⟩, Or.inr rfl⟩
      · left; exact memFa E e he 6
      · left; exact memFa E e he 7
      · left; exact memFa E e he 8
    · rcases (mem_RAW E f).mp hR with rfl | rfl | ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · left; exact Finset.mem_insert_self _ _
      · left; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · by_cases h : ∃ e ∈ E, e.1 = i ∨ e.2 = i
        · obtain ⟨e, he, h1 | h2⟩ := h
          · left; subst h1; exact memFa E e he 0
          · left; subst h2; exact memFa E e he 1
        · right
          refine ⟨i, fun e he => ⟨fun h1 => h ⟨e, he, Or.inl h1⟩, fun h2 => h ⟨e, he, Or.inr h2⟩⟩, Or.inl rfl⟩
      · left; exact memFa E e he 4
      · left; exact memFa E e he 5
  have inv : ∀ i, (∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i) → ∀ g ∈ NEED E ∪ RAW E, g ≠ bt i → g ≠ ng i →
      ∀ y, g (insert i y) = g y := by
    intro i hi g hg hgb hgn y
    rcases Finset.mem_union.mp hg with hN | hR
    · rcases (mem_NEED E g).mp hN with ⟨j, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · have hji : j ≠ i := fun h => hgn (h ▸ rfl)
        simp [ng, Finset.mem_insert, hji]
      · simp [k1, Finset.mem_insert, (hi e he).1, (hi e he).2]
      · simp [k2, Finset.mem_insert, (hi e he).1, (hi e he).2]
      · simp [k3, Finset.mem_insert, (hi e he).1, (hi e he).2]
    · rcases (mem_RAW E g).mp hR with rfl | rfl | ⟨j, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · rfl
      · rfl
      · have hji : j ≠ i := fun h => hgb (h ▸ rfl)
        simp [bt, Finset.mem_insert, hji]
      · simp [sm, Finset.mem_insert, (hi e he).1, (hi e he).2]
      · simp [ns, Finset.mem_insert, (hi e he).1, (hi e he).2]
  have isep : ∀ i, (∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i) → ∀ f, (f = bt i ∨ f = ng i) →
      ∀ g ∈ NEED E ∪ RAW E, f ≠ g → ∃ x ∈ A, f x ≠ g x := by
    intro i hi f hf g hg hfg
    have hcl := iso_col E color hcomp i hi
    have hyA := rowA (color i).val (by omega)
    have hzA := rowA ((color i).val + 1) (by have := (color i).isLt; omega)
    have hiy : i ∉ row (color i).val := by simp [row]
    have hz : row ((color i).val + 1) = insert i (row (color i).val) := by
      ext v
      simp only [row, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hv : color v = color i
        · left; exact hcl v hv
        · right
          have : (color v).val ≠ (color i).val := fun h' => hv (Fin.ext h')
          omega
      · rintro (rfl | h)
        · omega
        · omega
    by_cases hgi : g = bt i ∨ g = ng i
    · refine ⟨row (color i).val, hyA, ?_⟩
      rcases hf with rfl | rfl <;> rcases hgi with rfl | rfl
      · exact absurd rfl hfg
      · simp [bt, ng]
      · simp [bt, ng]
      · exact absurd rfl hfg
    · have hgi' : g ≠ bt i ∧ g ≠ ng i := ⟨fun h => hgi (Or.inl h), fun h => hgi (Or.inr h)⟩
      have hgz : g (row ((color i).val + 1)) = g (row (color i).val) := by
        rw [hz]; exact inv i hi g hg hgi'.1 hgi'.2 _
      have hfz : f (row ((color i).val + 1)) ≠ f (row (color i).val) := by
        rcases hf with rfl | rfl <;> simp [bt, ng, hz, hiy]
      by_cases hy : f (row (color i).val) = g (row (color i).val)
      · exact ⟨row ((color i).val + 1), hzA, fun h => hfz (by rw [h, hgz, ← hy])⟩
      · exact ⟨row (color i).val, hyA, hy⟩
  have sep : ∀ f ∈ NEED E ∪ RAW E, ∀ g ∈ NEED E ∪ RAW E, f ≠ g → ∃ x ∈ A, f x ≠ g x := by
    intro f hf g hg hfg
    rcases cls f hf with hfa | ⟨i, hi, hfi⟩
    · rcases cls g hg with hga | ⟨j, hj, hgj⟩
      · obtain ⟨k, hk⟩ := ht f hfa g hga hfg
        exact ⟨t k, tA k, hk⟩
      · obtain ⟨x, hx, hne⟩ := isep j hj g hgj f hf (Ne.symm hfg)
        exact ⟨x, hx, Ne.symm hne⟩
    · exact isep i hi f hfi g hg hfg
  have nr : ∀ f ∈ NEED E, ∀ g ∈ RAW E, f ≠ g := by
    intro f hf g hg h
    have raw01 : g ∅ = false ∨ g Finset.univ = true := by
      rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨j, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;> simp [bt, sm, ns]
    rcases (mem_NEED E f).mp hf with ⟨i, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · rcases raw01 with h0 | h0
      · rw [← h] at h0; simp [ng] at h0
      · rw [← h] at h0; simp [ng] at h0
    · rcases raw01 with h0 | h0
      · rw [← h] at h0; simp [k1] at h0
      · rw [← h] at h0; simp [k1] at h0
    · rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨j, rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
      · exact f_k2_0 e (hE e he) h
      · have := congrFun h ∅; simp [k2] at this
      · have := congrFun h Finset.univ; simp [k2, bt] at this
      · have := congrFun h ∅; simp [k2, sm] at this
      · exact f_k2_ns e e' (hE e he) (hE e' he') h
    · rcases (mem_RAW E g).mp hg with rfl | rfl | ⟨j, rfl⟩ | ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
      · exact f_k3_0 e (hE e he) h
      · have := congrFun h ∅; simp [k3] at this
      · have := congrFun h Finset.univ; simp [k3, bt] at this
      · have := congrFun h ∅; simp [k3, sm] at this
      · exact f_k3_ns e e' (hE e he) (hE e' he') h
  refine ⟨A, fun S p => suff E color hE hsurj hcomp A hF
    (fun f hf g hg hfg => sep f (Finset.mem_union_left _ hf) g (Finset.mem_union_left _ hg) hfg)
    (fun f hf g hg => sep f (Finset.mem_union_left _ hf) g (Finset.mem_union_right _ hg) (nr f hf g hg)) S p, ?_⟩
  calc A.card ≤ ((Finset.range (c + 1)).image row).card + (Finset.univ.image t).card := Finset.card_union_le _ _
    _ ≤ (c + 1) + r := Nat.add_le_add (Finset.card_image_le.trans (by simp)) (Finset.card_image_le.trans (by simp))
theorem mainA {c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hE : ∀ e ∈ E, e.1 < e.2) (hsurj : Function.Surjective color)
    (hcomp : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z))
    {dq : DecidableEq (Finset (Fin n) → Bool)}
    (bit neg : Fin n → Finset (Fin n) → Bool) (same : Fin n × Fin n → Finset (Fin n) → Bool)
    (hbit : ∀ i x, bit i x = true ↔ i ∈ x) (hneg : ∀ i x, neg i x = !(bit i x))
    (hsame : ∀ e x, same e x = (bit e.1 x == bit e.2 x))
    (raw need : Finset (Finset (Fin n) → Bool))
    (hraw : raw = {fun _ => false, fun _ => true} ∪ Finset.univ.image bit ∪ E.image same ∪
      E.image (fun e x => !(same e x)))
    (hneed : need = Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
      E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x))
    (r : ℕ) (hr : (9 * E.card + 2) ^ 2 * 3 ^ r < 4 ^ r) :
    ∃ A : Finset (Finset (Fin n)), (∀ (S : Finset (Fin n)) (p : ℕ),
      (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (raw ∪ S.image neg).toList.length C ∧
        C.output < (raw ∪ S.image neg).toList.length + C.size ∧ C.size ≤ p ∧
        ∀ f ∈ need, ∃ j < (raw ∪ S.image neg).toList.length + C.size,
          ∀ x ∈ A, (C.wires ((raw ∪ S.image neg).toList.map (fun g => g x))).getD j false = f x) ↔
      ((∀ j, ∃ i ∈ S, color i = j) ∧ n + 3 * E.card - S.card ≤ p)) ∧ A.card ≤ c + 1 + r := by
  have hb : bit = bt := by
    funext i x
    exact Bool.eq_iff_iff.mpr (by rw [hbit]; simp [bt])
  subst hb
  have hn : neg = ng := by
    funext i x
    rw [hneg]
    rfl
  subst hn
  have hs : same = sm := by
    funext e x
    rw [hsame]
    rfl
  subst hs
  subst hraw
  subst hneed
  exact main E color hE hsurj hcomp r hr
end Final
end PEqualNP.Outside.L_meta_53189
theorem PEqualNP.Outside.L_meta_53189 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  ∀ r : Nat, (9*E.card+2)^2 * 3^r < 4^r →
    ∃ A : Finset W, keeps A ∧ A.card ≤ c+1+r := by
  intro n c E color hE hsurj hcomp
  intro W bit neg same raw need keeps r hr
  exact PEqualNP.Outside.L_meta_53189.mainA E color hE hsurj hcomp bit neg same
    (fun i x => @decide_eq_true_iff _ (Classical.propDecidable _)) (fun _ _ => rfl)
    (fun e x => by simp [same, bit]) raw need rfl rfl r hr
