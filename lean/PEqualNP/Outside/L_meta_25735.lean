import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25735_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private lemma tableIndex_lt {n : ℕ} (x : Fin n → Bool) : tableIndex x < 2 ^ n := by
  induction n with
  | zero =>
    unfold tableIndex
    simp
  | succ n ih =>
    unfold tableIndex
    rw [Fin.sum_univ_castSucc]
    have hprev : (∑ i : Fin n, if x i.castSucc = true then 2 ^ (i.castSucc : ℕ) else 0) < 2 ^ n :=
      ih (fun i => x i.castSucc)
    have hlast : (if x (Fin.last n) = true then 2 ^ (Fin.last n : ℕ) else 0) ≤ 2 ^ n := by
      split_ifs <;> simp
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

private lemma tableIndex_mod_pow {a k : ℕ} (hak : a ≤ k) (x : Fin k → Bool) :
    tableIndex x % 2 ^ a = tableIndex (fun i : Fin a => x ⟨i.val, lt_of_lt_of_le i.isLt hak⟩) := by
  have hsplit :
      tableIndex x =
        tableIndex (fun i : Fin a => x ⟨i.val, lt_of_lt_of_le i.isLt hak⟩) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => a ≤ i.val),
          if x i = true then 2 ^ (i : ℕ) else 0 := by
    unfold tableIndex
    have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k))
      (fun i : Fin k => i.val < a) (fun i : Fin k => if x i = true then 2 ^ (i : ℕ) else 0)).symm
    rw [hpart]
    congr 1
    · refine (Finset.sum_nbij (fun i : Fin a => (⟨i.val, lt_of_lt_of_le i.isLt hak⟩ : Fin k))
        ?_ ?_ ?_ ?_).symm
      · intro i _; simp [i.isLt]
      · intro i₁ _ i₂ _ h
        exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) h)
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨⟨j.val, hj⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by ext; rfl⟩
      · intro i _; rfl
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i
      simp [not_lt]
  have hdvd : 2 ^ a ∣ ∑ i ∈ Finset.univ.filter (fun i : Fin k => a ≤ i.val),
      if x i = true then 2 ^ (i : ℕ) else 0 := by
    refine Finset.dvd_sum fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    split_ifs
    · exact Nat.pow_dvd_pow 2 hi
    · exact dvd_zero _
  rcases hdvd with ⟨q, hq⟩
  rw [hsplit, hq, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (tableIndex_lt _)

private lemma typ_ofNat_tableIndex {a k : ℕ} (hak : a ≤ k) (x : Fin k → Bool) :
    (Fin.ofNat (2 ^ a) (Fin.ofNat (2 ^ k) (tableIndex x)).val : Fin (2 ^ a)) =
      ⟨tableIndex (fun i : Fin a => x ⟨i.val, lt_of_lt_of_le i.isLt hak⟩), tableIndex_lt _⟩ := by
  ext
  change ((tableIndex x % 2 ^ k) % 2 ^ a) = _
  rw [Nat.mod_eq_of_lt (tableIndex_lt x)]
  exact tableIndex_mod_pow hak x

private lemma tableIndex_testBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (tableIndex x).testBit i.val = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    unfold tableIndex
    rw [Fin.sum_univ_castSucc]
    have hprev_lt : (∑ j : Fin n, if x j.castSucc = true then 2 ^ (j.castSucc : ℕ) else 0) < 2 ^ n :=
      tableIndex_lt (fun j => x j.castSucc)
    set S := ∑ j : Fin n, if x j.castSucc = true then 2 ^ (j.castSucc : ℕ) else 0
    have hval : S + (if x (Fin.last n) = true then 2 ^ n else 0) =
        S + 2 ^ n * (if x (Fin.last n) = true then 1 else 0) := by
      split_ifs <;> simp
    rw [Fin.val_last, hval]
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.val_last]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),
          Nat.div_eq_of_lt hprev_lt, zero_add]
      cases h : x (Fin.last n) <;> simp
    · intro j
      simp only [Fin.val_castSucc]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (S + 2 ^ n * (if x (Fin.last n) = true then 1 else 0)) / 2 ^ j.val =
          S / 2 ^ j.val + 2 ^ (n - j.val) * (if x (Fin.last n) = true then 1 else 0) := by
        have hpow : 2 ^ n = 2 ^ j.val * 2 ^ (n - j.val) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (le_of_lt j.isLt)]
        rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j.val)]
      rw [hdiv]
      have heven : 2 ∣ 2 ^ (n - j.val) * (if x (Fin.last n) = true then 1 else 0) := by
        have hpos : 1 ≤ n - j.val := by omega
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hpos) _
      rcases heven with ⟨q, hq⟩
      rw [hq, Nat.add_mul_mod_self_left, ← Nat.testBit_eq_decide_div_mod_eq]
      exact ih (fun r => x r.castSucc) j

private def ValidGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma validGates_nil : ValidGates [] := fun _ h => by simp at h

private lemma validGates_append {gs₁ gs₂ : List Gate}
    (h₁ : ValidGates gs₁) (h₂ : ValidGates gs₂) : ValidGates (gs₁ ++ gs₂) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h₁ g h
  · exact h₂ g h

private def wiresOf (gs : List Gate) (init : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires init

private lemma wiresOf_length (gs : List Gate) (init : List Bool) :
    (wiresOf gs init).length = init.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma wiresOf_append (gs₁ gs₂ : List Gate) (init : List Bool) :
    wiresOf (gs₁ ++ gs₂) init = wiresOf gs₂ (wiresOf gs₁ init) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

private lemma wiresOf_getD_prefix (gs₁ gs₂ : List Gate) (init : List Bool) (w : ℕ)
    (hw : w < init.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) init).getD w false = (wiresOf gs₁ init).getD w false := by
  rw [wiresOf_append]
  have hlen : w < (wiresOf gs₁ init).length := by rw [wiresOf_length]; exact hw
  generalize wiresOf gs₁ init = cur at hlen ⊢
  induction gs₂ generalizing cur with
  | nil => rfl
  | cons g rest ih =>
    unfold wiresOf Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    have hlen' : w < (cur ++ [g.op.eval (g.inputs.map fun i => cur.getD i false)]).length := by
      simp; omega
    rw [ih _ hlen']
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hlen]

private lemma wiresOf_snoc_new (gs : List Gate) (g : Gate) (init : List Bool) :
    (wiresOf (gs ++ [g]) init).getD (init.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs init).getD i false) := by
  rw [wiresOf_append]
  have hlen : (wiresOf gs init).length = init.length + gs.length := wiresOf_length gs init
  rw [← hlen]
  generalize wiresOf gs init = cur
  unfold wiresOf Circuit.wires
  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp

private def Computes {α : Type} (init : α → List Bool) (gs : List Gate) (w : ℕ) (f : α → Bool) :
    Prop :=
  (∀ x, w < (init x).length + gs.length) ∧ ∀ x, (wiresOf gs (init x)).getD w false = f x

private lemma computes_append {α : Type} {init : α → List Bool} {gs₁ gs₂ : List Gate}
    {w : ℕ} {f : α → Bool} (h : Computes init gs₁ w f) :
    Computes init (gs₁ ++ gs₂) w f := by
  refine ⟨fun x => by simp; have := h.1 x; omega, fun x => ?_⟩
  rw [wiresOf_getD_prefix gs₁ gs₂ (init x) w (h.1 x)]
  exact h.2 x

private lemma addConstFalse {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate) :
    ∃ (gs' : List Gate) (w : ℕ),
      ValidGates gs' ∧ gs'.length = 1 ∧
      Computes init (gs ++ gs') w (fun _ => false) := by
  let g : Gate := ⟨GateOp.or, []⟩
  refine ⟨[g], nIn + gs.length, ?_, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨by simp [g], by simp [g]⟩
  · intro x; rw [hlen x]; simp
  · intro x
    rw [← hlen x, wiresOf_snoc_new]
    rfl

private lemma addConstTrue {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate) :
    ∃ (gs' : List Gate) (w : ℕ),
      ValidGates gs' ∧ gs'.length = 1 ∧
      Computes init (gs ++ gs') w (fun _ => true) := by
  let g : Gate := ⟨GateOp.and, []⟩
  refine ⟨[g], nIn + gs.length, ?_, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨by simp [g], by simp [g]⟩
  · intro x; rw [hlen x]; simp
  · intro x
    rw [← hlen x, wiresOf_snoc_new]
    rfl

private lemma addAnd {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    {w₁ w₂ : ℕ} {f₁ f₂ : α → Bool}
    (h₁ : Computes init gs w₁ f₁) (h₂ : Computes init gs w₂ f₂) :
    ∃ (gs' : List Gate) (w : ℕ),
      ValidGates gs' ∧ gs'.length = 1 ∧
      Computes init (gs ++ gs') w (fun x => f₁ x && f₂ x) := by
  let g : Gate := ⟨GateOp.and, [w₁, w₂]⟩
  refine ⟨[g], nIn + gs.length, ?_, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨by simp [g], by simp [g]⟩
  · intro x; rw [hlen x]; simp
  · intro x
    rw [← hlen x, wiresOf_snoc_new]
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true]
    rw [h₁.2 x, h₂.2 x]

private lemma addOr {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    {w₁ w₂ : ℕ} {f₁ f₂ : α → Bool}
    (h₁ : Computes init gs w₁ f₁) (h₂ : Computes init gs w₂ f₂) :
    ∃ (gs' : List Gate) (w : ℕ),
      ValidGates gs' ∧ gs'.length = 1 ∧
      Computes init (gs ++ gs') w (fun x => f₁ x || f₂ x) := by
  let g : Gate := ⟨GateOp.or, [w₁, w₂]⟩
  refine ⟨[g], nIn + gs.length, ?_, rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨by simp [g], by simp [g]⟩
  · intro x; rw [hlen x]; simp
  · intro x
    rw [← hlen x, wiresOf_snoc_new]
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false]
    rw [h₁.2 x, h₂.2 x]

private lemma addOrList {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    {wF : ℕ} (hwF : Computes init gs wF (fun _ => false))
    (items : List (ℕ × (α → Bool)))
    (hitems : ∀ p ∈ items, Computes init gs p.1 p.2) :
    ∃ (gs' : List Gate) (w : ℕ),
      ValidGates gs' ∧ gs'.length ≤ items.length ∧
      Computes init (gs ++ gs') w (fun x => items.any (fun p => p.2 x)) := by
  induction items generalizing gs with
  | nil =>
    refine ⟨[], wF, validGates_nil, by simp, ?_⟩
    simpa using hwF
  | cons p rest ih =>
    have hp : Computes init gs p.1 p.2 := hitems p (by simp)
    have hrest : ∀ q ∈ rest, Computes init gs q.1 q.2 := fun q hq => hitems q (by simp [hq])
    rcases ih gs hwF hrest with ⟨gs₁, w₁, hv₁, hlen₁, hc₁⟩
    have hp₁ : Computes init (gs ++ gs₁) p.1 p.2 := computes_append hp
    rcases addOr init hlen (gs ++ gs₁) hp₁ hc₁ with ⟨gs₂, w₂, hv₂, hlen₂, hc₂⟩
    refine ⟨gs₁ ++ gs₂, w₂, validGates_append hv₁ hv₂, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · rw [← List.append_assoc]
      simpa [List.any_cons] using hc₂

private lemma buildDecoder {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) :
    ∀ (r : ℕ) (_ : 1 ≤ r) (gs : List Gate)
      (bits : α → Fin r → Bool)
      (pos neg : Fin r → ℕ)
      (_ : ∀ i : Fin r, Computes init gs (pos i) (fun x => bits x i))
      (_ : ∀ i : Fin r, Computes init gs (neg i) (fun x => !(bits x i))),
    ∃ (gs' : List Gate) (ind : Fin (2 ^ r) → ℕ),
      ValidGates gs' ∧ gs'.length ≤ 2 * 2 ^ r ∧
      ∀ t : Fin (2 ^ r), Computes init (gs ++ gs') (ind t)
        (fun x => decide (tableIndex (bits x) = t.val)) := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    intro gs bits pos neg hpos hneg
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨[], fun t => if t.val = 0 then neg 0 else pos 0,
        validGates_nil, by simp, ?_⟩
      intro t
      rw [List.append_nil]
      fin_cases t
      · dsimp only [Fin.zero_eta, Fin.val_zero]
        simp only [↓reduceIte]
        have hc := hneg 0
        refine ⟨hc.1, fun x => ?_⟩
        rw [hc.2 x]
        dsimp only
        unfold tableIndex
        rw [Fin.sum_univ_succ]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero]
        cases bits x 0 <;> rfl
      · dsimp only [Fin.mk_one, Fin.val_one]
        have h10 : (1 : ℕ) ≠ 0 := by omega
        simp only [h10, ↓reduceIte]
        have hc := hpos 0
        refine ⟨hc.1, fun x => ?_⟩
        rw [hc.2 x]
        dsimp only
        unfold tableIndex
        rw [Fin.sum_univ_succ]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero]
        cases bits x 0 <;> rfl
    · have hr1 : 1 ≤ r := by omega
      rcases ih hr1 gs (fun x i => bits x i.castSucc)
        (fun i => pos i.castSucc) (fun i => neg i.castSucc)
        (fun i => hpos i.castSucc) (fun i => hneg i.castSucc) with
        ⟨gs₁, ind₁, hv₁, hlen₁, hind₁⟩
      have hposL : Computes init (gs ++ gs₁) (pos (Fin.last r)) (fun x => bits x (Fin.last r)) :=
        computes_append (hpos (Fin.last r))
      have hnegL : Computes init (gs ++ gs₁) (neg (Fin.last r)) (fun x => !(bits x (Fin.last r))) :=
        computes_append (hneg (Fin.last r))
      have hstep : ∀ (n : ℕ) (hn : n ≤ 2 ^ r),
          ∃ (gs₂ : List Gate) (w0 w1 : Fin n → ℕ),
            ValidGates gs₂ ∧ gs₂.length ≤ 2 * n ∧
            ∀ (j : Fin n),
              Computes init ((gs ++ gs₁) ++ gs₂) (w0 j)
                (fun x => decide (tableIndex (fun i : Fin r => bits x i.castSucc) = j.val) &&
                  !(bits x (Fin.last r))) ∧
              Computes init ((gs ++ gs₁) ++ gs₂) (w1 j)
                (fun x => decide (tableIndex (fun i : Fin r => bits x i.castSucc) = j.val) &&
                  bits x (Fin.last r)) := by
        intro n
        induction n with
        | zero =>
          intro _
          exact ⟨[], Fin.elim0, Fin.elim0, validGates_nil, by simp, fun j => Fin.elim0 j⟩
        | succ n ihn =>
          intro hn
          rcases ihn (by omega) with ⟨gsA, w0A, w1A, hvA, hlenA, hcA⟩
          let jFin : Fin (2 ^ r) := ⟨n, by omega⟩
          have hIndA : Computes init ((gs ++ gs₁) ++ gsA) (ind₁ jFin)
              (fun x => decide (tableIndex (fun i : Fin r => bits x i.castSucc) = n)) :=
            computes_append (hind₁ jFin)
          have hNegA : Computes init ((gs ++ gs₁) ++ gsA) (neg (Fin.last r))
              (fun x => !(bits x (Fin.last r))) := computes_append hnegL
          have hPosA : Computes init ((gs ++ gs₁) ++ gsA) (pos (Fin.last r))
              (fun x => bits x (Fin.last r)) := computes_append hposL
          rcases addAnd init hlen ((gs ++ gs₁) ++ gsA) hIndA hNegA with ⟨gsB, wB, hvB, hlenB, hcB⟩
          have hIndB : Computes init (((gs ++ gs₁) ++ gsA) ++ gsB) (ind₁ jFin)
              (fun x => decide (tableIndex (fun i : Fin r => bits x i.castSucc) = n)) :=
            computes_append hIndA
          have hPosB : Computes init (((gs ++ gs₁) ++ gsA) ++ gsB) (pos (Fin.last r))
              (fun x => bits x (Fin.last r)) := computes_append hPosA
          rcases addAnd init hlen (((gs ++ gs₁) ++ gsA) ++ gsB) hIndB hPosB with
            ⟨gsC, wC, hvC, hlenC, hcC⟩
          refine ⟨gsA ++ gsB ++ gsC,
            fun j => if h : j.val < n then w0A ⟨j.val, h⟩ else wB,
            fun j => if h : j.val < n then w1A ⟨j.val, h⟩ else wC,
            validGates_append (validGates_append hvA hvB) hvC, ?_, ?_⟩
          · simp only [List.length_append]; omega
          · intro j
            by_cases hj : j.val < n
            · simp only [hj, ↓reduceDIte]
              have hprev := hcA ⟨j.val, hj⟩
              rw [← List.append_assoc, ← List.append_assoc]
              exact ⟨computes_append (computes_append hprev.1),
                     computes_append (computes_append hprev.2)⟩
            · have hjeq : j.val = n := by omega
              simp only [hj, ↓reduceDIte]
              rw [hjeq, ← List.append_assoc, ← List.append_assoc]
              exact ⟨computes_append hcB, hcC⟩
      rcases hstep (2 ^ r) (le_refl _) with ⟨gs₂, w0, w1, hv₂, hlen₂, hc₂⟩
      have hpow2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
      refine ⟨gs₁ ++ gs₂,
        fun t => if h : t.val < 2 ^ r then w0 ⟨t.val, h⟩
          else w1 ⟨t.val - 2 ^ r, by have := t.isLt; omega⟩,
        validGates_append hv₁ hv₂, ?_, ?_⟩
      · simp only [List.length_append]
        omega
      · intro t
        rw [← List.append_assoc]
        by_cases ht : t.val < 2 ^ r
        · simp only [ht, ↓reduceDIte]
          have hc := (hc₂ ⟨t.val, ht⟩).1
          refine ⟨hc.1, fun x => ?_⟩
          rw [hc.2 x]
          dsimp only
          have hti : tableIndex (bits x) =
              tableIndex (fun i : Fin r => bits x i.castSucc) +
              (if bits x (Fin.last r) = true then 2 ^ r else 0) := by
            unfold tableIndex
            rw [Fin.sum_univ_castSucc]
            simp
          have hlt := tableIndex_lt (fun i : Fin r => bits x i.castSucc)
          rw [hti]
          cases hb : bits x (Fin.last r) <;> simp <;> omega
        · simp only [ht, ↓reduceDIte]
          have hsub : t.val - 2 ^ r < 2 ^ r := by have := t.isLt; omega
          have hc := (hc₂ ⟨t.val - 2 ^ r, hsub⟩).2
          refine ⟨hc.1, fun x => ?_⟩
          rw [hc.2 x]
          dsimp only
          have hti : tableIndex (bits x) =
              tableIndex (fun i : Fin r => bits x i.castSucc) +
              (if bits x (Fin.last r) = true then 2 ^ r else 0) := by
            unfold tableIndex
            rw [Fin.sum_univ_castSucc]
            simp
          have hlt := tableIndex_lt (fun i : Fin r => bits x i.castSucc)
          rw [hti]
          cases hb : bits x (Fin.last r) <;> simp <;> omega

private lemma buildBlockLookup {α : Type} {nIn m s : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    (sel : α → Fin m) (ind : Fin m → ℕ)
    (hind : ∀ t : Fin m, Computes init gs (ind t) (fun x => decide (sel x = t)))
    {wF : ℕ} (hwF : Computes init gs wF (fun _ => false))
    (tbl : Fin m → Fin s → Bool) :
    ∃ (gs' : List Gate) (posOut negOut : Fin s → ℕ),
      ValidGates gs' ∧ gs'.length ≤ m + s * 2 ^ s ∧
      ∀ c : Fin s,
        Computes init (gs ++ gs') (posOut c) (fun x => tbl (sel x) c) ∧
        Computes init (gs ++ gs') (negOut c) (fun x => !(tbl (sel x) c)) := by
  let pat : Fin m → Fin (2 ^ s) := fun t => ⟨tableIndex (tbl t), tableIndex_lt _⟩
  let bucket : Fin (2 ^ s) → List (Fin m) :=
    fun p => (List.finRange m).filter (fun t => decide (pat t = p))
  have hbuck_build : ∀ (n : ℕ) (hn : n ≤ 2 ^ s),
      ∃ (gs₁ : List Gate) (bw : Fin n → ℕ),
        ValidGates gs₁ ∧
        gs₁.length ≤ ∑ i : Fin n, (bucket ⟨i.val, lt_of_lt_of_le i.isLt hn⟩).length ∧
        ∀ i : Fin n, Computes init (gs ++ gs₁) (bw i)
          (fun x => decide (pat (sel x) = ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[], Fin.elim0, validGates_nil, by simp, fun i => Fin.elim0 i⟩
    | succ n ihn =>
      intro hn
      rcases ihn (by omega) with ⟨gsA, bwA, hvA, hlenA, hcA⟩
      let pFin : Fin (2 ^ s) := ⟨n, by omega⟩
      let items := (bucket pFin).map (fun t => (ind t, fun x => decide (sel x = t)))
      have hitems : ∀ q ∈ items, Computes init (gs ++ gsA) q.1 q.2 := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨t, _, rfl⟩
        exact computes_append (hind t)
      rcases addOrList init hlen (gs ++ gsA) (computes_append hwF) items hitems with
        ⟨gsB, wB, hvB, hlenB, hcB⟩
      refine ⟨gsA ++ gsB,
        fun i => if h : i.val < n then bwA ⟨i.val, h⟩ else wB,
        validGates_append hvA hvB, ?_, ?_⟩
      · rw [List.length_append, Fin.sum_univ_castSucc]
        have hlenB' : gsB.length ≤ (bucket pFin).length := by
          simpa [items] using hlenB
        have hsum_eq : (∑ i : Fin n, (bucket ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).length) =
            ∑ i : Fin n, (bucket ⟨i.castSucc.val, lt_of_lt_of_le i.castSucc.isLt hn⟩).length := rfl
        have hlast_eq : (bucket ⟨(Fin.last n).val, lt_of_lt_of_le (Fin.last n).isLt hn⟩).length =
            (bucket pFin).length := rfl
        omega
      · intro i
        rw [← List.append_assoc]
        by_cases hi : i.val < n
        · simp only [hi, ↓reduceDIte]
          exact computes_append (hcA ⟨i.val, hi⟩)
        · have hieq : i.val = n := by omega
          simp only [hi, ↓reduceDIte]
          refine ⟨hcB.1, fun x => ?_⟩
          rw [hcB.2 x]
          dsimp only
          have hfin : (⟨i.val, lt_of_lt_of_le i.isLt hn⟩ : Fin (2 ^ s)) = pFin := by
            ext; exact hieq
          rw [hfin]
          apply Bool.eq_iff_iff.mpr
          simp only [items, List.any_map, List.any_eq_true, Function.comp_apply,
            bucket, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
          constructor
          · rintro ⟨t, ht, hst⟩; rw [hst]; exact ht
          · intro hp; exact ⟨sel x, hp, rfl⟩
  rcases hbuck_build (2 ^ s) (le_refl _) with ⟨gs₁, bw, hv₁, hlen₁, hbw⟩
  have hsum_buck : (∑ p : Fin (2 ^ s), (bucket p).length) = m := by
    have h1 : ∀ p : Fin (2 ^ s),
        (bucket p).length = ((Finset.univ : Finset (Fin m)).filter (fun t => pat t = p)).card := by
      intro p
      unfold bucket
      have hnd : (List.finRange m).Nodup := List.nodup_finRange m
      rw [← List.toFinset_card_of_nodup (hnd.filter _)]
      congr 1
      ext t
      simp
    simp_rw [h1]
    rw [← Finset.card_biUnion]
    · have hun : (Finset.univ.biUnion (fun p : Fin (2 ^ s) =>
          (Finset.univ : Finset (Fin m)).filter (fun t => pat t = p))) = Finset.univ := by
        ext t; simp
      rw [hun, Finset.card_univ, Fintype.card_fin]
    · intro p₁ _ p₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro t ht₁ ht₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht₁ ht₂
      exact hne (ht₁.symm.trans ht₂)
  have hlen₁' : gs₁.length ≤ m := by
    have heq : (∑ i : Fin (2 ^ s), (bucket ⟨i.val, lt_of_lt_of_le i.isLt (le_refl _)⟩).length) =
        ∑ p : Fin (2 ^ s), (bucket p).length := rfl
    omega
  have hcol_build : ∀ (n : ℕ) (hn : n ≤ s),
      ∃ (gs₂ : List Gate) (pOut nOut : Fin n → ℕ),
        ValidGates gs₂ ∧ gs₂.length ≤ n * 2 ^ s ∧
        ∀ c : Fin n,
          Computes init ((gs ++ gs₁) ++ gs₂) (pOut c)
            (fun x => tbl (sel x) ⟨c.val, lt_of_lt_of_le c.isLt hn⟩) ∧
          Computes init ((gs ++ gs₁) ++ gs₂) (nOut c)
            (fun x => !(tbl (sel x) ⟨c.val, lt_of_lt_of_le c.isLt hn⟩)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[], Fin.elim0, Fin.elim0, validGates_nil, by simp, fun c => Fin.elim0 c⟩
    | succ n ihn =>
      intro hn
      rcases ihn (by omega) with ⟨gsA, pA, nA, hvA, hlenA, hcA⟩
      let cFin : Fin s := ⟨n, by omega⟩
      let posPats := (List.finRange (2 ^ s)).filter (fun p => p.val.testBit n)
      let negPats := (List.finRange (2 ^ s)).filter (fun p => !(p.val.testBit n))
      let posItems := posPats.map (fun p => (bw p, fun x => decide (pat (sel x) = p)))
      let negItems := negPats.map (fun p => (bw p, fun x => decide (pat (sel x) = p)))
      have hposItems : ∀ q ∈ posItems, Computes init ((gs ++ gs₁) ++ gsA) q.1 q.2 := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨p, _, rfl⟩
        exact computes_append (hbw p)
      rcases addOrList init hlen ((gs ++ gs₁) ++ gsA)
        (computes_append (computes_append hwF)) posItems hposItems with
        ⟨gsB, wPos, hvB, hlenB, hcB⟩
      have hnegItems : ∀ q ∈ negItems, Computes init (((gs ++ gs₁) ++ gsA) ++ gsB) q.1 q.2 := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨p, _, rfl⟩
        exact computes_append (computes_append (hbw p))
      rcases addOrList init hlen (((gs ++ gs₁) ++ gsA) ++ gsB)
        (computes_append (computes_append (computes_append hwF))) negItems hnegItems with
        ⟨gsC, wNeg, hvC, hlenC, hcC⟩
      have hpart : posPats.length + negPats.length = 2 ^ s := by
        have hp : posPats.length + negPats.length = (List.finRange (2 ^ s)).length := by
          unfold posPats negPats
          induction (List.finRange (2 ^ s)) with
          | nil => rfl
          | cons a l ihl =>
            cases h : a.val.testBit n <;> simp [h] <;> omega
        simpa using hp
      refine ⟨gsA ++ gsB ++ gsC,
        fun c => if h : c.val < n then pA ⟨c.val, h⟩ else wPos,
        fun c => if h : c.val < n then nA ⟨c.val, h⟩ else wNeg,
        validGates_append (validGates_append hvA hvB) hvC, ?_, ?_⟩
      · have hB' : gsB.length ≤ posPats.length := by simpa [posItems] using hlenB
        have hC' : gsC.length ≤ negPats.length := by simpa [negItems] using hlenC
        simp only [List.length_append, Nat.succ_mul]
        omega
      · intro c
        rw [← List.append_assoc, ← List.append_assoc]
        by_cases hc : c.val < n
        · simp only [hc, ↓reduceDIte]
          have hprev := hcA ⟨c.val, hc⟩
          exact ⟨computes_append (computes_append hprev.1),
                 computes_append (computes_append hprev.2)⟩
        · have hceq : c.val = n := by omega
          simp only [hc, ↓reduceDIte]
          have hcfin : (⟨c.val, lt_of_lt_of_le c.isLt hn⟩ : Fin s) = cFin := by ext; exact hceq
          rw [hcfin]
          constructor
          · have hB1 := computes_append (gs₂ := gsC) hcB
            refine ⟨hB1.1, fun x => ?_⟩
            rw [hB1.2 x]
            dsimp only
            apply Bool.eq_iff_iff.mpr
            simp only [posItems, posPats, List.any_map, List.any_eq_true, Function.comp_apply,
              List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
            have htb : (pat (sel x)).val.testBit n = tbl (sel x) cFin :=
              tableIndex_testBit (tbl (sel x)) cFin
            constructor
            · rintro ⟨p, hp, hpeq⟩
              rw [← hpeq, htb] at hp
              exact hp
            · intro ht
              exact ⟨pat (sel x), by rw [htb]; exact ht, rfl⟩
          · refine ⟨hcC.1, fun x => ?_⟩
            rw [hcC.2 x]
            dsimp only
            apply Bool.eq_iff_iff.mpr
            simp only [negItems, negPats, List.any_map, List.any_eq_true, Function.comp_apply,
              List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
            have htb : (pat (sel x)).val.testBit n = tbl (sel x) cFin :=
              tableIndex_testBit (tbl (sel x)) cFin
            constructor
            · rintro ⟨p, hp, hpeq⟩
              rw [← hpeq, htb] at hp
              exact hp
            · intro ht
              exact ⟨pat (sel x), by rw [htb]; exact ht, rfl⟩
  rcases hcol_build s (le_refl _) with ⟨gs₂, pOut, nOut, hv₂, hlen₂, hc₂⟩
  refine ⟨gs₁ ++ gs₂, pOut, nOut, validGates_append hv₁ hv₂, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · intro c
    rw [← List.append_assoc]
    exact hc₂ c

private lemma buildAllLookups {α : Type} {nIn a : ℕ} (ha : 16 ≤ a) (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    (sel : α → Fin (2 ^ a)) (ind : Fin (2 ^ a) → ℕ)
    (hind : ∀ t : Fin (2 ^ a), Computes init gs (ind t) (fun x => decide (sel x = t)))
    {wF : ℕ} (hwF : Computes init gs wF (fun _ => false))
    (tbl : Fin (2 ^ a) → Fin (32 * a) → Bool) :
    ∃ (gs' : List Gate) (posOut negOut : Fin (32 * a) → ℕ),
      ValidGates gs' ∧ gs'.length ≤ 136 * 2 ^ a ∧
      ∀ j : Fin (32 * a),
        Computes init (gs ++ gs') (posOut j) (fun x => tbl (sel x) j) ∧
        Computes init (gs ++ gs') (negOut j) (fun x => !(tbl (sel x) j)) := by
  let s := a / 2
  have hs_ge : 8 ≤ s := by omega
  have h2s_le : 2 * s ≤ a := by omega
  have hs_2s : s * 2 ^ s ≤ 2 ^ a := by
    have h1 : s ≤ 2 ^ s := Nat.le_of_lt Nat.lt_two_pow_self
    calc s * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (s + s) := (Nat.pow_add 2 s s).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
  let B := 68
  have hcov : 32 * a ≤ B * s := by omega
  let blockTbl : Fin B → Fin (2 ^ a) → Fin s → Bool := fun b t c =>
    if h : b.val * s + c.val < 32 * a then tbl t ⟨b.val * s + c.val, h⟩ else false
  have hloop : ∀ (n : ℕ) (hn : n ≤ B),
      ∃ (gs' : List Gate) (pB nB : Fin n → Fin s → ℕ),
        ValidGates gs' ∧ gs'.length ≤ n * (2 * 2 ^ a) ∧
        ∀ (b : Fin n) (c : Fin s),
          Computes init (gs ++ gs') (pB b c)
            (fun x => blockTbl ⟨b.val, lt_of_lt_of_le b.isLt hn⟩ (sel x) c) ∧
          Computes init (gs ++ gs') (nB b c)
            (fun x => !(blockTbl ⟨b.val, lt_of_lt_of_le b.isLt hn⟩ (sel x) c)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[], Fin.elim0, Fin.elim0, validGates_nil, by simp, fun b => Fin.elim0 b⟩
    | succ n ihn =>
      intro hn
      rcases ihn (by omega) with ⟨gsA, pA, nA, hvA, hlenA, hcA⟩
      let bFin : Fin B := ⟨n, by omega⟩
      rcases buildBlockLookup init hlen (gs ++ gsA) sel ind
        (fun t => computes_append (hind t)) (computes_append hwF) (blockTbl bFin) with
        ⟨gsB, pB, nB, hvB, hlenB, hcB⟩
      refine ⟨gsA ++ gsB,
        fun b => if h : b.val < n then pA ⟨b.val, h⟩ else pB,
        fun b => if h : b.val < n then nA ⟨b.val, h⟩ else nB,
        validGates_append hvA hvB, ?_, ?_⟩
      · rw [List.length_append, Nat.succ_mul]
        omega
      · intro b c
        rw [← List.append_assoc]
        by_cases hb : b.val < n
        · simp only [hb, ↓reduceDIte]
          have hprev := hcA ⟨b.val, hb⟩ c
          exact ⟨computes_append hprev.1, computes_append hprev.2⟩
        · have hbeq : b.val = n := by omega
          simp only [hb, ↓reduceDIte]
          have hbfin : (⟨b.val, lt_of_lt_of_le b.isLt hn⟩ : Fin B) = bFin := by ext; exact hbeq
          rw [hbfin]
          exact hcB c
  rcases hloop B (le_refl _) with ⟨gs', pB, nB, hv', hlen', hc'⟩
  have hlen'' : gs'.length ≤ 136 * 2 ^ a := by
    have : B * (2 * 2 ^ a) = 136 * 2 ^ a := by ring
    omega
  refine ⟨gs',
    fun j => pB ⟨j.val / s, by have := j.isLt; exact Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨j.val % s, Nat.mod_lt _ (by omega)⟩,
    fun j => nB ⟨j.val / s, by have := j.isLt; exact Nat.div_lt_of_lt_mul (by omega)⟩
      ⟨j.val % s, Nat.mod_lt _ (by omega)⟩,
    hv', hlen'', ?_⟩
  intro j
  have hdiv : j.val / s * s + j.val % s = j.val := by
    rw [mul_comm]; exact Nat.div_add_mod j.val s
  have hlt : j.val / s * s + j.val % s < 32 * a := by rw [hdiv]; exact j.isLt
  have hc := hc' ⟨j.val / s, Nat.div_lt_of_lt_mul (by have := j.isLt; omega)⟩
    ⟨j.val % s, Nat.mod_lt _ (by omega)⟩
  have heq : ∀ x, blockTbl ⟨j.val / s, Nat.div_lt_of_lt_mul (by have := j.isLt; omega)⟩
      (sel x) ⟨j.val % s, Nat.mod_lt _ (by omega)⟩ = tbl (sel x) j := by
    intro x
    simp only [blockTbl, hlt, ↓reduceDIte]
    congr 1
    ext
    exact hdiv
  exact ⟨⟨hc.1.1, fun x => by rw [hc.1.2 x]; dsimp only; exact heq x⟩,
         ⟨hc.2.1, fun x => by rw [hc.2.2 x]; dsimp only; rw [heq x]⟩⟩

private lemma addDualXor {α : Type} {nIn : ℕ} (init : α → List Bool)
    (hlen : ∀ x, (init x).length = nIn) (gs : List Gate)
    {aP aN bP bN : ℕ} {fa fb : α → Bool}
    (haP : Computes init gs aP fa) (haN : Computes init gs aN (fun x => !fa x))
    (hbP : Computes init gs bP fb) (hbN : Computes init gs bN (fun x => !fb x)) :
    ∃ (gs' : List Gate) (oP oN : ℕ),
      ValidGates gs' ∧ gs'.length = 6 ∧
      Computes init (gs ++ gs') oP (fun x => Bool.xor (fa x) (fb x)) ∧
      Computes init (gs ++ gs') oN (fun x => !(Bool.xor (fa x) (fb x))) := by
  rcases addAnd init hlen gs haP hbN with ⟨g1, w1, hv1, hl1, hc1⟩
  rcases addAnd init hlen (gs ++ g1) (computes_append haN) (computes_append hbP) with
    ⟨g2, w2, hv2, hl2, hc2⟩
  rcases addOr init hlen ((gs ++ g1) ++ g2) (computes_append hc1) hc2 with
    ⟨g3, oP, hv3, hl3, hc3⟩
  rcases addAnd init hlen (((gs ++ g1) ++ g2) ++ g3)
    (computes_append (computes_append (computes_append haP)))
    (computes_append (computes_append (computes_append hbP))) with ⟨g4, w4, hv4, hl4, hc4⟩
  rcases addAnd init hlen ((((gs ++ g1) ++ g2) ++ g3) ++ g4)
    (computes_append (computes_append (computes_append (computes_append haN))))
    (computes_append (computes_append (computes_append (computes_append hbN)))) with
    ⟨g5, w5, hv5, hl5, hc5⟩
  rcases addOr init hlen (((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5)
    (computes_append hc4) hc5 with ⟨g6, oN, hv6, hl6, hc6⟩
  refine ⟨g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6, oP, oN,
    validGates_append (validGates_append (validGates_append (validGates_append
      (validGates_append hv1 hv2) hv3) hv4) hv5) hv6,
    by simp [hl1, hl2, hl3, hl4, hl5, hl6], ?_, ?_⟩
  · have hP : Computes init ((((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) ++ g6) oP
        (fun x => (fa x && !fb x) || (!fa x && fb x)) :=
      computes_append (computes_append (computes_append hc3))
    simp only [← List.append_assoc]
    refine ⟨hP.1, fun x => ?_⟩
    rw [hP.2 x]
    dsimp only
    cases fa x <;> cases fb x <;> rfl
  · simp only [← List.append_assoc]
    refine ⟨hc6.1, fun x => ?_⟩
    rw [hc6.2 x]
    dsimp only
    cases fa x <;> cases fb x <;> rfl

private lemma zmod2_sum_decide {d : ℕ} (f : Fin d → ZMod 2) :
    decide ((∑ j : Fin d, f j) = 1) =
      (List.finRange d).foldl (fun acc j => Bool.xor acc (decide (f j = 1))) false := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_succ, List.finRange_succ, List.foldl_cons]
    have hfold_xor : ∀ (l : List (Fin d)) (b : Bool),
        l.foldl (fun acc j => Bool.xor acc (decide (f j.succ = 1))) b =
        Bool.xor b (l.foldl (fun acc j => Bool.xor acc (decide (f j.succ = 1))) false) := by
      intro l
      induction l with
      | nil => intro b; simp
      | cons a rest ihr =>
        intro b
        simp only [List.foldl_cons]
        rw [ihr, ihr (Bool.xor false _)]
        cases b <;> cases decide (f a.succ = 1) <;>
          cases rest.foldl (fun acc j => Bool.xor acc (decide (f j.succ = 1))) false <;> rfl
    rw [List.foldl_map]
    simp only [Bool.false_xor]
    rw [hfold_xor, ← ih (fun j => f j.succ)]
    generalize (f 0) = x
    generalize (∑ j : Fin d, f j.succ) = y
    fin_cases x <;> fin_cases y <;> rfl

private lemma buildDotCircuit {a k : ℕ} (ha : 16 ≤ a) (hak : a ≤ k)
    (u v : Fin (2 ^ a) → (Fin (32 * a) → ZMod 2)) :
    let m := 2 ^ a
    let N := 2 ^ k
    let I := Fin N
    let typ : I → Fin m := fun label => Fin.ofNat m label.val
    let G : I → I → Bool := fun x y =>
      decide ((∑ j : Fin (32 * a), u (typ x) j * v (typ y) j) = 1)
    HasLitSize (k + k) (adjFun (k := k) (l := k) G) (1024 * m) := by
  intro m N I typ G
  let init : (Fin (k + k) → Bool) → List Bool :=
    fun x => List.ofFn x ++ List.ofFn (fun i => !x i)
  have hlen : ∀ x, (init x).length = 2 * (k + k) := by
    intro x; simp [init]; omega
  let bitsL : (Fin (k + k) → Bool) → Fin a → Bool :=
    fun x i => x (Fin.castAdd k ⟨i.val, lt_of_lt_of_le i.isLt hak⟩)
  let bitsR : (Fin (k + k) → Bool) → Fin a → Bool :=
    fun x i => x (Fin.natAdd k ⟨i.val, lt_of_lt_of_le i.isLt hak⟩)
  let selL : (Fin (k + k) → Bool) → Fin m := fun x => ⟨tableIndex (bitsL x), tableIndex_lt _⟩
  let selR : (Fin (k + k) → Bool) → Fin m := fun x => ⟨tableIndex (bitsR x), tableIndex_lt _⟩
  have hposL : ∀ i : Fin a, Computes init [] i.val (fun x => bitsL x i) := by
    intro i
    refine ⟨fun x => by rw [hlen x]; simp; omega, fun x => ?_⟩
    have hi : i.val < k + k := by omega
    simp only [wiresOf, Circuit.wires, List.foldl_nil, init, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega)]
    simp [bitsL, hi]
  have hnegL : ∀ i : Fin a, Computes init [] ((k + k) + i.val) (fun x => !(bitsL x i)) := by
    intro i
    refine ⟨fun x => by rw [hlen x]; simp; omega, fun x => ?_⟩
    have hi : i.val < k + k := by omega
    simp only [wiresOf, Circuit.wires, List.foldl_nil, init, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp [bitsL, hi]
  have hposR : ∀ i : Fin a, Computes init [] (k + i.val) (fun x => bitsR x i) := by
    intro i
    refine ⟨fun x => by rw [hlen x]; simp; omega, fun x => ?_⟩
    have hi : k + i.val < k + k := by omega
    simp only [wiresOf, Circuit.wires, List.foldl_nil, init, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, bitsR, Fin.natAdd]
  have hnegR : ∀ i : Fin a, Computes init [] ((k + k) + (k + i.val)) (fun x => !(bitsR x i)) := by
    intro i
    refine ⟨fun x => by rw [hlen x]; simp; omega, fun x => ?_⟩
    have hi : k + i.val < k + k := by omega
    simp only [wiresOf, Circuit.wires, List.foldl_nil, init, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_ofFn, add_tsub_cancel_left, List.getElem?_ofFn, hi, ↓reduceDIte,
      Option.getD_some, bitsR, Fin.natAdd]
  rcases addConstFalse init hlen [] with ⟨gF, wF, hvF, hlF, hcF⟩
  rcases addConstTrue init hlen ([] ++ gF) with ⟨gT, wT, hvT, hlT, hcT⟩
  let gs0 := ([] ++ gF) ++ gT
  have hcF0 : Computes init gs0 wF (fun _ => false) := computes_append hcF
  rcases buildDecoder init hlen a (by omega) gs0 bitsL
    (fun i => i.val) (fun i => (k + k) + i.val)
    (fun i => computes_append (computes_append (hposL i)))
    (fun i => computes_append (computes_append (hnegL i))) with
    ⟨gDecL, indL, hvDecL, hlDecL, hIndL⟩
  rcases buildDecoder init hlen a (by omega) (gs0 ++ gDecL) bitsR
    (fun i => k + i.val) (fun i => (k + k) + (k + i.val))
    (fun i => computes_append (computes_append (computes_append (hposR i))))
    (fun i => computes_append (computes_append (computes_append (hnegR i)))) with
    ⟨gDecR, indR, hvDecR, hlDecR, hIndR⟩
  let gs1 := (gs0 ++ gDecL) ++ gDecR
  have hIndL1 : ∀ t : Fin m, Computes init gs1 (indL t) (fun x => decide (selL x = t)) := by
    intro t
    have h := computes_append (gs₂ := gDecR) (hIndL t)
    refine ⟨h.1, fun x => ?_⟩
    rw [h.2 x]
    apply Bool.eq_iff_iff.mpr
    simp [selL, Fin.ext_iff]
  have hIndR1 : ∀ t : Fin m, Computes init gs1 (indR t) (fun x => decide (selR x = t)) := by
    intro t
    have h := hIndR t
    refine ⟨h.1, fun x => ?_⟩
    rw [h.2 x]
    apply Bool.eq_iff_iff.mpr
    simp [selR, Fin.ext_iff]
  have hcF1 : Computes init gs1 wF (fun _ => false) := computes_append (computes_append hcF0)
  have hcT1 : Computes init gs1 wT (fun _ => true) := computes_append (computes_append hcT)
  let uBool : Fin m → Fin (32 * a) → Bool := fun t j => decide (u t j = 1)
  let vBool : Fin m → Fin (32 * a) → Bool := fun t j => decide (v t j = 1)
  rcases buildAllLookups ha init hlen gs1 selL indL hIndL1 hcF1 uBool with
    ⟨gU, uP, uN, hvU, hlU, hU⟩
  rcases buildAllLookups ha init hlen (gs1 ++ gU) selR indR
    (fun t => computes_append (hIndR1 t)) (computes_append hcF1) vBool with
    ⟨gV, vP, vN, hvV, hlV, hV⟩
  let gs2 := (gs1 ++ gU) ++ gV
  have hU2 : ∀ j : Fin (32 * a),
      Computes init gs2 (uP j) (fun x => uBool (selL x) j) ∧
      Computes init gs2 (uN j) (fun x => !(uBool (selL x) j)) :=
    fun j => ⟨computes_append (hU j).1, computes_append (hU j).2⟩
  have hcF2 : Computes init gs2 wF (fun _ => false) := computes_append (computes_append hcF1)
  have hcT2 : Computes init gs2 wT (fun _ => true) := computes_append (computes_append hcT1)
  have hfold : ∀ (l : List (Fin (32 * a))),
      ∃ (gs3 : List Gate) (accP accN : ℕ),
        ValidGates gs3 ∧ gs3.length ≤ 8 * l.length ∧
        Computes init (gs2 ++ gs3) accP
          (fun x => l.foldl (fun acc j =>
            Bool.xor acc (decide (u (selL x) j * v (selR x) j = 1))) false) ∧
        Computes init (gs2 ++ gs3) accN
          (fun x => !(l.foldl (fun acc j =>
            Bool.xor acc (decide (u (selL x) j * v (selR x) j = 1))) false)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨[], wF, wT, validGates_nil, by simp, ?_, ?_⟩
      · simpa using hcF2
      · simpa using hcT2
    | append_singleton l j ih =>
      rcases ih with ⟨gsA, aP, aN, hvA, hlA, haP, haN⟩
      rcases addAnd init hlen (gs2 ++ gsA)
        (computes_append (hU2 j).1) (computes_append (hV j).1) with ⟨gP, pP, hvP, hlP, hcP⟩
      rcases addOr init hlen ((gs2 ++ gsA) ++ gP)
        (computes_append (computes_append (hU2 j).2))
        (computes_append (computes_append (hV j).2)) with ⟨gN, pN, hvN, hlN, hcN⟩
      have hpP : Computes init (((gs2 ++ gsA) ++ gP) ++ gN) pP
          (fun x => decide (u (selL x) j * v (selR x) j = 1)) := by
        have h := computes_append (gs₂ := gN) hcP
        refine ⟨h.1, fun x => ?_⟩
        rw [h.2 x]
        dsimp only [uBool, vBool]
        generalize u (selL x) j = ux
        generalize v (selR x) j = vx
        fin_cases ux <;> fin_cases vx <;> rfl
      have hpN : Computes init (((gs2 ++ gsA) ++ gP) ++ gN) pN
          (fun x => !(decide (u (selL x) j * v (selR x) j = 1))) := by
        refine ⟨hcN.1, fun x => ?_⟩
        rw [hcN.2 x]
        dsimp only [uBool, vBool]
        generalize u (selL x) j = ux
        generalize v (selR x) j = vx
        fin_cases ux <;> fin_cases vx <;> rfl
      rcases addDualXor init hlen (((gs2 ++ gsA) ++ gP) ++ gN)
        (computes_append (computes_append haP))
        (computes_append (computes_append haN))
        hpP hpN with ⟨gX, oP, oN, hvX, hlX, hoP, hoN⟩
      refine ⟨gsA ++ gP ++ gN ++ gX, oP, oN,
        validGates_append (validGates_append (validGates_append hvA hvP) hvN) hvX, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact hoP
      · simp only [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact hoN
  rcases hfold (List.finRange (32 * a)) with ⟨gs3, outW, _, hv3, hl3, hout, _⟩
  let C : Circuit := ⟨gs2 ++ gs3, outW⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · have hv0 : ValidGates gs0 := validGates_append (validGates_append validGates_nil hvF) hvT
    have hv1 : ValidGates gs1 := validGates_append (validGates_append hv0 hvDecL) hvDecR
    have hv2 : ValidGates gs2 := validGates_append (validGates_append hv1 hvU) hvV
    exact validGates_append hv2 hv3
  · have h256a : 256 * a ≤ m := by
      have hpow : ∀ n : ℕ, 16 ≤ n → 256 * n ≤ 2 ^ n := by
        intro n hn
        induction n with
        | zero => omega
        | succ n ihn =>
          by_cases h16 : n = 15
          · subst h16; norm_num
          · have h16' : 16 ≤ n := by omega
            have hprev := ihn h16'
            have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
            omega
      exact hpow a ha
    have hm_ge : 65536 ≤ m := by
      have : 2 ^ 16 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
      simpa [m] using this
    change (gs2 ++ gs3).length ≤ 1024 * m
    have hl3' : gs3.length ≤ 256 * a := by
      rw [List.length_finRange] at hl3
      omega
    have hgs2 : gs2.length = gF.length + gT.length + gDecL.length + gDecR.length +
        gU.length + gV.length := by
      simp [gs2, gs1, gs0]; omega
    rw [List.length_append, hgs2]
    omega
  · intro x
    change (wiresOf (gs2 ++ gs3) (init x)).getD outW false = adjFun (k := k) (l := k) G x
    rw [hout.2 x]
    dsimp only
    rw [← zmod2_sum_decide]
    unfold adjFun G typ
    have hL : Fin.ofNat m (Fin.ofNat (2 ^ k) (tableIndex fun i : Fin k => x (Fin.castAdd k i))).val =
        selL x := typ_ofNat_tableIndex hak (fun i => x (Fin.castAdd k i))
    have hR : Fin.ofNat m (Fin.ofNat (2 ^ k) (tableIndex fun j : Fin k => x (Fin.natAdd k j))).val =
        selR x := typ_ofNat_tableIndex hak (fun j => x (Fin.natAdd k j))
    rw [hL, hR]

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma zmod2_neg_eq (a : ZMod 2) : -a = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma decide_add_zmod2 (a b : ZMod 2) :
    Bool.xor (decide (a = 1)) (decide (b = 1)) = decide (a + b = 1) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma decide_b2z_add (a b : Bool) :
    Bool.xor a b = decide (b2z a + b2z b = 1) := by
  cases a <;> cases b <;> decide

private lemma decide_eq_one_iff (a b : ZMod 2) :
    (decide (a = 1) = decide (b = 1)) ↔ a = b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

private def dot {d : ℕ} (x y : Fin d → ZMod 2) : ZMod 2 :=
  ∑ j : Fin d, x j * y j

private def LinIndep {d r : ℕ} (xs : Fin r → (Fin d → ZMod 2)) : Prop :=
  ∀ c : Fin r → ZMod 2, (∀ j : Fin d, ∑ i : Fin r, c i * xs i j = 0) → ∀ i, c i = 0

private def InSpanList {d : ℕ} (l : List (Fin d → ZMod 2)) (v : Fin d → ZMod 2) : Prop :=
  ∃ c : Fin l.length → ZMod 2, ∀ j : Fin d, v j = ∑ i : Fin l.length, c i * l[i] j

private instance {d : ℕ} (l : List (Fin d → ZMod 2)) (v : Fin d → ZMod 2) :
    Decidable (InSpanList l v) := by
  unfold InSpanList; infer_instance

private lemma card_inSpanList {d : ℕ} (l : List (Fin d → ZMod 2)) :
    (Finset.univ.filter (fun v : Fin d → ZMod 2 => InSpanList l v)).card ≤ 2 ^ l.length := by
  let f : (Fin l.length → ZMod 2) → (Fin d → ZMod 2) :=
    fun c j => ∑ i : Fin l.length, c i * l[i] j
  have hsub : Finset.univ.filter (fun v : Fin d → ZMod 2 => InSpanList l v) ⊆
      Finset.univ.image f := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨c, hc⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, funext fun j => (hc j).symm⟩
  calc (Finset.univ.filter (fun v : Fin d → ZMod 2 => InSpanList l v)).card
      ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin l.length → ZMod 2)).card := Finset.card_image_le
    _ = 2 ^ l.length := by simp [Fintype.card_pi, ZMod.card]

private lemma linIndep_cons {d : ℕ} {l : List (Fin d → ZMod 2)} {v : Fin d → ZMod 2}
    (hl : LinIndep (fun i : Fin l.length => l[i]))
    (hv : ¬ InSpanList l v) :
    LinIndep (fun i : Fin (v :: l).length => (v :: l)[i]) := by
  intro c hc
  have hc0 : c 0 = 0 := by
    rcases zmod2_eq_zero_or_one (c 0) with h0 | h1
    · exact h0
    · exfalso
      apply hv
      refine ⟨fun i => c i.succ, fun j => ?_⟩
      have hcj := hc j
      change ∑ i : Fin (l.length + 1), c i * (v :: l)[i] j = 0 at hcj
      rw [Fin.sum_univ_succ] at hcj
      simp only [h1, one_mul] at hcj
      exact (zmod2_add_eq_zero_iff _ _).mp hcj
  have hrest : ∀ i : Fin l.length, c i.succ = 0 := by
    apply hl (fun i => c i.succ)
    intro j
    have hcj := hc j
    change ∑ i : Fin (l.length + 1), c i * (v :: l)[i] j = 0 at hcj
    rw [Fin.sum_univ_succ] at hcj
    simpa [hc0] using hcj
  intro i
  refine Fin.cases hc0 hrest i

private def prefixIdx {d : ℕ} : (n : ℕ) → (Fin n → (Fin d → ZMod 2)) → List (Fin n)
  | 0, _ => []
  | n + 1, xs =>
      let prev := prefixIdx n (fun i => xs i.castSucc)
      let prevVecs := prev.map (fun i => xs i.castSucc)
      if InSpanList prevVecs (xs (Fin.last n)) then
        prev.map Fin.castSucc
      else
        Fin.last n :: prev.map Fin.castSucc

private def depSet {d : ℕ} : (n : ℕ) → (Fin n → (Fin d → ZMod 2)) → Finset (Fin n)
  | 0, _ => ∅
  | n + 1, xs =>
      let prev := prefixIdx n (fun i => xs i.castSucc)
      let prevVecs := prev.map (fun i => xs i.castSucc)
      let prevDep := (depSet n (fun i => xs i.castSucc)).image Fin.castSucc
      if InSpanList prevVecs (xs (Fin.last n)) then
        insert (Fin.last n) prevDep
      else
        prevDep

private lemma prefixIdx_nodup {d : ℕ} : ∀ (n : ℕ) (xs : Fin n → (Fin d → ZMod 2)),
    (prefixIdx n xs).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, xs => by
      dsimp only [prefixIdx]
      have ih := prefixIdx_nodup n (fun i => xs i.castSucc)
      have hmap : ((prefixIdx n fun i => xs i.castSucc).map Fin.castSucc).Nodup :=
        ih.map (Fin.castSucc_injective n)
      split_ifs
      · exact hmap
      · refine List.nodup_cons.mpr ⟨?_, hmap⟩
        intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _, hi⟩
        exact Fin.castSucc_ne_last i hi

private lemma linIndep_list_of_eq {d : ℕ} {l₁ l₂ : List (Fin d → ZMod 2)} (h : l₁ = l₂) :
    LinIndep (fun i : Fin l₁.length => l₁[i]) → LinIndep (fun i : Fin l₂.length => l₂[i]) := by
  subst h; exact id

private lemma prefixIdx_vecs_linIndep {d : ℕ} : ∀ (n : ℕ) (xs : Fin n → (Fin d → ZMod 2)),
    LinIndep (fun i : Fin ((prefixIdx n xs).map xs).length => ((prefixIdx n xs).map xs)[i])
  | 0, _ => fun _ _ i => Fin.elim0 i
  | n + 1, xs => by
      have ih := prefixIdx_vecs_linIndep n (fun i => xs i.castSucc)
      by_cases hspan : InSpanList ((prefixIdx n fun i => xs i.castSucc).map fun i => xs i.castSucc)
          (xs (Fin.last n))
      · have heq : (prefixIdx (n + 1) xs).map xs =
            (prefixIdx n fun i => xs i.castSucc).map (fun i => xs i.castSucc) := by
          simp [prefixIdx, hspan, List.map_map, Function.comp_def]
        exact linIndep_list_of_eq heq.symm ih
      · have heq : (prefixIdx (n + 1) xs).map xs =
            xs (Fin.last n) :: (prefixIdx n fun i => xs i.castSucc).map (fun i => xs i.castSucc) := by
          simp [prefixIdx, hspan, List.map_map, Function.comp_def]
        exact linIndep_list_of_eq heq.symm (linIndep_cons ih hspan)

private lemma prefixIdx_add_depSet {d : ℕ} : ∀ (n : ℕ) (xs : Fin n → (Fin d → ZMod 2)),
    (prefixIdx n xs).length + (depSet n xs).card = n
  | 0, _ => rfl
  | n + 1, xs => by
      have ih := prefixIdx_add_depSet n (fun i => xs i.castSucc)
      dsimp only [prefixIdx, depSet]
      have hcard_img : ((depSet n fun i => xs i.castSucc).image Fin.castSucc).card =
          (depSet n fun i => xs i.castSucc).card :=
        Finset.card_image_of_injective _ (Fin.castSucc_injective n)
      have hnotmem : Fin.last n ∉ (depSet n fun i => xs i.castSucc).image Fin.castSucc := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
        exact Fin.castSucc_ne_last i hi
      split_ifs
      · rw [List.length_map, Finset.card_insert_of_notMem hnotmem, hcard_img]
        omega
      · rw [List.length_cons, List.length_map, hcard_img]
        omega

private lemma card_bad_prefix {d : ℕ} :
    ∀ (n R : ℕ) (J : Finset (Fin n)),
      (Finset.univ.filter (fun xs : Fin n → (Fin d → ZMod 2) =>
        J ⊆ depSet n xs ∧ (prefixIdx n xs).length < R)).card ≤
      (2 ^ R) ^ J.card * (2 ^ d) ^ (n - J.card)
  | 0, R, J => by
      have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
      subst hJ
      simp only [Finset.card_empty, pow_zero, mul_one, Nat.sub_zero]
      have : (Finset.univ : Finset (Fin 0 → (Fin d → ZMod 2))).card = 1 := by
        simp
      calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin 0 → (Fin d → ZMod 2))).card :=
            Finset.card_filter_le _ _
        _ = 1 := this
  | n + 1, R, J => by
      let J' : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.castSucc ∈ J)
      let BadPrev : Finset (Fin n → (Fin d → ZMod 2)) :=
        Finset.univ.filter (fun xs' => J' ⊆ depSet n xs' ∧ (prefixIdx n xs').length < R)
      have hih : BadPrev.card ≤ (2 ^ R) ^ J'.card * (2 ^ d) ^ (n - J'.card) :=
        card_bad_prefix n R J'
      have hJcard : J.card = J'.card + (if Fin.last n ∈ J then 1 else 0) := by
        have hbi : (J.filter (fun i : Fin (n + 1) => i ≠ Fin.last n)).card = J'.card := by
          refine Finset.card_bij (fun i hi => ⟨i.val, by
            have := i.isLt
            have hne : i ≠ Fin.last n := (Finset.mem_filter.mp hi).2
            have : i.val ≠ n := fun h => hne (Fin.ext h)
            omega⟩) ?_ ?_ ?_
          · intro i hi
            simp only [J', Finset.mem_filter, Finset.mem_univ, true_and]
            have hiJ : i ∈ J := (Finset.mem_filter.mp hi).1
            have heq : (⟨i.val, by
              have := i.isLt
              have hne : i ≠ Fin.last n := (Finset.mem_filter.mp hi).2
              have : i.val ≠ n := fun h => hne (Fin.ext h)
              omega⟩ : Fin n).castSucc = i := by ext; rfl
            rw [heq]
            exact hiJ
          · intro i₁ _ i₂ _ h
            exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) h)
          · intro j hj
            simp only [J', Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact ⟨j.castSucc, Finset.mem_filter.mpr ⟨hj, Fin.castSucc_ne_last j⟩, by ext; rfl⟩
        have hsplit := (Finset.card_filter_add_card_filter_not (s := J)
          (p := fun i : Fin (n + 1) => i ≠ Fin.last n)).symm
        rw [hsplit, hbi]
        congr 1
        by_cases hl : Fin.last n ∈ J
        · simp only [hl, ↓reduceIte]
          have hfeq : J.filter (fun i : Fin (n + 1) => ¬i ≠ Fin.last n) = {Fin.last n} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_singleton, not_ne_iff]
            exact ⟨fun h => h.2, fun h => ⟨h ▸ hl, h⟩⟩
          rw [hfeq, Finset.card_singleton]
        · simp only [hl, ↓reduceIte]
          have hfeq : J.filter (fun i : Fin (n + 1) => ¬i ≠ Fin.last n) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.notMem_empty, not_ne_iff, iff_false, not_and]
            intro hi heq; exact hl (heq ▸ hi)
          rw [hfeq, Finset.card_empty]
      have hJ'_le : J'.card ≤ n := by
        calc J'.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      let ValidLast : (Fin n → (Fin d → ZMod 2)) → Finset (Fin d → ZMod 2) := fun xs' =>
        if Fin.last n ∈ J then
          Finset.univ.filter (fun v => InSpanList ((prefixIdx n xs').map xs') v)
        else
          Finset.univ
      let BadCur := Finset.univ.filter (fun xs : Fin (n + 1) → (Fin d → ZMod 2) =>
        J ⊆ depSet (n + 1) xs ∧ (prefixIdx (n + 1) xs).length < R)
      have hinj : BadCur.card ≤ (BadPrev.sigma ValidLast).card := by
        refine Finset.card_le_card_of_injOn
          (fun xs => ⟨fun i => xs i.castSucc, xs (Fin.last n)⟩) ?_ ?_
        · intro xs hxs
          simp only [BadCur, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hxs
          rcases hxs with ⟨hJsub, hlen⟩
          have hlen' : (prefixIdx n (fun i => xs i.castSucc)).length < R := by
            dsimp only [prefixIdx] at hlen
            split_ifs at hlen <;> simp at hlen <;> omega
          have hJ'sub : J' ⊆ depSet n (fun i => xs i.castSucc) := by
            intro i hi
            simp only [J', Finset.mem_filter, Finset.mem_univ, true_and] at hi
            have hmem := hJsub hi
            dsimp only [depSet] at hmem
            split_ifs at hmem
            · rcases Finset.mem_insert.mp hmem with heq | hmem'
              · exact absurd heq (Fin.castSucc_ne_last i)
              · rcases Finset.mem_image.mp hmem' with ⟨j, hj, hji⟩
                rw [← Fin.castSucc_injective _ hji]; exact hj
            · rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
              rw [← Fin.castSucc_injective _ hji]; exact hj
          refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨?_, ?_⟩)
          · simp only [BadPrev, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hJ'sub, hlen'⟩
          · dsimp only [ValidLast]
            split_ifs with hlast
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hmem := hJsub hlast
              dsimp only [depSet] at hmem
              split_ifs at hmem with hsp
              · exact hsp
              · exfalso
                rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
                exact Fin.castSucc_ne_last j hj
            · exact Finset.mem_univ _
        · intro x₁ _ x₂ _ heq
          have h1 : (fun i : Fin n => x₁ i.castSucc) = (fun i : Fin n => x₂ i.castSucc) :=
            congrArg Sigma.fst heq
          have h2 : x₁ (Fin.last n) = x₂ (Fin.last n) := by
            have := congrArg Sigma.snd heq
            simpa using this
          funext i
          exact Fin.lastCases h2 (fun j => congrFun h1 j) i
      rw [Finset.card_sigma] at hinj
      by_cases hlast : Fin.last n ∈ J
      · have hbound : ∀ xs' ∈ BadPrev, (ValidLast xs').card ≤ 2 ^ R := by
          intro xs' hxs'
          simp only [BadPrev, Finset.mem_filter, Finset.mem_univ, true_and] at hxs'
          simp only [ValidLast, hlast, ↓reduceIte]
          calc (Finset.univ.filter (fun v => InSpanList ((prefixIdx n xs').map xs') v)).card
              ≤ 2 ^ ((prefixIdx n xs').map xs').length := card_inSpanList _
            _ = 2 ^ (prefixIdx n xs').length := by rw [List.length_map]
            _ ≤ 2 ^ R := Nat.pow_le_pow_right (by omega) (le_of_lt hxs'.2)
        have hsum : (∑ xs' ∈ BadPrev, (ValidLast xs').card) ≤ BadPrev.card * 2 ^ R := by
          calc ∑ xs' ∈ BadPrev, (ValidLast xs').card
              ≤ ∑ _xs' ∈ BadPrev, 2 ^ R := Finset.sum_le_sum hbound
            _ = BadPrev.card * 2 ^ R := by simp
        have hJeq : J.card = J'.card + 1 := by simp [hJcard, hlast]
        have hsub_eq : n + 1 - J.card = n - J'.card := by omega
        calc BadCur.card ≤ BadPrev.card * 2 ^ R := le_trans hinj hsum
          _ ≤ ((2 ^ R) ^ J'.card * (2 ^ d) ^ (n - J'.card)) * 2 ^ R :=
                Nat.mul_le_mul_right _ hih
          _ = (2 ^ R) ^ (J'.card + 1) * (2 ^ d) ^ (n - J'.card) := by rw [pow_succ]; ring
          _ = (2 ^ R) ^ J.card * (2 ^ d) ^ (n + 1 - J.card) := by rw [hsub_eq, hJeq]
      · have hbound : ∀ xs' ∈ BadPrev, (ValidLast xs').card ≤ 2 ^ d := by
          intro xs' _
          simp only [ValidLast, hlast, ↓reduceIte, Finset.card_univ, Fintype.card_pi, ZMod.card,
            Finset.prod_const, Fintype.card_fin]
          exact le_refl _
        have hsum : (∑ xs' ∈ BadPrev, (ValidLast xs').card) ≤ BadPrev.card * 2 ^ d := by
          calc ∑ xs' ∈ BadPrev, (ValidLast xs').card
              ≤ ∑ _xs' ∈ BadPrev, 2 ^ d := Finset.sum_le_sum hbound
            _ = BadPrev.card * 2 ^ d := by simp
        have hJeq : J.card = J'.card := by simp [hJcard, hlast]
        have hsub_eq : n + 1 - J.card = (n - J'.card) + 1 := by omega
        calc BadCur.card ≤ BadPrev.card * 2 ^ d := le_trans hinj hsum
          _ ≤ ((2 ^ R) ^ J'.card * (2 ^ d) ^ (n - J'.card)) * 2 ^ d :=
                Nat.mul_le_mul_right _ hih
          _ = (2 ^ R) ^ J'.card * (2 ^ d) ^ ((n - J'.card) + 1) := by rw [pow_succ]; ring
          _ = (2 ^ R) ^ J.card * (2 ^ d) ^ (n + 1 - J.card) := by rw [hsub_eq, hJeq]

private lemma exists_good_u {a : ℕ} (ha : 16 ≤ a) :
    let m := 2 ^ a
    let d := 32 * a
    let W := Fin d → ZMod 2
    ∃ u : Fin m → W, ∀ f : Fin d → Fin m, Function.Injective f →
      ∃ idx : Fin (16 * a) → Fin d, Function.Injective idx ∧
        LinIndep (fun i => u (f (idx i))) := by
  intro m d W
  let BadSeq : Finset (Fin d → W) :=
    Finset.univ.filter (fun xs => (prefixIdx d xs).length < 16 * a)
  have hBadSeq : BadSeq.card ≤ 2 ^ (32 * a) * (2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a) := by
    let Js : Finset (Finset (Fin d)) :=
      (Finset.univ : Finset (Fin d)).powersetCard (16 * a)
    have hsub : BadSeq ⊆ Js.biUnion (fun J => Finset.univ.filter (fun xs : Fin d → W =>
        J ⊆ depSet d xs ∧ (prefixIdx d xs).length < 16 * a)) := by
      intro xs hxs
      simp only [BadSeq, Finset.mem_filter, Finset.mem_univ, true_and] at hxs
      have hdep : 16 * a ≤ (depSet d xs).card := by
        have := prefixIdx_add_depSet d xs
        omega
      rcases Finset.exists_subset_card_eq hdep with ⟨J, hJsub, hJcard⟩
      refine Finset.mem_biUnion.mpr ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJcard⟩, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hJsub, hxs⟩
    have hJs_card : Js.card ≤ 2 ^ (32 * a) := by
      calc Js.card ≤ (Finset.univ : Finset (Fin d)).powerset.card :=
            Finset.card_le_card (fun J hJ => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
        _ = 2 ^ (32 * a) := by simp [d]
    calc BadSeq.card
        ≤ ∑ J ∈ Js, (Finset.univ.filter (fun xs : Fin d → W =>
            J ⊆ depSet d xs ∧ (prefixIdx d xs).length < 16 * a)).card :=
          le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
      _ ≤ ∑ _J ∈ Js, (2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a) := by
          refine Finset.sum_le_sum fun J hJ => ?_
          have hJc : J.card = 16 * a := (Finset.mem_powersetCard.mp hJ).2
          have hc := card_bad_prefix (d := d) d (16 * a) J
          have hsub_d : d - J.card = 16 * a := by omega
          rw [hsub_d, hJc] at hc
          exact hc
      _ = Js.card * ((2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a)) := by simp
      _ ≤ 2 ^ (32 * a) * ((2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a)) :=
          Nat.mul_le_mul_right _ hJs_card
      _ = 2 ^ (32 * a) * (2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a) := by ring
  let InjF : Finset (Fin d → Fin m) := Finset.univ.filter Function.Injective
  have hInjF : InjF.card ≤ m ^ d := by
    calc InjF.card ≤ (Finset.univ : Finset (Fin d → Fin m)).card := Finset.card_filter_le _ _
      _ = m ^ d := by simp [Fintype.card_pi]
  have hd_le_m : d ≤ m := by
    have hpow : ∀ n : ℕ, 16 ≤ n → 32 * n ≤ 2 ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ihn =>
        by_cases h16 : n = 15
        · subst h16; norm_num
        · have hprev := ihn (by omega)
          have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
          omega
    exact hpow a ha
  have hper_f : ∀ f ∈ InjF,
      (Finset.univ.filter (fun u : Fin m → W => (prefixIdx d (u ∘ f)).length < 16 * a)).card ≤
      BadSeq.card * (2 ^ d) ^ (m - d) := by
    intro f hf
    have hinj_f : Function.Injective f := (Finset.mem_filter.mp hf).2
    let S : Finset (Fin m) := Finset.univ.image f
    have hScard : S.card = d := by
      rw [Finset.card_image_of_injective _ hinj_f, Finset.card_univ, Fintype.card_fin]
    have hcomp_card : Fintype.card {x : Fin m // x ∉ S} = m - d := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hScard]
    let proj : (Fin m → W) → (Fin d → W) × ({x : Fin m // x ∉ S} → W) :=
      fun u => (u ∘ f, fun x => u x.val)
    have hproj_inj : Function.Injective proj := by
      intro u₁ u₂ heq
      have h1 : u₁ ∘ f = u₂ ∘ f := congrArg Prod.fst heq
      have h2 : (fun x : {x : Fin m // x ∉ S} => u₁ x.val) = (fun x => u₂ x.val) :=
        congrArg Prod.snd heq
      funext x
      by_cases hx : x ∈ S
      · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact congrFun h1 i
      · exact congrFun h2 ⟨x, hx⟩
    calc (Finset.univ.filter (fun u : Fin m → W => (prefixIdx d (u ∘ f)).length < 16 * a)).card
        ≤ (BadSeq ×ˢ (Finset.univ : Finset ({x : Fin m // x ∉ S} → W))).card := by
          refine Finset.card_le_card_of_injOn proj ?_ (fun _ _ _ _ h => hproj_inj h)
          intro u hu
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, Finset.mem_univ _⟩)
      _ = BadSeq.card * (2 ^ d) ^ (m - d) := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_pi]
          simp [W, Fintype.card_pi, ZMod.card, Finset.prod_const, Fintype.card_fin, hcomp_card]
  let BadU : Finset (Fin m → W) :=
    InjF.biUnion (fun f => Finset.univ.filter (fun u : Fin m → W => (prefixIdx d (u ∘ f)).length < 16 * a))
  have hBadU_lt : BadU.card < (Finset.univ : Finset (Fin m → W)).card := by
    have htot : (Finset.univ : Finset (Fin m → W)).card = (2 ^ d) ^ m := by
      simp [W, Fintype.card_pi, ZMod.card]
    rw [htot]
    have h1 : BadU.card ≤ m ^ d * (BadSeq.card * (2 ^ d) ^ (m - d)) := by
      calc BadU.card
          ≤ ∑ f ∈ InjF, (Finset.univ.filter (fun u : Fin m → W =>
              (prefixIdx d (u ∘ f)).length < 16 * a)).card := Finset.card_biUnion_le
        _ ≤ ∑ _f ∈ InjF, BadSeq.card * (2 ^ d) ^ (m - d) := Finset.sum_le_sum hper_f
        _ = InjF.card * (BadSeq.card * (2 ^ d) ^ (m - d)) := by simp
        _ ≤ m ^ d * (BadSeq.card * (2 ^ d) ^ (m - d)) := Nat.mul_le_mul_right _ hInjF
    have h2 : m ^ d * BadSeq.card < (2 ^ d) ^ d := by
      have hmd : m ^ d = 2 ^ (32 * a ^ 2) := by
        simp only [m, d, ← Nat.pow_mul]
        congr 1; ring
      have hrhs : (2 ^ d) ^ d = 2 ^ (1024 * a ^ 2) := by
        simp only [d, ← Nat.pow_mul]
        congr 1; ring
      have hseq : 2 ^ (32 * a) * (2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a) =
          2 ^ (32 * a + 768 * a ^ 2) := by
        simp only [d, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; ring
      calc m ^ d * BadSeq.card
          ≤ m ^ d * (2 ^ (32 * a) * (2 ^ (16 * a)) ^ (16 * a) * (2 ^ d) ^ (16 * a)) :=
            Nat.mul_le_mul_left _ hBadSeq
        _ = 2 ^ (32 * a ^ 2) * 2 ^ (32 * a + 768 * a ^ 2) := by rw [hmd, hseq]
        _ = 2 ^ (32 * a + 800 * a ^ 2) := by rw [← Nat.pow_add]; congr 1; ring
        _ < 2 ^ (1024 * a ^ 2) := Nat.pow_lt_pow_right (by omega) (by nlinarith)
        _ = (2 ^ d) ^ d := hrhs.symm
    have hpos : 0 < (2 ^ d) ^ (m - d) := Nat.pos_of_ne_zero (by positivity)
    calc BadU.card ≤ (m ^ d * BadSeq.card) * (2 ^ d) ^ (m - d) := by
            have := h1; ring_nf at this ⊢; exact this
      _ < (2 ^ d) ^ d * (2 ^ d) ^ (m - d) := Nat.mul_lt_mul_of_pos_right h2 hpos
      _ = (2 ^ d) ^ (d + (m - d)) := (Nat.pow_add _ _ _).symm
      _ = (2 ^ d) ^ m := by rw [Nat.add_sub_of_le hd_le_m]
  have hne : (Finset.univ \ BadU).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin m → W)) ⊆ BadU := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne with ⟨u, hu⟩
  have hu_not : u ∉ BadU := (Finset.mem_sdiff.mp hu).2
  refine ⟨u, fun f hf => ?_⟩
  have hge : 16 * a ≤ (prefixIdx d (u ∘ f)).length := by
    by_contra hlt
    push Not at hlt
    apply hu_not
    refine Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  let L := prefixIdx d (u ∘ f)
  let idx : Fin (16 * a) → Fin d := fun i => L[i.val]'(lt_of_lt_of_le i.isLt hge)
  refine ⟨idx, ?_, ?_⟩
  · intro i₁ i₂ heq
    have hnd := prefixIdx_nodup d (u ∘ f)
    have hval := (List.Nodup.getElem_inj_iff hnd).mp heq
    exact Fin.ext hval
  · intro c hc
    have hli := prefixIdx_vecs_linIndep d (u ∘ f)
    let c' : Fin (L.map (u ∘ f)).length → ZMod 2 :=
      fun i => if h : i.val < 16 * a then c ⟨i.val, h⟩ else 0
    have hc' : ∀ j : Fin d, ∑ i : Fin (L.map (u ∘ f)).length,
        c' i * (L.map (u ∘ f))[i] j = 0 := by
      intro j
      rw [← hc j]
      have hlen_map : (L.map (u ∘ f)).length = L.length := List.length_map _
      rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun i : Fin (L.map (u ∘ f)).length =>
          i.val < 16 * a)) (Finset.subset_univ _)]
      · refine (Finset.sum_nbij (fun i : Fin (16 * a) =>
            (⟨i.val, by rw [hlen_map]; exact lt_of_lt_of_le i.isLt hge⟩ : Fin (L.map (u ∘ f)).length))
          ?_ ?_ ?_ ?_).symm
        · intro i _; simp [i.isLt]
        · intro i₁ _ i₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin (L.map (u ∘ f)).length → ℕ) h)
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨i.val, hi⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by ext; rfl⟩
        · intro i _
          simp [c', idx]
      · intro i _ hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [c', hi]
    have hzero := hli c' hc'
    intro i
    have hlen_map : (L.map (u ∘ f)).length = L.length := List.length_map _
    have hz := hzero ⟨i.val, by rw [hlen_map]; exact lt_of_lt_of_le i.isLt hge⟩
    simpa [c', i.isLt] using hz

private def sgn (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

private lemma sgn_zero : sgn 0 = 1 := rfl

private lemma sgn_one : sgn 1 = -1 := rfl

private lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rfl

private lemma sgn_neg (a : ZMod 2) : sgn (-a) = sgn a := by
  rw [zmod2_neg_eq]

private lemma sum_sgn_dot_eq_zero {n : ℕ} (w : Fin n → ZMod 2) (hw : ∃ k : Fin n, w k ≠ 0) :
    (∑ y : Fin n → ZMod 2, sgn (∑ j : Fin n, w j * y j)) = 0 := by
  rcases hw with ⟨k, hk⟩
  have hk1 : w k = 1 := by
    rcases zmod2_eq_zero_or_one (w k) with h0 | h1
    · exact absurd h0 hk
    · exact h1
  let flip : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun y => Function.update y k (y k + 1)
  have hinv : Function.Involutive flip := by
    intro y
    funext j
    by_cases hj : j = k
    · subst hj
      simp only [flip, Function.update_self]
      rw [add_assoc, zmod2_add_self, add_zero]
    · simp [flip, Function.update_of_ne hj]
  have hneg : ∀ y : Fin n → ZMod 2,
      sgn (∑ j : Fin n, w j * flip y j) = - sgn (∑ j : Fin n, w j * y j) := by
    intro y
    have hdiff : (∑ j : Fin n, w j * flip y j) = (∑ j : Fin n, w j * y j) + 1 := by
      have h1 := Finset.add_sum_erase (s := Finset.univ) (f := fun j : Fin n => w j * flip y j)
        (a := k) (Finset.mem_univ k)
      have h2 := Finset.add_sum_erase (s := Finset.univ) (f := fun j : Fin n => w j * y j)
        (a := k) (Finset.mem_univ k)
      have hrest : ∑ j ∈ Finset.univ.erase k, w j * flip y j =
          ∑ j ∈ Finset.univ.erase k, w j * y j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ k := (Finset.mem_erase.mp hj).1
        simp [flip, Function.update_of_ne hne]
      rw [← h1, ← h2, hrest]
      simp only [flip, Function.update_self, hk1, one_mul]
      ring
    rw [hdiff, sgn_add, sgn_one]
    ring
  set S : ℤ := ∑ y : Fin n → ZMod 2, sgn (∑ j : Fin n, w j * y j)
  have hS : S = -S := by
    calc S = ∑ y : Fin n → ZMod 2, sgn (∑ j : Fin n, w j * flip y j) :=
            (Fintype.sum_bijective flip hinv.bijective _ _ (fun _ => rfl)).symm
      _ = ∑ y : Fin n → ZMod 2, - sgn (∑ j : Fin n, w j * y j) :=
            Finset.sum_congr rfl fun y _ => hneg y
      _ = -S := by
            rw [Finset.sum_neg_distrib]
  omega

private lemma card_dot_eq {d R : ℕ} (xs : Fin R → (Fin d → ZMod 2)) (hli : LinIndep xs)
    (b : Fin R → ZMod 2) :
    2 ^ R * (Finset.univ.filter (fun y : Fin d → ZMod 2 =>
      ∀ i : Fin R, dot (xs i) y = b i)).card = 2 ^ d := by
  let L : (Fin d → ZMod 2) → (Fin R → ZMod 2) := fun y i => dot (xs i) y
  have hlhs : (∑ y : Fin d → ZMod 2, ∑ c : Fin R → ZMod 2,
      sgn (∑ i : Fin R, c i * (L y i + b i))) =
      ((2 ^ R : ℕ) : ℤ) * ((Finset.univ.filter (fun y : Fin d → ZMod 2 =>
        ∀ i : Fin R, dot (xs i) y = b i)).card : ℤ) := by
    have hinner : ∀ y : Fin d → ZMod 2,
        (∑ c : Fin R → ZMod 2, sgn (∑ i : Fin R, c i * (L y i + b i))) =
        if ∀ i : Fin R, dot (xs i) y = b i then ((2 ^ R : ℕ) : ℤ) else 0 := by
      intro y
      split_ifs with hy
      · have h0 : ∀ c : Fin R → ZMod 2, sgn (∑ i : Fin R, c i * (L y i + b i)) = 1 := by
          intro c
          have : (∑ i : Fin R, c i * (L y i + b i)) = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            have hbi : L y i + b i = 0 := by dsimp only [L]; rw [hy i, zmod2_add_self]
            rw [hbi, mul_zero]
          rw [this, sgn_zero]
        simp_rw [h0]
        simp [Fintype.card_pi, ZMod.card]
      · push Not at hy
        rcases hy with ⟨k, hk⟩
        have hne : L y k + b k ≠ 0 := fun h => hk ((zmod2_add_eq_zero_iff _ _).mp h)
        have hcomm : ∀ c : Fin R → ZMod 2,
            (∑ i : Fin R, c i * (L y i + b i)) = ∑ i : Fin R, (L y i + b i) * c i := by
          intro c; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
        simp_rw [hcomm]
        exact sum_sgn_dot_eq_zero (fun i => L y i + b i) ⟨k, hne⟩
    simp_rw [hinner]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hrhs : (∑ y : Fin d → ZMod 2, ∑ c : Fin R → ZMod 2,
      sgn (∑ i : Fin R, c i * (L y i + b i))) = ((2 ^ d : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    have hsplit : ∀ c : Fin R → ZMod 2,
        (∑ y : Fin d → ZMod 2, sgn (∑ i : Fin R, c i * (L y i + b i))) =
        sgn (∑ i : Fin R, c i * b i) *
          (∑ y : Fin d → ZMod 2, sgn (∑ j : Fin d, (∑ i : Fin R, c i * xs i j) * y j)) := by
      intro c
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hrew : (∑ i : Fin R, c i * (L y i + b i)) =
          (∑ i : Fin R, c i * b i) + (∑ j : Fin d, (∑ i : Fin R, c i * xs i j) * y j) := by
        simp only [mul_add, Finset.sum_add_distrib, L, dot]
        rw [add_comm]
        congr 1
        simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [hrew, sgn_add]
    simp_rw [hsplit]
    rw [Finset.sum_eq_single (0 : Fin R → ZMod 2)]
    · have h0 : ∀ y : Fin d → ZMod 2,
          sgn (∑ j : Fin d, (∑ i : Fin R, (0 : Fin R → ZMod 2) i * xs i j) * y j) = 1 := by
        intro y; simp [sgn_zero]
      simp_rw [h0]
      simp [sgn_zero, Fintype.card_pi, ZMod.card]
    · intro c _ hc
      have hne : ∃ j : Fin d, (∑ i : Fin R, c i * xs i j) ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hc (funext (hli c hall))
      rw [sum_sgn_dot_eq_zero _ hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hInt : ((2 ^ R * (Finset.univ.filter (fun y : Fin d → ZMod 2 =>
      ∀ i : Fin R, dot (xs i) y = b i)).card : ℕ) : ℤ) = ((2 ^ d : ℕ) : ℤ) := by
    rw [Nat.cast_mul, ← hlhs, hrhs]
  exact Int.ofNat.inj hInt

private lemma sum_choose_le_pow (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Nat.choose (16 * n) k) ≤ 2 ^ (8 * n) := by
  have hq : ((∑ k ∈ Finset.range (n + 1), Nat.choose (16 * n) k : ℕ) : ℚ) ≤
      ((2 ^ (8 * n) : ℕ) : ℚ) := by
    have h1 : (∑ k ∈ Finset.range (n + 1), (Nat.choose (16 * n) k : ℚ)) * ((1 / 8 : ℚ) ^ n) ≤
        ∑ k ∈ Finset.range (16 * n + 1), (Nat.choose (16 * n) k : ℚ) * ((1 / 8 : ℚ) ^ k) := by
      rw [Finset.sum_mul]
      calc ∑ k ∈ Finset.range (n + 1), (Nat.choose (16 * n) k : ℚ) * (1 / 8 : ℚ) ^ n
          ≤ ∑ k ∈ Finset.range (n + 1), (Nat.choose (16 * n) k : ℚ) * (1 / 8 : ℚ) ^ k := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn
        _ ≤ ∑ k ∈ Finset.range (16 * n + 1), (Nat.choose (16 * n) k : ℚ) * (1 / 8 : ℚ) ^ k := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            exact Finset.range_mono (by omega)
    have hbinom : (∑ k ∈ Finset.range (16 * n + 1),
        (Nat.choose (16 * n) k : ℚ) * ((1 / 8 : ℚ) ^ k)) = (9 / 8 : ℚ) ^ (16 * n) := by
      have hadd := add_pow (1 / 8 : ℚ) (1 : ℚ) (16 * n)
      have h98 : (1 / 8 : ℚ) + 1 = 9 / 8 := by norm_num
      rw [h98] at hadd
      rw [hadd]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    have h2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose (16 * n) k : ℚ)) ≤
        ((9 ^ 16 / 8 ^ 15 : ℚ)) ^ n := by
      have hpos : (0 : ℚ) < (1 / 8 : ℚ) ^ n := by positivity
      have hmul : (∑ k ∈ Finset.range (n + 1), (Nat.choose (16 * n) k : ℚ)) * (1 / 8 : ℚ) ^ n ≤
          (9 / 8 : ℚ) ^ (16 * n) := by rw [← hbinom]; exact h1
      have hdiv : (9 / 8 : ℚ) ^ (16 * n) = ((9 ^ 16 / 8 ^ 15 : ℚ)) ^ n * (1 / 8 : ℚ) ^ n := by
        rw [← mul_pow, pow_mul]
        congr 1
        norm_num
      rw [hdiv] at hmul
      exact le_of_mul_le_mul_right hmul hpos
    have hbase : (9 ^ 16 / 8 ^ 15 : ℚ) ≤ (2 ^ 8 : ℚ) := by norm_num
    have h3 : ((9 ^ 16 / 8 ^ 15 : ℚ)) ^ n ≤ ((2 ^ 8 : ℚ)) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    have hcast : ((2 ^ 8 : ℚ)) ^ n = ((2 ^ (8 * n) : ℕ) : ℚ) := by
      rw [← pow_mul]; push_cast; rfl
    rw [Nat.cast_sum, ← hcast]
    exact le_trans h2 h3
  exact_mod_cast hq

private lemma card_weight_le {M K : ℕ} :
    (Finset.univ.filter (fun v : Fin M → ZMod 2 =>
      (Finset.univ.filter (fun i : Fin M => v i ≠ 0)).card ≤ K)).card ≤
    ∑ k ∈ Finset.range (K + 1), Nat.choose M k := by
  let S : Finset (Finset (Fin M)) :=
    (Finset.range (K + 1)).biUnion (fun k => (Finset.univ : Finset (Fin M)).powersetCard k)
  have hS : S.card ≤ ∑ k ∈ Finset.range (K + 1), Nat.choose M k := by
    calc S.card ≤ ∑ k ∈ Finset.range (K + 1),
          ((Finset.univ : Finset (Fin M)).powersetCard k).card := Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.range (K + 1), Nat.choose M k := by
          refine Finset.sum_congr rfl fun k _ => by simp
  refine le_trans ?_ hS
  refine Finset.card_le_card_of_injOn
    (fun v : Fin M → ZMod 2 => Finset.univ.filter (fun i : Fin M => v i ≠ 0)) ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨(Finset.univ.filter (fun i : Fin M => v i ≠ 0)).card,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hv),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩)
  · intro v₁ _ v₂ _ heq
    funext i
    have hiff : v₁ i ≠ 0 ↔ v₂ i ≠ 0 := by
      have := Finset.ext_iff.mp heq i
      simpa using this
    rcases zmod2_eq_zero_or_one (v₁ i) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (v₂ i) with h2 | h2
    · rw [h1, h2]
    · exfalso; rw [h1, h2] at hiff; simp at hiff
    · exfalso; rw [h1, h2] at hiff; simp at hiff
    · rw [h1, h2]

private lemma exists_good_uv {a : ℕ} (ha : 16 ≤ a) :
    let m := 2 ^ a
    let d := 32 * a
    let W := Fin d → ZMod 2
    ∃ u v : Fin m → W,
      ∀ (f g : Fin (64 * a) → Fin m) (_ : Function.Injective f) (_ : Function.Injective g)
        (s : Fin (64 * a) → ZMod 2),
        32 * a ^ 2 < ((Finset.univ : Finset (Fin (64 * a) × Fin (64 * a))).filter (fun z =>
          dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠ s z.1 + s z.2)).card := by
  intro m d W
  rcases exists_good_u ha with ⟨u, hu⟩
  let r₀ := 64 * a
  let h₀ := 32 * a
  let R := 16 * a
  let GoodTriples : Finset ((Fin r₀ → Fin m) × (Fin r₀ → Fin m) × (Fin r₀ → ZMod 2)) :=
    Finset.univ.filter (fun t => Function.Injective t.1 ∧ Function.Injective t.2.1)
  have hTriples_card : GoodTriples.card ≤ m ^ r₀ * m ^ r₀ * 2 ^ r₀ := by
    calc GoodTriples.card
        ≤ (Finset.univ : Finset ((Fin r₀ → Fin m) × (Fin r₀ → Fin m) × (Fin r₀ → ZMod 2))).card :=
          Finset.card_filter_le _ _
      _ = m ^ r₀ * (m ^ r₀ * 2 ^ r₀) := by simp [Fintype.card_pi, ZMod.card]
      _ = m ^ r₀ * m ^ r₀ * 2 ^ r₀ := by ring
  have hd_le_m : d ≤ m := by
    have hpow : ∀ n : ℕ, 16 ≤ n → 32 * n ≤ 2 ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ihn =>
        by_cases h16 : n = 15
        · subst h16; norm_num
        · have hprev := ihn (by omega)
          have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
          omega
    exact hpow a ha
  let badFor (f g : Fin r₀ → Fin m) (s : Fin r₀ → ZMod 2) : Finset (Fin m → W) :=
    Finset.univ.filter (fun v =>
      ((Finset.univ : Finset (Fin r₀ × Fin r₀)).filter (fun z =>
        dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠ s z.1 + s z.2)).card ≤
      32 * a ^ 2)
  have hper_t : ∀ t ∈ GoodTriples,
      2 ^ (256 * a ^ 2) * (badFor t.1 t.2.1 t.2.2).card ≤ (2 ^ d) ^ m := by
    intro ⟨f, g, s⟩ ht
    simp only [GoodTriples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨hf, hg⟩
    let embA : Fin h₀ → Fin r₀ := fun i => ⟨i.val, by omega⟩
    let embB : Fin h₀ → Fin r₀ := fun j => ⟨h₀ + j.val, by omega⟩
    have hfA : Function.Injective (f ∘ embA) := by
      intro i₁ i₂ heq
      have h1 : embA i₁ = embA i₂ := hf heq
      exact Fin.ext (congrArg (Fin.val : Fin r₀ → ℕ) h1)
    rcases hu (f ∘ embA) hfA with ⟨idx, hidx, hli⟩
    let xs : Fin R → W := fun i => u (f (embA (idx i)))
    let S_B : Finset (Fin m) := Finset.univ.image (fun j : Fin h₀ => g (embB j))
    have hhgB : Function.Injective (fun j : Fin h₀ => g (embB j)) := by
      intro j₁ j₂ heq
      have h1 : (embB j₁).val = (embB j₂).val := congrArg (Fin.val : Fin r₀ → ℕ) (hg heq)
      exact Fin.ext (by dsimp only [embB] at h1; omega)
    have hSB_card : S_B.card = h₀ := by
      rw [Finset.card_image_of_injective _ hhgB, Finset.card_univ, Fintype.card_fin]
    have hcomp_card : Fintype.card {x : Fin m // x ∉ S_B} = m - h₀ := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hSB_card]
    have hA_not_SB : ∀ i : Fin R, g (embA (idx i)) ∉ S_B := by
      intro i hmem
      rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
      have h1 : (embB j).val = (embA (idx i)).val := congrArg (Fin.val : Fin r₀ → ℕ) (hg hj)
      have h2 := (idx i).isLt
      dsimp only [embA, embB] at h1
      omega
    let proj : (Fin m → W) → ({x : Fin m // x ∉ S_B} → W) × (Fin h₀ → W) :=
      fun v => (fun x => v x.val, fun j => v (g (embB j)))
    have hproj_inj : Function.Injective proj := by
      intro v₁ v₂ heq
      have h1 : (fun x : {x : Fin m // x ∉ S_B} => v₁ x.val) = (fun x => v₂ x.val) :=
        congrArg Prod.fst heq
      have h2 : (fun j : Fin h₀ => v₁ (g (embB j))) = (fun j => v₂ (g (embB j))) :=
        congrArg Prod.snd heq
      funext x
      by_cases hx : x ∈ S_B
      · rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        exact congrFun h2 j
      · exact congrFun h1 ⟨x, hx⟩
    let errMat (vOut : {x : Fin m // x ∉ S_B} → W) (vIn : Fin h₀ → W) :
        Fin h₀ × Fin R → ZMod 2 :=
      fun p =>
        dot (xs p.2) (vIn p.1) +
        dot (u (f (embB p.1))) (vOut ⟨g (embA (idx p.2)), hA_not_SB p.2⟩) +
        s (embA (idx p.2)) + s (embB p.1)
    let SmallIn (vOut : {x : Fin m // x ∉ S_B} → W) : Finset (Fin h₀ → W) :=
      Finset.univ.filter (fun vIn =>
        (Finset.univ.filter (fun p : Fin h₀ × Fin R => errMat vOut vIn p ≠ 0)).card ≤ 32 * a ^ 2)
    have hbad_sub : (badFor f g s).card ≤
        ((Finset.univ : Finset ({x : Fin m // x ∉ S_B} → W)).sigma SmallIn).card := by
      refine Finset.card_le_card_of_injOn (fun v => ⟨(proj v).1, (proj v).2⟩) ?_ ?_
      · intro v hv
        simp only [badFor, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩)
        simp only [SmallIn, Finset.mem_filter, Finset.mem_univ, true_and]
        have hle : (Finset.univ.filter (fun p : Fin h₀ × Fin R =>
            errMat (proj v).1 (proj v).2 p ≠ 0)).card ≤
            ((Finset.univ : Finset (Fin r₀ × Fin r₀)).filter (fun z =>
              dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠ s z.1 + s z.2)).card := by
          refine Finset.card_le_card_of_injOn
            (fun p : Fin h₀ × Fin R => (embA (idx p.2), embB p.1)) ?_ ?_
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
            intro heq
            apply hp
            dsimp only [errMat, proj, xs]
            have hsum0 : (dot (u (f (embA (idx p.2)))) (v (g (embB p.1))) +
                dot (u (f (embB p.1))) (v (g (embA (idx p.2))))) +
                (s (embA (idx p.2)) + s (embB p.1)) = 0 := by
              rw [heq, zmod2_add_self]
            simpa [add_assoc] using hsum0
          · intro p₁ _ p₂ _ heq
            have h1 : idx p₁.2 = idx p₂.2 :=
              Fin.ext (congrArg (Fin.val : Fin r₀ → ℕ) (congrArg Prod.fst heq))
            have h2 : p₁.1 = p₂.1 := Fin.ext (by
              have hval : (embB p₁.1).val = (embB p₂.1).val :=
                congrArg (Fin.val : Fin r₀ → ℕ) (congrArg Prod.snd heq)
              dsimp only [embB] at hval; omega)
            exact Prod.ext h2 (hidx h1)
        exact le_trans hle hv
      · intro v₁ _ v₂ _ heq
        apply hproj_inj
        exact Prod.ext (congrArg Sigma.fst heq) (by simpa using congrArg Sigma.snd heq)
    have hSmallIn : ∀ vOut : {x : Fin m // x ∉ S_B} → W,
        (SmallIn vOut).card ≤ 2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2) := by
      intro vOut
      let SmallMat : Finset (Fin h₀ × Fin R → ZMod 2) :=
        Finset.univ.filter (fun M => (Finset.univ.filter (fun p => M p ≠ 0)).card ≤ 32 * a ^ 2)
      have hSmallMat_card : SmallMat.card ≤ 2 ^ (256 * a ^ 2) := by
        let e : Fin (h₀ * R) ≃ Fin h₀ × Fin R := finProdFinEquiv.symm
        have hcard_eq : SmallMat.card =
            (Finset.univ.filter (fun M : Fin (h₀ * R) → ZMod 2 =>
              (Finset.univ.filter (fun i => M i ≠ 0)).card ≤ 32 * a ^ 2)).card := by
          refine Finset.card_bij (fun M _ => M ∘ e) ?_ ?_ ?_
          · intro M hM
            simp only [SmallMat, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
            have hce : (Finset.univ.filter (fun i : Fin (h₀ * R) => M (e i) ≠ 0)).card =
                (Finset.univ.filter (fun p : Fin h₀ × Fin R => M p ≠ 0)).card := by
              refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
              · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
              · intro i₁ _ i₂ _ h; exact e.injective h
              · intro p hp
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
                exact ⟨e.symm p, by simp [hp], e.apply_symm_apply p⟩
            dsimp only [Function.comp_apply]
            rw [hce]; exact hM
          · intro M₁ _ M₂ _ h
            funext p
            have := congrFun h (e.symm p)
            simpa using this
          · intro M hM
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
            refine ⟨M ∘ e.symm, ?_, by funext i; simp⟩
            simp only [SmallMat, Finset.mem_filter, Finset.mem_univ, true_and]
            have hce : (Finset.univ.filter (fun p : Fin h₀ × Fin R => M (e.symm p) ≠ 0)).card =
                (Finset.univ.filter (fun i : Fin (h₀ * R) => M i ≠ 0)).card := by
              refine Finset.card_bij (fun p _ => e.symm p) ?_ ?_ ?_
              · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
              · intro p₁ _ p₂ _ h; exact e.symm.injective h
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                exact ⟨e i, by simp [hi], e.symm_apply_apply i⟩
            dsimp only [Function.comp_apply]
            rw [hce]; exact hM
        rw [hcard_eq]
        have hM_eq : h₀ * R = 16 * (32 * a ^ 2) := by dsimp [h₀, R]; ring
        have h8_eq : 8 * (32 * a ^ 2) = 256 * a ^ 2 := by ring
        calc (Finset.univ.filter (fun M : Fin (h₀ * R) → ZMod 2 =>
                (Finset.univ.filter (fun i => M i ≠ 0)).card ≤ 32 * a ^ 2)).card
            ≤ ∑ k ∈ Finset.range (32 * a ^ 2 + 1), Nat.choose (h₀ * R) k := card_weight_le
          _ = ∑ k ∈ Finset.range (32 * a ^ 2 + 1), Nat.choose (16 * (32 * a ^ 2)) k := by
              rw [hM_eq]
          _ ≤ 2 ^ (8 * (32 * a ^ 2)) := sum_choose_le_pow (32 * a ^ 2)
          _ = 2 ^ (256 * a ^ 2) := by rw [h8_eq]
      have hfiber : ∀ M : Fin h₀ × Fin R → ZMod 2,
          (Finset.univ.filter (fun vIn : Fin h₀ → W => errMat vOut vIn = M)).card =
          2 ^ (512 * a ^ 2) := by
        intro M
        let target : Fin h₀ → Fin R → ZMod 2 := fun j i =>
          M (j, i) + dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩) +
          s (embA (idx i)) + s (embB j)
        let fiberJ : Fin h₀ → Finset W := fun j =>
          Finset.univ.filter (fun w : W => ∀ i : Fin R, dot (xs i) w = target j i)
        have hfiber_eq : Finset.univ.filter (fun vIn : Fin h₀ → W => errMat vOut vIn = M) =
            Fintype.piFinset fiberJ := by
          ext vIn
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, fiberJ]
          constructor
          · intro h j i
            have hij := congrFun h (j, i)
            dsimp only [errMat] at hij
            dsimp only [target]
            rw [← hij]
            have hadd0 : ∀ x y : ZMod 2, (x + y) + y = x := fun x y => by
              rw [add_assoc, zmod2_add_self, add_zero]
            have : dot (xs i) (vIn j) +
                dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩) +
                s (embA (idx i)) + s (embB j) +
                dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩) +
                s (embA (idx i)) + s (embB j) = dot (xs i) (vIn j) := by
              have h1 := zmod2_add_self (dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩))
              have h2 := zmod2_add_self (s (embA (idx i)))
              have h3 := zmod2_add_self (s (embB j))
              calc _ = dot (xs i) (vIn j) +
                    (dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩) +
                     dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩)) +
                    (s (embA (idx i)) + s (embA (idx i))) +
                    (s (embB j) + s (embB j)) := by ring
                _ = dot (xs i) (vIn j) := by rw [h1, h2, h3]; simp
            exact this.symm
          · intro h
            funext ⟨j, i⟩
            dsimp only [errMat]
            rw [h j i]
            dsimp only [target]
            have h1 := zmod2_add_self (dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩))
            have h2 := zmod2_add_self (s (embA (idx i)))
            have h3 := zmod2_add_self (s (embB j))
            calc _ = M (j, i) +
                  (dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩) +
                   dot (u (f (embB j))) (vOut ⟨g (embA (idx i)), hA_not_SB i⟩)) +
                  (s (embA (idx i)) + s (embA (idx i))) +
                  (s (embB j) + s (embB j)) := by ring
              _ = M (j, i) := by rw [h1, h2, h3]; simp
        rw [hfiber_eq, Fintype.card_piFinset]
        have hj_card : ∀ j : Fin h₀, (fiberJ j).card = 2 ^ R := by
          intro j
          have hcd := card_dot_eq xs hli (target j)
          have hd_eq : 2 ^ d = 2 ^ R * 2 ^ R := by
            rw [← Nat.pow_add]; congr 1; dsimp [d, R]; omega
          rw [hd_eq] at hcd
          exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos R) hcd
        simp_rw [hj_card]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Nat.pow_mul]
        congr 1; dsimp [R, h₀]; ring
      have hdecomp : SmallIn vOut ⊆ SmallMat.biUnion
          (fun M => Finset.univ.filter (fun vIn : Fin h₀ → W => errMat vOut vIn = M)) := by
        intro vIn hvIn
        simp only [SmallIn, Finset.mem_filter, Finset.mem_univ, true_and] at hvIn
        refine Finset.mem_biUnion.mpr ⟨errMat vOut vIn, ?_, ?_⟩
        · simp only [SmallMat, Finset.mem_filter, Finset.mem_univ, true_and]; exact hvIn
        · simp
      calc (SmallIn vOut).card
          ≤ ∑ M ∈ SmallMat, (Finset.univ.filter (fun vIn : Fin h₀ → W => errMat vOut vIn = M)).card :=
            le_trans (Finset.card_le_card hdecomp) Finset.card_biUnion_le
        _ = ∑ _M ∈ SmallMat, 2 ^ (512 * a ^ 2) := by
            refine Finset.sum_congr rfl fun M _ => hfiber M
        _ = SmallMat.card * 2 ^ (512 * a ^ 2) := by simp
        _ ≤ 2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2) := Nat.mul_le_mul_right _ hSmallMat_card
    rw [Finset.card_sigma] at hbad_sub
    have hsum_out : (∑ vOut : {x : Fin m // x ∉ S_B} → W, (SmallIn vOut).card) ≤
        (2 ^ d) ^ (m - h₀) * (2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2)) := by
      calc ∑ vOut : {x : Fin m // x ∉ S_B} → W, (SmallIn vOut).card
          ≤ ∑ _vOut : {x : Fin m // x ∉ S_B} → W, 2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2) :=
            Finset.sum_le_sum fun vOut _ => hSmallIn vOut
        _ = (2 ^ d) ^ (m - h₀) * (2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2)) := by
            simp [W, Fintype.card_pi, ZMod.card, hcomp_card]
    have hpow_d : 2 ^ (256 * a ^ 2) * (2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2)) = (2 ^ d) ^ h₀ := by
      simp only [d, h₀, ← Nat.pow_mul, ← Nat.pow_add]
      congr 1; ring
    calc 2 ^ (256 * a ^ 2) * (badFor f g s).card
        ≤ 2 ^ (256 * a ^ 2) * ((2 ^ d) ^ (m - h₀) * (2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2))) :=
          Nat.mul_le_mul_left _ (le_trans hbad_sub hsum_out)
      _ = (2 ^ d) ^ (m - h₀) * (2 ^ (256 * a ^ 2) * (2 ^ (256 * a ^ 2) * 2 ^ (512 * a ^ 2))) := by
          ring
      _ = (2 ^ d) ^ (m - h₀) * (2 ^ d) ^ h₀ := by rw [hpow_d]
      _ = (2 ^ d) ^ ((m - h₀) + h₀) := (Nat.pow_add _ _ _).symm
      _ = (2 ^ d) ^ m := by rw [Nat.sub_add_cancel hd_le_m]
  let BadV : Finset (Fin m → W) :=
    GoodTriples.biUnion (fun t => badFor t.1 t.2.1 t.2.2)
  have hBadV_lt : BadV.card < (Finset.univ : Finset (Fin m → W)).card := by
    have htot : (Finset.univ : Finset (Fin m → W)).card = (2 ^ d) ^ m := by
      simp [W, Fintype.card_pi, ZMod.card]
    rw [htot]
    have hmul_le : 2 ^ (256 * a ^ 2) * BadV.card ≤ GoodTriples.card * (2 ^ d) ^ m := by
      calc 2 ^ (256 * a ^ 2) * BadV.card
          ≤ 2 ^ (256 * a ^ 2) * ∑ t ∈ GoodTriples, (badFor t.1 t.2.1 t.2.2).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ t ∈ GoodTriples, 2 ^ (256 * a ^ 2) * (badFor t.1 t.2.1 t.2.2).card :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ _t ∈ GoodTriples, (2 ^ d) ^ m := Finset.sum_le_sum hper_t
        _ = GoodTriples.card * (2 ^ d) ^ m := by simp
    have htrip_lt : GoodTriples.card < 2 ^ (256 * a ^ 2) := by
      have hbound : m ^ r₀ * m ^ r₀ * 2 ^ r₀ = 2 ^ (128 * a ^ 2 + 64 * a) := by
        simp only [m, r₀, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; ring
      calc GoodTriples.card ≤ m ^ r₀ * m ^ r₀ * 2 ^ r₀ := hTriples_card
        _ = 2 ^ (128 * a ^ 2 + 64 * a) := hbound
        _ < 2 ^ (256 * a ^ 2) := Nat.pow_lt_pow_right (by omega) (by nlinarith)
    have hpos : 0 < (2 ^ d) ^ m := Nat.pos_of_ne_zero (by positivity)
    have hstrict : 2 ^ (256 * a ^ 2) * BadV.card < 2 ^ (256 * a ^ 2) * (2 ^ d) ^ m :=
      lt_of_le_of_lt hmul_le (Nat.mul_lt_mul_of_pos_right htrip_lt hpos)
    exact Nat.lt_of_mul_lt_mul_left hstrict
  have hne : (Finset.univ \ BadV).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin m → W)) ⊆ BadV := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne with ⟨v, hv⟩
  have hv_not : v ∉ BadV := (Finset.mem_sdiff.mp hv).2
  refine ⟨u, v, fun f g hf hg s => ?_⟩
  by_contra hle
  push Not at hle
  apply hv_not
  refine Finset.mem_biUnion.mpr ⟨(f, g, s), ?_, ?_⟩
  · simp only [GoodTriples, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hf, hg⟩
  · simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and]; exact hle

private lemma choose_succ_mul (n r : ℕ) :
    Nat.choose (n + 1) (r + 1) * (r + 1) = (n + 1) * Nat.choose n r := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp
    | succ r =>
      have h0 : Nat.choose 1 (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [Nat.choose_succ_succ (n + 1) (r + 1)]
      have h1 := ih (r + 1)
      have h2 := ih r
      have h3 := Nat.choose_succ_succ n r
      nlinarith

private lemma choose_mul_two_step (n r : ℕ) (h2 : 2 ≤ r) (hrn : r ≤ n) :
    Nat.choose n r * (r * (r - 1)) = n * (n - 1) * Nat.choose (n - 2) (r - 2) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have h1 := choose_succ_mul (n' + 1) (r' + 1)
  have h2' := choose_succ_mul n' r'
  have hsub1 : r' + 2 - 1 = r' + 1 := by omega
  have hsub2 : n' + 2 - 1 = n' + 1 := by omega
  simp only [Nat.add_sub_cancel, hsub1, hsub2]
  nlinarith

private lemma large_class_conflicts {a m : ℕ} (ha : 16 ≤ a)
    (u v : Fin m → (Fin (32 * a) → ZMod 2))
    (huv : ∀ (f g : Fin (64 * a) → Fin m), Function.Injective f → Function.Injective g →
      ∀ s : Fin (64 * a) → ZMod 2,
        32 * a ^ 2 < ((Finset.univ : Finset (Fin (64 * a) × Fin (64 * a))).filter (fun z =>
          dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠ s z.1 + s z.2)).card)
    (P : Finset (Fin m)) (hP : 64 * a ≤ P.card)
    (β : Fin m → Fin m) (hβ : Set.InjOn β (P : Set (Fin m)))
    (s : Fin m → ZMod 2) :
    P.card ^ 2 < 256 * ((P ×ˢ P).filter (fun z =>
      dot (u z.1) (v (β z.2)) + dot (u z.2) (v (β z.1)) ≠ s z.1 + s z.2)).card := by
  let r₀ := 64 * a
  let K := (P ×ˢ P).filter (fun z =>
    dot (u z.1) (v (β z.2)) + dot (u z.2) (v (β z.1)) ≠ s z.1 + s z.2)
  have hne_K : ∀ z ∈ K, z.1 ≠ z.2 := by
    intro z hz heq
    simp only [K, Finset.mem_filter, Finset.mem_product] at hz
    apply hz.2
    rw [heq, zmod2_add_self, zmod2_add_self]
  let Qs := P.powersetCard r₀
  have hQ_each : ∀ Q ∈ Qs, 32 * a ^ 2 + 1 ≤ (K.filter (fun z => z.1 ∈ Q ∧ z.2 ∈ Q)).card := by
    intro Q hQ
    rcases Finset.mem_powersetCard.mp hQ with ⟨hQP, hQcard⟩
    let e : Fin r₀ ≃ Q := (Fintype.equivFinOfCardEq (by simp [hQcard])).symm
    let f : Fin r₀ → Fin m := fun i => (e i).val
    let g : Fin r₀ → Fin m := fun i => β (e i).val
    have hf : Function.Injective f := fun i₁ i₂ h => e.injective (Subtype.ext h)
    have hg : Function.Injective g := fun i₁ i₂ h =>
      e.injective (Subtype.ext (hβ (hQP (e i₁).property) (hQP (e i₂).property) h))
    have hlt := huv f g hf hg (fun i => s (e i).val)
    have hle : ((Finset.univ : Finset (Fin r₀ × Fin r₀)).filter (fun z =>
        dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠
          s (e z.1).val + s (e z.2).val)).card ≤
        (K.filter (fun z => z.1 ∈ Q ∧ z.2 ∈ Q)).card := by
      refine Finset.card_le_card_of_injOn (fun z => (f z.1, f z.2)) ?_ ?_
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, K,
          Finset.mem_product] at hz ⊢
        exact ⟨⟨⟨hQP (e z.1).property, hQP (e z.2).property⟩, hz⟩,
               (e z.1).property, (e z.2).property⟩
      · intro z₁ _ z₂ _ heq
        exact Prod.ext (hf (congrArg Prod.fst heq)) (hf (congrArg Prod.snd heq))
    have hlt' : 32 * a ^ 2 < (K.filter (fun z => z.1 ∈ Q ∧ z.2 ∈ Q)).card := lt_of_lt_of_le hlt hle
    omega
  have hK_each : ∀ z ∈ K, (Qs.filter (fun Q => z.1 ∈ Q ∧ z.2 ∈ Q)).card =
      Nat.choose (P.card - 2) (r₀ - 2) := by
    intro z hz
    have hmemP : z.1 ∈ P ∧ z.2 ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    have hne : z.1 ≠ z.2 := hne_K z hz
    let pair : Finset (Fin m) := {z.1, z.2}
    have hpair_sub : pair ⊆ P := by
      intro x hx
      simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hmemP.1; exact hmemP.2]
    have hpair_card : pair.card = 2 := Finset.card_pair hne
    have hsdiff_card : (P \ pair).card = P.card - 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpair_sub, hpair_card]
    have hbij : (Qs.filter (fun Q => z.1 ∈ Q ∧ z.2 ∈ Q)).card =
        ((P \ pair).powersetCard (r₀ - 2)).card := by
      refine Finset.card_bij (fun Q _ => Q \ pair) ?_ ?_ ?_
      · intro Q hQ
        simp only [Finset.mem_filter, Qs, Finset.mem_powersetCard] at hQ ⊢
        have hpQ : pair ⊆ Q := by
          intro x hx
          simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> [exact hQ.2.1; exact hQ.2.2]
        refine ⟨Finset.sdiff_subset_sdiff hQ.1.1 (subset_refl _), ?_⟩
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpQ, hQ.1.2, hpair_card]
      · intro Q₁ hQ₁ Q₂ hQ₂ heq
        simp only [Finset.mem_filter, Qs, Finset.mem_powersetCard] at hQ₁ hQ₂
        ext x
        by_cases hx : x ∈ pair
        · simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [hQ₁.2.1, hQ₁.2.2, hQ₂.2.1, hQ₂.2.2]
        · have hiff := Finset.ext_iff.mp heq x
          simpa [Finset.mem_sdiff, hx] using hiff
      · intro R hR
        rw [Finset.mem_powersetCard] at hR
        refine ⟨R ∪ pair, ?_, ?_⟩
        · simp only [Finset.mem_filter, Qs, Finset.mem_powersetCard]
          have hdisj : Disjoint R pair :=
            Disjoint.mono_left hR.1 Finset.sdiff_disjoint
          refine ⟨⟨Finset.union_subset (subset_trans hR.1 Finset.sdiff_subset) hpair_sub, ?_⟩,
            Finset.mem_union_right _ (Finset.mem_insert_self _ _),
            Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
          rw [Finset.card_union_of_disjoint hdisj, hR.2, hpair_card]
          omega
        · have hdisj : Disjoint R pair :=
            Disjoint.mono_left hR.1 Finset.sdiff_disjoint
          exact Finset.union_sdiff_cancel_right hdisj
    rw [hbij, Finset.card_powersetCard, hsdiff_card]
  have hdouble : (∑ Q ∈ Qs, (K.filter (fun z => z.1 ∈ Q ∧ z.2 ∈ Q)).card) =
      ∑ z ∈ K, (Qs.filter (fun Q => z.1 ∈ Q ∧ z.2 ∈ Q)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlo : Qs.card * (32 * a ^ 2 + 1) ≤ K.card * Nat.choose (P.card - 2) (r₀ - 2) := by
    calc Qs.card * (32 * a ^ 2 + 1)
        = ∑ _Q ∈ Qs, (32 * a ^ 2 + 1) := by simp
      _ ≤ ∑ Q ∈ Qs, (K.filter (fun z => z.1 ∈ Q ∧ z.2 ∈ Q)).card := Finset.sum_le_sum hQ_each
      _ = ∑ z ∈ K, (Qs.filter (fun Q => z.1 ∈ Q ∧ z.2 ∈ Q)).card := hdouble
      _ = ∑ _z ∈ K, Nat.choose (P.card - 2) (r₀ - 2) := Finset.sum_congr rfl hK_each
      _ = K.card * Nat.choose (P.card - 2) (r₀ - 2) := by simp
  have hQs_card : Qs.card = Nat.choose P.card r₀ := Finset.card_powersetCard r₀ P
  rw [hQs_card] at hlo
  have hmul := Nat.mul_le_mul_right (r₀ * (r₀ - 1)) hlo
  have hstep := choose_mul_two_step P.card r₀ (by omega) hP
  have hcho_pos : 0 < Nat.choose (P.card - 2) (r₀ - 2) :=
    Nat.choose_pos (by omega)
  have hcancel : P.card * (P.card - 1) * (32 * a ^ 2 + 1) ≤ K.card * (r₀ * (r₀ - 1)) := by
    apply Nat.le_of_mul_le_mul_right _ hcho_pos
    calc P.card * (P.card - 1) * (32 * a ^ 2 + 1) * Nat.choose (P.card - 2) (r₀ - 2)
        = (P.card * (P.card - 1) * Nat.choose (P.card - 2) (r₀ - 2)) * (32 * a ^ 2 + 1) := by ring
      _ = (Nat.choose P.card r₀ * (r₀ * (r₀ - 1))) * (32 * a ^ 2 + 1) := by rw [← hstep]
      _ = Nat.choose P.card r₀ * (32 * a ^ 2 + 1) * (r₀ * (r₀ - 1)) := by ring
      _ ≤ K.card * Nat.choose (P.card - 2) (r₀ - 2) * (r₀ * (r₀ - 1)) := hmul
      _ = K.card * (r₀ * (r₀ - 1)) * Nat.choose (P.card - 2) (r₀ - 2) := by ring
  have hP2 : P.card ^ 2 ≤ 2 * (P.card * (P.card - 1)) := by
    have : 2 ≤ P.card := by omega
    have h1 : P.card ≤ 2 * (P.card - 1) := by omega
    calc P.card ^ 2 = P.card * P.card := sq P.card
      _ ≤ P.card * (2 * (P.card - 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * (P.card * (P.card - 1)) := by ring
  have hr0_sq : r₀ * (r₀ - 1) ≤ 4096 * a ^ 2 := by
    calc r₀ * (r₀ - 1) ≤ r₀ * r₀ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 4096 * a ^ 2 := by dsimp [r₀]; ring
  have hfinal : P.card ^ 2 * (32 * a ^ 2 + 1) ≤ 2 * K.card * (4096 * a ^ 2) := by
    calc P.card ^ 2 * (32 * a ^ 2 + 1)
        ≤ 2 * (P.card * (P.card - 1)) * (32 * a ^ 2 + 1) := Nat.mul_le_mul_right _ hP2
      _ = 2 * (P.card * (P.card - 1) * (32 * a ^ 2 + 1)) := by ring
      _ ≤ 2 * (K.card * (r₀ * (r₀ - 1))) := Nat.mul_le_mul_left _ hcancel
      _ ≤ 2 * (K.card * (4096 * a ^ 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr0_sq)
      _ = 2 * K.card * (4096 * a ^ 2) := by ring
  have hPpos : 0 < P.card ^ 2 := by nlinarith
  nlinarith

private def p4 (x : ℚ) : ℚ := 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24

private lemma p4_pos {x : ℚ} (hx : 0 ≤ x) : 0 < p4 x := by
  unfold p4; positivity

private lemma one_sub_mul_p4_le {x : ℚ} (hx : 0 ≤ x) : (1 - x) * p4 x ≤ 1 := by
  unfold p4
  have h1 : 0 ≤ x ^ 2 := sq_nonneg x
  have h2 : 0 ≤ x ^ 3 := by positivity
  have h3 : 0 ≤ x ^ 4 := by positivity
  have h4 : 0 ≤ x ^ 5 := by positivity
  nlinarith

private lemma p4_add_le_mul {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p4 (x + y) ≤ p4 x * p4 y := by
  have heq : p4 x * p4 y - p4 (x + y) =
      x ^ 3 * y ^ 2 / 12 + x ^ 2 * y ^ 3 / 12 + x ^ 4 * y / 24 + x * y ^ 4 / 24 +
      x ^ 3 * y ^ 3 / 36 + x ^ 4 * y ^ 2 / 48 + x ^ 2 * y ^ 4 / 48 +
      x ^ 4 * y ^ 3 / 144 + x ^ 3 * y ^ 4 / 144 + x ^ 4 * y ^ 4 / 576 := by
    unfold p4; ring
  have hdiff : 0 ≤ p4 x * p4 y - p4 (x + y) := by
    rw [heq]; positivity
  linarith

private lemma prod_one_sub_le {ι : Type} (s : Finset ι) (p : ι → ℚ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (hsum : ∑ i ∈ s, p i = 1) :
    ∏ i ∈ s, (1 - p i) ≤ 24 / 65 := by
  have hp4_prod : p4 (∑ i ∈ s, p i) ≤ ∏ i ∈ s, p4 (p i) := by
    clear hsum hp1
    induction s using Finset.cons_induction with
    | empty => simp [p4]
    | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      have ha0 : 0 ≤ p a := hp0 a (Finset.mem_cons_self _ _)
      have ht0 : ∀ i ∈ t, 0 ≤ p i := fun i hi => hp0 i (Finset.mem_cons_of_mem hi)
      have htsum : 0 ≤ ∑ i ∈ t, p i := Finset.sum_nonneg ht0
      calc p4 (p a + ∑ i ∈ t, p i)
          ≤ p4 (p a) * p4 (∑ i ∈ t, p i) := p4_add_le_mul ha0 htsum
        _ ≤ p4 (p a) * ∏ i ∈ t, p4 (p i) :=
            mul_le_mul_of_nonneg_left (ih ht0) (le_of_lt (p4_pos ha0))
  rw [hsum] at hp4_prod
  have hp4_1 : p4 1 = 65 / 24 := by unfold p4; norm_num
  rw [hp4_1] at hp4_prod
  have hmul : (∏ i ∈ s, (1 - p i)) * (∏ i ∈ s, p4 (p i)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    clear hsum hp4_prod
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih =>
      rw [Finset.prod_cons]
      have ha0 : 0 ≤ p a := hp0 a (Finset.mem_cons_self _ _)
      have ha1 : p a ≤ 1 := hp1 a (Finset.mem_cons_self _ _)
      have ht0 : ∀ i ∈ t, 0 ≤ p i := fun i hi => hp0 i (Finset.mem_cons_of_mem hi)
      have ht1 : ∀ i ∈ t, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_cons_of_mem hi)
      have h1 : 0 ≤ (1 - p a) * p4 (p a) :=
        mul_nonneg (sub_nonneg.mpr ha1) (le_of_lt (p4_pos ha0))
      have h2 : (1 - p a) * p4 (p a) ≤ 1 := one_sub_mul_p4_le ha0
      have h3 : 0 ≤ ∏ i ∈ t, (1 - p i) * p4 (p i) :=
        Finset.prod_nonneg fun i hi => mul_nonneg (sub_nonneg.mpr (ht1 i hi)) (le_of_lt (p4_pos (ht0 i hi)))
      have h4 : ∏ i ∈ t, (1 - p i) * p4 (p i) ≤ 1 := ih ht0 ht1
      nlinarith
  have hnonneg : 0 ≤ ∏ i ∈ s, (1 - p i) :=
    Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hp1 i hi)
  have hmul2 : (∏ i ∈ s, (1 - p i)) * (65 / 24 : ℚ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hp4_prod hnonneg) hmul
  linarith

private lemma exists_paired_types {a k : ℕ} (ha : 16 ≤ a) (hak : a ≤ k)
    (π : Equiv.Perm (Fin (2 ^ k)))
    (Err : Finset (Fin (2 ^ k) × Fin (2 ^ k))) :
    let m := 2 ^ a
    let b := 2 ^ (k - a)
    let typ : Fin (2 ^ k) → Fin m := fun x => Fin.ofNat m x.val
    ∃ (T : Finset (Fin m)) (pick : Fin m → Fin (2 ^ k)),
      T.card = m / 2 ∧
      (∀ i : Fin m, typ (pick i) = i) ∧
      Set.InjOn (fun i => typ (π (pick i))) (T : Set (Fin m)) ∧
      b ^ 2 * ((T ×ˢ T).filter (fun p => p.1 ≠ p.2 ∧ (pick p.1, pick p.2) ∈ Err)).card ≤
        4 * Err.card := by
  intro m b typ
  have hbm : b * m = 2 ^ k := by
    dsimp [b, m]
    rw [← Nat.pow_add, Nat.sub_add_cancel hak]
  have hb_pos : 0 < b := Nat.two_pow_pos (k - a)
  have hm_pos : 0 < m := Nat.two_pow_pos a
  have hm_even : 2 * (m / 2) = m := by
    have h2 : 2 ∣ m := Nat.pow_dvd_pow 2 (by omega : 1 ≤ a)
    omega
  let mkLabel : Fin m → Fin b → Fin (2 ^ k) := fun i r =>
    ⟨r.val * m + i.val, by
      have hi := i.isLt
      have hr := r.isLt
      have : (r.val + 1) * m ≤ b * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hr)
      rw [add_mul, one_mul] at this
      omega⟩
  have htyp_mk : ∀ i r, typ (mkLabel i r) = i := by
    intro i r
    ext
    change (r.val * m + i.val) % m = i.val
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  have hmk_bij : Function.Bijective (fun p : Fin m × Fin b => mkLabel p.1 p.2) := by
    constructor
    · intro p₁ p₂ heq
      have hval : p₁.2.val * m + p₁.1.val = p₂.2.val * m + p₂.1.val := congrArg Fin.val heq
      have h1 : p₁.1.val = p₂.1.val := by
        have := congrArg (· % m) hval
        simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt p₁.1.isLt,
               Nat.mod_eq_of_lt p₂.1.isLt] using this
      have h2 : p₁.2.val = p₂.2.val := by
        have : p₁.2.val * m = p₂.2.val * m := by omega
        exact Nat.eq_of_mul_eq_mul_right hm_pos this
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro x
      have hx : x.val < b * m := by rw [hbm]; exact x.isLt
      refine ⟨(⟨x.val % m, Nat.mod_lt _ hm_pos⟩, ⟨x.val / m, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hx)⟩), ?_⟩
      ext
      change x.val / m * m + x.val % m = x.val
      rw [mul_comm]
      exact Nat.div_add_mod x.val m
  let B : Fin (2 ^ k) → Fin m := fun x => typ (π x)
  let d_ij : Fin m → Fin m → ℕ := fun i j =>
    (Finset.univ.filter (fun r : Fin b => B (mkLabel i r) = j)).card
  have hd_le : ∀ i j, d_ij i j ≤ b := fun i j => by
    calc d_ij i j ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_filter_le _ _
      _ = b := Fintype.card_fin b
  have hd_sum : ∀ j : Fin m, (∑ i : Fin m, d_ij i j) = b := by
    intro j
    have h1 : (∑ i : Fin m, d_ij i j) =
        ((Finset.univ : Finset (Fin m × Fin b)).filter (fun p => B (mkLabel p.1 p.2) = j)).card := by
      simp only [d_ij, Finset.card_filter]
      exact (Fintype.sum_prod_type (fun p : Fin m × Fin b =>
        if B (mkLabel p.1 p.2) = j then (1 : ℕ) else 0)).symm
    have h2 : ((Finset.univ : Finset (Fin m × Fin b)).filter (fun p => B (mkLabel p.1 p.2) = j)).card =
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y => typ y = j)).card := by
      refine Finset.card_bij (fun p _ => π (mkLabel p.1 p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p₁ _ p₂ _ heq
        exact hmk_bij.1 (π.injective heq)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rcases hmk_bij.2 (π.symm y) with ⟨p, hp⟩
        dsimp only at hp
        refine ⟨p, ?_, by rw [hp, π.apply_symm_apply]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
        rw [hp, π.apply_symm_apply]
        exact hy
    have h3 : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y => typ y = j)).card = b := by
      have hbi : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y => typ y = j)).card =
          (Finset.univ : Finset (Fin b)).card := by
        refine (Finset.card_bij (fun r _ => mkLabel j r) ?_ ?_ ?_).symm
        · intro r _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact htyp_mk j r
        · intro r₁ _ r₂ _ heq
          have := hmk_bij.1 (a₁ := (j, r₁)) (a₂ := (j, r₂)) heq
          exact congrArg Prod.snd this
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rcases hmk_bij.2 y with ⟨⟨i, r⟩, hir⟩
          dsimp only at hir
          have hij : i = j := by rw [← htyp_mk i r, hir, hy]
          subst hij
          exact ⟨r, Finset.mem_univ _, hir⟩
      rw [hbi, Finset.card_univ, Fintype.card_fin]
    rw [h1, h2, h3]
  let Ω := Fin m → Fin b
  have hΩ_card : Fintype.card Ω = b ^ m := by simp [Ω, Fintype.card_pi]
  let H : Ω → ℕ := fun ω => (Finset.univ.image (fun i : Fin m => B (mkLabel i (ω i)))).card
  let Z : Ω → ℕ := fun ω =>
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p =>
      p.1 ≠ p.2 ∧ (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card
  have hH_miss : ∀ j : Fin m,
      ((Finset.univ.filter (fun ω : Ω => ∀ i : Fin m, B (mkLabel i (ω i)) ≠ j)).card : ℚ) ≤
      (24 / 65 : ℚ) * (b ^ m : ℚ) := by
    intro j
    let missI : Fin m → Finset (Fin b) := fun i =>
      Finset.univ.filter (fun r : Fin b => B (mkLabel i r) ≠ j)
    have hmiss_eq : Finset.univ.filter (fun ω : Ω => ∀ i : Fin m, B (mkLabel i (ω i)) ≠ j) =
        Fintype.piFinset missI := by
      ext ω
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      simp [missI]
    have hmiss_card : ∀ i : Fin m, (missI i).card = b - d_ij i j := by
      intro i
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin b)))
        (p := fun r : Fin b => B (mkLabel i r) = j)
      have hc : (Finset.univ : Finset (Fin b)).card = b := Fintype.card_fin b
      have : (missI i).card + d_ij i j = b := by
        simpa [missI, d_ij, hc, add_comm] using htot
      omega
    rw [hmiss_eq, Fintype.card_piFinset]
    simp_rw [hmiss_card]
    have hb_ne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hprod_rat : ((∏ i : Fin m, (b - d_ij i j) : ℕ) : ℚ) =
        (∏ i : Fin m, (1 - (d_ij i j : ℚ) / (b : ℚ))) * (b ^ m : ℚ) := by
      have hbm_prod : (b ^ m : ℚ) = ∏ _i : Fin m, (b : ℚ) := by simp
      rw [hbm_prod, ← Finset.prod_mul_distrib, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hd_le i j)]
      field_simp [hb_ne]
    rw [hprod_rat]
    have hle := prod_one_sub_le (Finset.univ : Finset (Fin m)) (fun i => (d_ij i j : ℚ) / (b : ℚ))
      (fun i _ => by positivity)
      (fun i _ => by
        rw [div_le_one (by positivity)]
        exact Nat.cast_le.mpr (hd_le i j))
      (by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Nat.cast_sum, hd_sum j, mul_inv_cancel₀ hb_ne])
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hH_sum : (5 / 8 : ℚ) * (m : ℚ) * (b ^ m : ℚ) < ∑ ω : Ω, (H ω : ℚ) := by
    have hswap : (∑ ω : Ω, (H ω : ℚ)) =
        ∑ j : Fin m, ((Finset.univ.filter (fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card : ℚ) := by
      have hnat : (∑ ω : Ω, H ω) =
          ∑ j : Fin m, (Finset.univ.filter (fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card := by
        have hH_eq : ∀ ω : Ω, H ω =
            (Finset.univ.filter (fun j : Fin m => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card := by
          intro ω
          unfold H
          congr 1
          ext j
          simp
        simp_rw [hH_eq, Finset.card_filter]
        exact Finset.sum_comm
      exact_mod_cast hnat
    rw [hswap]
    have hterm : ∀ j : Fin m,
        (5 / 8 : ℚ) * (b ^ m : ℚ) <
        ((Finset.univ.filter (fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card : ℚ) := by
      intro j
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω))
        (p := fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)
      have hcompl : (Finset.univ.filter (fun ω : Ω => ¬∃ i : Fin m, B (mkLabel i (ω i)) = j)) =
          Finset.univ.filter (fun ω : Ω => ∀ i : Fin m, B (mkLabel i (ω i)) ≠ j) := by
        ext ω; simp
      rw [hcompl, Finset.card_univ, hΩ_card] at htot
      have htotQ : ((Finset.univ.filter (fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card : ℚ) +
          ((Finset.univ.filter (fun ω : Ω => ∀ i : Fin m, B (mkLabel i (ω i)) ≠ j)).card : ℚ) =
          (b ^ m : ℚ) := by exact_mod_cast htot
      have hmiss := hH_miss j
      have hbm_pos : (0 : ℚ) < (b ^ m : ℚ) := by positivity
      linarith
    have hne_m : (Finset.univ : Finset (Fin m)).Nonempty :=
      ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
    calc (5 / 8 : ℚ) * (m : ℚ) * (b ^ m : ℚ)
        = ∑ _j : Fin m, (5 / 8 : ℚ) * (b ^ m : ℚ) := by simp; ring
      _ < ∑ j : Fin m, ((Finset.univ.filter (fun ω : Ω => ∃ i : Fin m, B (mkLabel i (ω i)) = j)).card : ℚ) :=
          Finset.sum_lt_sum_of_nonempty hne_m (fun j _ => hterm j)
  let GoodΩ : Finset Ω := Finset.univ.filter (fun ω => m / 2 ≤ H ω)
  have hGood_card : b ^ m < 4 * GoodΩ.card := by
    have hH_le : ∀ ω : Ω, H ω ≤ m := fun ω => by
      calc H ω ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
        _ = m := Fintype.card_fin m
    have hupper : (∑ ω : Ω, (H ω : ℚ)) ≤
        ((m / 2 : ℕ) : ℚ) * (b ^ m : ℚ) + ((m / 2 : ℕ) : ℚ) * (GoodΩ.card : ℚ) := by
      have hpt : ∀ ω : Ω, (H ω : ℚ) ≤
          ((m / 2 : ℕ) : ℚ) + if m / 2 ≤ H ω then ((m / 2 : ℕ) : ℚ) else 0 := by
        intro ω
        split_ifs with hge
        · have : H ω ≤ m / 2 + m / 2 := by have := hH_le ω; omega
          exact_mod_cast this
        · have : H ω ≤ m / 2 := by omega
          exact_mod_cast this
      calc (∑ ω : Ω, (H ω : ℚ))
          ≤ ∑ ω : Ω, (((m / 2 : ℕ) : ℚ) + if m / 2 ≤ H ω then ((m / 2 : ℕ) : ℚ) else 0) :=
            Finset.sum_le_sum fun ω _ => hpt ω
        _ = (∑ _ω : Ω, ((m / 2 : ℕ) : ℚ)) +
            ∑ ω : Ω, (if m / 2 ≤ H ω then ((m / 2 : ℕ) : ℚ) else 0) := Finset.sum_add_distrib
        _ = ((m / 2 : ℕ) : ℚ) * (b ^ m : ℚ) + ((m / 2 : ℕ) : ℚ) * (GoodΩ.card : ℚ) := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.sum_const]
            simp only [Finset.card_univ, hΩ_card, nsmul_eq_mul, GoodΩ]
            push_cast
            ring
    have hm2Q : (2 : ℚ) * ((m / 2 : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast hm_even
    have hm_posQ : (0 : ℚ) < (m : ℚ) := by positivity
    have hltQ : (b ^ m : ℚ) < 4 * (GoodΩ.card : ℚ) := by nlinarith
    exact_mod_cast hltQ
  have hZ_sum : b ^ 2 * (∑ ω : Ω, Z ω) ≤ b ^ m * Err.card := by
    have hswap : (∑ ω : Ω, Z ω) =
        ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2),
          (Finset.univ.filter (fun ω : Ω => (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card := by
      simp only [Z, Finset.card_filter]
      rw [Finset.sum_comm]
      have hinner : ∀ p : Fin m × Fin m,
          (∑ ω : Ω, if p.1 ≠ p.2 ∧ (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err then 1 else 0) =
          if p.1 ≠ p.2 then ∑ ω : Ω, if (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err then 1 else 0
          else 0 := by
        intro p
        by_cases hp : p.1 ≠ p.2 <;> simp [hp]
      simp_rw [hinner]
      rw [← Finset.sum_filter]
    have hper_pair : ∀ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2),
        b ^ 2 * (Finset.univ.filter (fun ω : Ω => (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card =
        b ^ m * ((Finset.univ : Finset (Fin b × Fin b)).filter (fun r =>
          (mkLabel p.1 r.1, mkLabel p.2 r.2) ∈ Err)).card := by
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      let S2 : Finset (Fin m) := {p.1, p.2}
      have hS2_card : S2.card = 2 := Finset.card_pair hne
      have hcomp : Fintype.card {i : Fin m // i ∉ S2} = m - 2 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS2_card]
      let pairErr := (Finset.univ : Finset (Fin b × Fin b)).filter (fun r =>
        (mkLabel p.1 r.1, mkLabel p.2 r.2) ∈ Err)
      have hcard_eq : (Finset.univ.filter (fun ω : Ω =>
          (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card =
          pairErr.card * b ^ (m - 2) := by
        have hbij : (Finset.univ.filter (fun ω : Ω =>
            (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card =
            (pairErr ×ˢ (Finset.univ : Finset ({i : Fin m // i ∉ S2} → Fin b))).card := by
          refine Finset.card_bij (fun ω _ => ((ω p.1, ω p.2), fun i => ω i.val)) ?_ ?_ ?_
          · intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩, Finset.mem_univ _⟩
          · intro ω₁ _ ω₂ _ heq
            have h12 : (ω₁ p.1, ω₁ p.2) = (ω₂ p.1, ω₂ p.2) := congrArg Prod.fst heq
            have hrest : (fun i : {i : Fin m // i ∉ S2} => ω₁ i.val) = (fun i => ω₂ i.val) :=
              congrArg Prod.snd heq
            funext i
            by_cases hi1 : i = p.1
            · rw [hi1]; exact congrArg Prod.fst h12
            · by_cases hi2 : i = p.2
              · rw [hi2]; exact congrArg Prod.snd h12
              · have hnot : i ∉ S2 := by simp [S2, hi1, hi2]
                exact congrFun hrest ⟨i, hnot⟩
          · intro ⟨⟨r1, r2⟩, rest⟩ hmem
            have hr := (Finset.mem_product.mp hmem).1
            simp only [pairErr, Finset.mem_filter, Finset.mem_univ, true_and] at hr
            let ω : Ω := fun i =>
              if i = p.1 then r1 else if i = p.2 then r2 else
              if h : i ∉ S2 then rest ⟨i, h⟩ else r1
            have hω1 : ω p.1 = r1 := by simp [ω]
            have hω2 : ω p.2 = r2 := by simp [ω, hne.symm]
            refine ⟨ω, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hω1, hω2]
              exact hr
            · refine Prod.ext (by simp [hω1, hω2]) ?_
              funext ⟨i, hi⟩
              have hi1 : i ≠ p.1 := fun h => hi (by simp [S2, h])
              have hi2 : i ≠ p.2 := fun h => hi (by simp [S2, h])
              simp [ω, hi1, hi2, hi]
        rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_pi]
        simp [hcomp]
      rw [hcard_eq]
      have hm2 : 2 ≤ m := by
        have : 2 ^ 16 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
        dsimp [m]; omega
      calc b ^ 2 * (pairErr.card * b ^ (m - 2))
          = (b ^ 2 * b ^ (m - 2)) * pairErr.card := by ring
        _ = b ^ (2 + (m - 2)) * pairErr.card := by rw [← Nat.pow_add]
        _ = b ^ m * pairErr.card := by rw [Nat.add_sub_of_le hm2]
    rw [hswap, Finset.mul_sum]
    rw [Finset.sum_congr rfl hper_pair, ← Finset.mul_sum]
    refine Nat.mul_le_mul_left _ ?_
    have hsum_err : (∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2),
        ((Finset.univ : Finset (Fin b × Fin b)).filter (fun r =>
          (mkLabel p.1 r.1, mkLabel p.2 r.2) ∈ Err)).card) ≤ Err.card := by
      have htot_eq : (∑ p : Fin m × Fin m,
          ((Finset.univ : Finset (Fin b × Fin b)).filter (fun r =>
            (mkLabel p.1 r.1, mkLabel p.2 r.2) ∈ Err)).card) = Err.card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun q _ => (mkLabel q.1.1 q.2.1, mkLabel q.1.2 q.2.2)) ?_ ?_ ?_
        · intro q hq
          have h2 := (Finset.mem_sigma.mp hq).2
          exact (Finset.mem_filter.mp h2).2
        · intro q₁ _ q₂ _ heq
          have h1 := hmk_bij.1 (a₁ := (q₁.1.1, q₁.2.1)) (a₂ := (q₂.1.1, q₂.2.1)) (congrArg Prod.fst heq)
          have h2 := hmk_bij.1 (a₁ := (q₁.1.2, q₁.2.2)) (a₂ := (q₂.1.2, q₂.2.2)) (congrArg Prod.snd heq)
          refine Sigma.ext
            (Prod.ext (congrArg (Prod.fst : Fin m × Fin b → Fin m) h1)
                      (congrArg (Prod.fst : Fin m × Fin b → Fin m) h2)) ?_
          exact heq_of_eq (Prod.ext (congrArg (Prod.snd : Fin m × Fin b → Fin b) h1)
                                    (congrArg (Prod.snd : Fin m × Fin b → Fin b) h2))
        · intro z hz
          rcases hmk_bij.2 z.1 with ⟨⟨i1, r1⟩, h1⟩
          rcases hmk_bij.2 z.2 with ⟨⟨i2, r2⟩, h2⟩
          dsimp only at h1 h2
          refine ⟨⟨(i1, i2), (r1, r2)⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [h1, h2]; exact hz
          · exact Prod.ext h1 h2
      rw [← htot_eq]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    exact hsum_err
  have hex_ω : ∃ ω ∈ GoodΩ, b ^ 2 * Z ω ≤ 4 * Err.card := by
    by_contra hall
    push Not at hall
    have hne : GoodΩ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      rw [hemp, Finset.card_empty] at hGood_card
      have : 0 < b ^ m := Nat.pos_of_ne_zero (by positivity)
      omega
    have hstrict : GoodΩ.card * (4 * Err.card) < ∑ ω ∈ GoodΩ, b ^ 2 * Z ω := by
      calc GoodΩ.card * (4 * Err.card)
          = ∑ _ω ∈ GoodΩ, 4 * Err.card := by simp
        _ < ∑ ω ∈ GoodΩ, b ^ 2 * Z ω := Finset.sum_lt_sum_of_nonempty hne hall
    have hle_all : (∑ ω ∈ GoodΩ, b ^ 2 * Z ω) ≤ b ^ m * Err.card := by
      calc ∑ ω ∈ GoodΩ, b ^ 2 * Z ω
          ≤ ∑ ω : Ω, b ^ 2 * Z ω := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = b ^ 2 * ∑ ω : Ω, Z ω := (Finset.mul_sum _ _ _).symm
        _ ≤ b ^ m * Err.card := hZ_sum
    have hle_cmp : b ^ m * Err.card ≤ 4 * GoodΩ.card * Err.card :=
      Nat.mul_le_mul_right Err.card (le_of_lt hGood_card)
    have : 4 * GoodΩ.card * Err.card = GoodΩ.card * (4 * Err.card) := by ring
    omega
  rcases hex_ω with ⟨ω, hωGood, hωZ⟩
  have hH_ge : m / 2 ≤ (Finset.univ.image (fun i : Fin m => B (mkLabel i (ω i)))).card :=
    (Finset.mem_filter.mp hωGood).2
  rcases Finset.exists_subset_card_eq hH_ge with ⟨J, hJsub, hJcard⟩
  have hpre : ∀ j ∈ J, ∃ i : Fin m, B (mkLabel i (ω i)) = j := fun j hj => by
    rcases Finset.mem_image.mp (hJsub hj) with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  let pickInv : Fin m → Fin m := fun j =>
    if h : j ∈ J then Classical.choose (hpre j h) else 0
  have hpickInv_spec : ∀ j ∈ J, B (mkLabel (pickInv j) (ω (pickInv j))) = j := by
    intro j hj
    simp only [pickInv, hj, ↓reduceDIte]
    exact Classical.choose_spec (hpre j hj)
  let T : Finset (Fin m) := J.image pickInv
  have hT_card : T.card = m / 2 := by
    rw [Finset.card_image_of_injOn, hJcard]
    intro j₁ hj₁ j₂ hj₂ heq
    rw [← hpickInv_spec j₁ hj₁, ← hpickInv_spec j₂ hj₂, heq]
  have hT_inj : Set.InjOn (fun i => B (mkLabel i (ω i))) (T : Set (Fin m)) := by
    intro i₁ hi₁ i₂ hi₂ heq
    rcases Finset.mem_image.mp hi₁ with ⟨j₁, hj₁, rfl⟩
    rcases Finset.mem_image.mp hi₂ with ⟨j₂, hj₂, rfl⟩
    dsimp only at heq
    rw [hpickInv_spec j₁ hj₁, hpickInv_spec j₂ hj₂] at heq
    rw [heq]
  refine ⟨T, fun i => mkLabel i (ω i), hT_card, fun i => htyp_mk i (ω i), hT_inj, ?_⟩
  have hsub_Z : ((T ×ˢ T).filter (fun p => p.1 ≠ p.2 ∧ (mkLabel p.1 (ω p.1), mkLabel p.2 (ω p.2)) ∈ Err)).card ≤
      Z ω := Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  exact le_trans (Nat.mul_le_mul_left _ hsub_Z) hωZ

private lemma cauchy_schwarz_nat {ι : Type} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  have hz : ((∑ i ∈ s, (f i : ℤ)) ^ 2) ≤ (s.card : ℤ) * ∑ i ∈ s, ((f i : ℤ)) ^ 2 := by
    have hnonneg : (0 : ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hexp : (∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2) =
        2 * ((s.card : ℤ) * (∑ i ∈ s, (f i : ℤ) ^ 2) - (∑ i ∈ s, (f i : ℤ)) ^ 2) := by
      have hterm : ∀ i j : ι, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
          (f i : ℤ) ^ 2 + (f j : ℤ) ^ 2 - 2 * ((f i : ℤ) * (f j : ℤ)) := fun i j => by ring
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [sq]
      ring
    linarith
  exact_mod_cast hz

private def poolDigit (r c : Bool) : Fin 3 :=
  if r = c then 0 else if r then 1 else 2

private lemma poolDigit_eq_imp_or_eq (r₁ c₁ r₂ c₂ : Bool)
    (h : poolDigit r₁ c₁ = poolDigit r₂ c₂) :
    (r₁ || c₂) = (r₂ || c₁) := by
  cases r₁ <;> cases c₁ <;> cases r₂ <;> cases c₂ <;> simp [poolDigit] at h ⊢

private lemma lower_bound_from_uv {a k q : ℕ} (ha : 16 ≤ a) (hak : a ≤ k)
    (hq : 256 * a * 3 ^ q ≤ 2 ^ a)
    (u v : Fin (2 ^ a) → (Fin (32 * a) → ZMod 2))
    (huv : ∀ (f g : Fin (64 * a) → Fin (2 ^ a)), Function.Injective f → Function.Injective g →
      ∀ s : Fin (64 * a) → ZMod 2,
        32 * a ^ 2 < ((Finset.univ : Finset (Fin (64 * a) × Fin (64 * a))).filter (fun z =>
          dot (u (f z.1)) (v (g z.2)) + dot (u (f z.2)) (v (g z.1)) ≠ s z.1 + s z.2)).card)
    (π : Equiv.Perm (Fin (2 ^ k))) (rf cf : Fin (2 ^ k) → Bool)
    (R C : Fin q → Finset (Fin (2 ^ k)))
    (out : Finset (Fin (2 ^ k)) → (Fin q → Bool) → Bool) :
    let m := 2 ^ a
    let N := 2 ^ k
    let I := Fin N
    let typ : I → Fin m := fun label => Fin.ofNat m label.val
    let G : I → I → Bool := fun x y =>
      decide ((∑ j : Fin (32 * a), u (typ x) j * v (typ y) j) = 1)
    let E := ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1, z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card
    N ^ 2 < 65536 * 3 ^ q * E := by
  intro m N I typ G E
  let b := 2 ^ (k - a)
  have hbm : b * m = N := by
    dsimp [b, m, N]; rw [← Nat.pow_add, Nat.sub_add_cancel hak]
  have hb_pos : 0 < b := Nat.two_pow_pos (k - a)
  let Err : Finset (I × I) := Finset.univ.filter (fun z =>
    out {z.1, z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
      Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))
  have hE : Err.card = E := rfl
  rcases exists_paired_types ha hak π Err with ⟨T, pick, hTcard, htyp_pick, hTinj, hET⟩
  let β : Fin m → Fin m := fun i => typ (π (pick i))
  let dig : Fin m → (Fin q → Fin 3) := fun i t =>
    poolDigit (decide (pick i ∈ R t)) (decide (π (pick i) ∈ C t))
  let sw : Fin m → Bool := fun i => Bool.xor (rf (pick i)) (cf (π (pick i)))
  let swZ : Fin m → ZMod 2 := fun i => b2z (sw i)
  let K : Finset (Fin m × Fin m) := (T ×ˢ T).filter (fun p =>
    dig p.1 = dig p.2 ∧
    dot (u p.1) (v (β p.2)) + dot (u p.2) (v (β p.1)) ≠ swZ p.1 + swZ p.2)
  let ErrT : Finset (Fin m × Fin m) := (T ×ˢ T).filter (fun p =>
    p.1 ≠ p.2 ∧ (pick p.1, pick p.2) ∈ Err)
  have hK_le : K.card ≤ 2 * ErrT.card := by
    have hsub : K ⊆ ErrT ∪ ErrT.image Prod.swap := by
      intro p hp
      simp only [K, Finset.mem_filter, Finset.mem_product] at hp
      rcases hp with ⟨⟨hp1, hp2⟩, hdig, hconf⟩
      have hne : p.1 ≠ p.2 := by
        intro heq
        apply hconf
        rw [heq, zmod2_add_self, zmod2_add_self]
      have hword : (fun t : Fin q => decide (pick p.1 ∈ R t ∨ π (pick p.2) ∈ C t)) =
          (fun t : Fin q => decide (pick p.2 ∈ R t ∨ π (pick p.1) ∈ C t)) := by
        funext t
        have ht := congrFun hdig t
        have hor := poolDigit_eq_imp_or_eq _ _ _ _ ht
        simpa [Bool.or_eq_true, decide_eq_true_eq] using hor
      have hpair : ({pick p.1, pick p.2} : Finset I) = {pick p.2, pick p.1} :=
        Finset.pair_comm _ _
      have hout_eq :
          out {pick p.1, pick p.2} (fun t => decide (pick p.1 ∈ R t ∨ π (pick p.2) ∈ C t)) =
          out {pick p.2, pick p.1} (fun t => decide (pick p.2 ∈ R t ∨ π (pick p.1) ∈ C t)) := by
        rw [hpair, hword]
      have htarg_ne :
          Bool.xor (G (pick p.1) (π (pick p.2))) (Bool.xor (rf (pick p.1)) (cf (π (pick p.2)))) ≠
          Bool.xor (G (pick p.2) (π (pick p.1))) (Bool.xor (rf (pick p.2)) (cf (π (pick p.1)))) := by
        intro heq
        apply hconf
        have hG1 : G (pick p.1) (π (pick p.2)) = decide (dot (u p.1) (v (β p.2)) = 1) := by
          have hp1 : typ (pick p.1) = p.1 := htyp_pick p.1
          change decide (dot (u (typ (pick p.1))) (v (β p.2)) = 1) = decide (dot (u p.1) (v (β p.2)) = 1)
          rw [hp1]
        have hG2 : G (pick p.2) (π (pick p.1)) = decide (dot (u p.2) (v (β p.1)) = 1) := by
          have hp2 : typ (pick p.2) = p.2 := htyp_pick p.2
          change decide (dot (u (typ (pick p.2))) (v (β p.1)) = 1) = decide (dot (u p.2) (v (β p.1)) = 1)
          rw [hp2]
        have hxor_eq : Bool.xor (G (pick p.1) (π (pick p.2))) (G (pick p.2) (π (pick p.1))) =
            Bool.xor (sw p.1) (sw p.2) := by
          dsimp only [sw]
          generalize G (pick p.1) (π (pick p.2)) = g1 at heq ⊢
          generalize G (pick p.2) (π (pick p.1)) = g2 at heq ⊢
          generalize rf (pick p.1) = r1 at heq ⊢
          generalize cf (π (pick p.1)) = c1 at heq ⊢
          generalize rf (pick p.2) = r2 at heq ⊢
          generalize cf (π (pick p.2)) = c2 at heq ⊢
          cases g1 <;> cases g2 <;> cases r1 <;> cases c1 <;> cases r2 <;> cases c2 <;> simp at heq ⊢
        rw [hG1, hG2, decide_add_zmod2, decide_b2z_add] at hxor_eq
        exact (decide_eq_one_iff _ _).mp hxor_eq
      by_cases herr1 : (pick p.1, pick p.2) ∈ Err
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hne, herr1⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p.2, p.1), ?_, rfl⟩)
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, hne.symm, ?_⟩
        simp only [Err, Finset.mem_filter, Finset.mem_univ, true_and] at herr1 ⊢
        push Not at herr1
        rw [← hout_eq, herr1]
        exact htarg_ne
    calc K.card ≤ (ErrT ∪ ErrT.image Prod.swap).card := Finset.card_le_card hsub
      _ ≤ ErrT.card + (ErrT.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ ErrT.card + ErrT.card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * ErrT.card := by ring
  have hbK : b ^ 2 * K.card ≤ 8 * E := by
    calc b ^ 2 * K.card ≤ b ^ 2 * (2 * ErrT.card) := Nat.mul_le_mul_left _ hK_le
      _ = 2 * (b ^ 2 * ErrT.card) := by ring
      _ ≤ 2 * (4 * Err.card) := Nat.mul_le_mul_left _ hET
      _ = 8 * E := by rw [hE]; ring
  let P_c : (Fin q → Fin 3) → Finset (Fin m) := fun c => T.filter (fun i => dig i = c)
  let Large : Finset (Fin q → Fin 3) := Finset.univ.filter (fun c => 64 * a ≤ (P_c c).card)
  let Small : Finset (Fin q → Fin 3) := Finset.univ.filter (fun c => ¬ 64 * a ≤ (P_c c).card)
  have hsum_all : (∑ c : Fin q → Fin 3, (P_c c).card) = m / 2 := by
    rw [← hTcard, ← Finset.card_biUnion]
    · congr 1
      ext i
      simp [P_c]
    · intro c₁ _ c₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      simp only [P_c, Finset.mem_filter] at hi₁ hi₂
      exact hne (hi₁.2.symm.trans hi₂.2)
  have hcard_colors : Fintype.card (Fin q → Fin 3) = 3 ^ q := by
    simp [Fintype.card_pi]
  have hsum_small : (∑ c ∈ Small, (P_c c).card) ≤ 64 * a * 3 ^ q := by
    calc ∑ c ∈ Small, (P_c c).card
        ≤ ∑ _c ∈ Small, 64 * a := by
          refine Finset.sum_le_sum fun c hc => ?_
          have hlt : ¬ 64 * a ≤ (P_c c).card := (Finset.mem_filter.mp hc).2
          omega
      _ = Small.card * (64 * a) := by simp
      _ ≤ (Finset.univ : Finset (Fin q → Fin 3)).card * (64 * a) :=
          Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ = 64 * a * 3 ^ q := by rw [Finset.card_univ, hcard_colors]; ring
  have h4m : 4 * (m / 4) = m := by
    have h4 : 4 ∣ m := by
      have : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega : 2 ≤ a)
      simpa [m] using this
    omega
  have hsum_large : m / 4 ≤ ∑ c ∈ Large, (P_c c).card := by
    have hsplit : (∑ c ∈ Large, (P_c c).card) + (∑ c ∈ Small, (P_c c).card) = m / 2 := by
      rw [← hsum_all]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => 64 * a ≤ (P_c c).card) _
    have h64 : 4 * (64 * a * 3 ^ q) = 256 * a * 3 ^ q := by ring
    have hsmall_le : 64 * a * 3 ^ q ≤ m / 4 := by omega
    omega
  have hLarge_ne : Large.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.sum_empty] at hsum_large
    have hm16 : 65536 ≤ m := by
      have : 2 ^ 16 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
      simpa [m] using this
    omega
  have hLarge_card : Large.card ≤ 3 ^ q := by
    calc Large.card ≤ (Finset.univ : Finset (Fin q → Fin 3)).card := Finset.card_le_univ _
      _ = 3 ^ q := hcard_colors
  have hcs : m ^ 2 ≤ 16 * 3 ^ q * ∑ c ∈ Large, (P_c c).card ^ 2 := by
    have h1 := cauchy_schwarz_nat Large (fun c => (P_c c).card)
    have h2 : (m / 4) ^ 2 ≤ (∑ c ∈ Large, (P_c c).card) ^ 2 := Nat.pow_le_pow_left hsum_large 2
    have h3 : (m / 4) ^ 2 ≤ 3 ^ q * ∑ c ∈ Large, (P_c c).card ^ 2 :=
      le_trans h2 (le_trans h1 (Nat.mul_le_mul_right _ hLarge_card))
    have hm2 : m ^ 2 = 16 * (m / 4) ^ 2 := by
      calc m ^ 2 = (4 * (m / 4)) ^ 2 := by rw [h4m]
        _ = 16 * (m / 4) ^ 2 := by ring
    rw [hm2]
    calc 16 * (m / 4) ^ 2 ≤ 16 * (3 ^ q * ∑ c ∈ Large, (P_c c).card ^ 2) :=
          Nat.mul_le_mul_left 16 h3
      _ = 16 * 3 ^ q * ∑ c ∈ Large, (P_c c).card ^ 2 := by ring
  let K_c : (Fin q → Fin 3) → Finset (Fin m × Fin m) := fun c =>
    (P_c c ×ˢ P_c c).filter (fun z =>
      dot (u z.1) (v (β z.2)) + dot (u z.2) (v (β z.1)) ≠ swZ z.1 + swZ z.2)
  have hKc_lt : ∀ c ∈ Large, (P_c c).card ^ 2 < 256 * (K_c c).card := by
    intro c hc
    have hge : 64 * a ≤ (P_c c).card := (Finset.mem_filter.mp hc).2
    have hinj_c : Set.InjOn β (P_c c : Set (Fin m)) :=
      hTinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    exact large_class_conflicts ha u v huv (P_c c) hge β hinj_c swZ
  have hsum_Kc_le : (∑ c ∈ Large, (K_c c).card) ≤ K.card := by
    rw [← Finset.card_biUnion]
    · refine Finset.card_le_card ?_
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨c, _, hzc⟩
      simp only [K_c, P_c, Finset.mem_filter, Finset.mem_product, K] at hzc ⊢
      exact ⟨⟨hzc.1.1.1, hzc.1.2.1⟩, hzc.1.1.2.trans hzc.1.2.2.symm, hzc.2⟩
    · intro c₁ _ c₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      simp only [K_c, P_c, Finset.mem_filter, Finset.mem_product] at hz₁ hz₂
      exact hne (hz₁.1.1.2.symm.trans hz₂.1.1.2)
  have hsum_sq_lt : (∑ c ∈ Large, (P_c c).card ^ 2) < 256 * K.card := by
    calc ∑ c ∈ Large, (P_c c).card ^ 2
        < ∑ c ∈ Large, 256 * (K_c c).card := Finset.sum_lt_sum_of_nonempty hLarge_ne hKc_lt
      _ = 256 * ∑ c ∈ Large, (K_c c).card := (Finset.mul_sum _ _ _).symm
      _ ≤ 256 * K.card := Nat.mul_le_mul_left 256 hsum_Kc_le
  have h3q_pos : 0 < 16 * 3 ^ q := by positivity
  have hm2_lt : m ^ 2 < 4096 * 3 ^ q * K.card := by
    calc m ^ 2 ≤ 16 * 3 ^ q * ∑ c ∈ Large, (P_c c).card ^ 2 := hcs
      _ < 16 * 3 ^ q * (256 * K.card) := Nat.mul_lt_mul_of_pos_left hsum_sq_lt h3q_pos
      _ = 4096 * 3 ^ q * K.card := by ring
  have hb2_pos : 0 < b ^ 2 := by positivity
  have hN2 : N ^ 2 = b ^ 2 * m ^ 2 := by rw [← hbm, mul_pow]
  calc N ^ 2 = b ^ 2 * m ^ 2 := hN2
    _ < b ^ 2 * (4096 * 3 ^ q * K.card) := Nat.mul_lt_mul_of_pos_left hm2_lt hb2_pos
    _ = 4096 * 3 ^ q * (b ^ 2 * K.card) := by ring
    _ ≤ 4096 * 3 ^ q * (8 * E) := Nat.mul_le_mul_left _ hbK
    _ = 32768 * 3 ^ q * E := by ring
    _ ≤ 65536 * 3 ^ q * E := by
        have : 32768 ≤ 65536 := by omega
        exact Nat.mul_le_mul_right E (Nat.mul_le_mul_right (3 ^ q) this)

end PEqualNP.Outside.L_meta_25735_aux

theorem PEqualNP.Outside.L_meta_25735 : (∀ coreBits : ℕ, 16 ≤ coreBits →
  let m := 2^coreBits
  let F := ZMod 2
  let W := Fin (32*coreBits) → F
  ∃ u v : Fin m → W, ∀ k : ℕ, coreBits ≤ k →
    let N := 2^k
    let I := Fin N
    let typ := fun label : I => Fin.ofNat m label.val
    let G := fun x y : I => decide ((∑ j : Fin (32*coreBits), u (typ x) j * v (typ y) j) = 1)
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (1024*m) ∧
    ∀ q : ℕ, 256*coreBits*3^q ≤ m →
      ∀ (π : Equiv.Perm I) (rf cf : I → Bool) (R C : Fin q → Finset I)
        (out : Finset I → (Fin q → Bool) → Bool),
      let E := ((Finset.univ : Finset (I × I)).filter (fun z =>
        out {z.1,z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card
      N^2 < 65536*3^q*E) := by
  intro coreBits hcore
  dsimp only
  rcases PEqualNP.Outside.L_meta_25735_aux.exists_good_uv hcore with ⟨u, v, huv⟩
  refine ⟨u, v, fun k hak => ?_⟩
  refine ⟨PEqualNP.Outside.L_meta_25735_aux.buildDotCircuit hcore hak u v,
          fun q hq π rf cf R C out =>
            PEqualNP.Outside.L_meta_25735_aux.lower_bound_from_uv hcore hak hq u v huv π rf cf R C out⟩
