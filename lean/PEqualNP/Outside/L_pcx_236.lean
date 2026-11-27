import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_236_aux

open PEqualNP.ProofComplexity

private abbrev RawT (n : ℕ) := Fin n × (Bool × Bool)
private abbrev VarT (n a : ℕ) := Sum (RawT n) (Fin a)

private def nextIdx {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private def feasiblePred {n : ℕ} (hn : 0 < n) (tab : RawT n → Bool) : Prop :=
  ∃ x : Fin n → Bool, ∀ i : Fin n, tab (i, x i, x (nextIdx hn i)) = true

private def encPred {n : ℕ} (hn : 0 < n) (a : ℕ) (F : Finset (Clause (VarT n a))) : Prop :=
  ∀ tab : RawT n → Bool, feasiblePred hn tab ↔ ∃ y : Fin a → Bool,
    Satisfies (Sum.elim tab y) (↑F : Set _)

private def rowsFn {n : ℕ} (a : ℕ) (C : Clause (VarT n a)) : Finset (Fin n) :=
  Finset.univ.filter (fun location : Fin n => ∃ p : Bool × Bool, ∃ sign : Bool,
    (Sum.inl (location, p), sign) ∈ C)

private def cutState (L p q : ℕ) (s0 s1 : Bool) (c : ℕ → Bool) (j : ℕ) (a : Bool) : Bool :=
  if j = 0 then
    if p = 0 then decide (a = s0) else true
  else if j ≤ p then
    true
  else if j < q then
    decide (a = c j)
  else if j < L then
    false
  else
    if q = L then decide (a ≠ s1) else false

private def cutRawLits {n : ℕ} (hn : 0 < n) (b : ℕ) (start0 L p q : ℕ) (s0 s1 : Bool)
    (c : ℕ → Bool) : Finset (Literal (VarT n b)) :=
  ((Finset.range L) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool))).filter
    (fun t => cutState L p q s0 s1 c t.1 t.2.1 = true ∧
      cutState L p q s0 s1 c (t.1 + 1) t.2.2 = false) |>.image
    (fun t => (Sum.inl (⟨(start0 + t.1) % n, Nat.mod_lt _ hn⟩, (t.2.1, t.2.2)), true))

private def cutClause {n : ℕ} (hn : 0 < n) (b : ℕ) (r0 r1 : Fin b) (start0 L p q : ℕ)
    (s0 s1 : Bool) (c : ℕ → Bool) : Clause (VarT n b) :=
  insert (Sum.inr r0, !s0) (insert (Sum.inr r1, !s1) (cutRawLits hn b start0 L p q s0 s1 c))

private theorem cutState_zero {L p q : ℕ} {s0 s1 : Bool} {c : ℕ → Bool} :
    cutState L p q s0 s1 c 0 s0 = true := by
  simp only [cutState, ↓reduceIte]
  split_ifs <;> simp

private theorem cutState_end {L p q : ℕ} {s0 s1 : Bool} {c : ℕ → Bool}
    (hpq : p < q) (hqL : q ≤ L) :
    cutState L p q s0 s1 c L s1 = false := by
  unfold cutState
  have hL0 : L ≠ 0 := by omega
  have hLp : ¬ L ≤ p := by omega
  have hLq : ¬ L < q := by omega
  simp only [hL0, hLp, hLq, lt_irrefl, ↓reduceIte]
  split_ifs <;> simp

private theorem cutRawLits_card_le {n : ℕ} (hn : 0 < n) (b : ℕ) (start0 L p q : ℕ)
    (s0 s1 : Bool) (c : ℕ → Bool) (hpq : p < q) (hqL : q ≤ L) :
    (cutRawLits hn b start0 L p q s0 s1 c).card ≤ max 4 L := by
  classical
  have hle_filt :
      (cutRawLits hn b start0 L p q s0 s1 c).card ≤
      (((Finset.range L) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool))).filter
        (fun t => cutState L p q s0 s1 c t.1 t.2.1 = true ∧
          cutState L p q s0 s1 c (t.1 + 1) t.2.2 = false)).card := Finset.card_image_le
  refine hle_filt.trans ?_
  let stepCount : ℕ → ℕ := fun j =>
    (((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
      (fun ab => cutState L p q s0 s1 c j ab.1 = true ∧
        cutState L p q s0 s1 c (j + 1) ab.2 = false)).card
  have hsum_eq :
      (((Finset.range L) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool))).filter
        (fun t => cutState L p q s0 s1 c t.1 t.2.1 = true ∧
          cutState L p q s0 s1 c (t.1 + 1) t.2.2 = false)).card =
      ∑ j ∈ Finset.range L, stepCount j := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    simp only [stepCount, Finset.card_filter]
  rw [hsum_eq]
  have hzero_lt : ∀ j < L, j < p → stepCount j = 0 := by
    intro j hj hjp
    dsimp only [stepCount]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ab _ hcond
    have h2 := hcond.2
    unfold cutState at h2
    have h1 : j + 1 ≠ 0 := by omega
    have h2' : j + 1 ≤ p := by omega
    simp only [h1, h2', ↓reduceIte] at h2
    exact Bool.noConfusion h2
  have hzero_ge : ∀ j < L, q ≤ j → stepCount j = 0 := by
    intro j hj hqj
    dsimp only [stepCount]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ab _ hcond
    have h1 := hcond.1
    unfold cutState at h1
    have hne0 : j ≠ 0 := by omega
    have hnp : ¬ j ≤ p := by omega
    have hnq : ¬ j < q := by omega
    simp only [hne0, hnp, hnq, hj, ↓reduceIte] at h1
    exact Bool.noConfusion h1
  by_cases h1step : q = p + 1
  · have hsum_single : ∑ j ∈ Finset.range L, stepCount j = stepCount p := by
      rw [Finset.sum_eq_single p]
      · intro j hj hne
        have hjL := Finset.mem_range.mp hj
        by_cases hlt : j < p
        · exact hzero_lt j hjL hlt
        · exact hzero_ge j hjL (by omega)
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hsum_single]
    have hle4 : stepCount p ≤ 4 := by
      dsimp only [stepCount]
      exact (Finset.card_filter_le _ _).trans (by decide)
    omega
  · have hp2 : p + 2 ≤ q := by omega
    have hmid : ∀ j, p < j → j + 1 < q → stepCount j ≤ 1 := by
      intro j h1 h2
      dsimp only [stepCount]
      have hsub :
          ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
            (fun ab => cutState L p q s0 s1 c j ab.1 = true ∧
              cutState L p q s0 s1 c (j + 1) ab.2 = false) ⊆ {(c j, !(c (j + 1)))} := by
        intro ab hab
        rcases (Finset.mem_filter.mp hab).2 with ⟨ha, hb⟩
        unfold cutState at ha hb
        have hja : j ≠ 0 := by omega
        have hjp : ¬ j ≤ p := by omega
        have hjq : j < q := by omega
        have hj1a : j + 1 ≠ 0 := by omega
        have hj1p : ¬ j + 1 ≤ p := by omega
        simp only [hja, hjp, hjq, ↓reduceIte, decide_eq_true_eq] at ha
        simp only [hj1a, hj1p, h2, ↓reduceIte, decide_eq_false_iff_not] at hb
        rw [Finset.mem_singleton]
        cases ab with | mk a b =>
        dsimp only at ha hb
        subst ha
        cases hc1 : c (j + 1) <;> cases b <;> simp [hc1] at hb ⊢
      exact (Finset.card_le_card hsub).trans (by simp)
    have hfirst : stepCount p ≤ if p = 0 then 1 else 2 := by
      dsimp only [stepCount]
      by_cases hp0 : p = 0
      · subst hp0
        simp only [↓reduceIte]
        have hsub :
            ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
              (fun ab => cutState L 0 q s0 s1 c 0 ab.1 = true ∧
                cutState L 0 q s0 s1 c 1 ab.2 = false) ⊆ {(s0, !(c 1))} := by
          intro ab hab
          rcases (Finset.mem_filter.mp hab).2 with ⟨ha, hb⟩
          unfold cutState at ha hb
          have h1q : 1 < q := by omega
          simp only [↓reduceIte, decide_eq_true_eq] at ha
          simp only [Nat.one_ne_zero, h1q, ↓reduceIte] at hb
          rw [Finset.mem_singleton]
          cases ab with | mk a b =>
          dsimp only at ha hb
          subst ha
          cases hc1 : c 1 <;> cases b <;> simp [hc1] at hb ⊢
        exact (Finset.card_le_card hsub).trans (by simp)
      · simp only [hp0, ↓reduceIte]
        have hsub :
            ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
              (fun ab => cutState L p q s0 s1 c p ab.1 = true ∧
                cutState L p q s0 s1 c (p + 1) ab.2 = false) ⊆
            {(false, !(c (p + 1))), (true, !(c (p + 1)))} := by
          intro ab hab
          rcases (Finset.mem_filter.mp hab).2 with ⟨_, hb⟩
          unfold cutState at hb
          have h1a : p + 1 ≠ 0 := by omega
          have h1p : ¬ p + 1 ≤ p := by omega
          have h1q : p + 1 < q := by omega
          simp only [h1a, h1p, h1q, ↓reduceIte, decide_eq_false_iff_not] at hb
          cases ab with | mk a b =>
          dsimp only at hb
          cases a <;> cases hc1 : c (p + 1) <;> cases b <;> simp [hc1] at hb ⊢
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hlast : stepCount (q - 1) ≤ if q = L then 1 else 2 := by
      dsimp only [stepCount]
      have hq1_add : q - 1 + 1 = q := by omega
      by_cases hqeq : q = L
      · subst hqeq
        simp only [↓reduceIte]
        have hsub :
            ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
              (fun ab => cutState q p q s0 s1 c (q - 1) ab.1 = true ∧
                cutState q p q s0 s1 c (q - 1 + 1) ab.2 = false) ⊆ {(c (q - 1), s1)} := by
          intro ab hab
          rcases (Finset.mem_filter.mp hab).2 with ⟨ha, hb⟩
          rw [hq1_add] at hb
          unfold cutState at ha hb
          have h1a : q - 1 ≠ 0 := by omega
          have h1p : ¬ q - 1 ≤ p := by omega
          have h1q : q - 1 < q := by omega
          have h2a : q ≠ 0 := by omega
          have h2p : ¬ q ≤ p := by omega
          simp only [h1a, h1p, h1q, ↓reduceIte, decide_eq_true_eq] at ha
          simp only [h2a, h2p, lt_irrefl, ↓reduceIte, decide_eq_false_iff_not, not_not] at hb
          rw [Finset.mem_singleton]
          cases ab with | mk a b =>
          dsimp only at ha hb; subst ha; subst hb; rfl
        exact (Finset.card_le_card hsub).trans (by simp)
      · simp only [hqeq, ↓reduceIte]
        have hsub :
            ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool)).filter
              (fun ab => cutState L p q s0 s1 c (q - 1) ab.1 = true ∧
                cutState L p q s0 s1 c (q - 1 + 1) ab.2 = false) ⊆
            {(c (q - 1), false), (c (q - 1), true)} := by
          intro ab hab
          rcases (Finset.mem_filter.mp hab).2 with ⟨ha, _⟩
          unfold cutState at ha
          have h1a : q - 1 ≠ 0 := by omega
          have h1p : ¬ q - 1 ≤ p := by omega
          have h1q : q - 1 < q := by omega
          simp only [h1a, h1p, h1q, ↓reduceIte, decide_eq_true_eq] at ha
          cases ab with | mk a b =>
          dsimp only at ha; subst ha; cases b <;> simp
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hbound : ∑ j ∈ Finset.range L, stepCount j ≤
        ∑ j ∈ Finset.range L,
          if j = p then (if p = 0 then 1 else 2)
          else if j = q - 1 then (if q = L then 1 else 2)
          else if p < j ∧ j < q - 1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL := Finset.mem_range.mp hj
      by_cases hjp : j = p
      · subst hjp; simp only [↓reduceIte]; exact hfirst
      · simp only [hjp, ↓reduceIte]
        by_cases hjq : j = q - 1
        · subst hjq; simp only [↓reduceIte]; exact hlast
        · simp only [hjq, ↓reduceIte]
          by_cases hmid' : p < j ∧ j < q - 1
          · simp only [hmid']; exact hmid j hmid'.1 (by omega)
          · simp only [hmid', ite_false]
            by_cases hlt : j < p
            · exact le_of_eq (hzero_lt j hjL hlt)
            · exact le_of_eq (hzero_ge j hjL (by omega))
    have heval :
        ∑ j ∈ Finset.range L,
          (if j = p then (if p = 0 then 1 else 2)
           else if j = q - 1 then (if q = L then 1 else 2)
           else if p < j ∧ j < q - 1 then 1 else 0) =
        (if p = 0 then 1 else 2) + (if q = L then 1 else 2) + (q - p - 2) := by
      have hp_in : p ∈ Finset.range L := Finset.mem_range.mpr (by omega)
      have hq1_in : q - 1 ∈ (Finset.range L).erase p :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      rw [← Finset.add_sum_erase _ _ hp_in, ← Finset.add_sum_erase _ _ hq1_in]
      simp only [↓reduceIte, show q - 1 ≠ p by omega]
      have hrest :
          ∑ x ∈ ((Finset.range L).erase p).erase (q - 1),
            (if x = p then (if p = 0 then 1 else 2)
             else if x = q - 1 then (if q = L then 1 else 2)
             else if p < x ∧ x < q - 1 then 1 else 0) =
          (((Finset.range L).erase p).erase (q - 1) |>.filter (fun x => p < x ∧ x < q - 1)).card := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro x hx
        have hx1 : x ≠ q - 1 := (Finset.mem_erase.mp hx).1
        have hx2 : x ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        simp only [hx1, hx2, ↓reduceIte]
      rw [hrest]
      have hflt_eq :
          (((Finset.range L).erase p).erase (q - 1)).filter (fun x => p < x ∧ x < q - 1) =
          Finset.Ioo p (q - 1) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]
        omega
      rw [hflt_eq, Nat.card_Ioo]
      omega
    have hfinal : (if p = 0 then 1 else 2) + (if q = L then 1 else 2) + (q - p - 2) ≤ L := by
      split_ifs <;> omega
    omega

private theorem sum_cut_count (L : ℕ) :
    ∑ p ∈ Finset.range L, ∑ q ∈ Finset.Icc (p + 1) L, 2 ^ (q - p - 1) = 2 ^ (L + 1) - L - 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hlast : ∑ q ∈ Finset.Icc (L + 1) (L + 1), 2 ^ (q - L - 1) = 1 := by
      simp
    rw [hlast]
    have hsplit :
        ∑ p ∈ Finset.range L, ∑ q ∈ Finset.Icc (p + 1) (L + 1), 2 ^ (q - p - 1) =
        (∑ p ∈ Finset.range L, ∑ q ∈ Finset.Icc (p + 1) L, 2 ^ (q - p - 1)) +
        ∑ p ∈ Finset.range L, 2 ^ (L - p) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hpL := Finset.mem_range.mp hp
      have hIcc : Finset.Icc (p + 1) (L + 1) = insert (L + 1) (Finset.Icc (p + 1) L) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnm : L + 1 ∉ Finset.Icc (p + 1) L := by simp
      rw [hIcc, Finset.sum_insert hnm, add_comm]
      have : L + 1 - p - 1 = L - p := by omega
      rw [this]
    have hgeom : ∑ p ∈ Finset.range L, 2 ^ (L - p) = 2 ^ (L + 1) - 2 := by
      clear ih hsplit hlast
      induction L with
      | zero => simp
      | succ k ihk =>
        rw [Finset.sum_range_succ]
        have h1k : k + 1 - k = 1 := by omega
        rw [h1k, Nat.pow_one]
        have hshift : ∑ p ∈ Finset.range k, 2 ^ (k + 1 - p) = 2 * ∑ p ∈ Finset.range k, 2 ^ (k - p) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hpk := Finset.mem_range.mp hp
          have heq : k + 1 - p = (k - p) + 1 := by omega
          rw [heq, Nat.pow_succ]; ring
        rw [hshift, ihk]
        have hge : 2 ≤ 2 ^ (k + 1) := by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          rw [Nat.pow_succ]; omega
        rw [Nat.pow_succ]
        omega
    rw [hsplit, ih, hgeom]
    have hge : L + 2 ≤ 2 ^ (L + 1) := by
      clear ih hsplit hlast hgeom
      induction L with
      | zero => decide
      | succ k ihk =>
        rw [Nat.pow_succ]; omega
    rw [Nat.pow_succ]
    omega

private theorem cut_count_mono {L H : ℕ} (h : L ≤ H) :
    2 ^ (L + 1) - L - 2 ≤ 2 ^ (H + 1) - H - 2 := by
  induction h with
  | refl => exact le_rfl
  | @step m hLm ih =>
    have hge : m + 2 ≤ 2 ^ (m + 1) := by
      clear hLm ih
      induction m with
      | zero => decide
      | succ k ihk => rw [Nat.pow_succ]; omega
    rw [Nat.pow_succ] at *
    omega

private theorem block_cut_clauses {n : ℕ} (hn : 0 < n) (b : ℕ) (r0 r1 : Fin b)
    (start0 L H : ℕ) (hL1 : 1 ≤ L) (hLH : L ≤ H) :
    ∃ B : Finset (Clause (VarT n b)),
      B.card ≤ 4 * (2 ^ (H + 1) - H - 2) ∧
      (∀ C ∈ B, C.card ≤ max 4 H + 2 ∧
        (∀ e : RawT n, (Sum.inl e, false) ∉ C) ∧
        ∃ first : Fin n, ∀ site ∈ rowsFn b C, ∃ j : Fin H, (first.val + j.val) % n = site.val) ∧
      ∀ (tab : RawT n → Bool) (y : Fin b → Bool),
        (∀ C ∈ B, ClauseSat (Sum.elim tab y) C) ↔
        ∃ xs : ℕ → Bool, xs 0 = y r0 ∧ xs L = y r1 ∧
          ∀ j < L, tab (⟨(start0 + j) % n, Nat.mod_lt _ hn⟩, (xs j, xs (j + 1))) = true := by
  classical
  let Descs :=
    ((Finset.univ : Finset (Bool × Bool)) ×ˢ
      ((Finset.range L).sigma (fun p =>
        (Finset.Icc (p + 1) L).sigma (fun q =>
          (Finset.univ : Finset (Fin (q - p - 1) → Bool))))))
  let decodeC : ∀ (p q : ℕ), (Fin (q - p - 1) → Bool) → ℕ → Bool :=
    fun p q f j => if h : p < j ∧ j < q then f ⟨j - p - 1, by omega⟩ else false
  let mkCl : ((Bool × Bool) × Σ p : ℕ, Σ q : ℕ, (Fin (q - p - 1) → Bool)) → Clause (VarT n b) :=
    fun d => cutClause hn b r0 r1 start0 L d.2.1 d.2.2.1 d.1.1 d.1.2 (decodeC d.2.1 d.2.2.1 d.2.2.2)
  let B := Descs.image mkCl
  refine ⟨B, ?_, ?_, ?_⟩
  · have hcard_le : B.card ≤ Descs.card := Finset.card_image_le
    refine hcard_le.trans ?_
    dsimp only [Descs]
    rw [Finset.card_product, Finset.card_sigma]
    have h4 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
    rw [h4]
    have hsum :
        ∑ p ∈ Finset.range L,
          ((Finset.Icc (p + 1) L).sigma (fun q => (Finset.univ : Finset (Fin (q - p - 1) → Bool)))).card =
        2 ^ (L + 1) - L - 2 := by
      rw [← sum_cut_count L]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro q _
      simp
    rw [hsum]
    exact Nat.mul_le_mul_left 4 (cut_count_mono hLH)
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨⟨⟨s0, s1⟩, ⟨p, ⟨q, f⟩⟩⟩, hd, rfl⟩
    simp only [Descs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_sigma,
      Finset.mem_range, Finset.mem_Icc] at hd
    rcases hd with ⟨hpL, ⟨hpq, hqL⟩, _⟩
    dsimp only [mkCl, cutClause]
    refine ⟨?_, ?_, ?_⟩
    · have hraw := cutRawLits_card_le hn b start0 L p q s0 s1 (decodeC p q f) (by omega) hqL
      have h1 : (insert (Sum.inr r0, !s0) (insert (Sum.inr r1, !s1)
          (cutRawLits hn b start0 L p q s0 s1 (decodeC p q f)))).card ≤
          (cutRawLits hn b start0 L p q s0 s1 (decodeC p q f)).card + 2 := by
        have a1 := Finset.card_insert_le (Sum.inr r0, !s0)
          (insert (Sum.inr r1, !s1) (cutRawLits hn b start0 L p q s0 s1 (decodeC p q f)))
        have a2 := Finset.card_insert_le (Sum.inr r1, !s1)
          (cutRawLits hn b start0 L p q s0 s1 (decodeC p q f))
        omega
      omega
    · intro e hmem
      simp only [Finset.mem_insert, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
        cutRawLits, Finset.mem_image] at hmem
      rcases hmem with ⟨_, _, heq⟩
      exact heq.2
    · refine ⟨⟨start0 % n, Nat.mod_lt _ hn⟩, ?_⟩
      intro site hsite
      rcases (Finset.mem_filter.mp hsite).2 with ⟨pair, sign, hlit⟩
      simp only [Finset.mem_insert, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
        cutRawLits, Finset.mem_image] at hlit
      rcases hlit with ⟨t, ht, heq⟩
      have htL : t.1 < L := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
      refine ⟨⟨t.1, by omega⟩, ?_⟩
      have hloc : (⟨(start0 + t.1) % n, Nat.mod_lt _ hn⟩ : Fin n) = site := by
        have h1 := Sum.inl.inj heq.1
        exact congrArg Prod.fst h1
      rw [← hloc]
      simp [Nat.add_mod]
  · intro tab y
    constructor
    · intro hsat
      by_contra hno
      let R : ℕ → Bool → Prop := fun j a =>
        ∃ xs : ℕ → Bool, xs 0 = y r0 ∧ xs j = a ∧
          ∀ t < j, tab (⟨(start0 + t) % n, Nat.mod_lt _ hn⟩, (xs t, xs (t + 1))) = true
      have hR0 : R 0 (y r0) := ⟨fun _ => y r0, rfl, rfl, fun _ h => by omega⟩
      have hRL : ¬ R L (y r1) := fun ⟨xs, hx0, hxL, hst⟩ => hno ⟨xs, hx0, hxL, hst⟩
      have hRstep : ∀ j < L, ∀ a b0, R j a →
          tab (⟨(start0 + j) % n, Nat.mod_lt _ hn⟩, (a, b0)) = true → R (j + 1) b0 := by
        rintro j _ a b0 ⟨xs, hx0, hxj, hst⟩ htab
        refine ⟨fun t => if t ≤ j then xs t else b0, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp
        · intro t ht
          by_cases htj : t < j
          · have hle1 : t ≤ j := by omega
            have hle2 : t + 1 ≤ j := by omega
            simp only [hle1, hle2, ↓reduceIte]
            exact hst t htj
          · have heq : t = j := by omega
            subst heq
            simp only [le_refl, ↓reduceIte, show ¬ t + 1 ≤ t by omega, hxj]
            exact htab
      let Pset := (Finset.range L).filter (fun j => j = 0 ∨ (R j false ∧ R j true))
      have h0P : 0 ∈ Pset := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inl rfl⟩
      let p := Pset.max' ⟨0, h0P⟩
      have hp_mem : p ∈ Pset := Finset.max'_mem Pset ⟨0, h0P⟩
      have hpL : p < L := Finset.mem_range.mp (Finset.mem_filter.mp hp_mem).1
      have hp_prop : p = 0 ∨ (R p false ∧ R p true) := (Finset.mem_filter.mp hp_mem).2
      have hp_max : ∀ j, p < j → j < L → ¬ (R j false ∧ R j true) := by
        intro j hjp hjL hboth
        have hmem : j ∈ Pset := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjL, Or.inr hboth⟩
        have hle := Finset.le_max' Pset j hmem
        omega
      let Qset := (Finset.Icc (p + 1) L).filter (fun j => j = L ∨ ∀ a, ¬ R j a)
      have hLQ : L ∈ Qset := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, Or.inl rfl⟩
      let q := Qset.min' ⟨L, hLQ⟩
      have hq_mem : q ∈ Qset := Finset.min'_mem Qset ⟨L, hLQ⟩
      have hq_range := Finset.mem_Icc.mp (Finset.mem_filter.mp hq_mem).1
      have hq_prop : q = L ∨ ∀ a, ¬ R q a := (Finset.mem_filter.mp hq_mem).2
      have hq_min : ∀ j, p < j → j < q → ∃ a, R j a := by
        intro j hjp hjq
        by_contra hnone
        push Not at hnone
        have hmem : j ∈ Qset :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Or.inr hnone⟩
        have hle := Finset.min'_le Qset j hmem
        omega
      let f : Fin (q - p - 1) → Bool := fun t =>
        Classical.choose (hq_min (p + 1 + t.val) (by omega) (by omega))
      have hf_spec : ∀ j, p < j → j < q → R j (decodeC p q f j) := by
        intro j hjp hjq
        have hdec : decodeC p q f j = f ⟨j - p - 1, by omega⟩ := by
          dsimp only [decodeC]; split_ifs <;> first | rfl | omega
        rw [hdec]
        dsimp only [f]
        have hsp := Classical.choose_spec (hq_min (p + 1 + (j - p - 1)) (by omega) (by omega))
        generalize Classical.choose (hq_min (p + 1 + (j - p - 1)) (by omega) (by omega)) = v at hsp ⊢
        rw [show p + 1 + (j - p - 1) = j by omega] at hsp
        exact hsp
      have hC_in : cutClause hn b r0 r1 start0 L p q (y r0) (y r1) (decodeC p q f) ∈ B := by
        refine Finset.mem_image.mpr ⟨⟨(y r0, y r1), ⟨p, ⟨q, f⟩⟩⟩, ?_, rfl⟩
        simp only [Descs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_sigma,
          Finset.mem_range, Finset.mem_Icc]
        exact ⟨hpL, hq_range, trivial⟩
      rcases hsat _ hC_in with ⟨lit, hlit, hsat_lit⟩
      simp only [cutClause, Finset.mem_insert] at hlit
      rcases hlit with rfl | rfl | hraw
      · simp only [Sum.elim_inr] at hsat_lit
        cases y r0 <;> simp at hsat_lit
      · simp only [Sum.elim_inr] at hsat_lit
        cases y r1 <;> simp at hsat_lit
      · rcases Finset.mem_image.mp hraw with ⟨⟨j, ⟨a, b0⟩⟩, ht, rfl⟩
        rcases Finset.mem_filter.mp ht with ⟨htprod, ha, hb⟩
        have hjL : j < L := Finset.mem_range.mp (Finset.mem_product.mp htprod).1
        simp only [Sum.elim_inl] at hsat_lit
        have hjp : p ≤ j := by
          by_contra hlt
          unfold cutState at hb
          have h1 : j + 1 ≠ 0 := by omega
          have h2 : j + 1 ≤ p := by omega
          simp only [h1, h2, ↓reduceIte] at hb
          exact Bool.noConfusion hb
        have hjq : j < q := by
          by_contra hge
          unfold cutState at ha
          have h1 : j ≠ 0 := by omega
          have h2 : ¬ j ≤ p := by omega
          have h3 : ¬ j < q := by omega
          simp only [h1, h2, h3, hjL, ↓reduceIte] at ha
          exact Bool.noConfusion ha
        have hRa : R j a := by
          by_cases heq : j = p
          · subst heq
            rcases hp_prop with hp0 | ⟨hF, hT⟩
            · unfold cutState at ha
              dsimp only at ha
              have hpa : decide (a = y r0) = true := by
                split_ifs at ha
                exact ha
              simp only [decide_eq_true_eq] at hpa
              rw [hp0, hpa]; exact hR0
            · cases a
              · exact hF
              · exact hT
          · have hjp' : p < j := by omega
            unfold cutState at ha
            have h1 : j ≠ 0 := by omega
            have h2 : ¬ j ≤ p := by omega
            simp only [h1, h2, hjq, ↓reduceIte, decide_eq_true_eq] at ha
            subst ha
            exact hf_spec j hjp' hjq
        have hRb : R (j + 1) b0 := hRstep j hjL a b0 hRa (by simpa using hsat_lit)
        by_cases hj1q : j + 1 < q
        · unfold cutState at hb
          have h1 : j + 1 ≠ 0 := by omega
          have h2 : ¬ j + 1 ≤ p := by omega
          simp only [h1, h2, hj1q, ↓reduceIte, decide_eq_false_iff_not] at hb
          have hRc := hf_spec (j + 1) (by omega) hj1q
          have hnotboth := hp_max (j + 1) (by omega) (by omega)
          cases b0 <;> cases hc : decodeC p q f (j + 1) <;> simp [hc] at hb hRc hnotboth
          · exact hnotboth hRb hRc
          · exact hnotboth hRc hRb
        · have hj1eq : j + 1 = q := by omega
          rw [hj1eq] at hb hRb
          rcases hq_prop with hqL | hnone
          · unfold cutState at hb
            dsimp only at hb
            have hqb : decide (b0 ≠ y r1) = false := by
              split_ifs at hb <;> first | exact hb | omega
            simp only [decide_eq_false_iff_not, not_not] at hqb
            rw [hqL, hqb] at hRb
            exact hRL hRb
          · exact hnone b0 hRb
    · rintro ⟨xs, hx0, hxL, hst⟩ C hC
      rcases Finset.mem_image.mp hC with ⟨⟨⟨s0, s1⟩, ⟨p, ⟨q, f⟩⟩⟩, hd, rfl⟩
      simp only [Descs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_sigma,
        Finset.mem_range, Finset.mem_Icc] at hd
      rcases hd with ⟨hpL, ⟨hpq, hqL⟩, _⟩
      dsimp only [mkCl, cutClause]
      by_cases hs0 : y r0 = s0
      · by_cases hs1 : y r1 = s1
        · have h0 : cutState L p q s0 s1 (decodeC p q f) 0 (xs 0) = true := by
            rw [hx0, hs0]; exact cutState_zero
          have hL : cutState L p q s0 s1 (decodeC p q f) L (xs L) = false := by
            rw [hxL, hs1]; exact cutState_end (by omega) hqL
          have hex : ∃ j < L,
              cutState L p q s0 s1 (decodeC p q f) j (xs j) = true ∧
              cutState L p q s0 s1 (decodeC p q f) (j + 1) (xs (j + 1)) = false := by
            by_contra hall
            push Not at hall
            have hind : ∀ j ≤ L, cutState L p q s0 s1 (decodeC p q f) j (xs j) = true := by
              intro j
              induction j with
              | zero => intro _; exact h0
              | succ j ih =>
                intro hj
                have hprev := ih (by omega)
                have hnf := hall j (by omega) hprev
                exact Bool.eq_true_of_not_eq_false hnf
            rw [hind L le_rfl] at hL
            exact Bool.noConfusion hL
          rcases hex with ⟨j, hjL, hjT, hjF⟩
          refine ⟨(Sum.inl (⟨(start0 + j) % n, Nat.mod_lt _ hn⟩, (xs j, xs (j + 1))), true), ?_, ?_⟩
          · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
            refine Finset.mem_image.mpr ⟨(j, (xs j, xs (j + 1))), ?_, rfl⟩
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjL, Finset.mem_univ _⟩, hjT, hjF⟩
          · simpa using hst j hjL
        · refine ⟨(Sum.inr r1, !s1), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
          simp only [Sum.elim_inr]
          cases h1 : y r1 <;> cases s1 <;> simp [h1] at hs1 ⊢
      · refine ⟨(Sum.inr r0, !s0), Finset.mem_insert_self _ _, ?_⟩
        simp only [Sum.elim_inr]
        cases h0 : y r0 <;> cases s0 <;> simp [h0] at hs0 ⊢

private theorem solve_236_upper (n : ℕ) (hn : 0 < n) (b : ℕ) (hb : 0 < b) (hbn : b ≤ n) :
    let H := (n + b - 1) / b
    ∃ F : Finset (Clause (VarT n b)), encPred hn b F ∧
      F.card ≤ 4 * b * (2 ^ (H + 1) - H - 2) ∧
      ∀ C ∈ F, C.card ≤ max 4 H + 2 ∧
        (∀ e : RawT n, (Sum.inl e, false) ∉ C) ∧
        ∃ first : Fin n, ∀ site ∈ rowsFn b C, ∃ j : Fin H, (first.val + j.val) % n = site.val := by
  classical
  dsimp only
  let H := (n + b - 1) / b
  let startNat : ℕ → ℕ := fun r => r * n / b
  have hstart0 : startNat 0 = 0 := by simp [startNat]
  have hstartb : startNat b = n := by
    dsimp only [startNat]; exact Nat.mul_div_cancel_left n hb
  have hL_bounds : ∀ r : Fin b, 1 ≤ startNat (r.val + 1) - startNat r.val ∧
      startNat (r.val + 1) - startNat r.val ≤ H := by
    intro r
    dsimp only [startNat]
    constructor
    · have h1 : (r.val * n + b) / b ≤ ((r.val + 1) * n) / b :=
        Nat.div_le_div_right (by nlinarith)
      rw [Nat.add_div_right _ hb] at h1
      omega
    · have hHb : n ≤ H * b := by
        have hdm := Nat.div_add_mod (n + b - 1) b
        have hlt := Nat.mod_lt (n + b - 1) hb
        have hcomm : b * ((n + b - 1) / b) = ((n + b - 1) / b) * b := Nat.mul_comm _ _
        dsimp only [H]
        omega
      have hrm := Nat.div_add_mod (r.val * n) b
      have hrm_lt := Nat.mod_lt (r.val * n) hb
      have hle : (r.val + 1) * n < (r.val * n / b + H + 1) * b := by nlinarith
      have hdiv : ((r.val + 1) * n) / b < r.val * n / b + H + 1 :=
        (Nat.div_lt_iff_lt_mul hb).mpr hle
      have hdiv' : ((r.val + 1) * n) / b ≤ H + r.val * n / b := by
        have hlt := Nat.lt_succ_iff.mp hdiv
        rw [add_comm (r.val * n / b) H] at hlt
        exact hlt
      exact Nat.sub_le_iff_le_add.mpr hdiv'
  let nextB : Fin b → Fin b := fun r => ⟨(r.val + 1) % b, Nat.mod_lt _ hb⟩
  have hblock : ∀ r : Fin b,
      ∃ B : Finset (Clause (VarT n b)),
        B.card ≤ 4 * (2 ^ (H + 1) - H - 2) ∧
        (∀ C ∈ B, C.card ≤ max 4 H + 2 ∧
          (∀ e : RawT n, (Sum.inl e, false) ∉ C) ∧
          ∃ first : Fin n, ∀ site ∈ rowsFn b C, ∃ j : Fin H, (first.val + j.val) % n = site.val) ∧
        ∀ (tab : RawT n → Bool) (y : Fin b → Bool),
          (∀ C ∈ B, ClauseSat (Sum.elim tab y) C) ↔
          ∃ xs : ℕ → Bool, xs 0 = y r ∧ xs (startNat (r.val + 1) - startNat r.val) = y (nextB r) ∧
            ∀ j < startNat (r.val + 1) - startNat r.val,
              tab (⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩, (xs j, xs (j + 1))) = true :=
    fun r => block_cut_clauses hn b r (nextB r) (startNat r.val)
      (startNat (r.val + 1) - startNat r.val) H (hL_bounds r).1 (hL_bounds r).2
  let Bf : Fin b → Finset (Clause (VarT n b)) := fun r => Classical.choose (hblock r)
  have hBf : ∀ r : Fin b,
      (Bf r).card ≤ 4 * (2 ^ (H + 1) - H - 2) ∧
      (∀ C ∈ Bf r, C.card ≤ max 4 H + 2 ∧
        (∀ e : RawT n, (Sum.inl e, false) ∉ C) ∧
        ∃ first : Fin n, ∀ site ∈ rowsFn b C, ∃ j : Fin H, (first.val + j.val) % n = site.val) ∧
      ∀ (tab : RawT n → Bool) (y : Fin b → Bool),
        (∀ C ∈ Bf r, ClauseSat (Sum.elim tab y) C) ↔
        ∃ xs : ℕ → Bool, xs 0 = y r ∧ xs (startNat (r.val + 1) - startNat r.val) = y (nextB r) ∧
          ∀ j < startNat (r.val + 1) - startNat r.val,
            tab (⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩, (xs j, xs (j + 1))) = true :=
    fun r => Classical.choose_spec (hblock r)
  let F := (Finset.univ : Finset (Fin b)).biUnion Bf
  refine ⟨F, ?_, ?_, ?_⟩
  · intro tab
    constructor
    · rintro ⟨x, hx⟩
      have hstart_lt : ∀ r : Fin b, startNat r.val < n := by
        intro r
        have h1 : r.val * n < b * n := Nat.mul_lt_mul_of_pos_right r.isLt hn
        exact (Nat.div_lt_iff_lt_mul hb).mpr (by linarith)
      let y : Fin b → Bool := fun r => x ⟨startNat r.val, hstart_lt r⟩
      refine ⟨y, ?_⟩
      intro C hC
      rcases Finset.mem_biUnion.mp hC with ⟨r, _, hCr⟩
      exact ((hBf r).2.2 tab y).mpr ⟨fun j => x ⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩,
          by simp [y, Nat.mod_eq_of_lt (hstart_lt r)],
          by
            have hadd : startNat r.val + (startNat (r.val + 1) - startNat r.val) = startNat (r.val + 1) := by
              have := (hL_bounds r).1; omega
            dsimp only
            simp only [hadd]
            by_cases hrb : r.val + 1 < b
            · have hnb : nextB r = ⟨r.val + 1, hrb⟩ := by
                ext; simp [nextB, Nat.mod_eq_of_lt hrb]
              rw [hnb]
              simp [y, Nat.mod_eq_of_lt (hstart_lt ⟨r.val + 1, hrb⟩)]
            · have hreq : r.val + 1 = b := by have := r.isLt; omega
              have hnb : nextB r = ⟨0, hb⟩ := by
                ext; simp [nextB, hreq]
              simp only [hnb, hreq, hstartb, Nat.mod_self, y, hstart0],
          fun j hj => by
            have hnext : nextIdx hn ⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩ =
                ⟨(startNat r.val + (j + 1)) % n, Nat.mod_lt _ hn⟩ := by
              ext; dsimp only [nextIdx]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
            dsimp only
            rw [← hnext]
            exact hx _⟩ C hCr
    · rintro ⟨y, hy⟩
      have hxs : ∀ r : Fin b,
          ∃ xs : ℕ → Bool, xs 0 = y r ∧ xs (startNat (r.val + 1) - startNat r.val) = y (nextB r) ∧
            ∀ j < startNat (r.val + 1) - startNat r.val,
              tab (⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩, (xs j, xs (j + 1))) = true := by
        intro r
        exact ((hBf r).2.2 tab y).mp (fun C hCr => hy C (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hCr⟩))
      let xsF : Fin b → ℕ → Bool := fun r => Classical.choose (hxs r)
      have hxsF : ∀ r : Fin b,
          xsF r 0 = y r ∧ xsF r (startNat (r.val + 1) - startNat r.val) = y (nextB r) ∧
          ∀ j < startNat (r.val + 1) - startNat r.val,
            tab (⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩, (xsF r j, xsF r (j + 1))) = true :=
        fun r => Classical.choose_spec (hxs r)
      have hmono : ∀ r1 r2 : ℕ, r1 ≤ r2 → startNat r1 ≤ startNat r2 := fun r1 r2 h =>
        Nat.div_le_div_right (Nat.mul_le_mul_right n h)
      have hcover : ∀ i : Fin n, ∃ r : Fin b, startNat r.val ≤ i.val ∧ i.val < startNat (r.val + 1) := by
        intro i
        let S := (Finset.univ : Finset (Fin b)).filter (fun r => startNat r.val ≤ i.val)
        have h0S : ⟨0, hb⟩ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hstart0]⟩
        let r := S.max' ⟨⟨0, hb⟩, h0S⟩
        have hr_mem := Finset.max'_mem S ⟨⟨0, hb⟩, h0S⟩
        have hr_le : startNat r.val ≤ i.val := (Finset.mem_filter.mp hr_mem).2
        refine ⟨r, hr_le, ?_⟩
        by_cases hlt : r.val + 1 < b
        · by_contra hge
          have hmem : (⟨r.val + 1, hlt⟩ : Fin b) ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
          have hle := Finset.le_max' S ⟨r.val + 1, hlt⟩ hmem
          change r.val + 1 ≤ r.val at hle
          omega
        · have hreq : r.val + 1 = b := by have := r.isLt; omega
          rw [hreq, hstartb]; exact i.isLt
      have huniq : ∀ i : Fin n, ∀ r1 r2 : Fin b,
          startNat r1.val ≤ i.val → i.val < startNat (r1.val + 1) →
          startNat r2.val ≤ i.val → i.val < startNat (r2.val + 1) → r1 = r2 := by
        intro i r1 r2 h1a h1b h2a h2b
        ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := hmono (r1.val + 1) r2.val (by omega); omega
        · have := hmono (r2.val + 1) r1.val (by omega); omega
      let x : Fin n → Bool := fun i =>
        let r := Classical.choose (hcover i)
        xsF r (i.val - startNat r.val)
      have hx_at : ∀ (r : Fin b) (i : Fin n),
          startNat r.val ≤ i.val → i.val < startNat (r.val + 1) →
          x i = xsF r (i.val - startNat r.val) := by
        intro r i h1 h2
        dsimp only [x]
        have hsp := Classical.choose_spec (hcover i)
        have heq := huniq i (Classical.choose (hcover i)) r hsp.1 hsp.2 h1 h2
        rw [heq]
      refine ⟨x, ?_⟩
      intro i
      rcases hcover i with ⟨r, hr1, hr2⟩
      have hxi := hx_at r i hr1 hr2
      let j := i.val - startNat r.val
      have hj_lt : j < startNat (r.val + 1) - startNat r.val := by omega
      have hstep := (hxsF r).2.2 j hj_lt
      have hidx : (⟨(startNat r.val + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
        ext
        have hadd : startNat r.val + j = i.val := by omega
        simp only [hadd, Nat.mod_eq_of_lt i.isLt]
      rw [hidx] at hstep
      have hnext_val : x (nextIdx hn i) = xsF r (j + 1) := by
        by_cases hlast : i.val + 1 < startNat (r.val + 1)
        · have hi1_lt : i.val + 1 < n := by
            have := hmono (r.val + 1) b (by omega); rw [hstartb] at this; omega
          have hni : (nextIdx hn i).val = i.val + 1 := by simp [nextIdx, Nat.mod_eq_of_lt hi1_lt]
          rw [hx_at r (nextIdx hn i) (by omega) (by omega), hni]
          congr 1; omega
        · have heq_end : i.val + 1 = startNat (r.val + 1) := by omega
          have hj1_eq : j + 1 = startNat (r.val + 1) - startNat r.val := by omega
          rw [hj1_eq, (hxsF r).2.1]
          by_cases hrb : r.val + 1 < b
          · have hnb : nextB r = ⟨r.val + 1, hrb⟩ := by ext; simp [nextB, Nat.mod_eq_of_lt hrb]
            have hst_lt : startNat (r.val + 1) < n := by
              have h1 : (r.val + 1) * n < b * n := Nat.mul_lt_mul_of_pos_right hrb hn
              exact (Nat.div_lt_iff_lt_mul hb).mpr (by linarith)
            have hni : (nextIdx hn i).val = startNat (r.val + 1) := by
              simp [nextIdx, heq_end, Nat.mod_eq_of_lt hst_lt]
            have hlt_next : startNat (r.val + 1) < startNat (r.val + 1 + 1) := by
              have h := (hL_bounds ⟨r.val + 1, hrb⟩).1; dsimp only at h; omega
            have h1a : startNat (⟨r.val + 1, hrb⟩ : Fin b).val ≤ (nextIdx hn i).val := by
              dsimp only; omega
            have h1b : (nextIdx hn i).val < startNat ((⟨r.val + 1, hrb⟩ : Fin b).val + 1) := by
              dsimp only; omega
            rw [hx_at ⟨r.val + 1, hrb⟩ (nextIdx hn i) h1a h1b, hni, Nat.sub_self,
              (hxsF ⟨r.val + 1, hrb⟩).1, hnb]
          · have hreq : r.val + 1 = b := by have := r.isLt; omega
            have hnb : nextB r = ⟨0, hb⟩ := by ext; simp [nextB, hreq]
            have hni : (nextIdx hn i).val = 0 := by
              simp [nextIdx, heq_end, hreq, hstartb]
            have hlt0 : 0 < startNat 1 := by
              have h := (hL_bounds ⟨0, hb⟩).1
              change 1 ≤ startNat 1 - startNat 0 at h
              rw [hstart0] at h; omega
            rw [hx_at ⟨0, hb⟩ (nextIdx hn i) (by simp [hstart0]) (by simpa [hni] using hlt0),
              hni, hstart0, Nat.sub_self, (hxsF ⟨0, hb⟩).1, hnb]
      rw [hxi, hnext_val]
      exact hstep
  · calc F.card ≤ ∑ r : Fin b, (Bf r).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin b, 4 * (2 ^ (H + 1) - H - 2) := Finset.sum_le_sum (fun r _ => (hBf r).1)
      _ = 4 * b * (2 ^ (H + 1) - H - 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  · intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨r, _, hCr⟩
    exact (hBf r).2.1 C hCr

private def tabOf {n : ℕ} (w : Fin n → Bool) : RawT n → Bool :=
  fun e => decide (e.2.2 = (e.2.1 ^^ w e.1))

private def wordPar {n : ℕ} (w : Fin n → Bool) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).card)

private theorem wordPar_flip {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    wordPar (Function.update w i (!(w i))) = !(wordPar w) := by
  classical
  unfold wordPar
  by_cases hwi : w i = true
  · have hset : Finset.univ.filter (fun j : Fin n => w j = true) =
        insert i (Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = i
      · subst hj; simp [hwi]
      · simp [hj]
    have hnm : i ∉ Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true) := by
      simp [hwi]
    rw [hset, Finset.card_insert_of_notMem hnm]
    by_cases ho : Odd (Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true)).card
    · have hno : ¬ Odd ((Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true)).card + 1) := by
        rw [Nat.odd_add_one]; exact not_not.mpr ho
      rw [decide_eq_true ho, decide_eq_false hno]; rfl
    · have hyo : Odd ((Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true)).card + 1) := by
        rw [Nat.odd_add_one]; exact ho
      rw [decide_eq_false ho, decide_eq_true hyo]; rfl
  · have hwiF : w i = false := Bool.eq_false_iff.mpr hwi
    have hset : Finset.univ.filter (fun j : Fin n => Function.update w i (!(w i)) j = true) =
        insert i (Finset.univ.filter (fun j : Fin n => w j = true)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = i
      · subst hj; simp [hwiF]
      · simp [hj]
    have hnm : i ∉ Finset.univ.filter (fun j : Fin n => w j = true) := by simp [hwiF]
    rw [hset, Finset.card_insert_of_notMem hnm]
    by_cases ho : Odd (Finset.univ.filter (fun j : Fin n => w j = true)).card
    · have hno : ¬ Odd ((Finset.univ.filter (fun j : Fin n => w j = true)).card + 1) := by
        rw [Nat.odd_add_one]; exact not_not.mpr ho
      rw [decide_eq_true ho, decide_eq_false hno]; rfl
    · have hyo : Odd ((Finset.univ.filter (fun j : Fin n => w j = true)).card + 1) := by
        rw [Nat.odd_add_one]; exact ho
      rw [decide_eq_false ho, decide_eq_true hyo]; rfl

private theorem card_wordPar {n : ℕ} (hn : 0 < n) (b : Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = b)).card = 2 ^ (n - 1) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let flip0 : (Fin n → Bool) → (Fin n → Bool) := fun w => Function.update w i0 (!(w i0))
  have hinv : Function.Involutive flip0 := by
    intro w; funext j
    by_cases hj : j = i0
    · subst hj; simp [flip0]
    · simp [flip0, hj]
  have heq :
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = false)).card =
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = true)).card := by
    refine Finset.card_bij (fun w _ => flip0 w) ?_ ?_ ?_
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [wordPar_flip, (Finset.mem_filter.mp hw).2]; rfl⟩
    · intro w1 _ w2 _ h
      have := congrArg flip0 h; simpa [hinv w1, hinv w2] using this
    · intro w hw
      exact ⟨flip0 w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [wordPar_flip, (Finset.mem_filter.mp hw).2]; rfl⟩, hinv w⟩
  have hsum :
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = false)).card +
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = true)).card = 2 ^ n := by
    have hunion :
        (Finset.univ.filter (fun w : Fin n → Bool => wordPar w = false)) ∪
        (Finset.univ.filter (fun w : Fin n → Bool => wordPar w = true)) = Finset.univ := by
      ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases wordPar w <;> simp
    have hdisj : Disjoint
        (Finset.univ.filter (fun w : Fin n → Bool => wordPar w = false))
        (Finset.univ.filter (fun w : Fin n → Bool => wordPar w = true)) := by
      rw [Finset.disjoint_left]; intro w h1 h2
      have a1 := (Finset.mem_filter.mp h1).2
      have a2 := (Finset.mem_filter.mp h2).2
      rw [a1] at a2; exact Bool.noConfusion a2
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.pow_succ]
    ring
  cases b <;> omega

private theorem feasible_tabOf_iff {n : ℕ} (hn : 0 < n) (w : Fin n → Bool) :
    feasiblePred hn (tabOf w) ↔ wordPar w = false := by
  classical
  let prefPar : ℕ → Bool := fun k =>
    decide (Odd ((Finset.range k).filter (fun t => if h : t < n then w ⟨t, h⟩ = true else false)).card)
  have hpref_step : ∀ k (hk : k < n), prefPar (k + 1) = (prefPar k ^^ w ⟨k, hk⟩) := by
    intro k hk
    unfold prefPar
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hk, ↓reduceDIte]
    cases hwk : w ⟨k, hk⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    · simp only [↓reduceIte, Bool.xor_true]
      have hnm : k ∉ (Finset.range k).filter (fun t => if h : t < n then w ⟨t, h⟩ = true else false) := by
        simp
      rw [Finset.card_insert_of_notMem hnm]
      by_cases ho : Odd ((Finset.range k).filter (fun t => if h : t < n then w ⟨t, h⟩ = true else false)).card
      · have hno : ¬ Odd (((Finset.range k).filter (fun t => if h : t < n then w ⟨t, h⟩ = true else false)).card + 1) := by
          rw [Nat.odd_add_one]; exact not_not.mpr ho
        rw [decide_eq_true ho, decide_eq_false hno]; rfl
      · have hyo : Odd (((Finset.range k).filter (fun t => if h : t < n then w ⟨t, h⟩ = true else false)).card + 1) := by
          rw [Nat.odd_add_one]; exact ho
        rw [decide_eq_false ho, decide_eq_true hyo]; rfl
  have hpref_n : prefPar n = wordPar w := by
    unfold prefPar wordPar
    congr 2
    refine Finset.card_bij (fun t ht => ⟨t, Finset.mem_range.mp (Finset.mem_filter.mp ht).1⟩) ?_ ?_ ?_
    · intro t ht
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      have h2 := (Finset.mem_filter.mp ht).2
      simp only [hlt, ↓reduceDIte] at h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
    · intro t1 _ t2 _ h; exact congrArg Fin.val h
    · intro i hi
      refine ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, ?_⟩, rfl⟩
      simp only [i.isLt, ↓reduceDIte]
      exact (Finset.mem_filter.mp hi).2
  constructor
  · rintro ⟨x, hx⟩
    have hwalk : ∀ k ≤ n, x ⟨k % n, Nat.mod_lt _ hn⟩ = (x ⟨0, hn⟩ ^^ prefPar k) := by
      intro k
      induction k with
      | zero => intro _; simp [prefPar]
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hklt : k < n := by omega
        have hstep := hx ⟨k, hklt⟩
        simp only [tabOf, decide_eq_true_eq] at hstep
        have hnext : nextIdx hn ⟨k, hklt⟩ = ⟨(k + 1) % n, Nat.mod_lt _ hn⟩ := rfl
        rw [hnext] at hstep
        have hprev' : x ⟨k, hklt⟩ = (x ⟨0, hn⟩ ^^ prefPar k) := by
          convert hprev using 2
          ext; simp [Nat.mod_eq_of_lt hklt]
        rw [hstep, hprev', hpref_step k hklt]
        cases x ⟨0, hn⟩ <;> cases prefPar k <;> cases w ⟨k, hklt⟩ <;> rfl
    have h0 := hwalk n le_rfl
    simp only [Nat.mod_self, hpref_n] at h0
    cases hx0 : x ⟨0, hn⟩ <;> cases hp : wordPar w <;> simp [hx0, hp] at h0 ⊢
  · intro hpar
    refine ⟨fun i => prefPar i.val, ?_⟩
    intro i
    simp only [tabOf, decide_eq_true_eq]
    by_cases hlast : i.val + 1 < n
    · have hni : nextIdx hn i = ⟨i.val + 1, hlast⟩ := by ext; simp [nextIdx, Nat.mod_eq_of_lt hlast]
      rw [hni]
      exact hpref_step i.val i.isLt
    · have heq : i.val + 1 = n := by have := i.isLt; omega
      have hni : nextIdx hn i = ⟨0, hn⟩ := by ext; simp [nextIdx, heq]
      rw [hni]
      have h1 := hpref_step i.val i.isLt
      rw [heq, hpref_n, hpar] at h1
      simpa [prefPar] using h1

private theorem solve_236_a0 {n : ℕ} (hn : 0 < n) (G : Finset (Clause (VarT n 0)))
    (henc : encPred hn 0 G) :
    2 ^ (n - 1) ≤ (G.filter (fun item => 2 * n ≤ (item.filter (fun lit => lit.2 = true)).card)).card := by
  classical
  let Odds := (Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = true)
  have hpick : ∀ w ∈ Odds, ∃ C ∈ G, ¬ ClauseSat (Sum.elim (tabOf w) Fin.elim0) C := by
    intro w hw
    have hnf : ¬ feasiblePred hn (tabOf w) := by
      rw [feasible_tabOf_iff hn w, (Finset.mem_filter.mp hw).2]; decide
    by_contra hall
    push Not at hall
    exact hnf ((henc (tabOf w)).mpr ⟨Fin.elim0, fun C hC => hall C hC⟩)
  let f : (Fin n → Bool) → Clause (VarT n 0) := fun w =>
    if hw : w ∈ Odds then Classical.choose (hpick w hw) else ∅
  have hf_mem : ∀ w ∈ Odds, f w ∈ G ∧ ¬ ClauseSat (Sum.elim (tabOf w) Fin.elim0) (f w) := by
    intro w hw; dsimp only [f]; simp only [hw, ↓reduceDIte]; exact Classical.choose_spec (hpick w hw)
  have hf_has_lit : ∀ w ∈ Odds, ∀ (i : Fin n) (a : Bool),
      (Sum.inl (i, (a, !(a ^^ w i))), true) ∈ f w := by
    intro w hw i a
    let e0 : RawT n := (i, (a, !(a ^^ w i)))
    let tab' : RawT n → Bool := Function.update (tabOf w) e0 true
    have hfeas' : feasiblePred hn tab' := by
      let w' := Function.update w i (!(w i))
      have hpar' : wordPar w' = false := by
        rw [wordPar_flip, (Finset.mem_filter.mp hw).2]; rfl
      rcases (feasible_tabOf_iff hn w').mpr hpar' with ⟨x0, hx0⟩
      let flipAll : Bool := x0 i ^^ a
      refine ⟨fun j => x0 j ^^ flipAll, ?_⟩
      intro j
      have hstep := hx0 j
      simp only [tabOf, decide_eq_true_eq] at hstep
      by_cases hj : j = i
      · subst hj
        have hxi : (x0 j ^^ flipAll) = a := by
          dsimp only [flipAll]; cases x0 j <;> cases a <;> rfl
        have hxni : (x0 (nextIdx hn j) ^^ flipAll) = !(a ^^ w j) := by
          rw [hstep]
          simp only [w', Function.update_self, flipAll]
          cases x0 j <;> cases a <;> cases w j <;> rfl
        dsimp only
        rw [hxi, hxni]
        simp [tab', e0]
      · have hne : (j, (x0 j ^^ flipAll, x0 (nextIdx hn j) ^^ flipAll)) ≠ e0 :=
          fun h => hj (congrArg Prod.fst h)
        simp only [tab', Function.update_of_ne hne, tabOf, decide_eq_true_eq]
        rw [hstep]
        simp only [w', Function.update_of_ne hj]
        cases x0 j <;> cases flipAll <;> cases w j <;> rfl
    rcases (henc tab').mp hfeas' with ⟨y, hy⟩
    have hy0 : y = Fin.elim0 := funext (fun j => Fin.elim0 j)
    subst hy0
    have hsat := hy (f w) (hf_mem w hw).1
    rcases hsat with ⟨lit, hlit, hsat_lit⟩
    by_contra hnot
    apply (hf_mem w hw).2
    refine ⟨lit, hlit, ?_⟩
    cases lit with | mk v s =>
    cases v with
    | inr z => exact Fin.elim0 z
    | inl e =>
      simp only [Sum.elim_inl] at hsat_lit ⊢
      by_cases he : e = e0
      · subst he
        cases s
        · simp [tab'] at hsat_lit
        · exact absurd hlit hnot
      · simpa [tab', he] using hsat_lit
  have hf_card : ∀ w ∈ Odds, 2 * n ≤ ((f w).filter (fun lit => lit.2 = true)).card := by
    intro w hw
    let img := ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset Bool)).image
      (fun p => ((Sum.inl (p.1, (p.2, !(p.2 ^^ w p.1))) : VarT n 0), true))
    have hsub : img ⊆ (f w).filter (fun lit => lit.2 = true) := by
      intro lit hlit
      rcases Finset.mem_image.mp hlit with ⟨⟨i, a⟩, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨hf_has_lit w hw i a, rfl⟩
    have hinj : Function.Injective
        (fun p : Fin n × Bool => ((Sum.inl (p.1, (p.2, !(p.2 ^^ w p.1))) : VarT n 0), true)) := by
      intro ⟨i1, a1⟩ ⟨i2, a2⟩ h
      have h1 := Sum.inl.inj (Prod.mk.inj h).1
      have hi : i1 = i2 := (Prod.mk.inj h1).1
      have ha : a1 = a2 := (Prod.mk.inj (Prod.mk.inj h1).2).1
      exact Prod.ext hi ha
    have hcard_img : img.card = 2 * n := by
      dsimp only [img]
      rw [Finset.card_image_of_injective _ hinj, Finset.card_product]
      simp [Nat.mul_comm]
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  have hf_inj : Set.InjOn f (Odds : Set (Fin n → Bool)) := by
    intro w1 hw1 w2 hw2 heq
    by_contra hne
    have hex : ∃ i : Fin n, w1 i ≠ w2 i := by
      by_contra hall; push Not at hall; exact hne (funext hall)
    rcases hex with ⟨i, hi⟩
    have hlit : (Sum.inl (i, (false, !(false ^^ w1 i))), true) ∈ f w2 := by
      rw [← heq]; exact hf_has_lit w1 hw1 i false
    apply (hf_mem w2 hw2).2
    refine ⟨_, hlit, ?_⟩
    simp only [Sum.elim_inl, tabOf, decide_eq_true_eq]
    cases h1 : w1 i <;> cases h2 : w2 i <;> simp [h1, h2] at hi ⊢
  have hsub_G : Odds.image f ⊆ G.filter (fun item => 2 * n ≤ (item.filter (fun lit => lit.2 = true)).card) := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨w, hw, rfl⟩
    exact Finset.mem_filter.mpr ⟨(hf_mem w hw).1, hf_card w hw⟩
  calc 2 ^ (n - 1) = Odds.card := (card_wordPar hn true).symm
    _ = (Odds.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (G.filter (fun item => 2 * n ≤ (item.filter (fun lit => lit.2 = true)).card)).card :=
        Finset.card_le_card hsub_G

private theorem ppz_kraft {n : ℕ} (B : Finset (Fin n → Bool)) (π : Equiv.Perm (Fin n)) :
    ∑ w ∈ B, 2 ^ ((Finset.univ : Finset (Fin n)).filter
      (fun i => ∀ w' ∈ B, (∀ j, π j < π i → w' j = w j) → w' i = w i)).card ≤ 2 ^ n := by
  classical
  let forced : (Fin n → Bool) → Finset (Fin n) := fun w =>
    (Finset.univ : Finset (Fin n)).filter
      (fun i => ∀ w' ∈ B, (∀ j, π j < π i → w' j = w j) → w' i = w i)
  have hind : ∀ (r m : ℕ) (hrm : m + r = n) (u : Fin n → Bool),
      ∑ w ∈ B.filter (fun w => ∀ j, (π j).val < m → w j = u j),
        2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤ 2 ^ r := by
    intro r
    induction r with
    | zero =>
      intro m hrm u
      have hm : m = n := by omega
      have hcard_le1 : (B.filter (fun w => ∀ j, (π j).val < m → w j = u j)).card ≤ 1 := by
        have hsub : B.filter (fun w => ∀ j, (π j).val < m → w j = u j) ⊆ {u} := by
          intro w hw
          rw [Finset.mem_singleton]
          funext j
          exact (Finset.mem_filter.mp hw).2 j (by have := (π j).isLt; omega)
        exact (Finset.card_le_card hsub).trans (by simp)
      have hterm : ∀ w ∈ B.filter (fun w => ∀ j, (π j).val < m → w j = u j),
          2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card = 1 := by
        intro w _
        have hemp : (forced w).filter (fun i => m ≤ (π i).val) = ∅ := by
          ext i; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _; have := (π i).isLt; omega
        rw [hemp, Finset.card_empty, Nat.pow_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_one, Nat.pow_zero]
      exact hcard_le1
    | succ r ih =>
      intro m hrm u
      let im : Fin n := π.symm ⟨m, by omega⟩
      have hπ_im : (π im).val = m := by simp [im]
      let Bm := B.filter (fun w => ∀ j, (π j).val < m → w j = u j)
      let u0 := Function.update u im false
      let u1 := Function.update u im true
      let B0 := B.filter (fun w => ∀ j, (π j).val < m + 1 → w j = u0 j)
      let B1 := B.filter (fun w => ∀ j, (π j).val < m + 1 → w j = u1 j)
      have hsplit : Bm = B0 ∪ B1 ∧ Disjoint B0 B1 := by
        constructor
        · ext w
          simp only [Bm, B0, B1, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro ⟨hwB, hpre⟩
            cases hwim : w im
            · left
              refine ⟨hwB, fun j hj => ?_⟩
              by_cases hji : j = im
              · subst hji; simp [u0, hwim]
              · have hne : (π j).val ≠ m := fun h => hji (π.injective (by ext; rw [h, hπ_im]))
                simp [u0, hji, hpre j (by omega)]
            · right
              refine ⟨hwB, fun j hj => ?_⟩
              by_cases hji : j = im
              · subst hji; simp [u1, hwim]
              · have hne : (π j).val ≠ m := fun h => hji (π.injective (by ext; rw [h, hπ_im]))
                simp [u1, hji, hpre j (by omega)]
          · rintro (⟨hwB, hpre⟩ | ⟨hwB, hpre⟩)
            · refine ⟨hwB, fun j hj => ?_⟩
              have hne : j ≠ im := fun h => by subst h; omega
              simpa [u0, hne] using hpre j (by omega)
            · refine ⟨hwB, fun j hj => ?_⟩
              have hne : j ≠ im := fun h => by subst h; omega
              simpa [u1, hne] using hpre j (by omega)
        · rw [Finset.disjoint_left]
          intro w h0 h1
          have a0 := (Finset.mem_filter.mp h0).2 im (by omega)
          have a1 := (Finset.mem_filter.mp h1).2 im (by omega)
          simp only [u0, u1, Function.update_self] at a0 a1
          rw [a0] at a1; exact Bool.noConfusion a1
      have hcard_step : ∀ w : Fin n → Bool,
          ((forced w).filter (fun i => m ≤ (π i).val)).card =
          ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card + (if im ∈ forced w then 1 else 0) := by
        intro w
        by_cases him : im ∈ forced w
        · simp only [him, ↓reduceIte]
          have hset : (forced w).filter (fun i => m ≤ (π i).val) =
              insert im ((forced w).filter (fun i => m + 1 ≤ (π i).val)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hi, hge⟩
              by_cases heq : (π i).val = m
              · left; exact π.injective (by ext; rw [heq, hπ_im])
              · right; exact ⟨hi, by omega⟩
            · rintro (rfl | ⟨hi, hge⟩)
              · exact ⟨him, by omega⟩
              · exact ⟨hi, by omega⟩
          have hnm : im ∉ (forced w).filter (fun i => m + 1 ≤ (π i).val) := by
            simp only [Finset.mem_filter, not_and]; intro _; omega
          rw [hset, Finset.card_insert_of_notMem hnm]
        · simp only [him, ↓reduceIte, add_zero]
          congr 1; ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hge⟩
            refine ⟨hi, ?_⟩
            have hne : (π i).val ≠ m := fun heq => him ((π.injective (by ext; exact heq.trans hπ_im.symm)) ▸ hi)
            omega
          · rintro ⟨hi, hge⟩; exact ⟨hi, by omega⟩
      by_cases hne0 : B0.Nonempty
      · by_cases hne1 : B1.Nonempty
        · have hnotf : ∀ w ∈ Bm, im ∉ forced w := by
            intro w hw him
            have hfw := (Finset.mem_filter.mp him).2
            rcases hne0 with ⟨w0, hw0⟩
            rcases hne1 with ⟨w1, hw1⟩
            have hpre0 : ∀ j, π j < π im → w0 j = w j := by
              intro j hj
              have hjlt : (π j).val < m := by
                change (π j).val < (π im).val at hj; omega
              have hne : j ≠ im := fun h => by subst h; omega
              have a0 := (Finset.mem_filter.mp hw0).2 j (by omega)
              simp only [u0, Function.update_of_ne hne] at a0
              exact a0.trans ((Finset.mem_filter.mp hw).2 j hjlt).symm
            have hpre1 : ∀ j, π j < π im → w1 j = w j := by
              intro j hj
              have hjlt : (π j).val < m := by
                change (π j).val < (π im).val at hj; omega
              have hne : j ≠ im := fun h => by subst h; omega
              have a1 := (Finset.mem_filter.mp hw1).2 j (by omega)
              simp only [u1, Function.update_of_ne hne] at a1
              exact a1.trans ((Finset.mem_filter.mp hw).2 j hjlt).symm
            have e0 := hfw w0 (Finset.mem_filter.mp hw0).1 hpre0
            have e1 := hfw w1 (Finset.mem_filter.mp hw1).1 hpre1
            have v0 : w0 im = false := by simpa [u0] using (Finset.mem_filter.mp hw0).2 im (by omega)
            have v1 : w1 im = true := by simpa [u1] using (Finset.mem_filter.mp hw1).2 im (by omega)
            rw [v0] at e0; rw [v1] at e1; rw [← e0] at e1; exact Bool.noConfusion e1
          have hsum_eq :
              ∑ w ∈ Bm, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card =
              ∑ w ∈ Bm, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [hcard_step w]
            simp only [hnotf w hw, ↓reduceIte, add_zero]
          change ∑ w ∈ Bm, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤ 2 ^ (r + 1)
          rw [hsum_eq, hsplit.1, Finset.sum_union hsplit.2]
          have ih0 : ∑ w ∈ B0, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card ≤ 2 ^ r :=
            ih (m + 1) (by omega) u0
          have ih1 : ∑ w ∈ B1, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card ≤ 2 ^ r :=
            ih (m + 1) (by omega) u1
          rw [Nat.pow_succ]; omega
        · have hB1 : B1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne1
          change ∑ w ∈ Bm, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤ 2 ^ (r + 1)
          rw [hsplit.1, hB1, Finset.union_empty]
          have hle2 :
              ∑ w ∈ B0, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤
              2 * ∑ w ∈ B0, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro w _
            rw [hcard_step w]
            split_ifs
            · rw [Nat.pow_succ]; ring_nf; exact le_rfl
            · rw [add_zero]; omega
          have ih0 : ∑ w ∈ B0, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card ≤ 2 ^ r :=
            ih (m + 1) (by omega) u0
          rw [Nat.pow_succ]; omega
      · have hB0 : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne0
        change ∑ w ∈ Bm, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤ 2 ^ (r + 1)
        rw [hsplit.1, hB0, Finset.empty_union]
        have hle2 :
            ∑ w ∈ B1, 2 ^ ((forced w).filter (fun i => m ≤ (π i).val)).card ≤
            2 * ∑ w ∈ B1, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro w _
          rw [hcard_step w]
          split_ifs
          · rw [Nat.pow_succ]; ring_nf; exact le_rfl
          · rw [add_zero]; omega
        have ih1 : ∑ w ∈ B1, 2 ^ ((forced w).filter (fun i => m + 1 ≤ (π i).val)).card ≤ 2 ^ r :=
          ih (m + 1) (by omega) u1
        rw [Nat.pow_succ]; omega
  have h0 := hind n 0 (by omega) (fun _ => false)
  have hflt : B.filter (fun w => ∀ j, (π j).val < 0 → w j = false) = B := by
    ext w; simp
  rw [hflt] at h0
  have hterm : ∀ w ∈ B,
      ((forced w).filter (fun i => 0 ≤ (π i).val)).card = (forced w).card := by
    intro w _; congr 1; ext i; simp
  simpa [Finset.sum_congr rfl hterm] using h0

private theorem card_perm_last {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    (S.card + 1) *
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j ∈ S, π j < π i)).card =
    Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let T := insert i S
  have hT_card : T.card = S.card + 1 := Finset.card_insert_of_notMem hi
  let isMax : Fin n → Finset (Equiv.Perm (Fin n)) := fun a =>
    (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j ∈ T, j ≠ a → π j < π a)
  have hsame : ∀ a ∈ T, (isMax a).card = (isMax i).card := by
    intro a ha
    let sw := Equiv.swap i a
    refine Finset.card_bij (fun π _ => π * sw) ?_ ?_ ?_
    · intro π hπ
      have hmax := (Finset.mem_filter.mp hπ).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hjT hji => ?_⟩
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw, Equiv.swap_apply_left]
      have hsw_mem : sw j ∈ T := by
        by_cases hja : j = a
        · subst hja; simp [sw, T]
        · simp [sw, Equiv.swap_apply_of_ne_of_ne hji hja, hjT]
      have hsw_ne : sw j ≠ a := by
        intro heq
        have : j = i := by
          have := congrArg sw heq
          simpa [sw] using this
        exact hji this
      exact hmax (sw j) hsw_mem hsw_ne
    · intro π1 _ π2 _ h
      exact mul_right_cancel h
    · intro π hπ
      have hmax := (Finset.mem_filter.mp hπ).2
      refine ⟨π * sw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hjT hja => ?_⟩, ?_⟩
      · simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw, Equiv.swap_apply_right]
        have hsw_mem : sw j ∈ T := by
          by_cases hji : j = i
          · subst hji; simp [sw, ha]
          · simp [sw, Equiv.swap_apply_of_ne_of_ne hji hja, hjT]
        have hsw_ne : sw j ≠ i := by
          intro heq
          have : j = a := by
            have := congrArg sw heq
            simpa [sw] using this
          exact hja this
        exact hmax (sw j) hsw_mem hsw_ne
      · simp [mul_assoc, sw]
  have hpart : T.biUnion isMax = Finset.univ := by
    ext π
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    have hne : (T.image π).Nonempty := ⟨π i, Finset.mem_image_of_mem _ (Finset.mem_insert_self i S)⟩
    let mx := (T.image π).max' hne
    rcases Finset.mem_image.mp (Finset.max'_mem (T.image π) hne) with ⟨a, haT, ha_eq⟩
    refine ⟨a, haT, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hjT hja => ?_⟩⟩
    have hle : π j ≤ π a := ha_eq ▸ Finset.le_max' (T.image π) (π j) (Finset.mem_image_of_mem _ hjT)
    exact lt_of_le_of_ne hle (fun heq => hja (π.injective heq))
  have hdisj : Set.PairwiseDisjoint (T : Set (Fin n)) isMax := by
    intro a _ b _ hab
    change Disjoint (isMax a) (isMax b)
    rw [Finset.disjoint_left]
    intro π ha hb
    have h1 := (Finset.mem_filter.mp ha).2 b ‹b ∈ T› hab.symm
    have h2 := (Finset.mem_filter.mp hb).2 a ‹a ∈ T› hab
    exact lt_asymm h1 h2
  have htot : Fintype.card (Equiv.Perm (Fin n)) = T.card * (isMax i).card := by
    rw [← Finset.card_univ, ← hpart, Finset.card_biUnion hdisj,
      Finset.sum_congr rfl hsame, Finset.sum_const, smul_eq_mul]
  have hisMax_eq : isMax i =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j ∈ S, π j < π i) := by
    ext π
    simp only [isMax, T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h j hjS; exact h j (Or.inr hjS) (fun heq => hi (heq ▸ hjS))
    · rintro h j (rfl | hjS) hne
      · exact absurd rfl hne
      · exact h j hjS
  rw [htot, hT_card, hisMax_eq]

private theorem bernoulli_rat (k : ℕ) (t : ℚ) (ht : -1 ≤ t) :
    1 + (k : ℚ) * t ≤ (1 + t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h0 : 0 ≤ 1 + t := by linarith
    have h1 : (1 + (k : ℚ) * t) * (1 + t) ≤ (1 + t) ^ k * (1 + t) :=
      mul_le_mul_of_nonneg_right ih h0
    have h2 : 0 ≤ (k : ℚ) * (t * t) := mul_nonneg (Nat.cast_nonneg k) (mul_self_nonneg t)
    push_cast
    rw [pow_succ]
    linarith

private theorem am_gm_nat {α : Type} [DecidableEq α] (s : Finset α) (g : α → ℕ) :
    (∏ x ∈ s, g x) * s.card ^ s.card ≤ (∑ x ∈ s, g x) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    set m := s.card
    set P := ∏ x ∈ s, g x
    set S := ∑ x ∈ s, g x
    by_cases hm0 : m = 0
    · have hs : s = ∅ := Finset.card_eq_zero.mp hm0
      subst hs; simp [P, S, m]
    · by_cases hS0 : S = 0
      · have hP0 : P = 0 := by
          rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hm0) with ⟨x0, hx0⟩
          have gx0 : g x0 = 0 := Finset.sum_eq_zero_iff.mp hS0 x0 hx0
          exact Finset.prod_eq_zero hx0 gx0
        rw [hP0]; simp
      · have hstep : (m + 1) ^ (m + 1) * S ^ m * g a ≤ m ^ m * (g a + S) ^ (m + 1) := by
          have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
          have hSQ : (0 : ℚ) < (S : ℚ) := by exact_mod_cast (Nat.pos_of_ne_zero hS0)
          have haQ : (0 : ℚ) ≤ (g a : ℚ) := Nat.cast_nonneg _
          have hm1Q : (0 : ℚ) < ((m : ℚ) + 1) := by linarith
          let d : ℚ := ((m : ℚ) * (g a : ℚ) - (S : ℚ)) / (((m : ℚ) + 1) * (S : ℚ))
          have h1d : 1 + d = (m : ℚ) * ((g a : ℚ) + (S : ℚ)) / (((m : ℚ) + 1) * (S : ℚ)) := by
            dsimp only [d]; field_simp; ring
          have hd_ge : -1 ≤ d := by
            have hnn : 0 ≤ 1 + d := by rw [h1d]; positivity
            linarith
          have hb := bernoulli_rat (m + 1) d hd_ge
          have hlhs : 1 + ((m + 1 : ℕ) : ℚ) * d = (m : ℚ) * (g a : ℚ) / (S : ℚ) := by
            dsimp only [d]; push_cast; field_simp; ring
          rw [hlhs, h1d, div_pow] at hb
          have hden : (0 : ℚ) < (((m : ℚ) + 1) * (S : ℚ)) ^ (m + 1) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt hden)
          rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
          have hL : (m : ℚ) * (g a : ℚ) / (S : ℚ) * (((m : ℚ) + 1) * (S : ℚ)) ^ (m + 1) =
              (m : ℚ) * (((m : ℚ) + 1) ^ (m + 1) * (S : ℚ) ^ m * (g a : ℚ)) := by
            rw [mul_pow, pow_succ (S : ℚ) m]; field_simp
          have hR : ((m : ℚ) * ((g a : ℚ) + (S : ℚ))) ^ (m + 1) =
              (m : ℚ) * ((m : ℚ) ^ m * ((g a : ℚ) + (S : ℚ)) ^ (m + 1)) := by
            rw [mul_pow, pow_succ (m : ℚ) m]; ring
          rw [hL, hR] at hmul
          have hfinQ : ((m : ℚ) + 1) ^ (m + 1) * (S : ℚ) ^ m * (g a : ℚ) ≤
              (m : ℚ) ^ m * ((g a : ℚ) + (S : ℚ)) ^ (m + 1) :=
            le_of_mul_le_mul_left hmul hmQ
          exact_mod_cast hfinQ
        have hmul_ih : g a * P * (m + 1) ^ (m + 1) * m ^ m ≤
            (g a + S) ^ (m + 1) * m ^ m := by
          calc g a * P * (m + 1) ^ (m + 1) * m ^ m
              = (P * m ^ m) * ((m + 1) ^ (m + 1) * g a) := by ring
            _ ≤ S ^ m * ((m + 1) ^ (m + 1) * g a) := Nat.mul_le_mul_right _ ih
            _ = (m + 1) ^ (m + 1) * S ^ m * g a := by ring
            _ ≤ m ^ m * (g a + S) ^ (m + 1) := hstep
            _ = (g a + S) ^ (m + 1) * m ^ m := by ring
        have hmp : 0 < m ^ m := Nat.pos_of_ne_zero (pow_ne_zero m hm0)
        exact Nat.le_of_mul_le_mul_right hmul_ih hmp

private theorem ppz_coding_bound {n k : ℕ} (hk : 0 < k) (B : Finset (Fin n → Bool))
    (hiso : ∀ w ∈ B, ∀ i : Fin n, ∃ S : Finset (Fin n), i ∉ S ∧ S.card + 1 ≤ k ∧
      ∀ w' ∈ B, (∀ j ∈ S, w' j = w j) → w' i = w i) :
    B.card ^ k * 2 ^ n ≤ (2 ^ n) ^ k := by
  classical
  by_cases hBe : B = ∅
  · subst hBe
    have : 0 ^ k = 0 := Nat.zero_pow hk
    simp [this]
  have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBe
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  let P := (Finset.univ : Finset (Equiv.Perm (Fin n)))
  have hPpos : 0 < P.card := by simp [P, Fintype.card_pos]
  let forced : Equiv.Perm (Fin n) → (Fin n → Bool) → Finset (Fin n) := fun π w =>
    (Finset.univ : Finset (Fin n)).filter
      (fun i => ∀ w' ∈ B, (∀ j, π j < π i → w' j = w j) → w' i = w i)
  have havg_nat : P.card * B.card * n ≤ k * ∑ π ∈ P, ∑ w ∈ B, (forced π w).card := by
    have hswap : ∑ π ∈ P, ∑ w ∈ B, (forced π w).card =
        ∑ w ∈ B, ∑ i : Fin n, (P.filter (fun π => i ∈ forced π w)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      calc ∑ π ∈ P, (forced π w).card
          = ∑ π ∈ P, ∑ i : Fin n, if i ∈ forced π w then 1 else 0 := by
            apply Finset.sum_congr rfl; intro π _
            have h1 : (forced π w).card = (Finset.univ.filter (fun i => i ∈ forced π w)).card := by
              congr 1; ext i; simp
            rw [h1, Finset.card_filter]
        _ = ∑ i : Fin n, ∑ π ∈ P, if i ∈ forced π w then 1 else 0 := Finset.sum_comm
        _ = ∑ i : Fin n, (P.filter (fun π => i ∈ forced π w)).card := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.card_filter]
    rw [hswap, Finset.mul_sum]
    have hterm : ∀ w ∈ B, n * P.card ≤ k * ∑ i : Fin n, (P.filter (fun π => i ∈ forced π w)).card := by
      intro w hw
      rw [Finset.mul_sum]
      calc n * P.card = ∑ _ : Fin n, P.card := by simp
        _ ≤ ∑ i : Fin n, k * (P.filter (fun π => i ∈ forced π w)).card := by
            apply Finset.sum_le_sum
            intro i _
            rcases hiso w hw i with ⟨S, hiS, hSk, hSdet⟩
            have hsub : P.filter (fun π => ∀ j ∈ S, π j < π i) ⊆ P.filter (fun π => i ∈ forced π w) := by
              intro π hπ
              have hlt := (Finset.mem_filter.mp hπ).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
              intro w' hw' hpre
              exact hSdet w' hw' (fun j hjS => hpre j (hlt j hjS))
            have hcp := card_perm_last S i hiS
            have hle1 := Finset.card_le_card hsub
            have hPeq : P.card = Fintype.card (Equiv.Perm (Fin n)) := Finset.card_univ
            rw [hPeq, ← hcp]
            exact Nat.mul_le_mul hSk hle1
    calc P.card * B.card * n = ∑ _ ∈ B, n * P.card := by simp; ring
      _ ≤ ∑ w ∈ B, k * ∑ i : Fin n, (P.filter (fun π => i ∈ forced π w)).card :=
          Finset.sum_le_sum hterm
  have hkraft_nat : ∑ π ∈ P, ∑ w ∈ B, 2 ^ (forced π w).card ≤ P.card * 2 ^ n := by
    calc ∑ π ∈ P, ∑ w ∈ B, 2 ^ (forced π w).card
        ≤ ∑ _ ∈ P, 2 ^ n := Finset.sum_le_sum (fun π _ => ppz_kraft B π)
      _ = P.card * 2 ^ n := by simp
  let PB := P ×ˢ B
  have hPB_card : PB.card = P.card * B.card := Finset.card_product P B
  have hPB_pos : 0 < PB.card := by rw [hPB_card]; positivity
  have ham := am_gm_nat PB (fun x => 2 ^ (forced x.1 x.2).card)
  rw [Finset.prod_pow_eq_pow_sum] at ham
  have hsum_pb : ∑ x ∈ PB, (forced x.1 x.2).card = ∑ π ∈ P, ∑ w ∈ B, (forced π w).card := by
    simp only [PB, Finset.sum_product]
  have hsum_pow_pb : ∑ x ∈ PB, 2 ^ (forced x.1 x.2).card = ∑ π ∈ P, ∑ w ∈ B, 2 ^ (forced π w).card := by
    simp only [PB, Finset.sum_product]
  rw [hsum_pb, hsum_pow_pb] at ham
  have ham_k := Nat.pow_le_pow_left ham k
  have hpow_le : (P.card ^ k * (B.card ^ k * 2 ^ n)) ^ PB.card ≤
      (P.card ^ k * (2 ^ n) ^ k) ^ PB.card := by
    calc (P.card ^ k * (B.card ^ k * 2 ^ n)) ^ PB.card
        = 2 ^ (PB.card * n) * (PB.card ^ PB.card) ^ k := by
          rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul,
            ← Nat.pow_mul, hPB_card, Nat.mul_pow]
          have e1 : k * (P.card * B.card) = P.card * B.card * k := by ring
          have e2 : n * (P.card * B.card) = P.card * B.card * n := by ring
          rw [e1, e2]; ring
      _ ≤ 2 ^ (k * ∑ π ∈ P, ∑ w ∈ B, (forced π w).card) * (PB.card ^ PB.card) ^ k := by
          refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) ?_)
          rw [hPB_card]; exact havg_nat
      _ = (2 ^ (∑ π ∈ P, ∑ w ∈ B, (forced π w).card) * PB.card ^ PB.card) ^ k := by
          rw [Nat.mul_pow, ← Nat.pow_mul 2, mul_comm k]
      _ ≤ ((∑ π ∈ P, ∑ w ∈ B, 2 ^ (forced π w).card) ^ PB.card) ^ k := ham_k
      _ ≤ ((P.card * 2 ^ n) ^ PB.card) ^ k :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left hkraft_nat PB.card) k
      _ = (P.card ^ k * (2 ^ n) ^ k) ^ PB.card := by
          rw [← Nat.pow_mul, mul_comm PB.card k, Nat.pow_mul, Nat.mul_pow]
  have hcancel_PB : P.card ^ k * (B.card ^ k * 2 ^ n) ≤ P.card ^ k * (2 ^ n) ^ k := by
    by_contra hgt
    have hlt := Nat.pow_lt_pow_left (by omega : P.card ^ k * (2 ^ n) ^ k < P.card ^ k * (B.card ^ k * 2 ^ n))
      (ne_of_gt hPB_pos)
    omega
  exact Nat.le_of_mul_le_mul_left hcancel_PB (by positivity)

private theorem falsified_raw_card_le {n a : ℕ} (C : Clause (VarT n a)) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun u => ∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s)).card ≤
    2 ^ (n - (rowsFn a C).card) := by
  classical
  let R := rowsFn a C
  have hfix : ∀ r ∈ R, ∃ b0 : Bool, ∀ u : Fin n → Bool,
      (∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s) → u r = b0 := by
    intro r hr
    rcases (Finset.mem_filter.mp hr).2 with ⟨⟨p1, p2⟩, sign, hlit⟩
    refine ⟨p1 ^^ p2 ^^ sign, fun u hu => ?_⟩
    have hne := hu (r, (p1, p2)) sign hlit
    simp only [tabOf] at hne
    cases h1 : u r <;> cases p1 <;> cases p2 <;> cases sign <;> simp [h1] at hne ⊢
  let bFix : Fin n → Bool := fun r => if hr : r ∈ R then Classical.choose (hfix r hr) else false
  have hbFix : ∀ r ∈ R, ∀ u : Fin n → Bool,
      (∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s) → u r = bFix r := by
    intro r hr u hu
    dsimp only [bFix]; simp only [hr, ↓reduceDIte]
    exact Classical.choose_spec (hfix r hr) u hu
  let Rc := Finset.univ \ R
  let S := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun u => ∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s)
  have hinj : Set.InjOn (fun (u : Fin n → Bool) (r : {x // x ∈ Rc}) => u r.1) (S : Set (Fin n → Bool)) := by
    intro u1 hu1 u2 hu2 heq
    funext r
    by_cases hr : r ∈ R
    · rw [hbFix r hr u1 (Finset.mem_filter.mp hu1).2, hbFix r hr u2 (Finset.mem_filter.mp hu2).2]
    · have hrc : r ∈ Rc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hr⟩
      exact congrFun heq ⟨r, hrc⟩
  calc S.card = (S.image (fun (u : Fin n → Bool) (r : {x // x ∈ Rc}) => u r.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset ({x // x ∈ Rc} → Bool)).card := Finset.card_le_univ _
    _ = 2 ^ Rc.card := by simp
    _ = 2 ^ (n - R.card) := by
        have hRc : Rc.card = n - R.card := by
          dsimp only [Rc]
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin]
        rw [hRc]

private theorem j_mul_pow_mono {n k j : ℕ} (hk : 0 < k) (hkj : k + 1 ≤ j) (hjn : j ≤ n) :
    j * 2 ^ (n - j) ≤ (k + 1) * 2 ^ (n - (k + 1)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases heq : j + 1 = k + 1
    · rw [heq]
    · have hih := ih (by omega) (by omega)
      have hstep : (j + 1) * 2 ^ (n - (j + 1)) ≤ j * 2 ^ (n - j) := by
        have hexp : n - j = (n - (j + 1)) + 1 := by omega
        rw [hexp, Nat.pow_succ]
        have hj1 : 1 ≤ j := by omega
        have hpos : 0 < 2 ^ (n - (j + 1)) := by positivity
        nlinarith
      exact hstep.trans hih

private theorem solve_236_lower {n : ℕ} (hn : 0 < n) (a : ℕ) (G : Finset (Clause (VarT n a)))
    (henc : encPred hn a G) :
    (∃ C ∈ G, n ≤ (a + 1) * (rowsFn a C).card) ∧
    ∀ k : ℕ, 0 < k → k * (a + 2) ≤ n →
      2 ^ k ≤ 2 * (k + 1) * (G.filter (fun clause => k < (rowsFn a clause).card)).card := by
  classical
  let Evens := (Finset.univ : Finset (Fin n → Bool)).filter (fun w => wordPar w = false)
  have hEvens_card : Evens.card = 2 ^ (n - 1) := card_wordPar hn false
  have hwit : ∀ w ∈ Evens, ∃ y : Fin a → Bool, Satisfies (Sum.elim (tabOf w) y) (↑G : Set _) := by
    intro w hw
    exact (henc (tabOf w)).mp ((feasible_tabOf_iff hn w).mpr (Finset.mem_filter.mp hw).2)
  let wit : (Fin n → Bool) → (Fin a → Bool) := fun w =>
    if hw : w ∈ Evens then Classical.choose (hwit w hw) else fun _ => false
  have hwit_ok : ∀ w ∈ Evens, Satisfies (Sum.elim (tabOf w) (wit w)) (↑G : Set _) := by
    intro w hw; dsimp only [wit]; simp only [hw, ↓reduceDIte]; exact Classical.choose_spec (hwit w hw)
  have hcrit_ex : ∀ w ∈ Evens, ∀ i : Fin n,
      ∃ C ∈ G, ¬ ClauseSat (Sum.elim (tabOf (Function.update w i (!(w i)))) (wit w)) C ∧
        i ∈ rowsFn a C := by
    intro w hw i
    let w' := Function.update w i (!(w i))
    have hnf : ¬ feasiblePred hn (tabOf w') := by
      rw [feasible_tabOf_iff hn w', wordPar_flip, (Finset.mem_filter.mp hw).2]; decide
    have hunsat : ¬ Satisfies (Sum.elim (tabOf w') (wit w)) (↑G : Set _) :=
      fun h => hnf ((henc (tabOf w')).mpr ⟨wit w, h⟩)
    unfold Satisfies at hunsat
    push Not at hunsat
    rcases hunsat with ⟨C, hCG, hCfal⟩
    refine ⟨C, hCG, hCfal, ?_⟩
    have hCsat := hwit_ok w hw C hCG
    rcases hCsat with ⟨lit, hlit, hsat_lit⟩
    cases lit with | mk v s =>
    cases v with
    | inr z =>
      exfalso; apply hCfal; exact ⟨(Sum.inr z, s), hlit, hsat_lit⟩
    | inl e =>
      by_cases hei : e.1 = i
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, s, hei ▸ hlit⟩
      · exfalso; apply hCfal
        refine ⟨(Sum.inl e, s), hlit, ?_⟩
        simp only [Sum.elim_inl, tabOf, w', Function.update_of_ne hei] at hsat_lit ⊢
        exact hsat_lit
  have hcrit_det : ∀ (y : Fin a → Bool) (w w' : Fin n → Bool) (i : Fin n) (C : Clause (VarT n a)),
      ¬ ClauseSat (Sum.elim (tabOf (Function.update w i (!(w i)))) y) C →
      ClauseSat (Sum.elim (tabOf w') y) C →
      (∀ j ∈ (rowsFn a C).erase i, w' j = w j) →
      w' i = w i := by
    intro y w w' i C hfal hsat hagree
    by_contra hne
    have hwi' : w' i = !(w i) := by cases h1 : w' i <;> cases h2 : w i <;> simp [h1, h2] at hne ⊢
    apply hfal
    rcases hsat with ⟨lit, hlit, hsat_lit⟩
    refine ⟨lit, hlit, ?_⟩
    cases lit with | mk v s =>
    cases v with
    | inr z => exact hsat_lit
    | inl e =>
      simp only [Sum.elim_inl, tabOf] at hsat_lit ⊢
      have he_row : e.1 ∈ rowsFn a C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, s, hlit⟩
      by_cases hei : e.1 = i
      · rw [hei, hwi'] at hsat_lit
        simpa [hei] using hsat_lit
      · have hag := hagree e.1 (Finset.mem_erase.mpr ⟨hei, he_row⟩)
        rw [hag] at hsat_lit
        simpa [hei] using hsat_lit
  constructor
  · by_contra hno
    push Not at hno
    let k := G.sup (fun C => (rowsFn a C).card)
    have hk_bound : (a + 1) * k < n := by
      by_cases hGe : G = ∅
      · subst hGe
        have : k = 0 := by simp [k]
        rw [this]; omega
      · rcases Finset.exists_mem_eq_sup G (Finset.nonempty_iff_ne_empty.mpr hGe)
            (fun C => (rowsFn a C).card) with ⟨Cm, hCm, hkeq⟩
        have hlt := hno Cm hCm
        dsimp only [k]
        rw [hkeq]; exact hlt
    have hk_pos : 0 < k := by
      have hEne : Evens.Nonempty := Finset.card_pos.mp (by rw [hEvens_card]; positivity)
      rcases hEne with ⟨w0, hw0⟩
      rcases hcrit_ex w0 hw0 ⟨0, hn⟩ with ⟨C0, hC0G, _, h0row⟩
      have hpos : 0 < (rowsFn a C0).card := Finset.card_pos.mpr ⟨⟨0, hn⟩, h0row⟩
      have hle : (rowsFn a C0).card ≤ k := Finset.le_sup (f := fun C => (rowsFn a C).card) hC0G
      omega
    have hsum_Ey : ∑ y : Fin a → Bool, (Evens.filter (fun w => wit w = y)).card = 2 ^ (n - 1) := by
      rw [← hEvens_card, ← Finset.card_biUnion]
      · congr 1; ext w; simp
      · intro y1 _ y2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]; intro w h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hex_y : ∃ y : Fin a → Bool, 2 ^ (n - 1) ≤ 2 ^ a * (Evens.filter (fun w => wit w = y)).card := by
      by_contra hall
      push Not at hall
      have hlt : ∑ y : Fin a → Bool, 2 ^ a * (Evens.filter (fun w => wit w = y)).card <
          ∑ _ : Fin a → Bool, 2 ^ (n - 1) :=
        Finset.sum_lt_sum_of_nonempty ⟨fun _ => false, Finset.mem_univ _⟩ (fun y _ => hall y)
      rw [← Finset.mul_sum, hsum_Ey, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    rcases hex_y with ⟨y0, hy0⟩
    let Ey := Evens.filter (fun w => wit w = y0)
    have hppz := ppz_coding_bound hk_pos Ey (fun w hw i => by
      rcases Finset.mem_filter.mp hw with ⟨hwE, hwy⟩
      rcases hcrit_ex w hwE i with ⟨C, hCG, hCfal, hirow⟩
      rw [hwy] at hCfal
      refine ⟨(rowsFn a C).erase i, Finset.notMem_erase i _, ?_, ?_⟩
      · have h1 : ((rowsFn a C).erase i).card + 1 = (rowsFn a C).card :=
          Finset.card_erase_add_one hirow
        have h2 : (rowsFn a C).card ≤ k := Finset.le_sup (f := fun C => (rowsFn a C).card) hCG
        omega
      · intro w' hw' hagree
        rcases Finset.mem_filter.mp hw' with ⟨hw'E, hw'y⟩
        have hsat' := hwit_ok w' hw'E C hCG
        rw [hw'y] at hsat'
        exact hcrit_det y0 w w' i C hCfal hsat' hagree)
    have hpow_le : (2 ^ (n - 1)) ^ k * 2 ^ n ≤ (2 ^ a * Ey.card) ^ k * 2 ^ n :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hy0 k)
    have hcomb : 2 ^ ((n - 1) * k + n) ≤ 2 ^ (a * k + n * k) := by
      calc 2 ^ ((n - 1) * k + n) = (2 ^ (n - 1)) ^ k * 2 ^ n := by rw [Nat.pow_add, Nat.pow_mul]
        _ ≤ (2 ^ a * Ey.card) ^ k * 2 ^ n := hpow_le
        _ = 2 ^ (a * k) * (Ey.card ^ k * 2 ^ n) := by rw [Nat.mul_pow, Nat.pow_mul]; ring
        _ ≤ 2 ^ (a * k) * (2 ^ n) ^ k := Nat.mul_le_mul_left _ hppz
        _ = 2 ^ (a * k + n * k) := by rw [Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcomb
    have hsub_mul : (n - 1) * k + n = n * k + n - k := by
      have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
      rw [Nat.sub_mul, one_mul]; omega
    have ha1 : (a + 1) * k = a * k + k := by ring
    omega
  · intro k hk hka
    have hn2 : 2 ≤ n := by nlinarith
    let Glong := G.filter (fun C => k < (rowsFn a C).card)
    let By : (Fin a → Bool) → Finset (Fin n → Bool) := fun y =>
      (Evens.filter (fun w => wit w = y)).filter (fun w =>
        ∀ i : Fin n, ∃ C ∈ G, (rowsFn a C).card ≤ k ∧
          ¬ ClauseSat (Sum.elim (tabOf (Function.update w i (!(w i)))) y) C ∧ i ∈ rowsFn a C)
    have hBy_le : ∀ y : Fin a → Bool, (By y).card * 2 ^ (a + 2) ≤ 2 ^ n := by
      intro y
      have hppz := ppz_coding_bound hk (By y) (fun w hw i => by
        rcases Finset.mem_filter.mp hw with ⟨hw1, hshort⟩
        rcases hshort i with ⟨C, hCG, hCk, hCfal, hirow⟩
        refine ⟨(rowsFn a C).erase i, Finset.notMem_erase i _, ?_, ?_⟩
        · have h1 := Finset.card_erase_add_one hirow; omega
        · intro w' hw' hagree
          rcases Finset.mem_filter.mp (Finset.mem_filter.mp hw').1 with ⟨hw'E, hw'y⟩
          have hsat' := hwit_ok w' hw'E C hCG
          rw [hw'y] at hsat'
          exact hcrit_det y w w' i C hCfal hsat' hagree)
      have hpow : ((By y).card * 2 ^ (a + 2)) ^ k ≤ (2 ^ n) ^ k := by
        calc ((By y).card * 2 ^ (a + 2)) ^ k
            = (By y).card ^ k * 2 ^ ((a + 2) * k) := by rw [Nat.mul_pow, Nat.pow_mul]
          _ ≤ (By y).card ^ k * 2 ^ n :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by nlinarith))
          _ ≤ (2 ^ n) ^ k := hppz
      by_contra hgt
      have hlt : (2 ^ n) ^ k < ((By y).card * 2 ^ (a + 2)) ^ k :=
        Nat.pow_lt_pow_left (by omega) (by omega)
      omega
    let ShortAll := (Finset.univ : Finset (Fin a → Bool)).biUnion By
    have hShort_le : ShortAll.card ≤ 2 ^ (n - 2) := by
      have hsum_le : ShortAll.card * 2 ^ (a + 2) ≤ 2 ^ a * 2 ^ n := by
        calc ShortAll.card * 2 ^ (a + 2)
            ≤ (∑ y : Fin a → Bool, (By y).card) * 2 ^ (a + 2) :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ y : Fin a → Bool, (By y).card * 2 ^ (a + 2) := Finset.sum_mul _ _ _
          _ ≤ ∑ _ : Fin a → Bool, 2 ^ n := Finset.sum_le_sum (fun y _ => hBy_le y)
          _ = 2 ^ a * 2 ^ n := by simp
      have h1 : 2 ^ a * (ShortAll.card * 4) ≤ 2 ^ a * (2 ^ (n - 2) * 4) := by
        have hn_eq : 2 ^ n = 2 ^ (n - 2) * 4 := by
          have : n = (n - 2) + 2 := by omega
          conv_lhs => rw [this, Nat.pow_add]
        have ha_eq : 2 ^ (a + 2) = 2 ^ a * 4 := by rw [Nat.pow_add]
        rw [ha_eq] at hsum_le
        rw [hn_eq] at hsum_le
        linarith
      have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity : 0 < 2 ^ a)
      omega
    let Bad := Evens \ ShortAll
    have hShort_sub : ShortAll ⊆ Evens := by
      intro w hw
      rcases Finset.mem_biUnion.mp hw with ⟨y, _, hwy⟩
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hwy).1).1
    have hBad_ge : 2 ^ (n - 2) ≤ Bad.card := by
      have hcard_sdiff := Finset.card_sdiff_of_subset hShort_sub
      have h2eq : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        have : n - 1 = (n - 2) + 1 := by omega
        conv_lhs => rw [this, Nat.pow_succ]
        ring
      change 2 ^ (n - 2) ≤ (Evens \ ShortAll).card
      rw [hcard_sdiff, hEvens_card, h2eq]
      omega
    have hbad_pick : ∀ w ∈ Bad, ∃ C ∈ Glong, ∃ i ∈ rowsFn a C,
        ∀ e s, (Sum.inl e, s) ∈ C → tabOf (Function.update w i (!(w i))) e ≠ s := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hwE, hwNS⟩
      have hnot_all : ¬ ∀ i : Fin n, ∃ C ∈ G, (rowsFn a C).card ≤ k ∧
          ¬ ClauseSat (Sum.elim (tabOf (Function.update w i (!(w i)))) (wit w)) C ∧ i ∈ rowsFn a C := by
        intro hall
        apply hwNS
        refine Finset.mem_biUnion.mpr ⟨wit w, Finset.mem_univ _, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hwE, rfl⟩, hall⟩
      push Not at hnot_all
      rcases hnot_all with ⟨i, hi⟩
      rcases hcrit_ex w hwE i with ⟨C, hCG, hCfal, hirow⟩
      have hClong : k < (rowsFn a C).card := by
        by_contra hle
        exact hi C hCG (by omega) hCfal hirow
      refine ⟨C, Finset.mem_filter.mpr ⟨hCG, hClong⟩, i, hirow, ?_⟩
      intro e s hlit heq
      apply hCfal
      exact ⟨(Sum.inl e, s), hlit, heq⟩
    let Targets := Glong.sigma (fun C =>
      (rowsFn a C) ×ˢ ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun u => ∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s)))
    let toT : (Fin n → Bool) → Σ _ : Clause (VarT n a), Fin n × (Fin n → Bool) := fun w =>
      if hw : w ∈ Bad then
        let C := Classical.choose (hbad_pick w hw)
        let hC := Classical.choose_spec (hbad_pick w hw)
        let i := Classical.choose hC.2
        ⟨C, (i, Function.update w i (!(w i)))⟩
      else ⟨∅, (⟨0, hn⟩, w)⟩
    have htoT_mem : ∀ w ∈ Bad, toT w ∈ Targets := by
      intro w hw
      dsimp only [toT]; simp only [hw, ↓reduceDIte]
      have hC := Classical.choose_spec (hbad_pick w hw)
      have hi := Classical.choose_spec hC.2
      exact Finset.mem_sigma.mpr ⟨hC.1, Finset.mem_product.mpr ⟨hi.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2⟩⟩⟩
    have htoT_inj : Set.InjOn toT (Bad : Set (Fin n → Bool)) := by
      intro w1 hw1 w2 hw2 heq
      have hw1' : w1 ∈ Bad := hw1
      have hw2' : w2 ∈ Bad := hw2
      dsimp only [toT] at heq
      simp only [hw1', hw2', ↓reduceDIte] at heq
      have hpair : (Classical.choose (Classical.choose_spec (hbad_pick w1 hw1)).2,
          Function.update w1 (Classical.choose (Classical.choose_spec (hbad_pick w1 hw1)).2)
            (!(w1 (Classical.choose (Classical.choose_spec (hbad_pick w1 hw1)).2)))) =
          (Classical.choose (Classical.choose_spec (hbad_pick w2 hw2)).2,
          Function.update w2 (Classical.choose (Classical.choose_spec (hbad_pick w2 hw2)).2)
            (!(w2 (Classical.choose (Classical.choose_spec (hbad_pick w2 hw2)).2)))) :=
        congrArg Sigma.snd heq
      rcases Prod.mk.inj hpair with ⟨hi_eq, hu_eq⟩
      rw [← hi_eq] at hu_eq
      set i0 := Classical.choose (Classical.choose_spec (hbad_pick w1 hw1)).2
      funext j
      by_cases hj : j = i0
      · subst hj
        have h := congrFun hu_eq i0
        simp only [Function.update_self] at h
        cases h1 : w1 i0 <;> cases h2 : w2 i0 <;> simp [h1, h2] at h ⊢
      · have h := congrFun hu_eq j
        simpa [hj] using h
    have hTargets_le : Targets.card ≤ Glong.card * ((k + 1) * 2 ^ (n - (k + 1))) := by
      dsimp only [Targets]
      rw [Finset.card_sigma]
      calc ∑ C ∈ Glong, ((rowsFn a C) ×ˢ
              (Finset.univ.filter (fun u => ∀ e s, (Sum.inl e, s) ∈ C → tabOf u e ≠ s))).card
          ≤ ∑ _ ∈ Glong, (k + 1) * 2 ^ (n - (k + 1)) := by
            apply Finset.sum_le_sum
            intro C hC
            rw [Finset.card_product]
            have hClong : k + 1 ≤ (rowsFn a C).card := (Finset.mem_filter.mp hC).2
            have hCle : (rowsFn a C).card ≤ n := (Finset.card_le_univ _).trans (by simp)
            exact (Nat.mul_le_mul_left _ (falsified_raw_card_le C)).trans
              (j_mul_pow_mono hk hClong hCle)
        _ = Glong.card * ((k + 1) * 2 ^ (n - (k + 1))) := by simp
    have hBad_le : 2 ^ (n - 2) ≤ Glong.card * ((k + 1) * 2 ^ (n - (k + 1))) := by
      calc 2 ^ (n - 2) ≤ Bad.card := hBad_ge
        _ = (Bad.image toT).card := (Finset.card_image_of_injOn htoT_inj).symm
        _ ≤ Targets.card := Finset.card_le_card (Finset.image_subset_iff.mpr htoT_mem)
        _ ≤ Glong.card * ((k + 1) * 2 ^ (n - (k + 1))) := hTargets_le
    have hk1_le : k + 1 ≤ n := by nlinarith
    have hmul : 2 ^ (n - 1) * 2 ^ k ≤ 2 ^ (n - 1) * (2 * (k + 1) * Glong.card) := by
      have h1 : 2 ^ (n - 1) * 2 ^ k = 2 ^ (k + 1) * 2 ^ (n - 2) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      have h2 : 2 ^ (k + 1) * (Glong.card * ((k + 1) * 2 ^ (n - (k + 1)))) =
          2 ^ (n - 1) * (2 * (k + 1) * Glong.card) := by
        have hpow_n : 2 ^ (k + 1) * 2 ^ (n - (k + 1)) = 2 ^ (n - 1) * 2 := by
          rw [← Nat.pow_add, Nat.add_sub_of_le hk1_le]
          have : n = (n - 1) + 1 := by omega
          conv_lhs => rw [this, Nat.pow_succ]
        calc 2 ^ (k + 1) * (Glong.card * ((k + 1) * 2 ^ (n - (k + 1))))
            = (2 ^ (k + 1) * 2 ^ (n - (k + 1))) * ((k + 1) * Glong.card) := by ring
          _ = (2 ^ (n - 1) * 2) * ((k + 1) * Glong.card) := by rw [hpow_n]
          _ = 2 ^ (n - 1) * (2 * (k + 1) * Glong.card) := by ring
      rw [h1, ← h2]
      exact Nat.mul_le_mul_left _ hBad_le
    exact Nat.le_of_mul_le_mul_left hmul (by positivity : 0 < 2 ^ (n - 1))

end PEqualNP.Outside.L_pcx_236_aux

theorem PEqualNP.Outside.L_pcx_236 : (
∀ (n : ℕ) (hn : 0 < n),
  let Raw := Fin n × (Bool × Bool)
  let next := fun i : Fin n => (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let V := fun a : ℕ => Sum Raw (Fin a)
  let feasible := fun tab : Raw → Bool =>
    ∃ x : Fin n → Bool, ∀ i : Fin n, tab (i, x i, x (next i)) = true
  let enc := fun (a : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (V a))) =>
    ∀ tab : Raw → Bool, feasible tab ↔ ∃ y : Fin a → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim tab y) (↑F : Set _)
  let rows := fun (a : ℕ) (C : PEqualNP.ProofComplexity.Clause (V a)) =>
    Finset.univ.filter (fun location : Fin n => ∃ p : Bool × Bool, ∃ sign : Bool,
      (Sum.inl (location, p), sign) ∈ C)
  (∀ b : ℕ, 0 < b → b ≤ n →
    let H := (n + b - 1) / b
    ∃ F : Finset (PEqualNP.ProofComplexity.Clause (V b)), enc b F ∧
      F.card ≤ 4 * b * (2 ^ (H + 1) - H - 2) ∧
      ∀ C ∈ F, C.card ≤ max 4 H + 2 ∧
        (∀ e : Raw, (Sum.inl e, false) ∉ C) ∧
        ∃ first : Fin n, ∀ site ∈ rows b C, ∃ j : Fin H, (first.val + j.val) % n = site.val) ∧
  ∀ (a : ℕ) (G : Finset (PEqualNP.ProofComplexity.Clause (V a))), enc a G →
    (a = 0 → 2 ^ (n - 1) ≤ (G.filter (fun item =>
      2 * n ≤ (item.filter (fun lit => lit.2 = true)).card)).card) ∧
    (∃ C ∈ G, n ≤ (a + 1) * (rows a C).card) ∧
    ∀ k : ℕ, 0 < k → k * (a + 2) ≤ n →
      2 ^ k ≤ 2 * (k + 1) * (G.filter (fun clause => k < (rows a clause).card)).card
) := by
  intro n hn Raw next V feasible enc rows
  refine ⟨fun b hb hbn => PEqualNP.Outside.L_pcx_236_aux.solve_236_upper n hn b hb hbn,
    fun a G henc => ⟨?_, PEqualNP.Outside.L_pcx_236_aux.solve_236_lower hn a G henc⟩⟩
  rintro rfl
  exact PEqualNP.Outside.L_pcx_236_aux.solve_236_a0 hn G henc
