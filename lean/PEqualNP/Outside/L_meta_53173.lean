import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53173_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Fits (p b g n : ℕ) (word : Fin (n+1) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    C.size ≤ g ∧ C.output < n+2+C.size ∧ ∀ i : Fin (n+1),
      C.eval (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]) = word i

def alt (z : Bool) (i : ℕ) : Bool := if i % 2 = 0 then z else !z

def changes {n : ℕ} (w : Fin (n+1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc ≠ w i.succ)).card

theorem A_base_getD (n i e : ℕ) :
    (List.ofFn (fun j : Fin n => decide (j.val < i)) ++ [false, true]).getD e false
      = if e < n then decide (e < i) else if e = n + 1 then true else false := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge e n with h | h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simpa using h)]
    simp only [List.length_ofFn]
    rcases Nat.lt_or_ge e (n + 2) with h2 | h2
    · have : e = n ∨ e = n + 1 := by omega
      rcases this with rfl | rfl
      · simp
      · simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      have h4 : ¬ e < n := by omega
      have h5 : ¬ e = n + 1 := by omega
      simp [h4, h5]

theorem A_exists_wire (n : ℕ) (f : Fin (n+1) → Bool)
    (hf : ∀ i i' : Fin (n+1), i ≤ i' → f i = true → f i' = true) :
    ∃ e, e < n + 2 ∧ ∀ i : Fin (n+1),
      (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false, true]).getD e false = f i := by
  by_cases hl : f (Fin.last n) = true
  · have hex : ∃ j, ∃ h : j < n + 1, f ⟨j, h⟩ = true := ⟨n, by omega, hl⟩
    classical
    set j0 := Nat.find hex with hj0
    obtain ⟨hj0lt, hj0f⟩ := Nat.find_spec hex
    have key : ∀ i : Fin (n+1), f i = true ↔ j0 ≤ i.val := by
      intro i
      constructor
      · intro hi; exact Nat.find_min' hex ⟨i.isLt, hi⟩
      · intro hi; exact hf ⟨j0, hj0lt⟩ i (by simpa [Fin.le_def] using hi) hj0f
    rcases Nat.eq_zero_or_pos j0 with h0 | h0
    · refine ⟨n + 1, by omega, fun i => ?_⟩
      rw [A_base_getD]
      have := (key i).2 (by omega)
      simp [this]
    · refine ⟨j0 - 1, by omega, fun i => ?_⟩
      rw [A_base_getD]
      have hlt : j0 - 1 < n := by omega
      simp only [hlt, ite_true]
      by_cases hi : j0 ≤ i.val
      · rw [(key i).2 hi]; simp; omega
      · have : f i = false := by simpa using mt (key i).1 hi
        rw [this]; simp; omega
  · refine ⟨n, by omega, fun i => ?_⟩
    rw [A_base_getD]
    have : f i = false := by
      by_contra hc
      exact hl (hf i (Fin.last n) (Fin.le_last i) (by simpa using hc))
    simp [this]

def A_mapGate (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem A_fold (φ : ℕ → ℕ) (c n : ℕ)
    (ha : ∀ k m, m < c + 2 + k → φ m < n + 2 + k)
    (hb : ∀ k m, c + 2 + k ≤ m → n + 2 + k ≤ φ m) :
    ∀ (gs : List Gate) (W W' : List Bool) (k : ℕ), W.length = c + 2 + k →
      W'.length = n + 2 + k → (∀ m, W.getD m false = W'.getD (φ m) false) →
      ∀ m, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          m false =
        ((gs.map (A_mapGate φ)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
          (φ m) false := by
  intro gs
  induction gs with
  | nil => intro W W' k _ _ hP m; simpa using hP m
  | cons g gs ih =>
    intro W W' k hW hW' hP m
    simp only [List.foldl_cons, List.map_cons]
    have hv : g.op.eval (g.inputs.map fun i => W.getD i false)
        = (A_mapGate φ g).op.eval ((A_mapGate φ g).inputs.map fun i => W'.getD i false) := by
      simp only [A_mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simpa using hP i
    rw [hv]
    apply ih _ _ (k + 1) (by simp [hW]; omega) (by simp [hW']; omega)
    intro m'
    rcases lt_trichotomy m' (c + 2 + k) with h | h | h
    · have h' := ha k m' h
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hP m'
    · have h1 := ha (k + 1) m' (by omega)
      have h2 := hb k m' (by omega)
      have he : φ m' = W'.length := by omega
      rw [he, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [show m' - W.length = 0 by omega, Nat.sub_self]
    · have h2 := hb (k + 1) m' (by omega)
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def A_phi (c n : ℕ) (e : ℕ → ℕ) (m : ℕ) : ℕ :=
  if m < c then e m else if m = c then n else if m = c + 1 then n + 1 else m + n - c

theorem A_reindex (p b g c n : ℕ) (w' : Fin (c+1) → Bool) (ρ : Fin (n+1) → Fin (c+1))
    (hρ : Monotone ρ) (hw : Fits p b g c w') : Fits p b g n (w' ∘ ρ) := by
  obtain ⟨C, hfan, hrb, hp, hb, hg, hout, hev⟩ := hw
  have hex : ∀ k : ℕ, ∃ e, e < n + 2 ∧ ∀ i : Fin (n+1),
      (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false, true]).getD e false
        = decide (k < (ρ i).val) := fun k =>
    A_exists_wire n _ (fun i i' hii' hi => by
      have := hρ hii'
      simp only [decide_eq_true_eq] at hi ⊢
      exact lt_of_lt_of_le hi this)
  choose e he1 he2 using hex
  set φ := A_phi c n e with hφ
  have ha : ∀ k m, m < c + 2 + k → φ m < n + 2 + k := by
    intro k m hm
    simp only [hφ, A_phi]
    split_ifs
    · have := he1 m; omega
    all_goals omega
  have hb' : ∀ k m, c + 2 + k ≤ m → n + 2 + k ≤ φ m := by
    intro k m hm
    simp only [hφ, A_phi]
    split_ifs <;> omega
  have hnc : PEqualNP.NotBracket.notCount ⟨C.gates.map (A_mapGate φ), φ C.output⟩
      = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    rw [List.filter_map, List.length_map]
    rfl
  refine ⟨⟨C.gates.map (A_mapGate φ), φ C.output⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    simpa [A_mapGate] using hfan g0 hg0
  · intro j hj i hi
    simp only [List.length_map] at hj
    have hga : (List.map (A_mapGate φ) C.gates).getD j ⟨GateOp.or, []⟩
        = A_mapGate φ (C.gates.getD j ⟨GateOp.or, []⟩) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
        List.getElem_map]
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [hga] at hi
    simp only [A_mapGate, List.mem_map] at hi
    obtain ⟨m, hm, rfl⟩ := hi
    have := hrb j hj m hm
    exact ha j m (by omega)
  · rw [hnc]; simpa [Circuit.size] using hp
  · rw [hnc]; exact hb
  · simpa [Circuit.size] using hg
  · simp only [Circuit.size, List.length_map]
    exact ha _ _ (by simpa [Circuit.size] using hout)
  · intro i
    rw [Function.comp_apply, ← hev (ρ i)]
    simp only [Circuit.eval, Circuit.wires]
    symm
    apply A_fold φ c n ha hb' C.gates _ _ 0 (by simp) (by simp)
    intro m
    rw [A_base_getD, A_base_getD]
    simp only [hφ, A_phi]
    by_cases h1 : m < c
    · simp only [h1, ite_true]
      rw [← he2 m i, A_base_getD]
    · simp only [h1, ite_false]
      by_cases h2 : m = c
      · subst h2; simp
      · by_cases h3 : m = c + 1
        · subst h3; simp
        · have h4 : ¬ m + n - c < n := by omega
          have h5 : ¬ m + n - c = n + 1 := by omega
          simp [h2, h3, h4, h5]

theorem A_alt_succ (z : Bool) (k : ℕ) : alt z (k + 1) = alt (!z) k := by
  unfold alt
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h' : (k + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (k + 1) % 2 = 0 := by omega
    simp [h, h']

theorem A_alt_succ' (z : Bool) (k : ℕ) : alt z (k + 1) = !(alt z k) := by
  rw [A_alt_succ]; unfold alt; split_ifs <;> simp

def A_wN {n : ℕ} (w : Fin (n+1) → Bool) (m : ℕ) : Bool :=
  if h : m < n + 1 then w ⟨m, h⟩ else w (Fin.last n)

def A_pre {n : ℕ} (w : Fin (n+1) → Bool) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (fun j => A_wN w j ≠ A_wN w (j + 1))).card

theorem A_wN_val {n : ℕ} (w : Fin (n+1) → Bool) (i : Fin (n+1)) : A_wN w i.val = w i := by
  simp [A_wN, i.isLt]

theorem A_pre_zero {n : ℕ} (w : Fin (n+1) → Bool) : A_pre w 0 = 0 := by simp [A_pre]

theorem A_pre_succ {n : ℕ} (w : Fin (n+1) → Bool) (i : ℕ) :
    A_pre w (i + 1) = A_pre w i + if A_wN w i ≠ A_wN w (i + 1) then 1 else 0 := by
  unfold A_pre
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem A_pre_mono {n : ℕ} (w : Fin (n+1) → Bool) : Monotone (A_pre w) := by
  intro i i' h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem A_changes_eq {n : ℕ} (w : Fin (n+1) → Bool) : changes w = A_pre w n := by
  unfold changes A_pre
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if A_wN w j ≠ A_wN w (j + 1) then 1 else 0) n]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : A_wN w i.val = w i.castSucc := by
    rw [show i.val = (Fin.castSucc i).val from rfl, A_wN_val]
  have h2 : A_wN w (i.val + 1) = w i.succ := by
    rw [show i.val + 1 = (Fin.succ i).val from rfl, A_wN_val]
  rw [h1, h2]

theorem A_alt_pre {n : ℕ} (w : Fin (n+1) → Bool) :
    ∀ i, A_wN w i = alt (w 0) (A_pre w i) := by
  intro i
  induction i with
  | zero =>
    rw [A_pre_zero]
    simp [A_wN, alt]
  | succ i ih =>
    rw [A_pre_succ]
    by_cases h : A_wN w i ≠ A_wN w (i + 1)
    · simp only [h, ne_eq, not_false_eq_true, ite_true]
      rw [A_alt_succ', ← ih]
      revert h
      cases A_wN w i <;> cases A_wN w (i + 1) <;> simp
    · simp only [h, ite_false, Nat.add_zero]
      simp only [ne_eq, not_not] at h
      rw [← h, ih]

theorem A_ivt {n : ℕ} (w : Fin (n+1) → Bool) :
    ∀ i, ∀ m ≤ A_pre w i, ∃ j ≤ i, A_pre w j = m := by
  intro i
  induction i with
  | zero => intro m hm; rw [A_pre_zero] at hm; exact ⟨0, le_refl _, by rw [A_pre_zero]; omega⟩
  | succ i ih =>
    intro m hm
    by_cases hmi : m ≤ A_pre w i
    · obtain ⟨j, hj, hj'⟩ := ih m hmi
      exact ⟨j, by omega, hj'⟩
    · refine ⟨i + 1, le_refl _, ?_⟩
      have := A_pre_succ w i
      split_ifs at this <;> omega

theorem A_bwd (p b g : ℕ) (h : Bool → ℕ)
    (hh : ∀ (z : Bool) (k : ℕ), Fits p b g k (fun i => alt z i.val) ↔ k ≤ h z)
    (n : ℕ) (w : Fin (n+1) → Bool) (hc : changes w ≤ h (w 0)) : Fits p b g n w := by
  rw [A_changes_eq] at hc
  have hf := (hh (w 0) (A_pre w n)).2 hc
  let ρ : Fin (n+1) → Fin (A_pre w n + 1) := fun i =>
    ⟨A_pre w i.val, Nat.lt_succ_of_le (A_pre_mono w (Nat.le_of_lt_succ i.isLt))⟩
  have hρ : Monotone ρ := fun i i' hii' => by
    show A_pre w i.val ≤ A_pre w i'.val
    exact A_pre_mono w hii'
  have := A_reindex p b g _ n _ ρ hρ hf
  convert this using 1
  funext i
  simp only [Function.comp_apply, ρ]
  rw [← A_alt_pre, A_wN_val]

theorem A_fwd (p b g : ℕ) (h : Bool → ℕ)
    (hh : ∀ (z : Bool) (k : ℕ), Fits p b g k (fun i => alt z i.val) ↔ k ≤ h z)
    (n : ℕ) (w : Fin (n+1) → Bool) (hw : Fits p b g n w) : changes w ≤ h (w 0) := by
  rw [A_changes_eq]
  set c := A_pre w n with hc
  have hP : ∀ m : Fin (c+1), ∃ j, j ≤ n ∧ A_pre w j = m.val := fun m =>
    A_ivt w n m.val (Nat.le_of_lt_succ m.isLt)
  let σ : Fin (c+1) → Fin (n+1) := fun m => ⟨Nat.find (hP m), Nat.lt_succ_of_le (Nat.find_spec (hP m)).1⟩
  have hσ : Monotone σ := by
    intro m m' hmm'
    show Nat.find (hP m) ≤ Nat.find (hP m')
    obtain ⟨h1, h2⟩ := Nat.find_spec (hP m')
    obtain ⟨j, hj, hj'⟩ := A_ivt w (Nat.find (hP m')) m.val (by rw [h2]; exact hmm')
    exact le_trans (Nat.find_min' (hP m) ⟨by omega, hj'⟩) hj
  have := A_reindex p b g n c w σ hσ hw
  have heq : w ∘ σ = fun m => alt (w 0) m.val := by
    funext m
    show w (σ m) = _
    rw [← A_wN_val w (σ m), A_alt_pre]
    show alt (w 0) (A_pre w (Nat.find (hP m))) = _
    rw [(Nat.find_spec (hP m)).2]
  rw [heq] at this
  exact (hh (w 0) c).1 this

theorem fits_iff_changes (p b g K : ℕ)
    (hh : ∀ (z : Bool) (k : ℕ), Fits p b g k (fun i => alt z i.val) ↔ k ≤ K)
    (n : ℕ) (w : Fin (n+1) → Bool) :
    Fits p b g n w ↔ changes w ≤ K :=
  ⟨A_fwd p b g (fun _ => K) hh n w, A_bwd p b g (fun _ => K) hh n w⟩

def changesNat (m : ℕ) (w : ℕ → Bool) : ℕ :=
  ((Finset.range (m - 1)).filter (fun j => w j ≠ w (j + 1))).card

theorem changesNat_le_one {m : ℕ} (hm : m ≤ 1) (w : ℕ → Bool) : changesNat m w = 0 := by
  have : m - 1 = 0 := by omega
  simp [changesNat, this]

theorem changesNat_succ {r : ℕ} (hr : 1 ≤ r) (w : ℕ → Bool) :
    changesNat (r + 1) w = changesNat r w + (if w (r - 1) ≠ w r then 1 else 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_comm 1 k]
  unfold changesNat
  simp only [Nat.add_sub_cancel]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem changesNat_mono {r s : ℕ} (hrs : r ≤ s) (w : ℕ → Bool) :
    changesNat r w ≤ changesNat s w := by
  unfold changesNat
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

theorem changesNat_shift {m : ℕ} (w : ℕ → Bool) :
    changesNat (m + 1) w = changesNat m (fun t => w (t + 1)) +
      if 1 ≤ m ∧ w 0 ≠ w 1 then 1 else 0 := by
  cases m with
  | zero => simp [changesNat]
  | succ m =>
    unfold changesNat
    simp only [Nat.add_sub_cancel, show 1 ≤ m + 1 by omega, true_and]
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']

theorem changesNat_eq_changes {n : ℕ} (w : Fin (n+1) → Bool) :
    changes w = changesNat (n + 1) (A_wN w) := by
  rw [A_changes_eq]
  unfold A_pre changesNat
  simp

theorem changesNat_of_fin_eq {n : ℕ} (u : ℕ → Bool) :
    changes (fun i : Fin (n+1) => u i.val) = changesNat (n + 1) u := by
  rw [changesNat_eq_changes]
  unfold changesNat
  simp only [Nat.add_sub_cancel]
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have h1 : A_wN (fun i : Fin (n+1) => u i.val) j = u j := by
    simp [A_wN, show j < n + 1 by omega]
  have h2 : A_wN (fun i : Fin (n+1) => u i.val) (j + 1) = u (j + 1) := by
    simp [A_wN, show j + 1 < n + 1 by omega]
  rw [h1, h2]

theorem changesNat_const {m : ℕ} (w : ℕ → Bool) (h : changesNat m w = 0) :
    ∀ j < m, w j = w 0 := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < m - 1 := by omega
    have hmem : j ∉ (Finset.range (m - 1)).filter (fun i => w i ≠ w (i + 1)) := by
      intro hmem
      have := Finset.card_pos.2 ⟨j, hmem⟩
      unfold changesNat at h
      omega
    simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hmem
    rw [← hmem hlt]
    exact ih (by omega)

theorem changesNat_parity {r : ℕ} (hr : 1 ≤ r) (w : ℕ → Bool) :
    changesNat r w % 2 = 0 ↔ w 0 = w (r - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_comm 1 k]
  induction k with
  | zero => simp [changesNat]
  | succ k ih =>
    rw [changesNat_succ (by omega)]
    simp only [Nat.add_sub_cancel] at ih ⊢
    by_cases h : w k ≠ w (k + 1)
    · rw [if_pos h]
      have hc : (w 0 = w (k + 1)) ↔ ¬ (w 0 = w k) := by
        cases h0 : w 0 <;> cases h1 : w k <;> cases h2 : w (k + 1) <;> simp_all [ne_eq]
      rw [hc, ← ih (by omega)]
      omega
    · simp only [if_neg h, Nat.add_zero]
      simp only [ne_eq, not_not] at h
      rw [← h]
      exact ih (by omega)

theorem changesNat_neg {m : ℕ} (w : ℕ → Bool) :
    changesNat m (fun t => !w t) = changesNat m w := by
  unfold changesNat
  congr 1
  ext j
  simp [Bool.not_inj]

def listCost : List (Bool × ℕ) → (ℕ → Bool) → ℕ
  | [], _ => 0
  | (p, c) :: rest, u => (if u 0 = p then 0 else c) + listCost rest (fun t => u (t + 1))

def listSum (L : List (Bool × ℕ)) : ℕ := (L.map Prod.snd).sum

theorem listSum_pos_zero {L : List (Bool × ℕ)} (h : ∀ x ∈ L, 0 < x.2) :
    listSum L = 0 ↔ L = [] := by
  cases L with
  | nil => simp [listSum]
  | cons x rest =>
    have hx := h x (by simp)
    simp only [listSum, List.map_cons, List.sum_cons]
    constructor
    · intro hs; omega
    · intro hne; simp at hne

theorem listCost_neg (L : List (Bool × ℕ)) (u : ℕ → Bool) :
    listCost (L.map (fun x => (!x.1, x.2))) (fun t => !u t) = listCost L u := by
  induction L generalizing u with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    simp only [List.map_cons, listCost]
    rw [ih (fun t => u (t + 1))]
    cases u 0 <;> cases p <;> simp

def OptL (L : List (Bool × ℕ)) (K q : ℕ) : Prop :=
  ∀ u : ℕ → Bool, changesNat L.length u ≤ K → q ≤ listCost L u

def DelMinL (L : List (Bool × ℕ)) (K q : ℕ) : Prop :=
  ∀ j, j < L.length → ∃ u : ℕ → Bool,
    changesNat L.length u ≤ K ∧ listCost L u = q ∧ u j ≠ (L.getD j (false, 0)).1

def DelMinPosL (L : List (Bool × ℕ)) (K q : ℕ) : Prop :=
  ∀ j, j < L.length → 0 < (L.getD j (false, 0)).2 → ∃ u : ℕ → Bool,
    changesNat L.length u ≤ K ∧ listCost L u = q ∧ u j ≠ (L.getD j (false, 0)).1

def liftU : List (Bool × ℕ) → (ℕ → Bool) → ℕ → Bool
  | [], u, _ => u 0
  | (_, _) :: _, u, 0 => u 0
  | (_, c) :: rest, u, j + 1 =>
      if 0 < c then
        if (rest.filter (fun y => decide (0 < y.2))).isEmpty then u 0
        else liftU rest (fun t => u (t + 1)) j
      else liftU rest u j

theorem listCost_all_zero (M : List (Bool × ℕ)) (h : (M.filter (fun y => decide (0 < y.2))).isEmpty = true)
    (u : ℕ → Bool) : listCost M u = 0 := by
  induction M generalizing u with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    by_cases hc : 0 < c
    · simp [List.filter_cons, hc] at h
    · have hc0 : c = 0 := by omega
      simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false] at h
      simp only [listCost, ih h (fun t => u (t + 1))]
      split_ifs <;> omega

theorem liftU_cost (M : List (Bool × ℕ)) (u : ℕ → Bool) :
    listCost M (liftU M u) = listCost (M.filter (fun x => decide (0 < x.2))) u := by
  induction M generalizing u with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true]
      rw [listCost, listCost]
      have h0 : liftU ((p, c) :: rest) u 0 = u 0 := rfl
      by_cases he : (rest.filter (fun y => decide (0 < y.2))).isEmpty
      · have hemp : rest.filter (fun y => decide (0 < y.2)) = [] := by
          cases hf : rest.filter (fun y => decide (0 < y.2)) with
          | nil => rfl
          | cons _ _ => simp [hf] at he
        have heq : (fun t => liftU ((p, c) :: rest) u (t + 1)) = fun _ => u 0 := by
          funext t; simp [liftU, hc, he]
        simp only [h0, heq, hemp, listCost]
        rw [listCost_all_zero rest he (fun _ => u 0), Nat.add_zero]
      · have heq : (fun t => liftU ((p, c) :: rest) u (t + 1)) = liftU rest (fun t => u (t + 1)) := by
          funext t; simp [liftU, hc, he]
        simp only [h0, heq, ih]
    · have hc0 : c = 0 := by omega
      simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false]
      rw [listCost]
      have h0 : liftU ((p, c) :: rest) u 0 = u 0 := rfl
      have heq : (fun t => liftU ((p, c) :: rest) u (t + 1)) = liftU rest u := by
        funext t; simp [liftU, hc]
      rw [h0, heq, hc0]
      simp [ih]

theorem liftU_changes (M : List (Bool × ℕ)) (u : ℕ → Bool) :
    changesNat M.length (liftU M u) ≤ changesNat (M.filter (fun x => decide (0 < x.2))).length u := by
  induction M generalizing u with
  | nil => simp [changesNat]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    rw [List.length_cons, changesNat_shift]
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true, List.length_cons]
      by_cases he : (rest.filter (fun y => decide (0 < y.2))).isEmpty
      · have hconst : ∀ j, liftU ((p, c) :: rest) u j = u 0 := by
          intro j; cases j with | zero => rfl | succ j => simp [liftU, hc, he]
        have hz : changesNat (rest.length + 1) (liftU ((p, c) :: rest) u) = 0 := by
          unfold changesNat
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _; simp [hconst j, hconst (j + 1)]
        rw [← changesNat_shift]
        rw [hz]
        exact Nat.zero_le _
      · have hrf : 1 ≤ (rest.filter (fun y => decide (0 < y.2))).length := by
          cases hf : rest.filter (fun y => decide (0 < y.2)) with
          | nil => simp [hf] at he
          | cons _ _ => simp
        have hr : 1 ≤ rest.length := le_trans hrf (List.length_filter_le _ _)
        have heq : (fun t => liftU ((p, c) :: rest) u (t + 1)) = liftU rest (fun t => u (t + 1)) := by
          funext t; simp [liftU, hc, he]
        have h0 : liftU ((p, c) :: rest) u 0 = u 0 := rfl
        have h1 : liftU ((p, c) :: rest) u 1 = u 1 := by
          simp only [liftU, hc, he, Bool.false_eq_true, ite_false]
          cases rest <;> simp [liftU]
        rw [changesNat_shift]
        simp only [heq, hr, hrf, true_and, h0, h1]
        have ih' := ih (fun t => u (t + 1))
        omega
    · simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false]
      have heq : (fun t => liftU ((p, c) :: rest) u (t + 1)) = liftU rest u := by
        funext t; simp [liftU, hc]
      have h0 : liftU ((p, c) :: rest) u 0 = u 0 := rfl
      have h1 : liftU ((p, c) :: rest) u 1 = u 0 := by
        simp only [liftU, hc, ite_false]
        cases rest <;> simp [liftU]
      simp only [heq, h0, h1, ne_eq, not_true_eq_false, and_false, ite_false, Nat.add_zero]
      exact ih u

def projectU : List (Bool × ℕ) → (ℕ → Bool) → ℕ → Bool
  | [], v, _ => v 0
  | (_, c) :: rest, v, j =>
      if 0 < c then
        match j with
        | 0 => v 0
        | j' + 1 => projectU rest (fun t => v (t + 1)) j'
      else projectU rest (fun t => v (t + 1)) j

theorem projectU_cost (M : List (Bool × ℕ)) (v : ℕ → Bool) :
    listCost (M.filter (fun x => decide (0 < x.2))) (projectU M v) = listCost M v := by
  induction M generalizing v with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true, listCost]
      have h0 : projectU ((p, c) :: rest) v 0 = v 0 := by simp [projectU, hc]
      have h1 : (fun t => projectU ((p, c) :: rest) v (t + 1)) = projectU rest (fun t => v (t + 1)) := by
        funext t; simp [projectU, hc]
      rw [h0, h1, ih]
    · have hc0 : c = 0 := by omega
      simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false, listCost]
      have h0 : (if v 0 = p then 0 else c) = 0 := by split_ifs <;> omega
      rw [h0, Nat.zero_add]
      have h1 : projectU ((p, c) :: rest) v = projectU rest (fun t => v (t + 1)) := by
        funext t; simp [projectU, hc]
      rw [h1, ih]

theorem projectU_changes (M : List (Bool × ℕ)) (v : ℕ → Bool)
    (hne : M.filter (fun x => decide (0 < x.2)) ≠ []) :
    changesNat (M.filter (fun x => decide (0 < x.2))).length (projectU M v) +
      (if v 0 ≠ projectU M v 0 then 1 else 0) ≤ changesNat M.length v := by
  induction M generalizing v with
  | nil => simp at hne
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    rw [List.length_cons, changesNat_shift]
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true, List.length_cons]
      have h0 : projectU ((p, c) :: rest) v 0 = v 0 := by simp [projectU, hc]
      have h0' : projectU ((p, c) :: rest) v 1 = projectU rest (fun t => v (t + 1)) 0 := by
        simp [projectU, hc]
      have h1 : (fun t => projectU ((p, c) :: rest) v (t + 1)) = projectU rest (fun t => v (t + 1)) := by
        funext t; simp [projectU, hc]
      rw [changesNat_shift]
      simp only [h0, h0', h1, ne_eq, not_true_eq_false, ite_false, Nat.add_zero]
      by_cases hrf : 1 ≤ (rest.filter (fun y => decide (0 < y.2))).length
      · have hne' : rest.filter (fun y => decide (0 < y.2)) ≠ [] := by
          intro he; simp [he] at hrf
        have ih' := ih (fun t => v (t + 1)) hne'
        simp only [Nat.zero_add] at ih'
        have hr : 1 ≤ rest.length := le_trans hrf (List.length_filter_le _ _)
        simp only [hr, hrf, true_and]
        cases hv0 : v 0 <;> cases hv1 : v 1 <;>
          cases hp : projectU rest (fun t => v (t + 1)) 0 <;>
          simp [hv0, hv1, hp] at ih' ⊢ <;> omega
      · have hrf0 : (rest.filter (fun y => decide (0 < y.2))).length = 0 := by omega
        rw [hrf0, changesNat_le_one (by omega)]
        simp
    · simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false] at hne ⊢
      have ih' := ih (fun t => v (t + 1)) hne
      simp only [Nat.zero_add] at ih'
      have h1 : projectU ((p, c) :: rest) v = projectU rest (fun t => v (t + 1)) := by
        funext t; simp [projectU, hc]
      rw [h1]
      have hrf : 1 ≤ (rest.filter (fun y => decide (0 < y.2))).length :=
        List.length_pos_of_ne_nil hne
      have hr : 1 ≤ rest.length := le_trans hrf (List.length_filter_le _ _)
      simp only [hr, true_and]
      by_cases h01 : v 0 = v 1 <;>
        by_cases h1p : v 1 = projectU rest (fun t => v (t + 1)) 0 <;>
        by_cases h0p : v 0 = projectU rest (fun t => v (t + 1)) 0 <;>
        simp [h01, h1p, h0p] at ih' ⊢ <;> omega

theorem filter_getD_exists (M : List (Bool × ℕ)) (j : ℕ)
    (hj : j < (M.filter (fun x => decide (0 < x.2))).length) :
    ∃ i < M.length, 0 < (M.getD i (false, 0)).2 ∧
      (M.filter (fun x => decide (0 < x.2))).getD j (false, 0) = M.getD i (false, 0) ∧
      ∀ v : ℕ → Bool, projectU M v j = v i := by
  induction M generalizing j with
  | nil => simp at hj
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true, List.length_cons] at hj ⊢
      cases j with
      | zero =>
        refine ⟨0, by simp, by simpa using hc, by simp, fun v => by simp [projectU, hc]⟩
      | succ j' =>
        obtain ⟨i, hi1, hi2, hi3, hi4⟩ := ih j' (by omega)
        refine ⟨i + 1, by simp; omega, by simpa [List.getD_cons_succ] using hi2,
          by simpa [List.getD_cons_succ] using hi3, fun v => ?_⟩
        simpa [projectU, hc] using hi4 (fun t => v (t + 1))
    · simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false] at hj ⊢
      obtain ⟨i, hi1, hi2, hi3, hi4⟩ := ih j hj
      refine ⟨i + 1, by simp; omega, by simpa [List.getD_cons_succ] using hi2,
        by simpa [List.getD_cons_succ] using hi3, fun v => ?_⟩
      simpa [projectU, hc] using hi4 (fun t => v (t + 1))

theorem filter_opt_delMin (M : List (Bool × ℕ)) (K q : ℕ)
    (hopt : OptL M K q) (hdel : DelMinPosL M K q) :
    OptL (M.filter (fun x => decide (0 < x.2))) K q ∧
    DelMinL (M.filter (fun x => decide (0 < x.2))) K q := by
  constructor
  · intro u hu
    rw [← liftU_cost]
    exact hopt (liftU M u) (le_trans (liftU_changes M u) hu)
  · intro j hj
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := filter_getD_exists M j hj
    obtain ⟨v, hvc, hvcost, hvp⟩ := hdel i hi1 hi2
    refine ⟨projectU M v, ?_, ?_, ?_⟩
    · have := projectU_changes M v (List.ne_nil_of_length_pos (by omega)); omega
    · rw [projectU_cost, hvcost]
    · rw [hi3, hi4]; exact hvp

theorem listSum_filter_pos (M : List (Bool × ℕ)) :
    listSum (M.filter (fun x => decide (0 < x.2))) = listSum M := by
  induction M with
  | nil => rfl
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    by_cases hc : 0 < c
    · simp only [List.filter_cons, hc, decide_true, ite_true, listSum, List.map_cons, List.sum_cons]
      have := ih
      simp only [listSum] at this
      omega
    · have hc0 : c = 0 := by omega
      simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false]
      simp only [listSum, List.map_cons, List.sum_cons] at ih ⊢
      omega

def dupAt (k : ℕ) (u : ℕ → Bool) (t : ℕ) : Bool :=
  if t ≤ k then u t else u (t - 1)

def dropAt (k : ℕ) (v : ℕ → Bool) (t : ℕ) : Bool :=
  if t ≤ k then v t else v (t + 1)

def setAt (k : ℕ) (b : Bool) (v : ℕ → Bool) (t : ℕ) : Bool :=
  if t = k then b else v t

theorem listCost_append (L1 L2 : List (Bool × ℕ)) (u : ℕ → Bool) :
    listCost (L1 ++ L2) u = listCost L1 u + listCost L2 (fun t => u (t + L1.length)) := by
  induction L1 generalizing u with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    simp only [List.cons_append, listCost, List.length_cons]
    rw [ih (fun t => u (t + 1))]
    have heq : (fun t => u (t + rest.length + 1)) = (fun t => u (t + (rest.length + 1))) := by
      funext t; simp [Nat.add_assoc]
    rw [heq]
    omega

theorem listCost_congr_lt (L : List (Bool × ℕ)) (u v : ℕ → Bool)
    (h : ∀ j < L.length, u j = v j) : listCost L u = listCost L v := by
  induction L generalizing u v with
  | nil => simp [listCost]
  | cons x rest ih =>
    rcases x with ⟨p, c⟩
    simp only [listCost]
    have h0 : u 0 = v 0 := h 0 (by simp)
    rw [h0]
    congr 1
    apply ih
    intro j hj
    exact h (j + 1) (by simp; omega)

theorem changesNat_dupAt (m k : ℕ) (u : ℕ → Bool) (hk : k < m) :
    changesNat (m + 1) (dupAt k u) = changesNat m u := by
  induction k generalizing m u with
  | zero =>
    rw [changesNat_shift]
    have h01 : dupAt 0 u 0 = dupAt 0 u 1 := rfl
    have hs : (fun t => dupAt 0 u (t + 1)) = u := by
      funext t; simp [dupAt]
    simp [h01, hs]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      rw [changesNat_shift]
      have hs : (fun t => dupAt (k + 1) u (t + 1)) = dupAt k (fun t => u (t + 1)) := by
        funext t
        cases t with
        | zero => simp [dupAt]
        | succ t' =>
          unfold dupAt
          split_ifs with h1 h2 <;> simp_all <;> omega
      have h0 : dupAt (k + 1) u 0 = u 0 := rfl
      have h1 : dupAt (k + 1) u 1 = u 1 := by simp [dupAt]
      have hk1 : 1 ≤ m' := by omega
      rw [hs, ih m' (fun t => u (t + 1)) (by omega), h0, h1]
      rw [changesNat_shift]
      simp [hk1]

theorem changesNat_dropAt (m k : ℕ) (v : ℕ → Bool) (hk : k + 1 < m) (heq : v k = v (k + 1)) :
    changesNat (m - 1) (dropAt k v) = changesNat m v := by
  induction k generalizing m v with
  | zero =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    rw [show m' + 2 - 1 = m' + 1 by omega]
    rw [changesNat_shift, changesNat_shift]
    have hs1 : (fun t => dropAt 0 v (t + 1)) = fun t => v (t + 2) := by
      funext t; simp [dropAt]
    have h0 : dropAt 0 v 0 = v 1 := by simp [dropAt, heq]
    have h1 : dropAt 0 v 1 = v 2 := rfl
    have h01 : ¬ v 0 ≠ v 1 := not_not.2 heq
    have hs2 : (fun t => (fun t => v (t + 1)) (t + 1)) = fun t => v (t + 2) := rfl
    have ht0 : (fun t => v (t + 1)) 0 = v 1 := rfl
    have ht1 : (fun t => v (t + 1)) 1 = v 2 := rfl
    simp only [hs1, h0, h1, h01, and_false, ite_false, Nat.add_zero]
    rw [changesNat_shift]
    try simp only [hs2, ht0, ht1]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      have hm2 : 1 ≤ m' := by omega
      have hm3 : 1 ≤ m' - 1 := by omega
      rw [show m' + 1 - 1 = (m' - 1) + 1 by omega]
      rw [changesNat_shift]
      have hs : (fun t => dropAt (k + 1) v (t + 1)) = dropAt k (fun t => v (t + 1)) := by
        funext t; unfold dropAt; split_ifs <;> simp_all <;> omega
      have h0 : dropAt (k + 1) v 0 = v 0 := rfl
      have h1 : dropAt (k + 1) v 1 = v 1 := by simp [dropAt]
      rw [hs, ih m' (fun t => v (t + 1)) (by omega) (by simpa using heq), h0, h1]
      rw [changesNat_shift]
      simp [hm2, hm3]

theorem changesNat_setAt_left (m k : ℕ) (v : ℕ → Bool) (hk : k + 1 < m) (hne : v k ≠ v (k + 1)) :
    changesNat m (setAt k (v (k + 1)) v) ≤ changesNat m v := by
  induction k generalizing m v with
  | zero =>
    cases m with
    | zero => omega
    | succ m' =>
      rw [changesNat_shift, changesNat_shift]
      have hs : (fun t => setAt 0 (v 1) v (t + 1)) = fun t => v (t + 1) := by
        funext t; simp [setAt]
      have h0 : setAt 0 (v 1) v 0 = v 1 := rfl
      have h1 : setAt 0 (v 1) v 1 = v 1 := by simp [setAt]
      rw [hs, h0, h1]
      simp [hne]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      cases k with
      | zero =>
        cases m' with
        | zero => omega
        | succ m'' =>
          rw [changesNat_shift]
          have h0 : setAt 1 (v 2) v 0 = v 0 := rfl
          have h1 : setAt 1 (v 2) v 1 = v 2 := rfl
          have h0v : (fun t => setAt 1 (v 2) v (t + 1)) = setAt 0 (v 2) (fun t => v (t + 1)) := by
            funext t; cases t <;> simp [setAt]
          rw [h0v, h0, h1]
          have htail : changesNat (m'' + 1) (setAt 0 (v 2) (fun t => v (t + 1))) + 1 =
              changesNat (m'' + 1) (fun t => v (t + 1)) := by
            cases m'' with
            | zero => omega
            | succ m''' =>
              rw [changesNat_shift]
              have ht1 : (fun t => setAt 0 (v 2) (fun t => v (t + 1)) (t + 1)) = fun t => v (t + 2) := by
                funext t; simp [setAt]
              have ht2 : (fun t => (fun t => v (t + 1)) (t + 1)) = fun t => v (t + 2) := rfl
              rw [ht1]
              nth_rw 2 [changesNat_shift]
              simp only [ht2, setAt, ite_true, show (fun t => v (t + 1)) 0 ≠ (fun t => v (t + 1)) 1 from hne,
                show 1 ≤ m''' + 1 by omega, true_and, ne_eq, not_true_eq_false, ite_false, Nat.add_zero]
              simp
          nth_rw 2 [changesNat_shift]
          have h1m : 1 ≤ m'' + 1 := by omega
          simp only [h1m, true_and]
          split_ifs <;> omega
      | succ k' =>
        rw [changesNat_shift]
        have hs : (fun t => setAt (k' + 2) (v (k' + 3)) v (t + 1)) =
            setAt (k' + 1) (v (k' + 3)) (fun t => v (t + 1)) := by
          funext t; unfold setAt; split_ifs <;> simp_all <;> omega
        have h0 : setAt (k' + 2) (v (k' + 3)) v 0 = v 0 := rfl
        have h1 : setAt (k' + 2) (v (k' + 3)) v 1 = v 1 := rfl
        rw [hs, h0, h1]
        have ih' := ih m' (fun t => v (t + 1)) (by omega) (by simpa using hne)
        simp only [show k' + 1 + 1 + 1 = k' + 3 by omega] at ih'
        conv_rhs => rw [changesNat_shift]
        omega

theorem changesNat_setAt_right (m k : ℕ) (v : ℕ → Bool) (hk : k + 1 < m) (hne : v k ≠ v (k + 1)) :
    changesNat m (setAt (k + 1) (v k) v) ≤ changesNat m v := by
  induction k generalizing m v with
  | zero =>
    cases m with
    | zero => omega
    | succ m' =>
      cases m' with
      | zero => omega
      | succ m'' =>
        rw [changesNat_shift]
        have h0 : setAt 1 (v 0) v 0 = v 0 := rfl
        have h1 : setAt 1 (v 0) v 1 = v 0 := rfl
        have htail : (fun t => setAt 1 (v 0) v (t + 1)) = setAt 0 (v 0) (fun t => v (t + 1)) := by
          funext t; cases t <;> simp [setAt]
        rw [h0, h1, htail]
        have hm1 : 1 ≤ m'' + 1 := by omega
        simp only [hm1, true_and, ne_eq, not_true_eq_false, ite_false, Nat.add_zero]
        conv_rhs => rw [changesNat_shift]
        simp only [hm1, true_and]
        cases m'' with
        | zero => simp [changesNat]
        | succ m''' =>
          have hs1 : (fun t => setAt 0 (v 0) (fun t => v (t + 1)) (t + 1)) = fun t => v (t + 2) := by
            funext t; simp [setAt]
          have hs2 : (fun t => (fun t => v (t + 1)) (t + 1)) = fun t => v (t + 2) := rfl
          rw [changesNat_shift, hs1]
          conv_rhs => rw [changesNat_shift]
          simp only [hs2, setAt, ite_true]
          have hm2 : 1 ≤ m''' + 1 := by omega
          have hne01 : v 0 ≠ v 1 := hne
          simp only [hm2, true_and, hne01, ne_eq, not_false_eq_true, ite_true]
          split_ifs <;> omega
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      rw [changesNat_shift]
      have hs : (fun t => setAt (k + 2) (v (k + 1)) v (t + 1)) =
          setAt (k + 1) (v (k + 1)) (fun t => v (t + 1)) := by
        funext t; unfold setAt; split_ifs <;> simp_all <;> omega
      have h0 : setAt (k + 2) (v (k + 1)) v 0 = v 0 := rfl
      have h1 : setAt (k + 2) (v (k + 1)) v 1 = v 1 := rfl
      rw [hs, h0, h1]
      have ih' := ih m' (fun t => v (t + 1)) (by omega) (by simpa using hne)
      conv_rhs => rw [changesNat_shift]
      omega

theorem mergeAt_opt (pre suf : List (Bool × ℕ)) (b : Bool) (w1 w2 : ℕ) (K q : ℕ)
    (hopt : OptL (pre ++ (b, w1) :: (b, w2) :: suf) K q) :
    OptL (pre ++ (b, w1 + w2) :: suf) K q := by
  intro u hu
  have hc : changesNat (pre ++ (b, w1) :: (b, w2) :: suf).length (dupAt pre.length u) ≤ K := by
    have h1 : (pre ++ (b, w1) :: (b, w2) :: suf).length = (pre ++ (b, w1 + w2) :: suf).length + 1 := by
      simp; omega
    rw [h1, changesNat_dupAt _ _ _ (by simp)]
    exact hu
  have hcost : listCost (pre ++ (b, w1) :: (b, w2) :: suf) (dupAt pre.length u) =
      listCost (pre ++ (b, w1 + w2) :: suf) u := by
    rw [listCost_append, listCost_append]
    congr 1
    · apply listCost_congr_lt
      intro j hj
      simp [dupAt, show j ≤ pre.length by omega]
    · simp only [listCost]
      have h0 : dupAt pre.length u (0 + pre.length) = u pre.length := by simp [dupAt]
      have h0' : u (0 + pre.length) = u pre.length := by simp
      have htail2 : (fun t => dupAt pre.length u (t + 1 + pre.length)) 0 = u pre.length := by
        simp [dupAt]
      have htail3 : (fun t => (fun t => dupAt pre.length u (t + 1 + pre.length)) (t + 1)) =
          fun t => u (t + 1 + pre.length) := by
        funext t
        have hgt : pre.length < t + 1 + 1 + pre.length := by omega
        have hsub : t + 1 + 1 + pre.length - 1 = t + 1 + pre.length := by omega
        simp [dupAt, Nat.not_le_of_gt hgt, hsub]
      simp only [h0, h0', htail2, htail3]
      by_cases hu : u pre.length = b <;> simp [hu] <;> omega
  rw [← hcost]
  exact hopt (dupAt pre.length u) hc

theorem mergeAt_delMin (pre suf : List (Bool × ℕ)) (b : Bool) (w1 w2 : ℕ) (K q : ℕ)
    (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hopt : OptL (pre ++ (b, w1) :: (b, w2) :: suf) K q)
    (hdel : DelMinL (pre ++ (b, w1) :: (b, w2) :: suf) K q) :
    DelMinL (pre ++ (b, w1 + w2) :: suf) K q := by
  have heq_opt : ∀ v : ℕ → Bool, changesNat (pre ++ (b, w1) :: (b, w2) :: suf).length v ≤ K →
      listCost (pre ++ (b, w1) :: (b, w2) :: suf) v = q →
      v pre.length = v (pre.length + 1) := by
    intro v hvc hvcost
    by_contra hne
    have hlt : pre.length + 1 < (pre ++ (b, w1) :: (b, w2) :: suf).length := by simp
    by_cases hv1 : v (pre.length + 1) = b
    · have hc' := le_trans (changesNat_setAt_left _ pre.length v hlt hne) hvc
      have hv0 : v pre.length ≠ b := by rw [← hv1]; exact hne
      have hcost' : listCost (pre ++ (b, w1) :: (b, w2) :: suf) (setAt pre.length (v (pre.length + 1)) v) + w1 =
          listCost (pre ++ (b, w1) :: (b, w2) :: suf) v := by
        rw [listCost_append, listCost_append]
        have hpre : listCost pre (setAt pre.length (v (pre.length + 1)) v) = listCost pre v := by
          apply listCost_congr_lt
          intro j hj; simp [setAt, show j ≠ pre.length by omega]
        rw [hpre]
        dsimp only [listCost]
        have hsuf : listCost suf (fun t => setAt pre.length (v (pre.length + 1)) v (t + 1 + 1 + pre.length)) =
            listCost suf (fun t => v (t + 1 + 1 + pre.length)) := by
          apply listCost_congr_lt
          intro j _; simp [setAt, show j + 1 + 1 + pre.length ≠ pre.length by omega]
        rw [hsuf]
        simp only [setAt, show 0 + pre.length = pre.length by omega,
          show 0 + 1 + pre.length = pre.length + 1 by omega,
          show pre.length + 1 ≠ pre.length by omega, ite_false, hv1, ite_true]
        rw [if_neg hv0]
        omega
      have hq := hopt _ hc'
      omega
    · have hv0 : v pre.length = b := by cases hvp : v pre.length <;> cases hvp1 : v (pre.length + 1) <;> cases hb : b <;> simp_all
      have hc' := le_trans (changesNat_setAt_right _ pre.length v hlt hne) hvc
      have hcost' : listCost (pre ++ (b, w1) :: (b, w2) :: suf) (setAt (pre.length + 1) (v pre.length) v) + w2 =
          listCost (pre ++ (b, w1) :: (b, w2) :: suf) v := by
        rw [listCost_append, listCost_append]
        have hpre : listCost pre (setAt (pre.length + 1) (v pre.length) v) = listCost pre v := by
          apply listCost_congr_lt
          intro j hj; simp [setAt, show j ≠ pre.length + 1 by omega]
        rw [hpre]
        dsimp only [listCost]
        have hsuf : listCost suf (fun t => setAt (pre.length + 1) (v pre.length) v (t + 1 + 1 + pre.length)) =
            listCost suf (fun t => v (t + 1 + 1 + pre.length)) := by
          apply listCost_congr_lt
          intro j _; simp [setAt, show j + 1 + 1 + pre.length ≠ pre.length + 1 by omega]
        rw [hsuf]
        simp only [setAt, show 0 + pre.length = pre.length by omega,
          show 0 + 1 + pre.length = pre.length + 1 by omega,
          show pre.length ≠ pre.length + 1 by omega, ite_false, ite_true, hv0]
        rw [if_neg hv1]
        omega
      have hq := hopt _ hc'
      omega
  have drop_cost : ∀ v : ℕ → Bool, v pre.length = v (pre.length + 1) →
      listCost (pre ++ (b, w1 + w2) :: suf) (dropAt pre.length v) =
      listCost (pre ++ (b, w1) :: (b, w2) :: suf) v := by
    intro v hv
    rw [listCost_append, listCost_append]
    congr 1
    · apply listCost_congr_lt
      intro j hj; simp [dropAt, show j ≤ pre.length by omega]
    · dsimp only [listCost]
      have hsuf : listCost suf (fun t => dropAt pre.length v (t + 1 + pre.length)) =
          listCost suf (fun t => v (t + 1 + 1 + pre.length)) := by
        apply listCost_congr_lt
        intro j _
        have hgt : pre.length < j + 1 + pre.length := by omega
        have hadd : j + 1 + pre.length + 1 = j + 1 + 1 + pre.length := by omega
        simp [dropAt, Nat.not_le_of_gt hgt, hadd]
      rw [hsuf]
      simp only [dropAt, show 0 + pre.length ≤ pre.length by omega, ite_true,
        show 0 + pre.length = pre.length by omega,
        show 0 + 1 + pre.length = pre.length + 1 by omega, ← hv]
      by_cases hb : v pre.length = b <;> simp [hb] <;> omega
  intro j hj
  rcases lt_trichotomy j pre.length with hlt | heqj | hgt
  · obtain ⟨v, hvc, hvcost, hvp⟩ := hdel j (by simp; omega)
    have hveq := heq_opt v hvc hvcost
    refine ⟨dropAt pre.length v, ?_, ?_, ?_⟩
    · have hlen : (pre ++ (b, w1 + w2) :: suf).length =
          (pre ++ (b, w1) :: (b, w2) :: suf).length - 1 := by simp
      rw [hlen, changesNat_dropAt _ _ _ (by simp) hveq]
      exact hvc
    · rw [drop_cost v hveq, hvcost]
    · have hd : dropAt pre.length v j = v j := by simp [dropAt, show j ≤ pre.length by omega]
      have hg : (pre ++ (b, w1 + w2) :: suf).getD j (false, 0) =
          (pre ++ (b, w1) :: (b, w2) :: suf).getD j (false, 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hd, hg]; exact hvp
  · subst heqj
    obtain ⟨v, hvc, hvcost, hvp⟩ := hdel pre.length (by simp)
    have hveq := heq_opt v hvc hvcost
    refine ⟨dropAt pre.length v, ?_, ?_, ?_⟩
    · have hlen : (pre ++ (b, w1 + w2) :: suf).length =
          (pre ++ (b, w1) :: (b, w2) :: suf).length - 1 := by simp
      rw [hlen, changesNat_dropAt _ _ _ (by simp) hveq]
      exact hvc
    · rw [drop_cost v hveq, hvcost]
    · have hd : dropAt pre.length v pre.length = v pre.length := by simp [dropAt]
      have hg1 : (pre ++ (b, w1 + w2) :: suf).getD pre.length (false, 0) = (b, w1 + w2) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      have hg2 : (pre ++ (b, w1) :: (b, w2) :: suf).getD pre.length (false, 0) = (b, w1) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      rw [hd, hg1]
      rw [hg2] at hvp
      exact hvp
  · obtain ⟨v, hvc, hvcost, hvp⟩ := hdel (j + 1) (by simp at hj ⊢; omega)
    have hveq := heq_opt v hvc hvcost
    refine ⟨dropAt pre.length v, ?_, ?_, ?_⟩
    · have hlen : (pre ++ (b, w1 + w2) :: suf).length =
          (pre ++ (b, w1) :: (b, w2) :: suf).length - 1 := by simp
      rw [hlen, changesNat_dropAt _ _ _ (by simp) hveq]
      exact hvc
    · rw [drop_cost v hveq, hvcost]
    · have hd : dropAt pre.length v j = v (j + 1) := by
        simp [dropAt, show ¬ j ≤ pre.length by omega]
      obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + 1 + k := ⟨j - pre.length - 1, by omega⟩
      have hg1 : (pre ++ (b, w1 + w2) :: suf).getD (pre.length + 1 + k) (false, 0) =
          suf.getD k (false, 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        have : pre.length + 1 + k - pre.length = k + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      have hg2 : (pre ++ (b, w1) :: (b, w2) :: suf).getD (pre.length + 1 + k + 1) (false, 0) =
          suf.getD k (false, 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        have : pre.length + 1 + k + 1 - pre.length = k + 2 := by omega
        rw [this, List.getElem?_cons_succ, List.getElem?_cons_succ]
      rw [hd, hg1]
      rw [hg2] at hvp
      exact hvp

theorem reduce_to_alternating (n : ℕ) (L : List (Bool × ℕ)) (hlen : L.length ≤ n)
    (hpos : ∀ x ∈ L, 0 < x.2) (K q : ℕ) (hopt : OptL L K q) (hdel : DelMinL L K q) :
    ∃ A : List (Bool × ℕ), listSum A = listSum L ∧ (∀ x ∈ A, 0 < x.2) ∧
      (∀ j, j + 1 < A.length → (A.getD j (false, 0)).1 ≠ (A.getD (j + 1) (false, 0)).1) ∧
      OptL A K q ∧ DelMinL A K q := by
  induction n generalizing L with
  | zero =>
    have h0 : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst h0
    exact ⟨[], rfl, hpos, by simp, hopt, hdel⟩
  | succ n ih =>
    by_cases halt : ∀ j, j + 1 < L.length → (L.getD j (false, 0)).1 ≠ (L.getD (j + 1) (false, 0)).1
    · exact ⟨L, rfl, hpos, halt, hopt, hdel⟩
    · push_neg at halt
      obtain ⟨k, hk, heqb⟩ := halt
      let pre := L.take k
      let suf := L.drop (k + 2)
      let x1 := L.getD k (false, 0)
      let x2 := L.getD (k + 1) (false, 0)
      have hpre : pre.length = k := List.length_take_of_le (by omega)
      have hsplit : L = pre ++ x1 :: x2 :: suf := by
        apply List.ext_getElem
        · simp [pre, suf, hpre]; omega
        · intro j hj1 hj2
          rcases lt_trichotomy j k with h1 | rfl | h2
          · rw [List.getElem_append_left (by omega)]
            simp [pre]
          · rw [List.getElem_append_right (by omega)]
            simp only [hpre, Nat.sub_self, List.getElem_cons_zero, x1]
            rw [List.getD_eq_getElem _ _ (by omega)]
          · rw [List.getElem_append_right (by omega)]
            simp only [hpre]
            rcases eq_or_lt_of_le (show k + 1 ≤ j by omega) with rfl | h3
            · simp only [Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, x2]
              rw [List.getD_eq_getElem _ _ hk]
            · have hidx : j - k = (j - (k + 2)) + 2 := by omega
              have hj2' : j - k < (x1 :: x2 :: suf).length := by
                simp only [List.length_cons, suf, List.length_drop]; omega
              have hj_eq : j = k + 2 + (j - (k + 2)) := by omega
              have hget : ∀ (xs : List (Bool × ℕ)) {i1 i2} (a1 : i1 < xs.length) (a2 : i2 < xs.length),
                  i1 = i2 → xs[i1]'a1 = xs[i2]'a2 := by rintro xs i1 _ a1 a2 rfl; rfl
              calc L[j] = suf[j - (k + 2)]'(by simp only [suf, List.length_drop]; omega) := by
                      simp only [suf, List.getElem_drop]
                      exact hget L _ _ hj_eq
                _ = (x1 :: x2 :: suf)[(j - (k + 2)) + 2]'(by rw [← hidx]; exact hj2') := by
                      rw [List.getElem_cons_succ, List.getElem_cons_succ]
                _ = (x1 :: x2 :: suf)[j - k]'hj2' := by
                      exact hget (x1 :: x2 :: suf) _ _ hidx.symm
      change x1.1 = x2.1 at heqb
      rcases hx1 : x1 with ⟨b1, w1⟩
      rcases hx2 : x2 with ⟨b2, w2⟩
      rw [hx1, hx2] at heqb hsplit
      dsimp only at heqb
      subst heqb
      have hw1 : 0 < w1 := hpos (b1, w1) (by rw [hsplit]; simp)
      have hw2 : 0 < w2 := hpos (b1, w2) (by rw [hsplit]; simp)
      let L' := pre ++ (b1, w1 + w2) :: suf
      have hlen' : L'.length ≤ n := by
        have : L'.length + 1 = L.length := by rw [hsplit]; simp [L']; omega
        omega
      have hsum' : listSum L' = listSum L := by
        rw [hsplit]
        simp [listSum, L', List.map_append, List.sum_append, Nat.add_assoc]
      have hpos' : ∀ x ∈ L', 0 < x.2 := by
        intro x hx
        simp only [L', List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact hpos x (by rw [hsplit]; simp [hx])
        · simp only; omega
        · exact hpos x (by rw [hsplit]; simp [hx])
      have hopt' : OptL L' K q := mergeAt_opt pre suf b1 w1 w2 K q (by rwa [← hsplit])
      have hdel' : DelMinL L' K q := mergeAt_delMin pre suf b1 w1 w2 K q hw1 hw2
        (by rwa [← hsplit]) (by rwa [← hsplit])
      obtain ⟨A, hsA, hpA, haA, hoA, hdA⟩ := ih L' hlen' hpos' hopt' hdel'
      exact ⟨A, by rw [hsA, hsum'], hpA, haA, hoA, hdA⟩

def costAlt (r : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool) : ℕ :=
  ∑ j ∈ Finset.range r, if w j = decide (j % 2 = 0) then 0 else a j

theorem costAlt_succ (r : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool) :
    costAlt (r + 1) a w = costAlt r a w + (if w r = decide (r % 2 = 0) then 0 else a r) := by
  unfold costAlt
  rw [Finset.sum_range_succ]

def seqE (a : ℕ → ℕ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range r, if j % 2 = 0 then (a j : ℤ) else 0

def seqO (a : ℕ → ℕ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range r, if j % 2 = 1 then (a j : ℤ) else 0

def seqD (a : ℕ → ℕ) (r : ℕ) : ℤ := seqE a r - seqO a r

theorem seqE_zero (a : ℕ → ℕ) : seqE a 0 = 0 := by simp [seqE]
theorem seqO_zero (a : ℕ → ℕ) : seqO a 0 = 0 := by simp [seqO]
theorem seqD_zero (a : ℕ → ℕ) : seqD a 0 = 0 := by simp [seqD, seqE, seqO]

theorem seqE_succ (a : ℕ → ℕ) (r : ℕ) :
    seqE a (r + 1) = seqE a r + if r % 2 = 0 then (a r : ℤ) else 0 := by
  unfold seqE; rw [Finset.sum_range_succ]

theorem seqO_succ (a : ℕ → ℕ) (r : ℕ) :
    seqO a (r + 1) = seqO a r + if r % 2 = 1 then (a r : ℤ) else 0 := by
  unfold seqO; rw [Finset.sum_range_succ]

theorem seqD_succ (a : ℕ → ℕ) (r : ℕ) :
    seqD a (r + 1) = seqD a r + if r % 2 = 0 then (a r : ℤ) else -(a r : ℤ) := by
  unfold seqD
  rw [seqE_succ, seqO_succ]
  rcases Nat.mod_two_eq_zero_or_one r with h | h <;> simp [h] <;> omega

theorem seqE_add_seqO (a : ℕ → ℕ) (r : ℕ) :
    seqE a r + seqO a r = (∑ j ∈ Finset.range r, (a j : ℤ)) := by
  induction r with
  | zero => simp [seqE, seqO]
  | succ r ih =>
    rw [seqE_succ, seqO_succ, Finset.sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one r with h | h <;> simp [h] <;> omega

theorem seqE_mono (a : ℕ → ℕ) {r s : ℕ} (hrs : r ≤ s) : seqE a r ≤ seqE a s := by
  unfold seqE
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrs)
  intro j _ _; split_ifs <;> omega

theorem seqO_mono (a : ℕ → ℕ) {r s : ℕ} (hrs : r ≤ s) : seqO a r ≤ seqO a s := by
  unfold seqO
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrs)
  intro j _ _; split_ifs <;> omega

theorem costAlt_const (r : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool) (c : Bool)
    (hc : ∀ j < r, w j = c) :
    (costAlt r a w : ℤ) = if c then seqO a r else seqE a r := by
  induction r with
  | zero => simp [costAlt, seqE, seqO]
  | succ r ih =>
    rw [costAlt_succ, Nat.cast_add, ih (fun j hj => hc j (by omega))]
    rw [hc r (by omega), seqE_succ, seqO_succ]
    by_cases hr : r % 2 = 0
    · have hr1 : r % 2 ≠ 1 := by omega
      cases c <;> simp [hr, hr1] <;> omega
    · have hr1 : r % 2 = 1 := by omega
      cases c <;> simp [hr, hr1] <;> omega

theorem costAlt_sub_const (s r : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool) (c : Bool)
    (hsr : s ≤ r) (hc : ∀ j, s ≤ j → j < r → w j = c) :
    (costAlt r a w : ℤ) = (costAlt s a w : ℤ) + (if c then seqO a r - seqO a s else seqE a r - seqE a s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsr
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, costAlt_succ, Nat.cast_add, ih (by omega) (fun j h1 h2 => hc j h1 (by omega))]
    rw [hc (s + d) (by omega) (by omega), seqE_succ, seqO_succ]
    by_cases hr : (s + d) % 2 = 0
    · have hr1 : (s + d) % 2 ≠ 1 := by omega
      cases c <;> simp [hr, hr1] <;> omega
    · have hr1 : (s + d) % 2 = 1 := by omega
      cases c <;> simp [hr, hr1] <;> omega

theorem seqE_diff_le_costAlt (v u m : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool)
    (hvu : v ≤ u) (hum : u ≤ m) (hw : ∀ j, v ≤ j → j < u → w j = false) :
    seqE a u - seqE a v ≤ (costAlt m a w : ℤ) := by
  have hsub : seqE a u - seqE a v =
      ∑ j ∈ Finset.Ico v u, if j % 2 = 0 then (a j : ℤ) else 0 := by
    unfold seqE
    have hr : Finset.range u = Finset.range v ∪ Finset.Ico v u := by
      ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
    rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
    omega
  rw [hsub]
  have hsub_m : (∑ j ∈ Finset.Ico v u, if j % 2 = 0 then (a j : ℤ) else 0) ≤
      (∑ j ∈ Finset.range m, if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
    calc (∑ j ∈ Finset.Ico v u, if j % 2 = 0 then (a j : ℤ) else 0)
        ≤ ∑ j ∈ Finset.Ico v u, (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [hw j hj.1 hj.2]
          by_cases h : j % 2 = 0 <;> simp [h]
      _ ≤ ∑ j ∈ Finset.range m, (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]; omega
          · intro j _ _; split_ifs <;> omega
  simpa [costAlt] using hsub_m

theorem seqO_diff_le_costAlt (u v m : ℕ) (a : ℕ → ℕ) (w : ℕ → Bool)
    (huv : u ≤ v) (hvm : v ≤ m) (hw : ∀ j, u ≤ j → j < v → w j = true) :
    seqO a v - seqO a u ≤ (costAlt m a w : ℤ) := by
  have hsub : seqO a v - seqO a u =
      ∑ j ∈ Finset.Ico u v, if j % 2 = 1 then (a j : ℤ) else 0 := by
    unfold seqO
    have hr : Finset.range v = Finset.range u ∪ Finset.Ico u v := by
      ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
    rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
    omega
  rw [hsub]
  have hsub_m : (∑ j ∈ Finset.Ico u v, if j % 2 = 1 then (a j : ℤ) else 0) ≤
      (∑ j ∈ Finset.range m, if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
    calc (∑ j ∈ Finset.Ico u v, if j % 2 = 1 then (a j : ℤ) else 0)
        ≤ ∑ j ∈ Finset.Ico u v, (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [hw j hj.1 hj.2]
          by_cases h : j % 2 = 0
          · have h1 : j % 2 ≠ 1 := by omega
            simp [h, h1]
          · have h1 : j % 2 = 1 := by omega
            simp [h, h1]
      _ ≤ ∑ j ∈ Finset.range m, (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]; omega
          · intro j _ _; split_ifs <;> omega
  simpa [costAlt] using hsub_m

def endBit (k : ℕ) (b : Bool) : Bool := if k % 2 = 0 then b else !b

theorem endBit_succ (k : ℕ) (b : Bool) : endBit (k + 1) b = !(endBit k b) := by
  unfold endBit
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, show (k + 1) % 2 = 1 - k % 2 by omega]

theorem endBit_neg (k : ℕ) (b : Bool) : endBit k (!b) = !(endBit k b) := by
  unfold endBit; split_ifs <;> simp

def baseCost (a : ℕ → ℕ) (k : ℕ) (b : Bool) (r : ℕ) : ℤ :=
  if endBit k b then seqO a r else seqE a r

theorem baseCost_diff (a : ℕ → ℕ) (k : ℕ) (b : Bool) (s : ℕ) :
    baseCost a (k + 1) b s - baseCost a k b s =
      if endBit k b then seqD a s else -(seqD a s) := by
  unfold baseCost
  rw [endBit_succ]
  cases endBit k b <;> simp [seqD] <;> omega

def altM (a : ℕ → ℕ) : ℕ → Bool → ℕ → ℤ
  | 0, _, _ => 0
  | k + 1, b, r =>
      ((Finset.range (r + 1)).image
        (fun s => (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s)).max'
        (Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (by omega)⟩)

theorem altM_nonneg (a : ℕ → ℕ) (k : ℕ) (b : Bool) (r : ℕ) : 0 ≤ altM a k b r := by
  induction k generalizing r with
  | zero => simp [altM]
  | succ k ih =>
    unfold altM
    have h0 : (0 : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.2 (by omega)
    have hle := Finset.le_max' ((Finset.range (r + 1)).image
      (fun s => (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s))
      ((if endBit k b then seqD a 0 else -(seqD a 0)) + altM a k b 0)
      (Finset.mem_image_of_mem _ h0)
    have hdz : seqD a 0 = 0 := seqD_zero a
    simp only [hdz, neg_zero, ite_self, zero_add] at hle
    exact le_trans (ih 0) hle

theorem altM_mono (a : ℕ → ℕ) (k : ℕ) (b : Bool) {s r : ℕ} (hsr : s ≤ r) :
    altM a k b s ≤ altM a k b r := by
  cases k with
  | zero => simp [altM]
  | succ k =>
    unfold altM
    apply Finset.max'_le
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_range] at ht
    have htr : t ∈ Finset.range (r + 1) := Finset.mem_range.2 (by omega)
    exact Finset.le_max' ((Finset.range (r + 1)).image
      (fun s => (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s)) _
      (Finset.mem_image_of_mem _ htr)

theorem altM_le_step (a : ℕ → ℕ) (k : ℕ) (b : Bool) (s r : ℕ) (hsr : s ≤ r) :
    (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s ≤ altM a (k + 1) b r := by
  conv_rhs => unfold altM
  have hs_mem : s ∈ Finset.range (r + 1) := Finset.mem_range.2 (by omega)
  exact Finset.le_max' ((Finset.range (r + 1)).image
    (fun s => (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s)) _
    (Finset.mem_image_of_mem _ hs_mem)

theorem altM_pair_bound (a : ℕ → ℕ) (k m : ℕ) (mx mn : ℤ)
    (hmx : ∀ s ≤ m, seqD a s ≤ mx) (hmn : ∀ s ≤ m, mn ≤ seqD a s) :
    altM a k false m + altM a k true m ≤ (k : ℤ) * (mx - mn) := by
  induction k with
  | zero => simp [altM]
  | succ k ih =>
    let F : Bool → Finset ℤ := fun b => (Finset.range (m + 1)).image
      (fun s => (if endBit k b then seqD a s else -(seqD a s)) + altM a k b s)
    have hne : ∀ b : Bool, (F b).Nonempty :=
      fun _ => Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (by omega)⟩
    obtain ⟨s0, hs0, hy0eq⟩ := Finset.mem_image.1 (Finset.max'_mem (F false) (hne false))
    obtain ⟨s1, hs1, hy1eq⟩ := Finset.mem_image.1 (Finset.max'_mem (F true) (hne true))
    rw [Finset.mem_range] at hs0 hs1
    have e0 : altM a (k + 1) false m =
        (if endBit k false then seqD a s0 else -(seqD a s0)) + altM a k false s0 := hy0eq.symm
    have e1 : altM a (k + 1) true m =
        (if endBit k true then seqD a s1 else -(seqD a s1)) + altM a k true s1 := hy1eq.symm
    have hm0 := altM_mono a k false (show s0 ≤ m by omega)
    have hm1 := altM_mono a k true (show s1 ≤ m by omega)
    have hdiff : (if endBit k false then seqD a s0 else -(seqD a s0)) +
        (if endBit k true then seqD a s1 else -(seqD a s1)) ≤ mx - mn := by
      have hxs0 := hmx s0 (by omega)
      have hns0 := hmn s0 (by omega)
      have hxs1 := hmx s1 (by omega)
      have hns1 := hmn s1 (by omega)
      rw [show true = !false from rfl, endBit_neg]
      cases endBit k false <;> simp <;> omega
    rw [e0, e1, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith [ih, hm0, hm1, hdiff]

theorem baseCost_sub_altM_le (a : ℕ → ℕ) (k : ℕ) :
    ∀ (r : ℕ) (b : Bool) (w : ℕ → Bool), 1 ≤ r → changesNat r w ≤ k → w 0 = b →
      baseCost a k b r - altM a k b r ≤ (costAlt r a w : ℤ) := by
  induction k with
  | zero =>
    intro r b w hr hchg hw0
    have h0 : changesNat r w = 0 := by omega
    have hconst : ∀ j < r, w j = b := fun j hj => by rw [changesNat_const w h0 j hj, hw0]
    rw [costAlt_const r a w b hconst]
    simp [baseCost, altM, endBit]
  | succ k ih =>
    intro r b w hr hchg hw0
    by_cases he : w (r - 1) = endBit k b
    · have hpar' : changesNat r w % 2 = k % 2 := by
        unfold endBit at he
        by_cases hk : k % 2 = 0
        · simp [hk] at he
          have : w 0 = w (r - 1) := by rw [hw0, he]
          have := (changesNat_parity hr w).2 this
          omega
        · simp [hk] at he
          have : w 0 ≠ w (r - 1) := by rw [hw0, he]; cases b <;> simp
          have hnp : ¬ (changesNat r w % 2 = 0) := by rw [changesNat_parity hr w]; exact this
          omega
      have hchg' : changesNat r w ≤ k := by omega
      have hih := ih r b w hr hchg' hw0
      have hm := altM_le_step a k b r r (le_refl r)
      have hdiff := baseCost_diff a k b r
      omega
    · have he1 : w (r - 1) = endBit (k + 1) b := by
        rw [endBit_succ]
        cases hwr : w (r - 1) <;> cases heb : endBit k b <;> simp_all
      by_cases hex : ∃ j ∈ Finset.range (r - 1), w j ≠ w (j + 1)
      · let jumps := (Finset.range (r - 1)).filter (fun j => w j ≠ w (j + 1))
        have hjne : jumps.Nonempty := by
          obtain ⟨j, hj1, hj2⟩ := hex
          exact ⟨j, Finset.mem_filter.2 ⟨hj1, hj2⟩⟩
        let s0 := jumps.max' hjne
        have hs0m : s0 ∈ jumps := Finset.max'_mem jumps hjne
        have hs0r : s0 < r - 1 := (Finset.mem_range.1 (Finset.mem_filter.1 hs0m).1)
        let s := s0 + 1
        have hs1 : 1 ≤ s := by omega
        have hconst_tail : ∀ j, s ≤ j → j < r → w j = endBit (k + 1) b := by
          intro j hj1 hj2
          rw [← he1]
          suffices ∀ d, j + d ≤ r - 1 → w j = w (j + d) by
            have := this (r - 1 - j) (by omega)
            rwa [show j + (r - 1 - j) = r - 1 by omega] at this
          intro d
          induction d with
          | zero => intro _; rfl
          | succ d ihd =>
            intro hd
            rw [ihd (by omega), ← Nat.add_assoc]
            have hnot : j + d ∉ jumps := by
              intro hm
              have hle := Finset.le_max' jumps (j + d) hm
              change j + d ≤ s0 at hle
              omega
            simp only [jumps, Finset.mem_filter, Finset.mem_range, not_and, not_not] at hnot
            exact hnot (by omega)
        have hchg_s : changesNat s w + 1 ≤ changesNat r w := by
          unfold changesNat
          have hsub : (Finset.range (s - 1)).filter (fun j => w j ≠ w (j + 1)) ⊆
              jumps.erase s0 := by
            intro j hj
            rw [Finset.mem_filter, Finset.mem_range] at hj
            exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hj.2⟩⟩
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hs0m] at hcard
          have hr1 : 1 ≤ jumps.card := Finset.card_pos.2 hjne
          change ((Finset.range (s - 1)).filter (fun j => w j ≠ w (j + 1))).card + 1 ≤ jumps.card
          omega
        have hih := ih s b w hs1 (by omega) hw0
        have htail := costAlt_sub_const s r a w (endBit (k + 1) b) (by omega) hconst_tail
        have hm := altM_le_step a k b s r (by omega)
        have hdiff := baseCost_diff a k b s
        have hsucc := endBit_succ k b
        unfold baseCost at hdiff hih ⊢
        unfold seqD at hdiff hm
        rw [htail]
        cases hcb : endBit k b <;>
          simp only [hsucc, hcb, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self_iff_true,
            ite_true, ite_false] at hdiff htail hih hm ⊢ <;> omega
      · have h0 : changesNat r w = 0 := by
          unfold changesNat
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj hne
          exact hex ⟨j, hj, hne⟩
        have hconst : ∀ j < r, w j = endBit (k + 1) b := fun j hj => by
          rw [changesNat_const w h0 j hj, ← changesNat_const w h0 (r - 1) (by omega), he1]
        rw [costAlt_const r a w (endBit (k + 1) b) hconst]
        have hnn := altM_nonneg a (k + 1) b r
        unfold baseCost
        omega

theorem changesNat_flat_left (m v s : ℕ) (w : ℕ → Bool) (c : Bool)
    (hvs : v < s) (hsm : s < m) (hws : w s = c) (hwv : ∀ j, v ≤ j → j < s → w j = !c) :
    changesNat m (fun t => if v ≤ t ∧ t < s then c else w t) ≤ changesNat m w := by
  let w' : ℕ → Bool := fun t => if v ≤ t ∧ t < s then c else w t
  unfold changesNat
  rw [Finset.card_filter, Finset.card_filter]
  have hs1 : s - 1 ∈ Finset.range (m - 1) := Finset.mem_range.2 (by omega)
  have hdiff_s : (if w (s - 1) ≠ w s then 1 else 0) = 1 := by
    rw [hwv (s - 1) (by omega) (by omega), hws]; cases c <;> simp
  have hdiff_s' : (if w' (s - 1) ≠ w' s then 1 else 0) = 0 := by
    have h1 : w' (s - 1) = c := by simp [w', show v ≤ s - 1 ∧ s - 1 < s by omega]
    have h2 : w' s = c := by simp [w', hws]
    simp [h1, h2]
  by_cases hv0 : v = 0
  · subst hv0
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjs : j < s - 1
    · have hj1 : j < s := by omega
      have hj2 : j + 1 < s := by omega
      simp [hj1, hj2]
    · by_cases hjeq : j = s - 1
      · subst hjeq
        rw [show s - 1 + 1 = s by omega, hdiff_s, hdiff_s']
        omega
      · have hj1 : ¬ j < s := by omega
        have hj2 : ¬ j + 1 < s := by omega
        simp [hj1, hj2]
  · have hv1 : v - 1 ∈ Finset.range (m - 1) := Finset.mem_range.2 (by omega)
    have hne_vs : v - 1 ≠ s - 1 := by omega
    have hsub : ∑ j ∈ ((Finset.range (m - 1)).erase (s - 1)).erase (v - 1),
        (if w' j ≠ w' (j + 1) then 1 else 0) ≤
        ∑ j ∈ ((Finset.range (m - 1)).erase (s - 1)).erase (v - 1),
        (if w j ≠ w (j + 1) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_range] at hj
      rcases lt_or_ge j (v - 1) with h1 | h1
      · have ha : w' j = w j := by simp [w', show ¬ v ≤ j by omega]
        have hb : w' (j + 1) = w (j + 1) := by simp [w', show ¬ v ≤ j + 1 by omega]
        simp [ha, hb]
      · rcases lt_or_ge j (s - 1) with h2 | h2
        · have ha : w' j = c := by simp [w', show v ≤ j ∧ j < s by omega]
          have hb : w' (j + 1) = c := by simp [w', show v ≤ j + 1 ∧ j + 1 < s by omega]
          simp [ha, hb]
        · have ha : w' j = w j := by simp [w', show ¬ j < s by omega]
          have hb : w' (j + 1) = w (j + 1) := by simp [w', show ¬ j + 1 < s by omega]
          simp [ha, hb]
    have hs_eq : s - 1 + 1 = s := by omega
    have hsplit1 := Finset.add_sum_erase (Finset.range (m - 1)) (fun j => if w' j ≠ w' (j + 1) then 1 else 0) hs1
    have hsplit2 := Finset.add_sum_erase ((Finset.range (m - 1)).erase (s - 1))
      (fun j => if w' j ≠ w' (j + 1) then 1 else 0) (Finset.mem_erase.2 ⟨hne_vs, hv1⟩)
    have hsplit3 := Finset.add_sum_erase (Finset.range (m - 1)) (fun j => if w j ≠ w (j + 1) then 1 else 0) hs1
    have hsplit4 := Finset.add_sum_erase ((Finset.range (m - 1)).erase (s - 1))
      (fun j => if w j ≠ w (j + 1) then 1 else 0) (Finset.mem_erase.2 ⟨hne_vs, hv1⟩)
    rw [hs_eq, hdiff_s'] at hsplit1
    rw [hs_eq, hdiff_s] at hsplit3
    have hbdv : (if w' (v - 1) ≠ w' (v - 1 + 1) then 1 else 0) ≤ 1 := by split_ifs <;> omega
    change ∑ j ∈ Finset.range (m - 1), (if w' j ≠ w' (j + 1) then 1 else 0) ≤
      ∑ j ∈ Finset.range (m - 1), (if w j ≠ w (j + 1) then 1 else 0)
    rw [← hsplit1, ← hsplit2, ← hsplit3, ← hsplit4]
    omega

theorem span_le_opt (m K q : ℕ) (a : ℕ → ℕ) (hm : 2 ≤ m) (ha : ∀ j < m, 0 < a j)
    (hopt : ∀ w : ℕ → Bool, changesNat m w ≤ K → q ≤ costAlt m a w)
    (hdel : ∀ j < m, ∃ w : ℕ → Bool, changesNat m w ≤ K ∧ costAlt m a w = q ∧ w j ≠ decide (j % 2 = 0)) :
    let S := (Finset.range (m + 1)).image (seqD a)
    have hSne : S.Nonempty := Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (by omega)⟩
    S.max' hSne - S.min' hSne ≤ (q : ℤ) := by
  intro S hSne
  let mx := S.max' hSne
  let mn := S.min' hSne
  let P := (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => seqD a p.1 = mx ∧ seqD a p.2 = mn)
  have hPne : P.Nonempty := by
    obtain ⟨u0, hu0, hu0e⟩ := Finset.mem_image.1 (Finset.max'_mem S hSne)
    obtain ⟨v0, hv0, hv0e⟩ := Finset.mem_image.1 (Finset.min'_mem S hSne)
    exact ⟨(u0, v0), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hu0, hv0⟩, hu0e, hv0e⟩⟩
  obtain ⟨⟨u, v⟩, hmem, hmin⟩ := Finset.exists_min_image P (fun p => Int.natAbs ((p.1 : ℤ) - p.2)) hPne
  have hmem' := Finset.mem_filter.1 hmem
  have hu_le : u ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_product.1 hmem'.1).1)
  have hv_le : v ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_product.1 hmem'.1).2)
  have hDu : seqD a u = mx := hmem'.2.1
  have hDv : seqD a v = mn := hmem'.2.2
  have hmx_all : ∀ s ≤ m, seqD a s ≤ mx := fun s hs => Finset.le_max' S _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
  have hmn_all : ∀ s ≤ m, mn ≤ seqD a s := fun s hs => Finset.min'_le S _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
  rcases lt_trichotomy v u with hvu | huv_eq | huv
  · have hv_lt : v < m := by omega
    have hveven : v % 2 = 0 := by
      by_contra hodd
      have hv1 : v % 2 = 1 := by omega
      have hsucc := seqD_succ a v
      simp only [show v % 2 ≠ 0 by omega, ite_false] at hsucc
      have hle := hmn_all (v + 1) (by omega)
      have hpos := ha v hv_lt
      omega
    obtain ⟨w, hwc, hwcost, hwp⟩ := hdel v hv_lt
    have hwv : w v = false := by
      simp only [hveven, decide_true, ne_eq] at hwp
      cases hwvc : w v <;> simp_all
    have hconst : ∀ j, v ≤ j → j < u → w j = false := by
      by_contra hnc
      push Not at hnc
      have hex : ∃ s ∈ Finset.Ico v u, w s = true := by
        obtain ⟨j, hj1, hj2, hjw⟩ := hnc
        exact ⟨j, Finset.mem_Ico.2 ⟨hj1, hj2⟩, by cases h : w j <;> simp_all⟩
      let bad := (Finset.Ico v u).filter (fun s => w s = true)
      have hbne : bad.Nonempty := by
        obtain ⟨s, hs1, hs2⟩ := hex
        exact ⟨s, Finset.mem_filter.2 ⟨hs1, hs2⟩⟩
      let s := bad.min' hbne
      have hsm : s ∈ bad := Finset.min'_mem bad hbne
      have hsr := Finset.mem_Ico.1 (Finset.mem_filter.1 hsm).1
      have hws : w s = true := (Finset.mem_filter.1 hsm).2
      have hvs : v < s := by
        rcases eq_or_lt_of_le hsr.1 with heq | h
        · rw [heq] at hwv; simp [hwv] at hws
        · exact h
      have hwprev : ∀ j, v ≤ j → j < s → w j = false := by
        intro j hj1 hj2
        by_contra hjt
        have hjb : w j = true := by cases h : w j <;> simp_all
        have hle := Finset.min'_le bad j (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hj1, by omega⟩, hjb⟩)
        change s ≤ j at hle
        omega
      let w' : ℕ → Bool := fun t => if v ≤ t ∧ t < s then true else w t
      have hwc' : changesNat m w' ≤ K :=
        le_trans (changesNat_flat_left m v s w true hvs (by omega) hws (fun j h1 h2 => by simpa using hwprev j h1 h2)) hwc
      have hcost_diff : (costAlt m a w' : ℤ) - (costAlt m a w : ℤ) = seqD a v - seqD a s := by
        have hm1 : (costAlt m a w' : ℤ) = ∑ j ∈ Finset.range m, if w' j = decide (j % 2 = 0) then 0 else (a j : ℤ) := by
          simp [costAlt]
        have hm2 : (costAlt m a w : ℤ) = ∑ j ∈ Finset.range m, if w j = decide (j % 2 = 0) then 0 else (a j : ℤ) := by
          simp [costAlt]
        have hd_sum : (costAlt m a w' : ℤ) - (costAlt m a w : ℤ) =
            ∑ j ∈ Finset.Ico v s, (if j % 2 = 1 then (a j : ℤ) else 0) -
            ∑ j ∈ Finset.Ico v s, (if j % 2 = 0 then (a j : ℤ) else 0) := by
          rw [hm1, hm2, ← Finset.sum_sub_distrib]
          have hsub_ico : ∀ j ∈ Finset.range m,
              (if w' j = decide (j % 2 = 0) then 0 else (a j : ℤ)) -
              (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) =
              if j ∈ Finset.Ico v s then (if j % 2 = 1 then (a j : ℤ) else 0) -
                (if j % 2 = 0 then (a j : ℤ) else 0) else 0 := by
            intro j _
            by_cases hj : v ≤ j ∧ j < s
            · have hw'j : w' j = true := if_pos hj
              have hwj : w j = false := hwprev j hj.1 hj.2
              have hm_ico : j ∈ Finset.Ico v s := Finset.mem_Ico.2 hj
              rw [if_pos hm_ico]
              simp only [hw'j, hwj]
              by_cases hje : j % 2 = 0
              · have hj1 : j % 2 ≠ 1 := by omega
                simp [hje, hj1]
              · have hj1 : j % 2 = 1 := by omega
                simp [hje, hj1]
            · have hw'j : w' j = w j := if_neg hj
              have hm_ico : j ∉ Finset.Ico v s := by rw [Finset.mem_Ico]; exact hj
              rw [if_neg hm_ico, hw'j, sub_self]
          rw [Finset.sum_congr rfl hsub_ico, ← Finset.sum_filter]
          have hf : (Finset.range m).filter (fun j => j ∈ Finset.Ico v s) = Finset.Ico v s := by
            ext j; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hf, Finset.sum_sub_distrib]
        have hE : seqE a s - seqE a v = ∑ j ∈ Finset.Ico v s, if j % 2 = 0 then (a j : ℤ) else 0 := by
          unfold seqE
          have hr : Finset.range s = Finset.range v ∪ Finset.Ico v s := by
            ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
          omega
        have hO : seqO a s - seqO a v = ∑ j ∈ Finset.Ico v s, if j % 2 = 1 then (a j : ℤ) else 0 := by
          unfold seqO
          have hr : Finset.range s = Finset.range v ∪ Finset.Ico v s := by
            ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
          omega
        rw [hd_sum, ← hO, ← hE]
        unfold seqD; omega
      have hq' : (q : ℤ) ≤ (costAlt m a w' : ℤ) := by exact_mod_cast hopt w' hwc'
      have hDs_le : seqD a s ≤ mn := by omega
      have hDs_ge := hmn_all s (by omega)
      have hDs : seqD a s = mn := le_antisymm hDs_le hDs_ge
      have hus_mem : (u, s) ∈ P := Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩, hDu, hDs⟩
      have hle_min := hmin (u, s) hus_mem
      omega
    have hE := seqE_diff_le_costAlt v u m a w (by omega) hu_le hconst
    have hO : seqO a v ≤ seqO a u := seqO_mono a (by omega)
    unfold seqD at hDu hDv
    omega
  · show mx - mn ≤ (q : ℤ)
    rw [← hDu, ← hDv, huv_eq]
    omega
  · have hu_lt : u < m := by omega
    have huodd : u % 2 = 1 := by
      by_contra heven
      have hu0 : u % 2 = 0 := by omega
      have hsucc := seqD_succ a u
      simp only [hu0, ite_true] at hsucc
      have hle := hmx_all (u + 1) (by omega)
      have hpos := ha u hu_lt
      omega
    obtain ⟨w, hwc, hwcost, hwp⟩ := hdel u hu_lt
    have hwu : w u = true := by
      simp only [show u % 2 ≠ 0 by omega, decide_false, ne_eq] at hwp
      cases hwuc : w u <;> simp_all
    have hconst : ∀ j, u ≤ j → j < v → w j = true := by
      by_contra hnc
      push Not at hnc
      have hex : ∃ s ∈ Finset.Ico u v, w s = false := by
        obtain ⟨j, hj1, hj2, hjw⟩ := hnc
        exact ⟨j, Finset.mem_Ico.2 ⟨hj1, hj2⟩, by cases h : w j <;> simp_all⟩
      let bad := (Finset.Ico u v).filter (fun s => w s = false)
      have hbne : bad.Nonempty := by
        obtain ⟨s, hs1, hs2⟩ := hex
        exact ⟨s, Finset.mem_filter.2 ⟨hs1, hs2⟩⟩
      let s := bad.min' hbne
      have hsm : s ∈ bad := Finset.min'_mem bad hbne
      have hsr := Finset.mem_Ico.1 (Finset.mem_filter.1 hsm).1
      have hws : w s = false := (Finset.mem_filter.1 hsm).2
      have hus : u < s := by
        rcases eq_or_lt_of_le hsr.1 with heq | h
        · rw [heq] at hwu; simp [hwu] at hws
        · exact h
      have hwprev : ∀ j, u ≤ j → j < s → w j = true := by
        intro j hj1 hj2
        by_contra hjt
        have hjb : w j = false := by cases h : w j <;> simp_all
        have hle := Finset.min'_le bad j (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hj1, by omega⟩, hjb⟩)
        change s ≤ j at hle
        omega
      let w' : ℕ → Bool := fun t => if u ≤ t ∧ t < s then false else w t
      have hwc' : changesNat m w' ≤ K :=
        le_trans (changesNat_flat_left m u s w false hus (by omega) hws (fun j h1 h2 => by simpa using hwprev j h1 h2)) hwc
      have hcost_diff : (costAlt m a w' : ℤ) - (costAlt m a w : ℤ) = seqD a s - seqD a u := by
        have hm1 : (costAlt m a w' : ℤ) = ∑ j ∈ Finset.range m, if w' j = decide (j % 2 = 0) then 0 else (a j : ℤ) := by
          simp [costAlt]
        have hm2 : (costAlt m a w : ℤ) = ∑ j ∈ Finset.range m, if w j = decide (j % 2 = 0) then 0 else (a j : ℤ) := by
          simp [costAlt]
        have hd_sum : (costAlt m a w' : ℤ) - (costAlt m a w : ℤ) =
            ∑ j ∈ Finset.Ico u s, (if j % 2 = 0 then (a j : ℤ) else 0) -
            ∑ j ∈ Finset.Ico u s, (if j % 2 = 1 then (a j : ℤ) else 0) := by
          rw [hm1, hm2, ← Finset.sum_sub_distrib]
          have hsub_ico : ∀ j ∈ Finset.range m,
              (if w' j = decide (j % 2 = 0) then 0 else (a j : ℤ)) -
              (if w j = decide (j % 2 = 0) then 0 else (a j : ℤ)) =
              if j ∈ Finset.Ico u s then (if j % 2 = 0 then (a j : ℤ) else 0) -
                (if j % 2 = 1 then (a j : ℤ) else 0) else 0 := by
            intro j _
            by_cases hj : u ≤ j ∧ j < s
            · have hw'j : w' j = false := if_pos hj
              have hwj : w j = true := hwprev j hj.1 hj.2
              have hm_ico : j ∈ Finset.Ico u s := Finset.mem_Ico.2 hj
              rw [if_pos hm_ico]
              simp only [hw'j, hwj]
              by_cases hje : j % 2 = 0
              · have hj1 : j % 2 ≠ 1 := by omega
                simp [hje, hj1]
              · have hj1 : j % 2 = 1 := by omega
                simp [hje, hj1]
            · have hw'j : w' j = w j := if_neg hj
              have hm_ico : j ∉ Finset.Ico u s := by rw [Finset.mem_Ico]; exact hj
              rw [if_neg hm_ico, hw'j, sub_self]
          rw [Finset.sum_congr rfl hsub_ico, ← Finset.sum_filter]
          have hf : (Finset.range m).filter (fun j => j ∈ Finset.Ico u s) = Finset.Ico u s := by
            ext j; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hf, Finset.sum_sub_distrib]
        have hE : seqE a s - seqE a u = ∑ j ∈ Finset.Ico u s, if j % 2 = 0 then (a j : ℤ) else 0 := by
          unfold seqE
          have hr : Finset.range s = Finset.range u ∪ Finset.Ico u s := by
            ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
          omega
        have hO : seqO a s - seqO a u = ∑ j ∈ Finset.Ico u s, if j % 2 = 1 then (a j : ℤ) else 0 := by
          unfold seqO
          have hr : Finset.range s = Finset.range u ∪ Finset.Ico u s := by
            ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
          rw [hr, Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
          omega
        rw [hd_sum, ← hE, ← hO]
        unfold seqD; omega
      have hq' : (q : ℤ) ≤ (costAlt m a w' : ℤ) := by exact_mod_cast hopt w' hwc'
      have hDs_ge : mx ≤ seqD a s := by omega
      have hDs_le := hmx_all s (by omega)
      have hDs : seqD a s = mx := le_antisymm hDs_le hDs_ge
      have hsv_mem : (s, v) ∈ P := Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩, hDs, hDv⟩
      have hle_min := hmin (s, v) hsv_mem
      omega
    have hO := seqO_diff_le_costAlt u v m a w (by omega) hv_le hconst
    have hE : seqE a u ≤ seqE a v := seqE_mono a (by omega)
    unfold seqD at hDu hDv
    omega

theorem alt_sum_bound (m K q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℕ) (ha : ∀ j < m, 0 < a j)
    (hopt : ∀ w : ℕ → Bool, changesNat m w ≤ K → q ≤ costAlt m a w)
    (hdel : ∀ j < m, ∃ w : ℕ → Bool, changesNat m w ≤ K ∧ costAlt m a w = q ∧ w j ≠ decide (j % 2 = 0)) :
    ∑ j ∈ Finset.range m, a j ≤ (K + 2) * q := by
  have hm : 2 ≤ m := by
    by_contra hm
    have hle : m ≤ 1 := by omega
    have h0 := hopt (fun j => decide (j % 2 = 0)) (by rw [changesNat_le_one hle]; exact Nat.zero_le _)
    have hc0 : costAlt m a (fun j => decide (j % 2 = 0)) = 0 := by simp [costAlt]
    omega
  obtain ⟨w0, hw0c, hw0cost, hw0p⟩ := hdel 0 (by omega)
  have hw0_0 : w0 0 = false := by
    simp only [Nat.zero_mod, decide_true, ne_eq] at hw0p
    cases h0 : w0 0 <;> simp_all
  obtain ⟨w1, hw1c, hw1cost, hw1p⟩ := hdel 1 (by omega)
  have hw1_1 : w1 1 = true := by
    simp only [Nat.one_mod, ne_eq] at hw1p
    cases h1 : w1 1 <;> simp_all
  have hw1_0 : w1 0 = true := by
    by_contra hf
    have hwf : w1 0 = false := by cases h0 : w1 0 <;> simp_all
    let w1' := setAt 0 true w1
    have hne : w1 0 ≠ w1 1 := by rw [hwf, hw1_1]; simp
    have hwc' : changesNat m w1' ≤ K := le_trans (by simpa [hw1_1] using changesNat_setAt_left m 0 w1 (by omega) hne) hw1c
    have hcost' : costAlt m a w1' + a 0 = costAlt m a w1 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      unfold costAlt
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h0' : w1' 0 = true := rfl
      have hrest : ∑ j ∈ Finset.range m', (if w1' (j + 1) = decide ((j + 1) % 2 = 0) then 0 else a (j + 1)) =
          ∑ j ∈ Finset.range m', (if w1 (j + 1) = decide ((j + 1) % 2 = 0) then 0 else a (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        simp [w1', setAt]
      rw [hrest, h0', hwf]
      simp
    have hq1 := hopt w1' hwc'
    have ha0 := ha 0 (by omega)
    omega
  have hb1 : baseCost a K true m - altM a K true m ≤ (q : ℤ) := by
    have := baseCost_sub_altM_le a K m true w1 (by omega) hw1c hw1_0
    omega
  have hb0 : baseCost a K false m - altM a K false m ≤ (q : ℤ) := by
    have := baseCost_sub_altM_le a K m false w0 (by omega) hw0c hw0_0
    omega
  let S := (Finset.range (m + 1)).image (seqD a)
  have hSne : S.Nonempty := Finset.image_nonempty.2 ⟨0, Finset.mem_range.2 (by omega)⟩
  have hspan := span_le_opt m K q a hm ha hopt hdel
  dsimp only at hspan
  have hpair := altM_pair_bound a K m (S.max' hSne) (S.min' hSne)
    (fun s hs => Finset.le_max' S _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))))
    (fun s hs => Finset.min'_le S _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))))
  have hbase_sum : baseCost a K false m + baseCost a K true m = (∑ j ∈ Finset.range m, (a j : ℤ)) := by
    unfold baseCost
    rw [show true = !false from rfl, endBit_neg]
    cases endBit K false
    · simp; rw [seqE_add_seqO]
    · simp; rw [add_comm, seqE_add_seqO]
  have htot : (∑ j ∈ Finset.range m, (a j : ℤ)) ≤ ((K : ℤ) + 2) * (q : ℤ) := by
    have hmp : altM a K false m + altM a K true m ≤ (K : ℤ) * (q : ℤ) :=
      le_trans hpair (mul_le_mul_of_nonneg_left hspan (Int.natCast_nonneg K))
    linarith
  exact_mod_cast htot

theorem alt_list_sum_bound (A : List (Bool × ℕ)) (K q : ℕ) (hq : 1 ≤ q)
    (hpos : ∀ x ∈ A, 0 < x.2)
    (halt : ∀ j, j + 1 < A.length → (A.getD j (false, 0)).1 ≠ (A.getD (j + 1) (false, 0)).1)
    (hopt : OptL A K q) (hdel : DelMinL A K q) :
    listSum A ≤ (K + 2) * q := by
  cases hA : A with
  | nil => simp [listSum]
  | cons x0 rest =>
    subst hA
    rcases x0 with ⟨z0, a0⟩
    have alt_helper : ∀ (B : List (Bool × ℕ)) (b0 : Bool),
        (B.getD 0 (false, 0)).1 = b0 →
        (∀ j, j + 1 < B.length → (B.getD j (false, 0)).1 ≠ (B.getD (j + 1) (false, 0)).1) →
        ∀ j, j < B.length → (B.getD j (false, 0)).1 = if j % 2 = 0 then b0 else !b0 := by
      intro B b0 hb0 hB j hj
      induction j with
      | zero => simpa using hb0
      | succ j ih =>
        have hlt : j < B.length := by omega
        have hstep := hB j hj
        rw [ih hlt] at hstep
        rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
        · have h1 : (j + 1) % 2 = 1 := by omega
          simp [hj0] at hstep
          simp only [h1, Nat.one_ne_zero, ite_false]
          cases hb0 : b0 <;> cases hgt : (B.getD (j + 1) (false, 0)).1 <;> simp_all
        · have h0 : (j + 1) % 2 = 0 := by omega
          simp [hj1] at hstep
          simp only [h0, ite_true]
          cases hb0 : b0 <;> cases hgt : (B.getD (j + 1) (false, 0)).1 <;> simp_all
    let B := if z0 then (z0, a0) :: rest else ((z0, a0) :: rest).map (fun x => (!x.1, x.2))
    have hB_len : B.length = ((z0, a0) :: rest).length := by cases z0 <;> simp [B]
    have hB_sum : listSum B = listSum ((z0, a0) :: rest) := by
      cases z0 <;> simp [B, listSum, List.map_map, Function.comp_def]
    have hB_pos : ∀ x ∈ B, 0 < x.2 := by
      cases hz : z0
      · intro x hx
        simp only [B, hz, Bool.false_eq_true, ite_false, List.mem_map] at hx
        obtain ⟨⟨y1, y2⟩, hy, hyeq⟩ := hx
        rcases hyeq with rfl
        exact hpos (y1, y2) (by simpa [hz] using hy)
      · simpa [B, hz] using hpos
    have hB_0 : (B.getD 0 (false, 0)).1 = true := by
      cases z0 <;> simp [B]
    have hB_alt : ∀ j, j + 1 < B.length → (B.getD j (false, 0)).1 ≠ (B.getD (j + 1) (false, 0)).1 := by
      cases z0
      · intro j hj
        have hj' : j + 1 < ((false, a0) :: rest).length := by
          simpa [B] using hj
        have hj0 : j < (((false, a0) :: rest).map (fun p => (!p.1, p.2))).length := by
          simp only [List.length_map]; exact Nat.lt_of_succ_lt hj'
        have hj1 : j + 1 < (((false, a0) :: rest).map (fun p => (!p.1, p.2))).length := by
          simp only [List.length_map]; exact hj'
        simp only [B, Bool.false_eq_true, ite_false]
        rw [List.getD_eq_getElem _ _ hj0, List.getD_eq_getElem _ _ hj1,
          List.getElem_map, List.getElem_map]
        have hne := halt j hj'
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj'] at hne
        exact fun heq => hne (Bool.not_inj heq)
      · exact halt
    have hB_opt : OptL B K q := by
      cases z0
      · intro u hu
        simp only [B, Bool.false_eq_true, ite_false] at hu ⊢
        have heq : (fun t => !(!u t)) = u := by funext t; simp
        have hcn := listCost_neg ((false, a0) :: rest) (fun t => !u t)
        rw [heq] at hcn
        rw [hcn]
        apply hopt (fun t => !u t)
        rw [changesNat_neg]
        simpa using hu
      · exact hopt
    have hB_del : DelMinL B K q := by
      cases z0
      · intro j hj
        have hj' : j < ((false, a0) :: rest).length := by
          simpa [B] using hj
        obtain ⟨u, huc, hucost, hup⟩ := hdel j hj'
        refine ⟨fun t => !u t, ?_, ?_, ?_⟩
        · rw [changesNat_neg]; simpa [B] using huc
        · simp only [B, Bool.false_eq_true, ite_false]
          rw [listCost_neg ((false, a0) :: rest) u]
          exact hucost
        · simp only [B, Bool.false_eq_true, ite_false]
          have hj0 : j < (((false, a0) :: rest).map (fun p => (!p.1, p.2))).length := by
            simp only [List.length_map]; exact hj'
          rw [List.getD_eq_getElem _ _ hj0, List.getElem_map]
          rw [List.getD_eq_getElem _ _ hj'] at hup
          exact fun heq => hup (Bool.not_inj heq)
      · exact hdel
    have hB_pat : ∀ j < B.length, (B.getD j (false, 0)).1 = decide (j % 2 = 0) := by
      intro j hj
      rw [alt_helper B true hB_0 hB_alt j hj]
      rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
    let a : ℕ → ℕ := fun j => (B.getD j (false, 0)).2
    have hcost_eq : ∀ (L0 : List (Bool × ℕ)) (off : ℕ) (u : ℕ → Bool),
        (∀ j < L0.length, (L0.getD j (false, 0)).1 = decide ((j + off) % 2 = 0)) →
        listCost L0 u = ∑ j ∈ Finset.range L0.length,
          if u j = decide ((j + off) % 2 = 0) then 0 else (L0.getD j (false, 0)).2 := by
      intro L0
      induction L0 with
      | nil => intro off u _; simp [listCost]
      | cons y ys ih =>
        intro off u hpat
        rcases y with ⟨py, cy⟩
        simp only [listCost, List.length_cons, Finset.sum_range_succ']
        have h0 : py = decide ((0 + off) % 2 = 0) := hpat 0 (by simp)
        have htail : ∀ j < ys.length, (ys.getD j (false, 0)).1 = decide ((j + (off + 1)) % 2 = 0) := by
          intro j hj
          have := hpat (j + 1) (by simp; omega)
          simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 off] using this
        rw [ih (off + 1) (fun t => u (t + 1)) htail]
        have hsum_eq : ∑ j ∈ Finset.range ys.length,
            (if u (j + 1) = decide ((j + (off + 1)) % 2 = 0) then 0 else (ys.getD j (false, 0)).2) =
            ∑ j ∈ Finset.range ys.length,
            (if u (j + 1) = decide ((j + 1 + off) % 2 = 0) then 0 else (((py, cy) :: ys).getD (j + 1) (false, 0)).2) := by
          apply Finset.sum_congr rfl
          intro j _
          simp [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 off]
        rw [hsum_eq, h0]
        simp only [Nat.zero_add, List.getD_cons_zero]
        rw [Nat.add_comm]
    have hcost_B : ∀ u : ℕ → Bool, listCost B u = costAlt B.length a u := by
      intro u
      have := hcost_eq B 0 u (by simpa using hB_pat)
      simpa [costAlt, a] using this
    have hsum_B : listSum B = ∑ j ∈ Finset.range B.length, a j := by
      have hgen : ∀ (L0 : List (Bool × ℕ)), listSum L0 = ∑ j ∈ Finset.range L0.length, (L0.getD j (false, 0)).2 := by
        intro L0
        induction L0 with
        | nil => simp [listSum]
        | cons y ys ih =>
          rw [listSum, List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
          change y.2 + listSum ys = _
          rw [ih, Nat.add_comm]
          simp [List.getD_cons_succ]
      exact hgen B
    rw [← hB_sum, hsum_B]
    refine alt_sum_bound B.length K q hq a ?_ ?_ ?_
    · intro j hj
      have hmem : B.getD j (false, 0) ∈ B := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      exact hB_pos _ hmem
    · intro w hw; rw [← hcost_B]; exact hB_opt w hw
    · intro j hj
      obtain ⟨u, huc, hucost, hup⟩ := hB_del j hj
      refine ⟨u, huc, by rw [← hcost_B]; exact hucost, ?_⟩
      rwa [← hB_pat j hj]

theorem pen_bound_minimal (n K q : ℕ) (hq : 1 ≤ q)
    (pref : Fin (n+1) → Bool) (pen : Fin (n+1) → ℕ)
    (hopt : ∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ ∑ i : Fin (n+1), if w i = pref i then 0 else pen i)
    (hdel : ∀ i : Fin (n+1), 0 < pen i → ∃ w : Fin (n+1) → Bool,
      changes w ≤ K ∧ (∑ k : Fin (n+1), if w k = pref k then 0 else pen k) = q ∧ w i ≠ pref i) :
    ∑ i : Fin (n+1), pen i ≤ (K + 2) * q := by
  let M : List (Bool × ℕ) := List.ofFn (fun i : Fin (n+1) => (pref i, pen i))
  have hM_len : M.length = n + 1 := by simp [M]
  have hM_getD : ∀ j (hj : j < n + 1), M.getD j (false, 0) = (pref ⟨j, hj⟩, pen ⟨j, hj⟩) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa [M] using hj)]
    exact List.getElem_ofFn (h := by simpa [M] using hj)
  have hM_cost : ∀ u : ℕ → Bool,
      listCost M u = ∑ i : Fin (n+1), if u i.val = pref i then 0 else pen i := by
    intro u
    have hgen : ∀ (k : ℕ) (f : Fin k → Bool × ℕ) (v : ℕ → Bool),
        listCost (List.ofFn f) v = ∑ i : Fin k, if v i.val = (f i).1 then 0 else (f i).2 := by
      intro k
      induction k with
      | zero => intro f v; simp [listCost]
      | succ k ih =>
        intro f v
        rw [List.ofFn_succ, listCost, ih (fun i => f i.succ) (fun t => v (t + 1)), Fin.sum_univ_succ]
        rfl
    exact hgen (n + 1) (fun i => (pref i, pen i)) u
  have hM_sum : listSum M = ∑ i : Fin (n+1), pen i := by
    have hgen : ∀ (k : ℕ) (f : Fin k → Bool × ℕ),
        listSum (List.ofFn f) = ∑ i : Fin k, (f i).2 := by
      intro k
      induction k with
      | zero => intro f; simp [listSum]
      | succ k ih =>
        intro f
        rw [List.ofFn_succ, listSum, List.map_cons, List.sum_cons]
        have := ih (fun i => f i.succ)
        simp only [listSum] at this
        rw [this, Fin.sum_univ_succ]
    exact hgen (n + 1) (fun i => (pref i, pen i))
  have hM_opt : OptL M K q := by
    intro u hu
    rw [hM_cost]
    apply hopt (fun i => u i.val)
    rwa [changesNat_of_fin_eq, ← hM_len]
  have hM_del : DelMinPosL M K q := by
    intro j hj hpos
    have hj' : j < n + 1 := by omega
    rw [hM_getD j hj'] at hpos ⊢
    obtain ⟨w, hwc, hwcost, hwp⟩ := hdel ⟨j, hj'⟩ hpos
    refine ⟨A_wN w, ?_, ?_, ?_⟩
    · rw [hM_len, ← changesNat_eq_changes]; exact hwc
    · rw [hM_cost]
      have heq : (fun i : Fin (n+1) => if A_wN w i.val = pref i then 0 else pen i) =
          fun i : Fin (n+1) => if w i = pref i then 0 else pen i := by
        funext i; rw [A_wN_val]
      rw [heq]; exact hwcost
    · have hwv : A_wN w j = w ⟨j, hj'⟩ := A_wN_val w ⟨j, hj'⟩
      rw [hwv]; exact hwp
  let L := M.filter (fun x => decide (0 < x.2))
  obtain ⟨hL_opt, hL_del⟩ := filter_opt_delMin M K q hM_opt hM_del
  have hL_pos : ∀ x ∈ L, 0 < x.2 := by
    intro x hx
    have := (List.mem_filter.1 hx).2
    simpa using this
  have hL_len : L.length ≤ n + 1 := le_trans (List.length_filter_le _ _) (by rw [hM_len])
  obtain ⟨A, hAsum, hApos, hAalt, hAopt, hAdel⟩ :=
    reduce_to_alternating (n + 1) L hL_len hL_pos K q hL_opt hL_del
  rw [← hM_sum, ← listSum_filter_pos M, ← hAsum]
  exact alt_list_sum_bound A K q hq hApos hAalt hAopt hAdel

theorem pen_bound (n K q : ℕ) (hq : 1 ≤ q) (pref : Fin (n+1) → Bool) :
    ∀ (N : ℕ) (pen : Fin (n+1) → ℕ), ∑ i : Fin (n+1), pen i ≤ N →
    (∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ ∑ i : Fin (n+1), if w i = pref i then 0 else pen i) →
    ∃ pen' : Fin (n+1) → ℕ, (∀ i, pen' i ≤ pen i) ∧
      (∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ ∑ i : Fin (n+1), if w i = pref i then 0 else pen' i) ∧
      ∑ i : Fin (n+1), pen' i ≤ (K + 2) * q := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro pen hsum hopt
    by_cases hred : ∃ i0 : Fin (n+1), 0 < pen i0 ∧
        ∀ w : Fin (n+1) → Bool, changes w ≤ K →
          q ≤ ∑ i : Fin (n+1), if w i = pref i then 0 else (if i = i0 then pen i - 1 else pen i)
    · obtain ⟨i0, hi0, hopt'⟩ := hred
      let pen1 : Fin (n+1) → ℕ := fun i => if i = i0 then pen i - 1 else pen i
      have hsum1 : ∑ i : Fin (n+1), pen1 i + 1 = ∑ i : Fin (n+1), pen i := by
        rw [← Finset.add_sum_erase Finset.univ pen1 (Finset.mem_univ i0),
          ← Finset.add_sum_erase Finset.univ pen (Finset.mem_univ i0)]
        have h1 : pen1 i0 = pen i0 - 1 := if_pos rfl
        have h2 : ∑ i ∈ Finset.univ.erase i0, pen1 i = ∑ i ∈ Finset.univ.erase i0, pen i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [pen1, (Finset.mem_erase.1 hi).1]
        rw [h1, h2]
        omega
      have hlt : ∑ i : Fin (n+1), pen1 i < N := by omega
      obtain ⟨pen', hle', hopt'', hbound'⟩ := ih _ hlt pen1 (le_refl _) hopt'
      refine ⟨pen', fun i => le_trans (hle' i) ?_, hopt'', hbound'⟩
      simp only [pen1]; split_ifs <;> omega
    · push Not at hred
      refine ⟨pen, fun _ => le_refl _, hopt, ?_⟩
      apply pen_bound_minimal n K q hq pref pen hopt
      intro i hi
      obtain ⟨w, hwc, hwlt⟩ := hred i hi
      have hge := hopt w hwc
      have hdiff : (∑ k : Fin (n+1), if w k = pref k then 0 else pen k) ≤
          (∑ k : Fin (n+1), if w k = pref k then 0 else (if k = i then pen k - 1 else pen k)) +
          (if w i = pref i then 0 else 1) := by
        rw [← Finset.add_sum_erase Finset.univ (fun k => if w k = pref k then 0 else pen k) (Finset.mem_univ i),
          ← Finset.add_sum_erase Finset.univ (fun k => if w k = pref k then 0 else (if k = i then pen k - 1 else pen k)) (Finset.mem_univ i)]
        have hrest : ∑ k ∈ Finset.univ.erase i, (if w k = pref k then 0 else pen k) =
            ∑ k ∈ Finset.univ.erase i, (if w k = pref k then 0 else (if k = i then pen k - 1 else pen k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [(Finset.mem_erase.1 hk).1]
        rw [hrest]
        split_ifs <;> omega
      have hne : w i ≠ pref i := by
        intro heq; simp [heq] at hdiff; omega
      have hsum_eq : (∑ k : Fin (n+1), if w k = pref k then 0 else pen k) = q := by
        simp [hne] at hdiff; omega
      exact ⟨w, hwc, hsum_eq, hne⟩

theorem minimal_base_subset (n q : ℕ) (hq : 1 ≤ q) (base : Fin (n+1) → ℕ)
    (hsum : q ≤ ∑ i : Fin (n+1), base i) :
    ∃ S : Finset (Fin (n+1)), S.card ≤ q ∧ q ≤ S.sum base := by
  let S0 : Finset (Fin (n+1)) := Finset.univ.filter (fun i => 0 < base i)
  have hS0 : q ≤ S0.sum base := by
    have heq : S0.sum base = ∑ i : Fin (n+1), base i := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < base i) base]
      have h0 : (Finset.univ.filter (fun i => ¬ 0 < base i)).sum base = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have := (Finset.mem_filter.1 hi).2
        omega
      rw [h0, add_zero]
    omega
  have hpos0 : ∀ i ∈ S0, 0 < base i := fun i hi => (Finset.mem_filter.1 hi).2
  suffices ∀ (k : ℕ) (T : Finset (Fin (n+1))), T.card ≤ k → q ≤ T.sum base → (∀ i ∈ T, 0 < base i) →
      ∃ S : Finset (Fin (n+1)), S.card ≤ q ∧ q ≤ S.sum base by
    exact this S0.card S0 (le_refl _) hS0 hpos0
  intro k
  induction k with
  | zero =>
    intro T hk hT _
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hT0
    simp at hT; omega
  | succ k ih =>
    intro T hk hT hpos
    by_cases hred : ∃ x ∈ T, q ≤ (T.erase x).sum base
    · obtain ⟨x, hx, hTx⟩ := hred
      have hcard : (T.erase x).card ≤ k := by rw [Finset.card_erase_of_mem hx]; omega
      exact ih (T.erase x) hcard hTx (fun y hy => hpos y (Finset.erase_subset _ _ hy))
    · push Not at hred
      have hne : T.Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty.1 he] at hT
        simp at hT; omega
      obtain ⟨x, hx⟩ := hne
      have hlt := hred x hx
      have hcard_er : (T.erase x).card ≤ (T.erase x).sum base := by
        calc (T.erase x).card = ∑ _ ∈ T.erase x, 1 := by simp
          _ ≤ ∑ y ∈ T.erase x, base y := by
            apply Finset.sum_le_sum
            intro y hy
            exact hpos y (Finset.erase_subset _ _ hy)
      have hcard : T.card ≤ q := by
        rw [← Finset.card_erase_add_one hx]
        omega
      exact ⟨T, hcard, hT⟩

theorem core_bound (n E K : ℕ) (cost : Fin (n+1) → Bool → ℕ) :
    ∃ (q : ℕ) (S : Finset (Fin (n+1))), q ≤ E + 1 ∧ S.card ≤ (K + 2) * q ∧
      (∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ ∑ i : Fin (n+1), cost i (w i)) ∧
      (∀ e ≤ E, q ≤ e → ∃ w : Fin (n+1) → Bool, changes w ≤ K ∧ ∑ i : Fin (n+1), cost i (w i) ≤ e) ∧
      (∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ S.sum (fun i => cost i (w i))) := by
  have hex : ∃ c : ℕ, ∃ w : Fin (n+1) → Bool, changes w ≤ K ∧ ∑ i : Fin (n+1), cost i (w i) ≤ c := by
    refine ⟨∑ i : Fin (n+1), cost i false, fun _ => false, ?_, le_refl _⟩
    have hc0 : changes (fun _ : Fin (n+1) => false) = 0 := by
      unfold changes; simp
    omega
  classical
  let m := Nat.find hex
  have hm_spec := Nat.find_spec hex
  let q := min m (E + 1)
  have hq_le : q ≤ E + 1 := min_le_right _ _
  have hq_lb : ∀ w : Fin (n+1) → Bool, changes w ≤ K → q ≤ ∑ i : Fin (n+1), cost i (w i) := by
    intro w hw
    have hle := Nat.find_min' hex ⟨w, hw, le_refl _⟩
    exact le_trans (min_le_left _ _) hle
  have hq_ub : ∀ e ≤ E, q ≤ e → ∃ w : Fin (n+1) → Bool, changes w ≤ K ∧ ∑ i : Fin (n+1), cost i (w i) ≤ e := by
    intro e he hqe
    have hm_le : m ≤ e := by
      rcases le_or_gt m (E + 1) with h | h
      · simpa [q, min_eq_left h] using hqe
      · exfalso
        have : q = E + 1 := min_eq_right (le_of_lt h)
        omega
    obtain ⟨w, hwc, hws⟩ := hm_spec
    exact ⟨w, hwc, le_trans hws hm_le⟩
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · refine ⟨0, ∅, by omega, by simp, ?_, ?_, by simp⟩
    · intro _ _; simp
    · intro e _ _
      obtain ⟨w, hwc, hws⟩ := hm_spec
      have hm0 : m = 0 := by
        rcases le_or_gt m (E + 1) with h | h
        · simpa [q, min_eq_left h] using hq0
        · have : q = E + 1 := min_eq_right (le_of_lt h)
          omega
      exact ⟨w, hwc, by omega⟩
  · let base : Fin (n+1) → ℕ := fun i => min (cost i false) (cost i true)
    let pref : Fin (n+1) → Bool := fun i => decide (cost i true < cost i false)
    let pen : Fin (n+1) → ℕ := fun i => cost i (!pref i) - base i
    have hdecomp : ∀ i (b : Bool), cost i b = base i + if b = pref i then 0 else pen i := by
      intro i b
      dsimp only [base, pref, pen]
      by_cases h : cost i true < cost i false
      · have hp : decide (cost i true < cost i false) = true := decide_eq_true h
        cases b <;> simp [hp] <;> omega
      · have hp : decide (cost i true < cost i false) = false := decide_eq_false h
        cases b <;> simp [hp] <;> omega
    have hbase_le_cost : ∀ i b, base i ≤ cost i b := fun i b => by
      rw [hdecomp i b]; exact Nat.le_add_right _ _
    by_cases hbq : q ≤ ∑ i : Fin (n+1), base i
    · obtain ⟨S, hSc, hSs⟩ := minimal_base_subset n q hqpos base hbq
      refine ⟨q, S, hq_le, le_trans hSc (Nat.le_mul_of_pos_left q (by omega)), hq_lb, hq_ub, ?_⟩
      intro w _
      calc q ≤ S.sum base := hSs
        _ ≤ S.sum (fun i => cost i (w i)) := Finset.sum_le_sum (fun i _ => hbase_le_cost i (w i))
    · let B := ∑ i : Fin (n+1), base i
      let q' := q - B
      have hq'pos : 1 ≤ q' := by omega
      have hpen_opt : ∀ w : Fin (n+1) → Bool, changes w ≤ K →
          q' ≤ ∑ i : Fin (n+1), if w i = pref i then 0 else pen i := by
        intro w hw
        have hwcost := hq_lb w hw
        have hsum_split : ∑ i : Fin (n+1), cost i (w i) =
            B + ∑ i : Fin (n+1), if w i = pref i then 0 else pen i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          exact hdecomp i (w i)
        omega
      obtain ⟨pen', hpen'le, hpen'opt, hpen'sum⟩ :=
        pen_bound n K q' hq'pos pref (∑ i : Fin (n+1), pen i) pen (le_refl _) hpen_opt
      let Sbase := Finset.univ.filter (fun i : Fin (n+1) => 0 < base i)
      let Spen := Finset.univ.filter (fun i : Fin (n+1) => 0 < pen' i)
      let S := Sbase ∪ Spen
      refine ⟨q, S, hq_le, ?_, hq_lb, hq_ub, ?_⟩
      · have hSb : Sbase.card ≤ B := by
          calc Sbase.card = ∑ _ ∈ Sbase, 1 := by simp
            _ ≤ ∑ i ∈ Sbase, base i := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
            _ ≤ B := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        have hSp : Spen.card ≤ (K + 2) * q' := by
          calc Spen.card = ∑ _ ∈ Spen, 1 := by simp
            _ ≤ ∑ i ∈ Spen, pen' i := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
            _ ≤ ∑ i : Fin (n+1), pen' i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
            _ ≤ (K + 2) * q' := hpen'sum
        calc S.card ≤ Sbase.card + Spen.card := Finset.card_union_le _ _
          _ ≤ B + (K + 2) * q' := Nat.add_le_add hSb hSp
          _ ≤ (K + 2) * B + (K + 2) * q' := Nat.add_le_add_right (Nat.le_mul_of_pos_left B (by omega)) _
          _ = (K + 2) * q := by rw [← Nat.mul_add]; congr 1; omega
      · intro w hw
        have hSb_sum : B ≤ S.sum base := by
          have h1 : B = Sbase.sum base := by
            dsimp only [B, Sbase]
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < base i) base]
            have h0 : (Finset.univ.filter (fun i => ¬ 0 < base i)).sum base = 0 :=
              Finset.sum_eq_zero (fun i hi => by exact Nat.eq_zero_of_not_pos (Finset.mem_filter.1 hi).2)
            rw [h0, add_zero]
          rw [h1]
          exact Finset.sum_le_sum_of_subset Finset.subset_union_left
        have hSp_sum : q' ≤ S.sum (fun i => if w i = pref i then 0 else pen i) := by
          have h1 : ∑ i : Fin (n+1), (if w i = pref i then 0 else pen' i) =
              Spen.sum (fun i => if w i = pref i then 0 else pen' i) := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < pen' i)]
            have h0 : (Finset.univ.filter (fun i => ¬ 0 < pen' i)).sum (fun i => if w i = pref i then 0 else pen' i) = 0 :=
              Finset.sum_eq_zero (fun i hi => by have := (Finset.mem_filter.1 hi).2; split_ifs <;> omega)
            rw [h0, add_zero]
          have h2 : Spen.sum (fun i => if w i = pref i then 0 else pen' i) ≤
              S.sum (fun i => if w i = pref i then 0 else pen i) := by
            calc Spen.sum (fun i => if w i = pref i then 0 else pen' i)
                ≤ Spen.sum (fun i => if w i = pref i then 0 else pen i) := by
                  apply Finset.sum_le_sum
                  intro i _
                  split_ifs
                  · exact le_refl 0
                  · exact hpen'le i
              _ ≤ S.sum (fun i => if w i = pref i then 0 else pen i) :=
                  Finset.sum_le_sum_of_subset Finset.subset_union_right
          calc q' ≤ ∑ i : Fin (n+1), (if w i = pref i then 0 else pen' i) := hpen'opt w hw
            _ = Spen.sum (fun i => if w i = pref i then 0 else pen' i) := h1
            _ ≤ S.sum (fun i => if w i = pref i then 0 else pen i) := h2
        have hsum_S : S.sum (fun i => cost i (w i)) =
            S.sum base + S.sum (fun i => if w i = pref i then 0 else pen i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          exact hdecomp i (w i)
        rw [hsum_S]
        have hBq' : B + q' = q := by dsimp only [B, q']; omega
        omega

end PEqualNP.Outside.L_meta_53173_aux

theorem PEqualNP.Outside.L_meta_53173 :
(
let fits := fun (n p b g : Nat) (word : Fin (n+1) → Bool) =>
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.size-PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    C.size ≤ g ∧ C.output < n+2+C.size ∧ ∀ i : Fin (n+1),
      C.eval (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]) = word i
let afford := fun (n p b g e : Nat) (cost : Fin (n+1) → Bool → Nat) (S : Finset (Fin (n+1))) =>
  ∃ word : Fin (n+1) → Bool, fits n p b g word ∧ S.sum (fun i => cost i (word i)) ≤ e
∀ (p b g K : Nat),
  (∀ (z : Bool) (k : Nat), fits k p b g (fun i => if i.val % 2 = 0 then z else !z) ↔ k ≤ K) →
  ∀ (n E : Nat) (cost : Fin (n+1) → Bool → Nat),
    ∃ (q : Nat) (S : Finset (Fin (n+1))), q ≤ E+1 ∧ S.card ≤ (K+2)*q ∧
      ∀ e ≤ E, (afford n p b g e cost Finset.univ ↔ q ≤ e) ∧
        (afford n p b g e cost S ↔ q ≤ e)) := by
  intro fits afford p b g K hh n E cost
  have hfits : ∀ m (w : Fin (m+1) → Bool),
      fits m p b g w ↔ PEqualNP.Outside.L_meta_53173_aux.changes w ≤ K :=
    PEqualNP.Outside.L_meta_53173_aux.fits_iff_changes p b g K hh
  obtain ⟨q, S, hqle, hScard, hqlb, hqub, hSlb⟩ :=
    PEqualNP.Outside.L_meta_53173_aux.core_bound n E K cost
  refine ⟨q, S, hqle, hScard, fun e he => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · rintro ⟨w, hwf, hws⟩
    exact le_trans (hqlb w ((hfits n w).1 hwf)) hws
  · intro hqe
    obtain ⟨w, hwc, hws⟩ := hqub e he hqe
    exact ⟨w, (hfits n w).2 hwc, hws⟩
  · rintro ⟨w, hwf, hws⟩
    exact le_trans (hSlb w ((hfits n w).1 hwf)) hws
  · intro hqe
    obtain ⟨w, hwc, hws⟩ := hqub e he hqe
    refine ⟨w, (hfits n w).2 hwc, le_trans ?_ hws⟩
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
