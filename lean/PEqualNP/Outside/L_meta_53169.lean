import Mathlib
import PEqualNP.Defs

-- Adapted from lean/PEqualNP/Outside/L_meta_53170.lean (merged upstream, PR 56537 by l-koehler), Apache-2.0.
-- The interval version there is specialised here to singleton intervals and the explicit cyclic family.

namespace PEqualNP.Outside.L_meta_53169_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Fits (p b g n : ℕ) (word : Fin (n+1) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    C.size ≤ g ∧ C.output < n+2+C.size ∧ ∀ i : Fin (n+1),
      C.eval (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]) = word i

def alt (z : Bool) (i : ℕ) : Bool := if i % 2 = 0 then z else !z

def changes {n : ℕ} (w : Fin (n+1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc ≠ w i.succ)).card

def clampF {n : ℕ} (lo hi : Fin (n+1) → ℕ) (i : Fin (n+1)) (s : ℕ) : ℕ := max (lo i) (min (hi i) s)

def startF {n : ℕ} (lo hi : Fin (n+1) → ℕ) : ℕ :=
  (List.finRange (n+1)).reverse.foldl (fun z i => clampF lo hi i z) (lo (Fin.last n))

def xF {n : ℕ} (lo hi : Fin (n+1) → ℕ) (i : Fin (n+1)) : ℕ :=
  ((List.finRange (n+1)).scanl (fun z i => clampF lo hi i z) (startF lo hi)).getD (i.val+1) (startF lo hi)

def upF {n : ℕ} (x : Fin (n+1) → ℕ) : ℕ := ∑ i : Fin n, (x i.succ - x i.castSucc)

def downF {n : ℕ} (x : Fin (n+1) → ℕ) : ℕ := ∑ i : Fin n, (x i.castSucc - x i.succ)

def upCapF (T hf ht s : ℕ) : ℕ := (T-s)*((hf+1)/2) + s*(ht/2)

def downCapF (T hf ht s : ℕ) : ℕ := (T-s)*(hf/2) + s*((ht+1)/2)

def countF {n T : ℕ} (w : Fin T → Fin (n+1) → Bool) (i : Fin (n+1)) : ℕ :=
  ((Finset.univ : Finset (Fin T)).filter (fun t => w t i)).card

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

theorem A_h_le (p b g : ℕ) (h : Bool → ℕ)
    (hh : ∀ (z : Bool) (k : ℕ), Fits p b g k (fun i => alt z i.val) ↔ k ≤ h z) (z : Bool) :
    h z ≤ h (!z) + 1 := by
  rcases Nat.eq_zero_or_pos (h z) with h0 | h0
  · omega
  · obtain ⟨k, hk⟩ : ∃ k, h z = k + 1 := ⟨h z - 1, by omega⟩
    have hf := (hh z (k + 1)).2 (by omega)
    have hm : Monotone (Fin.succ : Fin (k+1) → Fin (k+2)) := Fin.strictMono_succ.monotone
    have := A_reindex p b g (k + 1) k _ Fin.succ hm hf
    have heq : ((fun i : Fin (k+2) => alt z i.val) ∘ Fin.succ) = fun i : Fin (k+1) => alt (!z) i.val := by
      funext i
      simp only [Function.comp_apply, Fin.val_succ]
      exact A_alt_succ z i.val
    rw [heq] at this
    have := (hh (!z) k).1 this
    omega

theorem A_main (p b g : ℕ) (h : Bool → ℕ)
    (hh : ∀ (z : Bool) (k : ℕ), Fits p b g k (fun i => alt z i.val) ↔ k ≤ h z) :
    (∀ n (w : Fin (n+1) → Bool), Fits p b g n w ↔ changes w ≤ h (w 0)) ∧
    h true ≤ h false + 1 ∧ h false ≤ h true + 1 :=
  ⟨fun n w => ⟨A_fwd p b g h hh n w, A_bwd p b g h hh n w⟩,
    A_h_le p b g h hh true, A_h_le p b g h hh false⟩

def B2_xN {n : ℕ} (x : Fin (n+1) → ℕ) (j : ℕ) : ℕ := if h : j ≤ n then x ⟨j, by omega⟩ else 0

def B2_U {n : ℕ} (x : Fin (n+1) → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, (B2_xN x (i+1) - B2_xN x i)

def B2_D {n : ℕ} (x : Fin (n+1) → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, (B2_xN x i - B2_xN x (i+1))

def B2_W (T a e t : ℕ) : Bool := decide (∃ k ∈ Finset.Ico a e, k % T = t)

theorem B2_W_iff (T a e t : ℕ) : B2_W T a e t = true ↔ ∃ k ∈ Finset.Ico a e, k % T = t := by
  simp [B2_W]

theorem B2_xN_fin {n : ℕ} (x : Fin (n+1) → ℕ) (i : Fin (n+1)) : B2_xN x i.val = x i := by
  simp [B2_xN, Nat.lt_succ_iff.mp i.isLt]

theorem B2_upF {n : ℕ} (x : Fin (n+1) → ℕ) : upF x = B2_U x n := by
  unfold upF B2_U
  rw [← Fin.sum_univ_eq_sum_range (fun i => B2_xN x (i+1) - B2_xN x i) n]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : B2_xN x (i.val+1) = x i.succ := B2_xN_fin x i.succ
  have h2 : B2_xN x i.val = x i.castSucc := B2_xN_fin x i.castSucc
  rw [h1, h2]

theorem B2_downF {n : ℕ} (x : Fin (n+1) → ℕ) : downF x = B2_D x n := by
  unfold downF B2_D
  rw [← Fin.sum_univ_eq_sum_range (fun i => B2_xN x i - B2_xN x (i+1)) n]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : B2_xN x (i.val+1) = x i.succ := B2_xN_fin x i.succ
  have h2 : B2_xN x i.val = x i.castSucc := B2_xN_fin x i.castSucc
  rw [h1, h2]

theorem B2_inv {n : ℕ} (x : Fin (n+1) → ℕ) :
    ∀ j, j ≤ n → B2_xN x j + B2_D x j = x 0 + B2_U x j
  | 0, _ => by simp [B2_xN, B2_D, B2_U]
  | j+1, hj => by
    have ih := B2_inv x j (by omega)
    simp only [B2_D, B2_U, Finset.sum_range_succ] at ih ⊢
    omega

theorem B2_U_mono {n : ℕ} (x : Fin (n+1) → ℕ) (j : ℕ) : B2_U x j ≤ B2_U x (j+1) := by
  simp [B2_U, Finset.sum_range_succ]

theorem B2_D_mono {n : ℕ} (x : Fin (n+1) → ℕ) (j : ℕ) : B2_D x j ≤ B2_D x (j+1) := by
  simp [B2_D, Finset.sum_range_succ]

theorem B2_tele (f : ℕ → ℕ) (hf : ∀ i, f i ≤ f (i+1)) (p : ℕ → Prop) [DecidablePred p] :
    ∀ n, ∑ i ∈ Finset.range n, ((Finset.Ico (f i) (f (i+1))).filter p).card
      = ((Finset.Ico (f 0) (f n)).filter p).card ∧ f 0 ≤ f n
  | 0 => by simp
  | n+1 => by
    obtain ⟨ih, hmono⟩ := B2_tele f hf p n
    refine ⟨?_, hmono.trans (hf n)⟩
    rw [Finset.sum_range_succ, ih, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico hmono (hf n)]

theorem B2_step (T a e a' e' t : ℕ) (ha : a ≤ a') (he : e ≤ e')
    (hne : B2_W T a e t ≠ B2_W T a' e' t) :
    0 < ((Finset.Ico e e').filter (fun k => k % T = t)).card +
      ((Finset.Ico a a').filter (fun k => k % T = t)).card := by
  simp only [B2_W, ne_eq, decide_eq_decide] at hne
  by_cases h1 : ∃ k ∈ Finset.Ico a e, k % T = t
  · have h2 : ¬ ∃ k ∈ Finset.Ico a' e', k % T = t := fun h2 => hne ⟨fun _ => h2, fun _ => h1⟩
    obtain ⟨k, hk, hkt⟩ := h1
    rw [Finset.mem_Ico] at hk
    have hk' : k < a' := by
      by_contra hc
      exact h2 ⟨k, Finset.mem_Ico.2 ⟨by omega, by omega⟩, hkt⟩
    have : k ∈ (Finset.Ico a a').filter (fun k => k % T = t) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨hk.1, hk'⟩, hkt⟩
    have := Finset.card_pos.2 ⟨k, this⟩
    omega
  · have h2 : ∃ k ∈ Finset.Ico a' e', k % T = t := by
      by_contra h2; exact hne ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    obtain ⟨k, hk, hkt⟩ := h2
    rw [Finset.mem_Ico] at hk
    have hk' : e ≤ k := by
      by_contra hc
      exact h1 ⟨k, Finset.mem_Ico.2 ⟨by omega, by omega⟩, hkt⟩
    have : k ∈ (Finset.Ico e e').filter (fun k => k % T = t) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨hk', hk.2⟩, hkt⟩
    have := Finset.card_pos.2 ⟨k, this⟩
    omega

theorem B2_count_fin (T a e : ℕ) (hT : 0 < T) (hae : e - a ≤ T) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => B2_W T a e t.val = true)).card = e - a := by
  have himg : (Finset.univ : Finset (Fin T)).filter (fun t => B2_W T a e t.val = true)
      = (Finset.Ico a e).image (fun k => (⟨k % T, Nat.mod_lt _ hT⟩ : Fin T)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B2_W_iff, Finset.mem_image,
      Fin.ext_iff]
  rw [himg, Finset.card_image_of_injOn, Nat.card_Ico]
  intro k1 hk1 k2 hk2 heq
  simp only [Finset.coe_Ico, Set.mem_Ico] at hk1 hk2
  simp only [Fin.mk.injEq] at heq
  rcases le_total k1 k2 with h | h
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq heq
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega

theorem B2_cnt (T t m M c₀ c₁ : ℕ)
    (h : ∀ k, m ≤ k → k < M → k % T = t → c₀ ≤ k / T ∧ k / T < c₁) :
    ((Finset.Ico m M).filter (fun k => k % T = t)).card ≤ c₁ - c₀ := by
  have : ((Finset.Ico m M).filter (fun k => k % T = t)).card ≤ (Finset.Ico c₀ c₁).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / T)
    · intro k hk
      simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_Ico,
        Set.mem_ofPred_eq] at hk ⊢
      exact h k hk.1.1 hk.1.2 hk.2
    · intro k1 hk1 k2 hk2 heq
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hk1 hk2
      have e1 := Nat.div_add_mod k1 T
      have e2 := Nat.div_add_mod k2 T
      simp only at heq
      rw [hk1.2] at e1
      rw [hk2.2, ← heq] at e2
      omega
  simpa using this

theorem B2_W0 (T s t : ℕ) (ht : t < T) (hs : s ≤ T) : B2_W T 0 s t = decide (t < s) := by
  rw [Bool.eq_iff_iff, B2_W_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hkt⟩
    rw [Finset.mem_Ico] at hk
    rw [Nat.mod_eq_of_lt (by omega)] at hkt
    omega
  · intro h
    exact ⟨t, Finset.mem_Ico.2 ⟨Nat.zero_le _, h⟩, Nat.mod_eq_of_lt ht⟩

theorem B2_qlt (T q c : ℕ) (h : T * q < T * c) : q < c := Nat.lt_of_mul_lt_mul_left h

theorem B2_main (hf ht : ℕ) (h1 : ht ≤ hf + 1) (h2 : hf ≤ ht + 1) (n T : ℕ)
    (x : Fin (n+1) → ℕ) (hx : ∀ i, x i ≤ T)
    (hu : upF x ≤ upCapF T hf ht (x 0)) (hd : downF x ≤ downCapF T hf ht (x 0)) :
    (∀ t : Fin T, changes (fun i : Fin (n+1) => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val) ≤
        (if B2_W T (B2_D x (0 : Fin (n+1)).val) (x 0 + B2_U x (0 : Fin (n+1)).val) t.val then ht else hf)) ∧
      ∀ i, countF (fun (t : Fin T) (i : Fin (n+1)) => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val) i = x i := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    refine ⟨fun t => Fin.elim0 t, fun i => ?_⟩
    have := hx i
    simp [countF]; omega
  have hs : x 0 ≤ T := hx 0
  refine ⟨?_, ?_⟩
  · intro t
    have htT := t.isLt
    set U := upF x with hU
    set D := downF x with hD
    unfold upCapF at hu
    unfold downCapF at hd
    set Af := (hf+1)/2 with hAf
    set At := ht/2 with hAt
    set Bf := hf/2 with hBf
    set Bt := (ht+1)/2 with hBt
    have hA1 : At ≤ Af := by omega
    have hA2 : Af ≤ At + 1 := by omega
    have hB1 : Bf ≤ Bt := by omega
    have hB2 : Bt ≤ Bf + 1 := by omega
    have hsum : ∀ c, (T - x 0) * c + x 0 * c = T * c := fun c => by
      rw [← Nat.add_mul, Nat.sub_add_cancel hs]
    have hU1 : U ≤ T * Af := by
      have := Nat.mul_le_mul_left (x 0) hA1
      have := hsum Af
      omega
    have hU2 : U + x 0 ≤ T * (At + 1) := by
      have := Nat.mul_le_mul_left (T - x 0) hA2
      have := hsum At
      have e : T * (At + 1) = T * At + T := by ring
      have e2 : (T - x 0) * (At + 1) = (T - x 0) * At + (T - x 0) := by ring
      omega
    have hD1 : D ≤ T * Bt := by
      have := Nat.mul_le_mul_left (T - x 0) hB1
      have := hsum Bt
      omega
    have hD2 : D ≤ T * Bf + x 0 := by
      have := Nat.mul_le_mul_left (x 0) hB2
      have := hsum Bf
      have e2 : x 0 * (Bf + 1) = x 0 * Bf + x 0 := by ring
      omega
    have hchg : changes (fun i : Fin (n+1) => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val)
        ≤ ((Finset.Ico (x 0) (x 0 + U)).filter (fun k => k % T = t.val)).card +
          ((Finset.Ico 0 D).filter (fun k => k % T = t.val)).card := by
      let g : ℕ → ℕ := fun j =>
        ((Finset.Ico (x 0 + B2_U x j) (x 0 + B2_U x (j+1))).filter (fun k => k % T = t.val)).card +
        ((Finset.Ico (B2_D x j) (B2_D x (j+1))).filter (fun k => k % T = t.val)).card
      calc changes (fun i : Fin (n+1) => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val)
          ≤ ∑ i : Fin n, g i.val := by
            unfold changes
            rw [Finset.card_filter]
            apply Finset.sum_le_sum
            intro i _
            split_ifs with hne
            · exact B2_step T _ _ _ _ t.val (B2_D_mono x i.val)
                (Nat.add_le_add_left (B2_U_mono x i.val) _) hne
            · exact Nat.zero_le _
        _ = ∑ j ∈ Finset.range n, g j := Fin.sum_univ_eq_sum_range g n
        _ = _ := by
            rw [Finset.sum_add_distrib,
              (B2_tele (fun j => x 0 + B2_U x j)
                (fun j => Nat.add_le_add_left (B2_U_mono x j) _) _ n).1,
              (B2_tele (fun j => B2_D x j) (fun j => B2_D_mono x j) _ n).1, hU, hD,
              B2_upF, B2_downF]
            simp [B2_U, B2_D]
    have hw0 : B2_W T (B2_D x (0 : Fin (n+1)).val) (x 0 + B2_U x (0 : Fin (n+1)).val) t.val
        = decide (t.val < x 0) := by
      simp only [Fin.val_zero, B2_D, B2_U, Finset.range_zero, Finset.sum_empty, add_zero]
      exact B2_W0 T (x 0) t.val htT hs
    show changes (fun i : Fin (n+1) => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val)
      ≤ (if B2_W T (B2_D x (0 : Fin (n+1)).val) (x 0 + B2_U x (0 : Fin (n+1)).val) t.val = true
          then ht else hf)
    rw [hw0]
    by_cases hts : t.val < x 0
    · have hR : ((Finset.Ico (x 0) (x 0 + U)).filter (fun k => k % T = t.val)).card ≤ At + 1 - 1 :=
        B2_cnt T t.val _ _ 1 (At + 1) (fun k hk1 hk2 hk3 => by
          have e := Nat.div_add_mod k T
          rw [hk3] at e
          constructor
          · by_contra hc
            have : k / T = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
            rw [this, Nat.mul_zero, Nat.zero_add] at e
            omega
          · apply B2_qlt T
            omega)
      have hF : ((Finset.Ico 0 D).filter (fun k => k % T = t.val)).card ≤ Bt - 0 :=
        B2_cnt T t.val _ _ 0 Bt (fun k hk1 hk2 hk3 => by
          have e := Nat.div_add_mod k T
          rw [hk3] at e
          exact ⟨Nat.zero_le _, B2_qlt T _ _ (by omega)⟩)
      simp only [hts, decide_true, ite_true]
      omega
    · have hR : ((Finset.Ico (x 0) (x 0 + U)).filter (fun k => k % T = t.val)).card ≤ Af - 0 :=
        B2_cnt T t.val _ _ 0 Af (fun k hk1 hk2 hk3 => by
          have e := Nat.div_add_mod k T
          rw [hk3] at e
          exact ⟨Nat.zero_le _, B2_qlt T _ _ (by omega)⟩)
      have hF : ((Finset.Ico 0 D).filter (fun k => k % T = t.val)).card ≤ Bf - 0 :=
        B2_cnt T t.val _ _ 0 Bf (fun k hk1 hk2 hk3 => by
          have e := Nat.div_add_mod k T
          rw [hk3] at e
          exact ⟨Nat.zero_le _, B2_qlt T _ _ (by omega)⟩)
      simp only [hts, decide_false, Bool.false_eq_true, ite_false]
      omega
  · intro i
    show ((Finset.univ : Finset (Fin T)).filter
      (fun t => B2_W T (B2_D x i.val) (x 0 + B2_U x i.val) t.val = true)).card = x i
    have hinv := B2_inv x i.val (Nat.lt_succ_iff.mp i.isLt)
    rw [B2_xN_fin] at hinv
    have := hx i
    rw [B2_count_fin T _ _ hT (by omega)]
    omega

def B1_cl (I : ℕ × ℕ) (s : ℕ) : ℕ := max I.1 (min I.2 s)

def B1_P : ℕ → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | s, I :: ℓ => B1_cl I s :: B1_P (B1_cl I s) ℓ

def B1_U : ℕ → List (ℕ × ℕ) → ℕ
  | _, [] => 0
  | s, I :: ℓ => (B1_cl I s - s) + B1_U (B1_cl I s) ℓ

def B1_D : ℕ → List (ℕ × ℕ) → ℕ
  | _, [] => 0
  | s, I :: ℓ => (s - B1_cl I s) + B1_D (B1_cl I s) ℓ

def B1_upL : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, c :: cs => (c - p) + B1_upL c cs

def B1_dnL : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, c :: cs => (p - c) + B1_dnL c cs

def B1_st : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [I] => I.1
  | I :: J :: ℓ => B1_cl I (B1_st (J :: ℓ))

theorem B1_cl_spec (I : ℕ × ℕ) (hI : I.1 ≤ I.2) (s : ℕ) :
    B1_cl I s = if s < I.1 then I.1 else if I.2 < s then I.2 else s := by
  simp only [B1_cl, max_def, min_def]
  split_ifs <;> omega

theorem B1_st_cons (I : ℕ × ℕ) (ℓ : List (ℕ × ℕ)) (h : ℓ ≠ []) :
    B1_st (I :: ℓ) = B1_cl I (B1_st ℓ) := by
  cases ℓ with
  | nil => exact absurd rfl h
  | cons J ℓ => rfl

theorem B1_st_mem (I : ℕ × ℕ) (ℓ : List (ℕ × ℕ)) (hI : I.1 ≤ I.2) :
    I.1 ≤ B1_st (I :: ℓ) ∧ B1_st (I :: ℓ) ≤ I.2 := by
  cases ℓ with
  | nil => exact ⟨le_refl _, hI⟩
  | cons J ℓ =>
    have h := B1_cl_spec I hI (B1_st (J :: ℓ))
    show I.1 ≤ B1_cl I (B1_st (J :: ℓ)) ∧ B1_cl I (B1_st (J :: ℓ)) ≤ I.2
    split_ifs at h <;> omega

theorem B1_P_length (s : ℕ) (ℓ : List (ℕ × ℕ)) : (B1_P s ℓ).length = ℓ.length := by
  induction ℓ generalizing s with
  | nil => rfl
  | cons I ℓ ih => simp [B1_P, ih]

theorem B1_upL_P (s : ℕ) (ℓ : List (ℕ × ℕ)) : B1_upL s (B1_P s ℓ) = B1_U s ℓ := by
  induction ℓ generalizing s with
  | nil => rfl
  | cons I ℓ ih => simp only [B1_P, B1_upL, B1_U, ih]

theorem B1_dnL_P (s : ℕ) (ℓ : List (ℕ × ℕ)) : B1_dnL s (B1_P s ℓ) = B1_D s ℓ := by
  induction ℓ generalizing s with
  | nil => rfl
  | cons I ℓ ih => simp only [B1_P, B1_dnL, B1_D, ih]

theorem B1_lip : ∀ (ℓ : List (ℕ × ℕ)), (∀ I ∈ ℓ, I.1 ≤ I.2) → ∀ a b,
    B1_U a ℓ ≤ B1_U b ℓ + (b - a) ∧ B1_D a ℓ ≤ B1_D b ℓ + (a - b) := by
  intro ℓ
  induction ℓ with
  | nil => intro _ a b; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons I ℓ ih =>
    intro hv a b
    have hI : I.1 ≤ I.2 := hv I (by simp)
    have h := ih (fun K hK => hv K (by simp [hK])) (B1_cl I a) (B1_cl I b)
    have ha := B1_cl_spec I hI a
    have hb := B1_cl_spec I hI b
    show (B1_cl I a - a) + B1_U (B1_cl I a) ℓ ≤ ((B1_cl I b - b) + B1_U (B1_cl I b) ℓ) + (b - a) ∧
      (a - B1_cl I a) + B1_D (B1_cl I a) ℓ ≤ ((b - B1_cl I b) + B1_D (B1_cl I b) ℓ) + (a - b)
    constructor <;> split_ifs at ha hb <;> omega

theorem B1_min : ∀ (cs : List ℕ) (ℓ : List (ℕ × ℕ)),
    List.Forall₂ (fun c I => I.1 ≤ c ∧ c ≤ I.2) cs ℓ → ∀ p s,
      B1_U s ℓ ≤ B1_upL p cs + (p - s) ∧ B1_D s ℓ ≤ B1_dnL p cs + (s - p) := by
  intro cs ℓ h
  induction h with
  | nil => intro p s; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | @cons c I cs ℓ hcI _ ih =>
    intro p s
    have hI : I.1 ≤ I.2 := le_trans hcI.1 hcI.2
    have h := ih c (B1_cl I s)
    have hs := B1_cl_spec I hI s
    show (B1_cl I s - s) + B1_U (B1_cl I s) ℓ ≤ ((c - p) + B1_upL c cs) + (p - s) ∧
      (s - B1_cl I s) + B1_D (B1_cl I s) ℓ ≤ ((p - c) + B1_dnL c cs) + (s - p)
    constructor <;> split_ifs at hs <;> omega

theorem B1_Q : ∀ (ℓ : List (ℕ × ℕ)), ℓ ≠ [] → (∀ I ∈ ℓ, I.1 ≤ I.2) →
    (B1_U (B1_st ℓ) ℓ + B1_D (B1_st ℓ) ℓ = 0 →
      ∃ H, B1_st ℓ ≤ H ∧ ∀ a, B1_U a ℓ = B1_st ℓ - a ∧ B1_D a ℓ = a - H) ∧
    (0 < B1_U (B1_st ℓ) ℓ + B1_D (B1_st ℓ) ℓ →
      ∀ a, B1_U (B1_st ℓ) ℓ + (B1_st ℓ - a) ≤ B1_U a ℓ ∧
        B1_D (B1_st ℓ) ℓ + (a - B1_st ℓ) ≤ B1_D a ℓ) := by
  intro ℓ
  induction ℓ with
  | nil => intro h; exact absurd rfl h
  | cons I ℓ' ih =>
    intro _ hv
    have hI : I.1 ≤ I.2 := hv I (by simp)
    have hcl := B1_cl_spec I hI
    have hU : ∀ a, B1_U a (I :: ℓ') = (B1_cl I a - a) + B1_U (B1_cl I a) ℓ' := fun a => rfl
    have hD : ∀ a, B1_D a (I :: ℓ') = (a - B1_cl I a) + B1_D (B1_cl I a) ℓ' := fun a => rfl
    rcases ℓ' with _ | ⟨J, ℓ''⟩
    · have hs : B1_st [I] = I.1 := rfl
      have hU0 : ∀ a, B1_U a [] = 0 := fun a => rfl
      have hD0 : ∀ a, B1_D a [] = 0 := fun a => rfl
      simp only [hs, hU, hD, hU0, hD0, add_zero]
      refine ⟨fun _ => ⟨I.2, hI, fun a => ?_⟩, fun h => ?_⟩
      · have h1 := hcl a
        split_ifs at h1 <;> omega
      · exfalso
        have h1 := hcl I.1
        split_ifs at h1 <;> omega
    · have hne : (J :: ℓ'') ≠ [] := List.cons_ne_nil _ _
      have hv' : ∀ K ∈ J :: ℓ'', K.1 ≤ K.2 := fun K hK => hv K (List.mem_cons_of_mem _ hK)
      obtain ⟨ihc, ihn⟩ := ih hne hv'
      have L := B1_lip (J :: ℓ'') hv'
      rw [B1_st_cons I _ hne]
      generalize J :: ℓ'' = ℓ' at *
      generalize hst' : B1_st ℓ' = st' at *
      generalize hst : B1_cl I st' = st
      have h2 := hcl st'
      rw [hst] at h2
      have hid : B1_cl I st = st := by
        have h3 := hcl st
        split_ifs at h2 h3 <;> omega
      simp only [hU, hD, hid, Nat.sub_self, zero_add]
      by_cases hc : B1_U st' ℓ' + B1_D st' ℓ' = 0
      · obtain ⟨H', hH', hUD⟩ := ihc hc
        have hU' : ∀ x, B1_U x ℓ' = st' - x := fun x => (hUD x).1
        have hD' : ∀ x, B1_D x ℓ' = x - H' := fun x => (hUD x).2
        simp only [hU', hD']
        refine ⟨fun h0 => ?_, fun h0 a => ?_⟩
        · rcases le_total I.2 H' with hh | hh
          · refine ⟨I.2, by split_ifs at h2 <;> omega, fun a => ?_⟩
            have h1 := hcl a
            constructor <;> split_ifs at h1 h2 <;> omega
          · refine ⟨H', by split_ifs at h2 <;> omega, fun a => ?_⟩
            have h1 := hcl a
            constructor <;> split_ifs at h1 h2 <;> omega
        · have h1 := hcl a
          constructor <;> split_ifs at h1 h2 <;> omega
      · have hn := ihn (by omega)
        refine ⟨fun h0 => ?_, fun _ a => ?_⟩
        · exfalso
          have := hn st
          omega
        · have h1 := hn (B1_cl I a)
          have h3 := L st st'
          have h4 := hcl a
          constructor <;> split_ifs at h4 h2 <;> omega

theorem B1_scanl_map {α : Type} (g : α → ℕ × ℕ) (L : List α) (s : ℕ) :
    List.scanl (fun z i => B1_cl (g i) z) s L = s :: B1_P s (L.map g) := by
  induction L generalizing s with
  | nil => rfl
  | cons a L ih => rw [List.scanl_cons, ih]; rfl

theorem B1_xF_eq {n : ℕ} (lo hi : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    xF lo hi i = (B1_P (startF lo hi) (List.ofFn (fun j => (lo j, hi j)))).getD i.val
      (startF lo hi) := by
  unfold xF
  have := B1_scanl_map (fun j : Fin (n+1) => (lo j, hi j)) (List.finRange (n+1)) (startF lo hi)
  rw [List.ofFn_eq_map]
  show ((List.finRange (n+1)).scanl (fun z i => B1_cl ((fun j : Fin (n+1) => (lo j, hi j)) i) z)
    (startF lo hi)).getD (i.val+1) (startF lo hi) = _
  rw [this, List.getD_cons_succ]

theorem B1_ofFn_getD {n : ℕ} (g : Fin n → ℕ × ℕ) (i : Fin n) :
    (List.ofFn g).getD i.val (0, 0) = g i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem B1_P_get : ∀ (ℓ : List (ℕ × ℕ)) (s k d : ℕ), k < ℓ.length → (∀ I ∈ ℓ, I.1 ≤ I.2) →
    (ℓ.getD k (0, 0)).1 ≤ (B1_P s ℓ).getD k d ∧ (B1_P s ℓ).getD k d ≤ (ℓ.getD k (0, 0)).2 := by
  intro ℓ
  induction ℓ with
  | nil => intro s k d hk; simp at hk
  | cons I ℓ ih =>
    intro s k d hk hv
    have hI : I.1 ≤ I.2 := hv I (by simp)
    cases k with
    | zero =>
      simp only [B1_P, List.getD_cons_zero]
      have h := B1_cl_spec I hI s
      split_ifs at h <;> omega
    | succ k =>
      simp only [B1_P, List.getD_cons_succ]
      exact ih _ k d (by simp at hk; omega) (fun K hK => hv K (by simp [hK]))

theorem B1_st_ofFn : ∀ (n : ℕ) (g : Fin (n+1) → ℕ × ℕ), (∀ i, (g i).1 ≤ (g i).2) →
    List.foldr (fun I z => B1_cl I z) (g (Fin.last n)).1 (List.ofFn g) = B1_st (List.ofFn g) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    rw [List.ofFn_succ, List.ofFn_zero]
    show B1_cl (g 0) (g 0).1 = (g 0).1
    simp only [B1_cl, min_eq_right (hg 0), max_self]
  | succ n ih =>
    intro g hg
    have hne : List.ofFn (fun i : Fin (n+1) => g i.succ) ≠ [] :=
      List.ne_nil_of_length_pos (by simp)
    rw [List.ofFn_succ, List.foldr_cons, B1_st_cons _ _ hne]
    congr 1
    rw [← Fin.succ_last]
    exact ih (fun i => g i.succ) (fun i => hg i.succ)

theorem B1_startF {n : ℕ} (lo hi : Fin (n+1) → ℕ) (hlh : ∀ i, lo i ≤ hi i) :
    startF lo hi = B1_st (List.ofFn (fun j => (lo j, hi j))) := by
  rw [← B1_st_ofFn n (fun j => (lo j, hi j)) hlh, List.ofFn_eq_map, List.foldr_map]
  unfold startF
  rw [List.foldl_reverse]
  rfl

theorem B1_upL_ofFn : ∀ (n : ℕ) (x : Fin (n+1) → ℕ) (p : ℕ),
    B1_upL p (List.ofFn x) = (x 0 - p) + upF x := by
  intro n
  induction n with
  | zero => intro x p; simp [upF, B1_upL, List.ofFn_succ]
  | succ n ih =>
    intro x p
    rw [List.ofFn_succ, B1_upL, ih (fun i => x i.succ) (x 0)]
    have e : upF x = (x (Fin.succ 0) - x 0) + upF (fun i => x i.succ) := by
      unfold upF
      rw [Fin.sum_univ_succ]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc]
    rw [e]

theorem B1_dnL_ofFn : ∀ (n : ℕ) (x : Fin (n+1) → ℕ) (p : ℕ),
    B1_dnL p (List.ofFn x) = (p - x 0) + downF x := by
  intro n
  induction n with
  | zero => intro x p; simp [downF, B1_dnL, List.ofFn_succ]
  | succ n ih =>
    intro x p
    rw [List.ofFn_succ, B1_dnL, ih (fun i => x i.succ) (x 0)]
    have e : downF x = (x 0 - x (Fin.succ 0)) + downF (fun i => x i.succ) := by
      unfold downF
      rw [Fin.sum_univ_succ]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc]
    rw [e]

theorem B1_forall2 : ∀ (n : ℕ) (c : Fin n → ℕ) (g : Fin n → ℕ × ℕ),
    (∀ i, (g i).1 ≤ c i ∧ c i ≤ (g i).2) →
      List.Forall₂ (fun c I => I.1 ≤ c ∧ c ≤ I.2) (List.ofFn c) (List.ofFn g) := by
  intro n
  induction n with
  | zero => intro c g _; rw [List.ofFn_zero, List.ofFn_zero]; exact List.Forall₂.nil
  | succ n ih =>
    intro c g h
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

def B1_r {n : ℕ} (w : Fin (n+1) → Bool) (i : Fin n) : ℕ :=
  if w i.castSucc = false ∧ w i.succ = true then 1 else 0

def B1_f {n : ℕ} (w : Fin (n+1) → Bool) (i : Fin n) : ℕ :=
  if w i.castSucc = true ∧ w i.succ = false then 1 else 0

def B1_b (v : Bool) : ℕ := if v = true then 1 else 0

theorem B1_rf {n : ℕ} (w : Fin (n+1) → Bool) :
    ∑ i, B1_r w i + ∑ i, B1_f w i = changes w := by
  rw [← Finset.sum_add_distrib, changes, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold B1_r B1_f
  cases w i.castSucc <;> cases w i.succ <;> simp

theorem B1_tele {n : ℕ} (w : Fin (n+1) → Bool) :
    ∑ i, B1_r w i + B1_b (w 0) = ∑ i, B1_f w i + B1_b (w (Fin.last n)) := by
  have h1 : ∑ i : Fin n, (B1_r w i + B1_b (w i.castSucc)) =
      ∑ i : Fin n, (B1_f w i + B1_b (w i.succ)) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold B1_r B1_f B1_b
    cases w i.castSucc <;> cases w i.succ <;> simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
  have h2 : ∑ j, B1_b (w j) = ∑ i : Fin n, B1_b (w i.castSucc) + B1_b (w (Fin.last n)) :=
    Fin.sum_univ_castSucc _
  have h3 : ∑ j, B1_b (w j) = B1_b (w 0) + ∑ i : Fin n, B1_b (w i.succ) :=
    Fin.sum_univ_succ _
  omega

theorem B1_word (hf ht : ℕ) {n : ℕ} (w : Fin (n+1) → Bool)
    (hw : changes w ≤ if w 0 then ht else hf) :
    ∑ i, B1_r w i ≤ (if w 0 then ht/2 else (hf+1)/2) ∧
      ∑ i, B1_f w i ≤ (if w 0 then (ht+1)/2 else hf/2) := by
  have h1 := B1_rf w
  have h2 := B1_tele w
  unfold B1_b at h2
  cases h0 : w 0 <;> cases hl : w (Fin.last n) <;> simp only [h0, hl] at hw h2 ⊢ <;>
    simp at hw h2 ⊢ <;> omega

theorem B1_cnt {n T : ℕ} (w : Fin T → Fin (n+1) → Bool) (i : Fin (n+1)) :
    countF w i = ∑ t, B1_b (w t i) := by
  unfold countF B1_b
  rw [Finset.card_filter]

theorem B1_sum_ite {n T : ℕ} (w : Fin T → Fin (n+1) → Bool) (A B : ℕ) :
    ∑ t, (if w t 0 then A else B) = countF w 0 * A + (T - countF w 0) * B := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T)))
    (fun t => w t 0 = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  unfold countF
  rw [show (Finset.univ.filter (fun t => ¬ (w t 0 = true))).card =
    T - (Finset.univ.filter (fun t => w t 0 = true)).card by omega]

theorem B1_count {n T : ℕ} (hf ht : ℕ) (w : Fin T → Fin (n+1) → Bool)
    (hw : ∀ t, changes (w t) ≤ (if w t 0 then ht else hf)) :
    upF (countF w) ≤ upCapF T hf ht (countF w 0) ∧
      downF (countF w) ≤ downCapF T hf ht (countF w 0) := by
  have stepU : ∀ i : Fin n, countF w i.succ - countF w i.castSucc ≤ ∑ t, B1_r (w t) i := by
    intro i
    rw [B1_cnt, B1_cnt]
    have h : ∀ t, B1_b (w t i.succ) ≤ B1_b (w t i.castSucc) + B1_r (w t) i := by
      intro t; unfold B1_b B1_r; cases w t i.castSucc <;> cases w t i.succ <;> simp
    have := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h t)
    rw [Finset.sum_add_distrib] at this
    omega
  have stepD : ∀ i : Fin n, countF w i.castSucc - countF w i.succ ≤ ∑ t, B1_f (w t) i := by
    intro i
    rw [B1_cnt, B1_cnt]
    have h : ∀ t, B1_b (w t i.castSucc) ≤ B1_b (w t i.succ) + B1_f (w t) i := by
      intro t; unfold B1_b B1_f; cases w t i.castSucc <;> cases w t i.succ <;> simp
    have := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h t)
    rw [Finset.sum_add_distrib] at this
    omega
  have sU : upF (countF w) ≤ ∑ t, ∑ i, B1_r (w t) i := by
    unfold upF
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ => stepU i)
  have sD : downF (countF w) ≤ ∑ t, ∑ i, B1_f (w t) i := by
    unfold downF
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ => stepD i)
  have wU : ∑ t, ∑ i, B1_r (w t) i ≤ ∑ t, (if w t 0 then ht/2 else (hf+1)/2) :=
    Finset.sum_le_sum (fun t _ => (B1_word hf ht (w t) (hw t)).1)
  have wD : ∑ t, ∑ i, B1_f (w t) i ≤ ∑ t, (if w t 0 then (ht+1)/2 else hf/2) :=
    Finset.sum_le_sum (fun t _ => (B1_word hf ht (w t) (hw t)).2)
  rw [B1_sum_ite] at wU wD
  unfold upCapF downCapF
  constructor
  · calc upF (countF w) ≤ _ := le_trans sU wU
      _ = _ := Nat.add_comm _ _
  · calc downF (countF w) ≤ _ := le_trans sD wD
      _ = _ := Nat.add_comm _ _

theorem B1_idU (T s A B : ℕ) (hs : s ≤ T) (hAB : B ≤ A) :
    (T - s) * A + s * B = T * B + (T - s) * (A - B) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hAB
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  ring

theorem B1_idD (T s A B : ℕ) (hs : s ≤ T) (hAB : A ≤ B) :
    (T - s) * A + s * B = T * A + s * (B - A) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hAB
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  ring

theorem B1_capU (T hf ht s c u v : ℕ) (h1 : ht ≤ hf + 1) (h2 : hf ≤ ht + 1) (hs : s ≤ T)
    (hc : c ≤ T) (hu : u + (s - c) ≤ v) (hv : v ≤ upCapF T hf ht c) : u ≤ upCapF T hf ht s := by
  unfold upCapF at *
  have hA : ht/2 ≤ (hf+1)/2 := by omega
  rw [B1_idU T s _ _ hs hA]
  rw [B1_idU T c _ _ hc hA] at hv
  rcases (show (hf+1)/2 - ht/2 = 0 ∨ (hf+1)/2 - ht/2 = 1 by omega) with e | e <;>
    rw [e] at hv ⊢ <;> simp only [mul_zero, mul_one, add_zero] at hv ⊢ <;> omega

theorem B1_capD (T hf ht s c u v : ℕ) (h1 : ht ≤ hf + 1) (h2 : hf ≤ ht + 1) (hs : s ≤ T)
    (hc : c ≤ T) (hu : u + (c - s) ≤ v) (hv : v ≤ downCapF T hf ht c) :
    u ≤ downCapF T hf ht s := by
  unfold downCapF at *
  have hA : hf/2 ≤ (ht+1)/2 := by omega
  rw [B1_idD T s _ _ hs hA]
  rw [B1_idD T c _ _ hc hA] at hv
  rcases (show (ht+1)/2 - hf/2 = 0 ∨ (ht+1)/2 - hf/2 = 1 by omega) with e | e <;>
    rw [e] at hv ⊢ <;> simp only [mul_zero, mul_one, add_zero] at hv ⊢ <;> omega

theorem B1_path {n : ℕ} (lo hi : Fin (n+1) → ℕ) (hlh : ∀ i, lo i ≤ hi i) :
    (∀ i, lo i ≤ xF lo hi i ∧ xF lo hi i ≤ hi i) ∧ xF lo hi 0 = startF lo hi := by
  have hv : ∀ I ∈ List.ofFn (fun j => (lo j, hi j)), I.1 ≤ I.2 := by
    intro I hI
    rw [List.mem_ofFn] at hI
    obtain ⟨i, rfl⟩ := hI
    exact hlh i
  constructor
  · intro i
    rw [B1_xF_eq]
    have := B1_P_get (List.ofFn (fun j => (lo j, hi j))) (startF lo hi) i.val (startF lo hi)
      (by have := i.isLt; simp; omega) hv
    rwa [B1_ofFn_getD] at this
  · have hmem : lo 0 ≤ startF lo hi ∧ startF lo hi ≤ hi 0 := by
      rw [B1_startF lo hi hlh, List.ofFn_succ]
      exact B1_st_mem (lo 0, hi 0) _ (hlh 0)
    rw [B1_xF_eq, List.ofFn_succ]
    simp only [B1_P, Fin.val_zero, List.getD_cons_zero]
    have h := B1_cl_spec (lo 0, hi 0) (hlh 0) (startF lo hi)
    split_ifs at h <;> simp only at * <;> omega

theorem B1_main (hf ht : ℕ) (h1 : ht ≤ hf + 1) (h2 : hf ≤ ht + 1) (n T : ℕ)
    (lo hi : Fin (n+1) → ℕ) (hlh : ∀ i, lo i ≤ hi i ∧ hi i ≤ T)
    (w : Fin T → Fin (n+1) → Bool) (hw : ∀ t, changes (w t) ≤ (if w t 0 then ht else hf))
    (hc : ∀ i, lo i ≤ countF w i ∧ countF w i ≤ hi i) :
    upF (xF lo hi) ≤ upCapF T hf ht (startF lo hi) ∧
      downF (xF lo hi) ≤ downCapF T hf ht (startF lo hi) := by
  have hlh' : ∀ i, lo i ≤ hi i := fun i => (hlh i).1
  have hv : ∀ I ∈ List.ofFn (fun j => (lo j, hi j)), I.1 ≤ I.2 := by
    intro I hI
    rw [List.mem_ofFn] at hI
    obtain ⟨i, rfl⟩ := hI
    exact hlh' i
  have hne : List.ofFn (fun j => (lo j, hi j)) ≠ [] := List.ne_nil_of_length_pos (by simp)
  obtain ⟨hpb, hp0⟩ := B1_path lo hi hlh'
  have hup : upF (xF lo hi) = B1_U (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) := by
    have e := B1_upL_ofFn n (xF lo hi) (xF lo hi 0)
    rw [Nat.sub_self, zero_add] at e
    rw [← e, hp0]
    have e2 : List.ofFn (xF lo hi) = B1_P (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) := by
      apply List.ext_getElem
      · simp [B1_P_length]
      · intro k h1 h2
        rw [List.getElem_ofFn, B1_xF_eq, List.getD_eq_getElem _ _ h2]
    rw [e2, B1_upL_P]
  have hdn : downF (xF lo hi) = B1_D (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) := by
    have e := B1_dnL_ofFn n (xF lo hi) (xF lo hi 0)
    rw [Nat.sub_self, zero_add] at e
    rw [← e, hp0]
    have e2 : List.ofFn (xF lo hi) = B1_P (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) := by
      apply List.ext_getElem
      · simp [B1_P_length]
      · intro k h1 h2
        rw [List.getElem_ofFn, B1_xF_eq, List.getD_eq_getElem _ _ h2]
    rw [e2, B1_dnL_P]
  have hm := B1_min _ _ (B1_forall2 (n+1) (countF w) (fun j => (lo j, hi j)) hc)
    (countF w 0) (countF w 0)
  have eu := B1_upL_ofFn n (countF w) (countF w 0)
  have ed := B1_dnL_ofFn n (countF w) (countF w 0)
  rw [Nat.sub_self, zero_add] at eu ed
  rw [eu, ed, Nat.sub_self, add_zero, add_zero] at hm
  obtain ⟨hcu, hcd⟩ := B1_count hf ht w hw
  have hsT : startF lo hi ≤ T := by
    have := (hpb 0).2; have := (hlh 0).2; omega
  have hcT : countF w 0 ≤ T := by
    have := (hc 0).2; have := (hlh 0).2; omega
  obtain ⟨hQc, hQn⟩ := B1_Q _ hne hv
  rw [← B1_startF lo hi hlh'] at hQc hQn
  rw [hup, hdn]
  by_cases hk : B1_U (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) +
      B1_D (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) = 0
  · constructor
    · have : B1_U (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) = 0 := by omega
      rw [this]; exact Nat.zero_le _
    · have : B1_D (startF lo hi) (List.ofFn (fun j => (lo j, hi j))) = 0 := by omega
      rw [this]; exact Nat.zero_le _
  · obtain ⟨q1, q2⟩ := hQn (by omega) (countF w 0)
    exact ⟨B1_capU T hf ht _ _ _ _ h1 h2 hsT hcT (le_trans q1 hm.1) hcu,
      B1_capD T hf ht _ _ _ _ h1 h2 hsT hcT (le_trans q2 hm.2) hcd⟩

theorem fits_iff_Fits (p b g k : ℕ) (w : Fin (k+1) → Bool) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
     ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
      C.size-PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size ≤ g ∧ C.output < k+2+C.size ∧ ∀ i : Fin (k+1),
        C.eval (List.ofFn (fun j : Fin k => decide (j.val < i.val)) ++ [false,true]) = w i) ↔
    Fits p b g k w := by
  unfold Fits
  constructor <;> rintro ⟨C, h1, h2, h3, h4, h5, h6, h7⟩ <;>
    exact ⟨C, h1, h2, h3, h4, h5, h6, fun i => by rw [← h7 i]; congr; funext j; congr⟩

theorem C_up {n : ℕ} (x : Fin (n+1) → ℕ) (k : ℕ) (hk : k ≤ n)
    (inst : DecidablePred (fun i : Fin n => i.val < k)) :
    (@Finset.filter (Fin n) (fun i => i.val < k) inst Finset.univ).sum
      (fun i => x i.succ - x i.castSucc) = B2_U x k := by
  unfold B2_U
  have e : ∑ i ∈ Finset.range k, (B2_xN x (i+1) - B2_xN x i)
      = ∑ i ∈ Finset.range n, (if i < k then (B2_xN x (i+1) - B2_xN x i) else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  rw [e, ← Fin.sum_univ_eq_sum_range (fun i => if i < k then (B2_xN x (i+1) - B2_xN x i) else 0) n,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : B2_xN x (i.val+1) = x i.succ := B2_xN_fin x i.succ
  have h2 : B2_xN x i.val = x i.castSucc := B2_xN_fin x i.castSucc
  by_cases hik : i.val < k <;> simp [hik, h1, h2]

theorem C_down {n : ℕ} (x : Fin (n+1) → ℕ) (k : ℕ) (hk : k ≤ n)
    (inst : DecidablePred (fun i : Fin n => i.val < k)) :
    (@Finset.filter (Fin n) (fun i => i.val < k) inst Finset.univ).sum
      (fun i => x i.castSucc - x i.succ) = B2_D x k := by
  unfold B2_D
  have e : ∑ i ∈ Finset.range k, (B2_xN x i - B2_xN x (i+1))
      = ∑ i ∈ Finset.range n, (if i < k then (B2_xN x i - B2_xN x (i+1)) else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  rw [e, ← Fin.sum_univ_eq_sum_range (fun i => if i < k then (B2_xN x i - B2_xN x (i+1)) else 0) n,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : B2_xN x (i.val+1) = x i.succ := B2_xN_fin x i.succ
  have h2 : B2_xN x i.val = x i.castSucc := B2_xN_fin x i.castSucc
  by_cases hik : i.val < k <;> simp [hik, h1, h2]

theorem C_cyc (T a e t : ℕ) (ht : t < T) :
    (∃ j : ℕ, a ≤ t + j * T ∧ t + j * T < e) ↔ B2_W T a e t = true := by
  rw [B2_W_iff]
  constructor
  · rintro ⟨j, h1, h2⟩
    exact ⟨t + j * T, Finset.mem_Ico.2 ⟨h1, h2⟩, by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]⟩
  · rintro ⟨k, hk, hkt⟩
    refine ⟨k / T, ?_⟩
    have e1 := Nat.mod_add_div k T
    rw [hkt] at e1
    have e2 : t + k / T * T = k := by rw [Nat.mul_comm]; exact e1
    rw [e2]
    exact Finset.mem_Ico.1 hk

theorem C_count {n T : ℕ} (w : Fin T → Fin (n+1) → Bool) (i : Fin (n+1))
    (inst : DecidablePred (fun t : Fin T => w t i = true)) :
    (@Finset.filter (Fin T) (fun t => w t i = true) inst Finset.univ).card = countF w i := by
  unfold countF
  convert rfl

end PEqualNP.Outside.L_meta_53169_aux

theorem PEqualNP.Outside.L_meta_53169 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (p b g : Nat),
  let fits := fun (n : Nat) (word : Fin (n+1) → Bool) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.size-PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size ≤ g ∧ C.output < n+2+C.size ∧ ∀ i : Fin (n+1),
        C.eval (List.ofFn (fun j : Fin n => decide (j.val < i.val)) ++ [false,true]) = word i
  let alternating := fun (z : Bool) (i : Nat) => if i % 2 = 0 then z else !z
  ∀ h : Bool → Nat, (∀ (z : Bool) (k : Nat),
    fits k (fun i => alternating z i.val) ↔ k ≤ h z) →
  ∀ (n T : Nat),
  ∀ x : Fin (n+1) → Nat, (∀ i, x i ≤ T) →
  let initial := x 0
  let up := fun (k : Nat) => ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)).sum
    (fun i => x i.succ - x i.castSucc)
  let down := fun (k : Nat) => ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)).sum
    (fun i => x i.castSucc - x i.succ)
  let upCap := fun s => (T-s)*((h false+1)/2) + s*(h true/2)
  let downCap := fun s => (T-s)*(h false/2) + s*((h true+1)/2)
  let realizes := fun (w : Fin T → Fin (n+1) → Bool) =>
    (∀ t, fits n (w t)) ∧ ∀ i, ((Finset.univ : Finset (Fin T)).filter (fun t => w t i)).card = x i
  let capacity := up n ≤ upCap initial ∧ down n ≤ downCap initial
  let cyclic := fun (t : Fin T) (i : Fin (n+1)) => decide (∃ j : Nat,
    down i.val ≤ t.val+j*T ∧ t.val+j*T < initial+up i.val)
  ((∃ w, realizes w) ↔ capacity) ∧ (capacity → realizes cyclic)) := by
  intro p b g fits alternating h hh n T x hx initial up down upCap downCap realizes capacity cyclic
  have key : ∀ k w, fits k w ↔ PEqualNP.Outside.L_meta_53169_aux.Fits p b g k w :=
    fun k w => PEqualNP.Outside.L_meta_53169_aux.fits_iff_Fits p b g k w
  have halt : ∀ (z : Bool) (k : ℕ),
      (fun i : Fin (k+1) => alternating z i.val) = (fun i => PEqualNP.Outside.L_meta_53169_aux.alt z i.val) := by
    intro z k; funext i
    by_cases hi : i.val % 2 = 0 <;> simp [alternating, PEqualNP.Outside.L_meta_53169_aux.alt, hi]
  obtain ⟨hA, hh1, hh2⟩ := PEqualNP.Outside.L_meta_53169_aux.A_main p b g h
    (fun z k => by rw [← halt z k, ← key]; exact hh z k)
  have hfw : ∀ v : Fin (n+1) → Bool, fits n v ↔
      PEqualNP.Outside.L_meta_53169_aux.changes v ≤ (if v 0 then h true else h false) := by
    intro v; rw [key, hA]; cases v 0 <;> rfl
  have hupk : ∀ k, k ≤ n → up k = PEqualNP.Outside.L_meta_53169_aux.B2_U x k :=
    fun k hk => PEqualNP.Outside.L_meta_53169_aux.C_up x k hk _
  have hdownk : ∀ k, k ≤ n → down k = PEqualNP.Outside.L_meta_53169_aux.B2_D x k :=
    fun k hk => PEqualNP.Outside.L_meta_53169_aux.C_down x k hk _
  have hupn : up n = PEqualNP.Outside.L_meta_53169_aux.upF x := by
    rw [hupk n le_rfl, PEqualNP.Outside.L_meta_53169_aux.B2_upF]
  have hdownn : down n = PEqualNP.Outside.L_meta_53169_aux.downF x := by
    rw [hdownk n le_rfl, PEqualNP.Outside.L_meta_53169_aux.B2_downF]
  have hcap : capacity ↔
      (PEqualNP.Outside.L_meta_53169_aux.upF x ≤ PEqualNP.Outside.L_meta_53169_aux.upCapF T (h false) (h true) (x 0) ∧
       PEqualNP.Outside.L_meta_53169_aux.downF x ≤ PEqualNP.Outside.L_meta_53169_aux.downCapF T (h false) (h true) (x 0)) := by
    show (up n ≤ upCap initial ∧ down n ≤ downCap initial) ↔ _
    rw [hupn, hdownn]
    exact Iff.rfl
  have nec : (∃ w, realizes w) → capacity := by
    rintro ⟨w, hw, hc⟩
    obtain ⟨hpath, hx0⟩ := PEqualNP.Outside.L_meta_53169_aux.B1_path x x (fun i => le_rfl)
    have hxF : PEqualNP.Outside.L_meta_53169_aux.xF x x = x :=
      funext fun i => le_antisymm (hpath i).2 (hpath i).1
    have hst : PEqualNP.Outside.L_meta_53169_aux.startF x x = x 0 := by rw [← hx0, hxF]
    have hm := PEqualNP.Outside.L_meta_53169_aux.B1_main (h false) (h true) hh1 hh2 n T x x
      (fun i => ⟨le_rfl, hx i⟩) w (fun t => (hfw (w t)).1 (hw t))
      (fun i => by
        have e : PEqualNP.Outside.L_meta_53169_aux.countF w i = x i := by
          rw [← PEqualNP.Outside.L_meta_53169_aux.C_count w i _]; exact hc i
        rw [e]; exact ⟨le_rfl, le_rfl⟩)
    rw [hxF, hst] at hm
    exact hcap.2 hm
  have hcy : cyclic = fun (t : Fin T) (i : Fin (n+1)) =>
      PEqualNP.Outside.L_meta_53169_aux.B2_W T (PEqualNP.Outside.L_meta_53169_aux.B2_D x i.val)
        (x 0 + PEqualNP.Outside.L_meta_53169_aux.B2_U x i.val) t.val := by
    funext t i
    have hi : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    show @decide (∃ j : Nat, down i.val ≤ t.val+j*T ∧ t.val+j*T < x 0 + up i.val) (Classical.propDecidable _) = _
    rw [hdownk i.val hi, hupk i.val hi, Bool.eq_iff_iff, ← PEqualNP.Outside.L_meta_53169_aux.C_cyc T _ _ t.val t.isLt]
    exact @decide_eq_true_iff _ (Classical.propDecidable _)
  have suf : capacity → realizes cyclic := by
    intro hcp
    obtain ⟨hu, hd⟩ := hcap.1 hcp
    obtain ⟨hA1, hA2⟩ := PEqualNP.Outside.L_meta_53169_aux.B2_main (h false) (h true) hh1 hh2 n T x hx hu hd
    rw [hcy]
    exact ⟨fun t => (hfw _).2 (hA1 t), fun i => by rw [PEqualNP.Outside.L_meta_53169_aux.C_count (fun (t : Fin T) (i : Fin (n+1)) => PEqualNP.Outside.L_meta_53169_aux.B2_W T (PEqualNP.Outside.L_meta_53169_aux.B2_D x i.val) (x 0 + PEqualNP.Outside.L_meta_53169_aux.B2_U x i.val) t.val) i _]; exact hA2 i⟩
  exact ⟨⟨nec, fun hc => ⟨cyclic, suf hc⟩⟩, suf⟩
