import PEqualNP.Defs
import PEqualNP.Outside.L_lib_388

namespace PEqualNP.Outside.L_lib_836_aux

section Walks

variable (d : ℕ)

abbrev State := Fin (d + 1) → Bool
abbrev Tab := (Fin (d + 2) → Bool) → Bool

def window (s : State d) (b : Bool) : Fin (d + 2) → Bool :=
  fun off => if h : off.val < d + 1 then s ⟨off.val, h⟩ else b

def shift (s : State d) (b : Bool) : State d :=
  fun j => if h : j.val + 1 < d + 1 then s ⟨j.val + 1, h⟩ else b

def walks : ℕ → (ℕ → Tab d) → State d → State d → ℕ
  | 0, _, s, s' => if s = s' then 1 else 0
  | L + 1, T, s, s' => ∑ b : Bool,
      if T 0 (window d s b) = true then walks L (fun i => T (i + 1)) (shift d s b) s' else 0

lemma walks_congr (L : ℕ) : ∀ (T T' : ℕ → Tab d), (∀ i < L, T i = T' i) →
    walks d L T = walks d L T' := by
  induction L with
  | zero => intro T T' _; rfl
  | succ L ih =>
    intro T T' h
    funext s s'
    simp only [walks, h 0 (Nat.succ_pos L),
      ih (fun i => T (i + 1)) (fun i => T' (i + 1)) (fun i hi => h (i + 1) (by omega))]

lemma walks_add (L₁ L₂ : ℕ) : ∀ (T : ℕ → Tab d) (s s' : State d),
    walks d (L₁ + L₂) T s s' = ∑ m, walks d L₁ T s m * walks d L₂ (fun i => T (L₁ + i)) m s' := by
  induction L₁ with
  | zero => intro T s s'; simp [walks]
  | succ L ih =>
    intro T s s'
    have hT : (fun i => T (L + 1 + i)) = (fun i => T (L + i + 1)) :=
      funext fun i => by rw [Nat.add_right_comm]
    rw [Nat.add_right_comm L 1 L₂]
    simp only [walks, ih, hT, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma app_eq {n : ℕ} (x : Fin n → Bool) {a b : ℕ} (ha : a < n) (hb : b < n) (h : a = b) :
    x ⟨a, ha⟩ = x ⟨b, hb⟩ := by
  subst h; rfl

abbrev Accepts (L : ℕ) (T : ℕ → Tab d) (s s' : State d) (x : Fin (L + (d + 1)) → Bool) : Prop :=
  (∀ j : Fin (d + 1), x ⟨j.val, by omega⟩ = s j ∧ x ⟨L + j.val, by omega⟩ = s' j) ∧
  ∀ i : Fin L, T i.val (fun off => x ⟨i.val + off.val, by omega⟩) = true

lemma card_accepts (L : ℕ) : ∀ (T : ℕ → Tab d) (s s' : State d),
    (Finset.univ.filter (Accepts d L T s s')).card = walks d L T s s' := by
  induction L with
  | zero =>
    intro T s s'
    simp only [walks]
    split_ifs with h
    · subst h
      rw [Finset.card_eq_one]
      refine ⟨fun k => s ⟨k.val, by omega⟩, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, -⟩
        funext k
        exact (h1 ⟨k.val, by omega⟩).1
      · rintro rfl
        exact ⟨fun j => ⟨rfl, congrArg s (Fin.ext (by simp))⟩, fun i => i.elim0⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨h1, -⟩
      exact h (funext fun j => (h1 j).1.symm.trans ((app_eq x _ _ (by simp)).trans (h1 j).2))
  | succ L ih =>
    intro T s s'
    simp only [walks, ← ih]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x ⟨d + 1, by omega⟩) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.filter_filter]
    split_ifs with hb
    · refine Finset.card_nbij' (fun x k => x ⟨k.val + 1, by omega⟩)
        (fun y k => if h : k.val = 0 then s 0 else y ⟨k.val - 1, by omega⟩) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
        obtain ⟨-, ⟨h1, h2⟩, hxb⟩ := hx
        refine ⟨Finset.mem_univ _, fun j => ⟨?_, ?_⟩, fun i => ?_⟩
        · show x ⟨j.val + 1, _⟩ = shift d s b j
          unfold shift
          split_ifs with hj
          · exact (h1 ⟨j.val + 1, hj⟩).1
          · exact (app_eq x _ _ (by omega)).trans hxb
        · show x ⟨L + j.val + 1, _⟩ = s' j
          exact (app_eq x _ _ (by omega)).trans (h1 j).2
        · refine Eq.trans ?_ (h2 ⟨i.val + 1, by omega⟩)
          show T (i.val + 1) _ = T (i.val + 1) _
          congr 1
          funext off
          exact app_eq x _ _ (by dsimp only; omega)
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
        obtain ⟨-, h1, h2⟩ := hy
        have hy : ∀ k (hk : k < d + 2), (if h : k = 0 then s 0 else y ⟨k - 1, by omega⟩) =
            window d s b ⟨k, hk⟩ := by
          intro k hk
          unfold window
          dsimp only
          split_ifs with h0 h0'
          · exact congrArg s (Fin.ext h0.symm)
          · omega
          · refine (h1 ⟨k - 1, by omega⟩).1.trans ?_
            unfold shift
            rw [dite_eq_left (by dsimp only; omega)]
            exact congrArg s (Fin.ext (by dsimp only; omega))
          · refine (h1 ⟨k - 1, by omega⟩).1.trans ?_
            unfold shift
            rw [dite_eq_right (by dsimp only; omega)]
        refine ⟨Finset.mem_univ _, ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩, ?_⟩
        · refine (hy j.val (by omega)).trans ?_
          unfold window
          rw [dite_eq_left j.isLt]
        · show (if h : L + 1 + j.val = 0 then s 0 else y ⟨L + 1 + j.val - 1, _⟩) = s' j
          rw [dite_eq_right (by omega)]
          exact (app_eq y _ _ (by omega)).trans (h1 j).2
        · obtain ⟨_ | i, hi⟩ := i
          · have hw : (fun off : Fin (d + 2) => (if h : 0 + off.val = 0 then s 0
                else y ⟨0 + off.val - 1, by omega⟩)) = window d s b := by
              funext off
              rw [← hy off.val off.isLt]
              simp only [zero_add]
            show T 0 (fun off => if h : 0 + off.val = 0 then s 0
                else y ⟨0 + off.val - 1, by omega⟩) = true
            rw [hw]
            exact hb
          · refine Eq.trans ?_ (h2 ⟨i, by omega⟩)
            show T (i + 1) _ = T (i + 1) _
            congr 1
            funext off
            show (if h : i + 1 + off.val = 0 then s 0 else y ⟨i + 1 + off.val - 1, _⟩) = _
            rw [dite_eq_right (by omega)]
            exact app_eq y _ _ (by dsimp only; omega)
        · show (if h : d + 1 = 0 then s 0 else y ⟨d + 1 - 1, _⟩) = b
          rw [dite_eq_right (by omega)]
          have h1d := (h1 ⟨d, Nat.lt_succ_self d⟩).1
          refine (app_eq y _ _ (by dsimp only; omega)).trans (h1d.trans ?_)
          unfold shift
          rw [dite_eq_right (by simp)]
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        obtain ⟨-, ⟨h1, -⟩, -⟩ := hx
        funext k
        show (if h : k.val = 0 then s 0 else x ⟨k.val - 1 + 1, _⟩) = x k
        split_ifs with h0
        · exact (h1 ⟨0, by omega⟩).1.symm.trans (app_eq x _ _ h0.symm)
        · exact app_eq x _ _ (by omega)
      · intro y _
        funext k
        show (if h : k.val + 1 = 0 then s 0 else y ⟨k.val + 1 - 1, _⟩) = y k
        rw [dite_eq_right (by omega)]
        exact app_eq y _ _ (by omega)
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨⟨h1, h2⟩, hxb⟩
      apply hb
      refine Eq.trans ?_ (h2 ⟨0, by omega⟩)
      show T 0 _ = T 0 _
      congr 1
      funext off
      unfold window
      split_ifs with ho
      · exact (h1 ⟨off.val, ho⟩).1.symm.trans (app_eq x _ _ (by simp))
      · exact hxb.symm.trans (app_eq x _ _ (by simp; omega))

end Walks

section Sweeps

variable (d : ℕ)

def copyTab : Tab d := fun win => decide (win (Fin.last (d + 1)) = win 0)

def rot (k : ℕ) (s : State d) : State d :=
  fun j => s ⟨(j.val + k) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

lemma rot_zero (s : State d) : rot d 0 s = s :=
  funext fun j => congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt]))

lemma rot_full (s : State d) : rot d (d + 1) s = s :=
  funext fun j => congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt]))

lemma shift_rot (k : ℕ) (s : State d) : shift d (rot d k s) (rot d k s 0) = rot d (k + 1) s := by
  funext j
  unfold shift rot
  split_ifs with h
  · exact congrArg s (Fin.ext (by dsimp only; congr 1; omega))
  · apply congrArg s
    apply Fin.ext
    dsimp only
    rw [show j.val + (k + 1) = k + (d + 1) by omega, Nat.add_mod_right, Fin.val_zero, zero_add]

lemma walks_copy_step (L : ℕ) (T : ℕ → Tab d) (hT : T 0 = copyTab d) (s s' : State d) :
    walks d (L + 1) T s s' = walks d L (fun i => T (i + 1)) (shift d s (s 0)) s' := by
  simp only [walks, hT, copyTab, window, Fintype.sum_bool]
  cases h : s 0 <;> simp [h]

lemma walks_copies (k : ℕ) : ∀ (T : ℕ → Tab d), (∀ i < k, T i = copyTab d) →
    ∀ (m : ℕ) (s s' : State d),
      walks d k T (rot d m s) s' = if rot d (m + k) s = s' then 1 else 0 := by
  induction k with
  | zero => intro T _ m s s'; rfl
  | succ k ih =>
    intro T hT m s s'
    rw [walks_copy_step d k T (hT 0 (by omega)), shift_rot,
      ih _ (fun i hi => hT (i + 1) (by omega)), show m + 1 + k = m + (k + 1) by omega]

end Sweeps

section Sweep

variable (e : ℕ)

def sweepTab (R : Bool → Bool → Bool → Bool) (i : ℕ) : Tab (e + 1) :=
  if i = 1 then fun win => R (win 0) (win ⟨e + 1, by omega⟩) (win (Fin.last (e + 2)))
  else copyTab (e + 1)

lemma mod_two (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h'
  · exact Nat.mod_eq_of_lt h'
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma shift_rot_one (s : State (e + 1)) (b : Bool) :
    shift (e + 1) (rot (e + 1) 1 s) b = rot (e + 1) 2 (Function.update s 1 b) := by
  funext j
  unfold shift rot
  rw [Function.update_apply]
  split_ifs with h1 h2 h2
  · rw [Fin.ext_iff] at h2
    simp only [Fin.val_one] at h2
    rw [mod_two _ _ (by omega)] at h2
    split_ifs at h2 <;> omega
  · exact congrArg s (Fin.ext rfl)
  · rfl
  · rw [Fin.ext_iff] at h2
    simp only [Fin.val_one] at h2
    rw [mod_two _ _ (by omega)] at h2
    split_ifs at h2 <;> omega

lemma walks_sweep (R : Bool → Bool → Bool → Bool) (s s' : State (e + 1)) :
    walks (e + 1) (e + 2) (sweepTab e R) s s' =
      ∑ b : Bool, if R (s 1) (s 0) b = true then
        (if Function.update s 1 b = s' then 1 else 0) else 0 := by
  rw [walks_copy_step (e + 1) (e + 1) _ (by simp [sweepTab])]
  conv_lhs => rw [← rot_zero (e + 1) s, shift_rot, zero_add]
  simp only [walks]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h0 : rot (e + 1) 1 s 0 = s 1 :=
    congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt (show 1 < e + 2 by omega)]))
  have hl : rot (e + 1) 1 s ⟨e + 1, by omega⟩ = s 0 := congrArg s (Fin.ext (by simp))
  have hR : sweepTab e R (0 + 1) (window (e + 1) (rot (e + 1) 1 s) b) = R (s 1) (s 0) b := by
    simp [sweepTab, window, ← h0, ← hl]
  rw [hR, shift_rot_one, walks_copies (e + 1) e _ (fun i hi => by simp [sweepTab]),
    show 2 + e = e + 1 + 1 by omega, rot_full]

end Sweep

section Plane

variable (e : ℕ)

def pack (t : Bool) (u : Fin e → Bool) : State (e + 1) := Fin.cons t (Fin.cons false u)

lemma pack_zero (t : Bool) (u : Fin e → Bool) : pack e t u 0 = t := by simp [pack]

lemma pack_one (t : Bool) (u : Fin e → Bool) : pack e t u 1 = false := by
  rw [← Fin.succ_zero_eq_one, pack, Fin.cons_succ, Fin.cons_zero]

def flipRule (old tag new : Bool) : Bool := decide (new = old) || (tag && new)

def clearRule (old tag new : Bool) : Bool := decide (new = (!tag && old))

lemma walks_flipSweep (t : Bool) (u : Fin e → Bool) (s' : State (e + 1)) :
    walks (e + 1) (e + 2) (sweepTab e flipRule) (pack e t u) s' =
      (if pack e t u = s' then 1 else 0) +
        (if t then (if Function.update (pack e t u) 1 true = s' then 1 else 0) else 0) := by
  have hu : Function.update (pack e t u) 1 false = pack e t u :=
    Function.update_eq_self_iff.2 (pack_one e t u).symm
  rw [walks_sweep, Fintype.sum_bool]
  cases t <;> simp [flipRule, pack_zero, pack_one, hu, add_comm]

lemma walks_clearSweep (s s' : State (e + 1)) (hs : s 0 = true ∨ s 1 = false) :
    walks (e + 1) (e + 2) (sweepTab e clearRule) s s' =
      if Function.update s 1 false = s' then 1 else 0 := by
  rw [walks_sweep, Fintype.sum_bool]
  rcases hs with hs | hs <;> simp [clearRule, hs]

def planeTab (seg : ℕ → Tab (e + 1)) (r : ℕ) : Tab (e + 1) :=
  if r < e + 2 then sweepTab e flipRule r
  else if r < 2 * (e + 2) then sweepTab e clearRule (r - (e + 2)) else seg (r - 2 * (e + 2))

lemma walks_plane (L' : ℕ) (seg : ℕ → Tab (e + 1)) (t : Bool) (u : Fin e → Bool)
    (s' : State (e + 1)) :
    walks (e + 1) (2 * (e + 2) + L') (planeTab e seg) (pack e t u) s' =
      (if t then 2 else 1) * walks (e + 1) L' seg (pack e t u) s' := by
  have hG : ∀ m, walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i)) m s' =
      ∑ m', walks (e + 1) (e + 2) (sweepTab e clearRule) m m' * walks (e + 1) L' seg m' s' := by
    intro m
    rw [walks_add, walks_congr (e + 1) (e + 2) _ (sweepTab e clearRule) (fun i hi => by
        simp [planeTab, show e + 2 + i < 2 * (e + 2) by omega]),
      walks_congr (e + 1) L' _ seg (fun i hi => by
        simp [planeTab, show ¬ e + 2 + (e + 2 + i) < 2 * (e + 2) by omega,
          show e + 2 + (e + 2 + i) - 2 * (e + 2) = i by omega])]
  have hu : Function.update (pack e t u) 1 false = pack e t u :=
    Function.update_eq_self_iff.2 (pack_one e t u).symm
  have hp : walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i)) (pack e t u) s' =
      walks (e + 1) L' seg (pack e t u) s' := by
    rw [hG]
    simp [walks_clearSweep e _ _ (Or.inr (pack_one e t u)), hu]
  have hq : walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i))
      (Function.update (pack e true u) 1 true) s' = walks (e + 1) L' seg (pack e true u) s' := by
    have h0 : Function.update (pack e true u) 1 true 0 = true := by
      rw [Function.update_of_ne zero_ne_one, pack_zero]
    have h1 : Function.update (Function.update (pack e true u) 1 true) 1 false = pack e true u := by
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.2 (pack_one e true u).symm
    rw [hG]
    simp [walks_clearSweep e _ _ (Or.inl h0), h1]
  rw [show 2 * (e + 2) + L' = e + 2 + (e + 2 + L') by omega, walks_add,
    walks_congr (e + 1) (e + 2) (planeTab e seg) (sweepTab e flipRule)
      (fun i hi => by simp [planeTab, hi])]
  simp only [walks_flipSweep, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, hp]
  cases t <;> simp [hq, two_mul]

end Plane

section Bridge

variable (d : ℕ)

lemma app_mod {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) (h : k % n < n) :
    x ⟨k % n, h⟩ = x ⟨k, hk⟩ := app_eq x _ _ (Nat.mod_eq_of_lt hk)

def extTab (L : ℕ) (tab : Fin L → Tab d) (k : ℕ) : Tab d :=
  if h : k < L then tab ⟨k, h⟩ else fun _ => true

lemma card_mod (L : ℕ) (tab : Fin L → Tab d) (s s' : State d) :
    (Finset.univ.filter (fun x : Fin (L + (d + 1)) → Bool =>
      (∀ j : Fin (d + 1), x ⟨j.val % (L + (d + 1)), Nat.mod_lt _ (by omega)⟩ = s j ∧
        x ⟨(L + j.val) % (L + (d + 1)), Nat.mod_lt _ (by omega)⟩ = s' j) ∧
      ∀ i : Fin L, tab i (fun off => x ⟨(i.val + off.val) % (L + (d + 1)),
        Nat.mod_lt _ (by omega)⟩) = true)).card =
    walks d L (extTab d L tab) s s' := by
  rw [← card_accepts]
  congr 1
  apply Finset.filter_congr
  intro x _
  refine and_congr (forall_congr' fun j => ?_) (forall_congr' fun i => ?_)
  · rw [app_mod x j.val (by omega), app_mod x (L + j.val) (by omega)]
  · have hw : (fun off : Fin (d + 2) => x ⟨(i.val + off.val) % (L + (d + 1)),
        Nat.mod_lt _ (by omega)⟩) = fun off => x ⟨i.val + off.val, by omega⟩ :=
      funext fun off => app_mod x _ (by omega) _
    rw [hw, extTab, dite_eq_left i.isLt]

end Bridge

section Seg

variable (d : ℕ)

abbrev Cell := Fin (2 ^ (d + 2) - 1) × (Fin (d + 3) → Bool)
abbrev Pair := (Fin (d + 1) → Bool) × (Fin (d + 1) → Bool)

def segOf (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d)
    (allowed : Finset (Pair d)) : ℕ → Tab (d + 1) :=
  extTab (d + 1) (2 ^ (d + 2) - 1) fun i win =>
    base3 (i, win) || decide ((i, win) ∈ allowed.image port3)

def Transfers (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d) : Prop :=
  ∀ allowed (s s' : State (d + 1)),
    walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 allowed) s s' =
      (if s = s' then 1 else 0) + (if s 0 = false ∧ s' 0 = true ∧
        ((fun j : Fin (d + 1) => s j.succ), (fun j : Fin (d + 1) => s' j.succ)) ∈ allowed
        then 1 else 0)

lemma seg388 : ∃ (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d),
    Function.Injective port3 ∧ (∀ p, base3 (port3 p) = false) ∧ Transfers d base3 port3 := by
  obtain ⟨base3, port3, hinj, hbase, hcount⟩ := PEqualNP.Outside.L_lib_388 (d + 1)
  refine ⟨base3, port3, hinj, hbase, fun allowed s s' => ?_⟩
  rw [segOf, ← card_mod]
  refine Eq.trans ?_ (hcount allowed s s')
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rfl

end Seg

section Main

variable (e L' : ℕ) (seg : ℕ → ℕ → Tab (e + 1)) (dg : ℕ → (Fin e → Bool) → (Fin e → Bool) → Bool)

def globalTab (q k : ℕ) : Tab (e + 1) :=
  planeTab e (seg (q - 1 - k / (2 * (e + 2) + L'))) (k % (2 * (e + 2) + L'))

lemma pack_inj {t t' : Bool} {u u' : Fin e → Bool} :
    pack e t u = pack e t' u' ↔ t = t' ∧ u = u' := by
  simp [pack, Fin.cons_inj]

lemma main_count
    (hF : ∀ β u (G : State (e + 1) → ℕ), ∑ m, walks (e + 1) L' (seg β) (pack e false u) m * G m =
      G (pack e false u) + ∑ v, if dg β u v = true then G (pack e true v) else 0)
    (hT : ∀ β u m, walks (e + 1) L' (seg β) (pack e true u) m = if pack e true u = m then 1 else 0)
    (q : ℕ) : ∀ (a : Bool) (u : Fin e → Bool) (b : Bool) (v : Fin e → Bool),
    walks (e + 1) (q * (2 * (e + 2) + L')) (globalTab e L' seg q) (pack e a u) (pack e b v) =
      if a = b then (if u = v then (if a then 2 ^ q else 1) else 0)
      else if a then 0 else ∑ β ∈ Finset.range q, if dg β u v = true then 2 ^ β else 0 := by
  induction q with
  | zero => intro a u b v; cases a <;> cases b <;> simp [walks, pack_inj]
  | succ q ih =>
    intro a u b v
    have hshift : (fun i => globalTab e L' seg (q + 1) (2 * (e + 2) + L' + i)) =
        globalTab e L' seg q := by
      funext i
      simp only [globalTab]
      rw [show 2 * (e + 2) + L' + i = i + 1 * (2 * (e + 2) + L') by ring,
        Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_mod_self_right]
      congr 2
      omega
    rw [Nat.succ_mul, Nat.add_comm (q * _), walks_add, hshift,
      walks_congr (e + 1) _ (globalTab e L' seg (q + 1)) (planeTab e (seg q)) (fun i hi => by
        simp [globalTab, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi])]
    simp only [walks_plane]
    cases a
    · have h := hF q u (fun m => walks (e + 1) (q * (2 * (e + 2) + L')) (globalTab e L' seg q) m
        (pack e b v))
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [h]
      simp only [ih]
      cases b
      · simp
      · have hs : (∑ x, if dg q u x = true then (if x = v then 2 ^ q else 0) else 0) =
            if dg q u v = true then 2 ^ q else 0 := by
          rw [Finset.sum_eq_single v (fun x _ hx => by simp [hx]) (by simp)]
          simp
        simp [Finset.sum_range_succ, hs]
    · simp only [↓reduceIte, hT, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ih]
      cases b <;> simp [pow_succ, mul_comm]

end Main

section Final

variable (d q : ℕ)

abbrev planeLen : ℕ := 2 * (d + 2) + (2 ^ (d + 2) - 1)

lemma planeLen_eq : planeLen d = 2 * (d + 2) + (2 ^ (d + 2) - 1) := rfl

abbrev Digit := Fin q × (Fin d → Bool) × (Fin d → Bool)

def dig (digits : Finset (Digit d q)) (β : ℕ)
    (u v : Fin d → Bool) : Bool :=
  if h : β < q then decide ((⟨β, h⟩, u, v) ∈ digits) else false

def allowedOf (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool) (β : ℕ) :
    Finset (Pair d) :=
  (Finset.univ.filter fun p : (Fin d → Bool) × (Fin d → Bool) => dg β p.1 p.2).image
    fun p => (Fin.cons false p.1, Fin.cons false p.2)

lemma pos_lt {A c P : ℕ} (hA : A < q) (hc : c < P) : A * P + c < q * P :=
  calc A * P + c < A * P + P := by omega
    _ = (A + 1) * P := by ring
    _ ≤ q * P := Nat.mul_le_mul_right _ hA

lemma pos_div {A c P : ℕ} (hc : c < P) : (A * P + c) / P = A := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]

lemma pos_mod {A c P : ℕ} (hc : c < P) : (A * P + c) % P = c := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

variable (base3 : Cell d → Bool) (port3 : Pair d → Cell d)

abbrev Slot := Fin (q * planeLen d) × (Fin (d + 3) → Bool)

def portCell (e : Digit d q) : Cell d := port3 (Fin.cons false e.2.1, Fin.cons false e.2.2)

lemma portCell_lt (e : Digit d q) : 2 * (d + 2) + (portCell d q port3 e).1.val < planeLen d := by
  have := (portCell d q port3 e).1.isLt
  have := planeLen_eq d
  omega

def portOf (e : Digit d q) : Slot d q :=
  (⟨(q - 1 - e.1.val) * planeLen d + (2 * (d + 2) + (portCell d q port3 e).1.val),
    pos_lt q (by have := e.1.isLt; omega) (portCell_lt d q port3 e)⟩, (portCell d q port3 e).2)

def baseOf (s : Slot d q) : Bool :=
  planeTab d (extTab (d + 1) (2 ^ (d + 2) - 1) fun i win => base3 (i, win))
    (s.1.val % planeLen d) s.2

lemma portOf_div (e : Digit d q) : (portOf d q port3 e).1.val / planeLen d = q - 1 - e.1.val :=
  pos_div (portCell_lt d q port3 e)

lemma portOf_mod (e : Digit d q) :
    (portOf d q port3 e).1.val % planeLen d = 2 * (d + 2) + (portCell d q port3 e).1.val :=
  pos_mod (portCell_lt d q port3 e)

lemma portOf_injective (hinj : Function.Injective port3) :
    Function.Injective (portOf d q port3) := by
  rintro ⟨β, u, v⟩ ⟨β', u', v'⟩ h
  have hd := portOf_div d q port3 (β, u, v)
  have hm := portOf_mod d q port3 (β, u, v)
  rw [h, portOf_div] at hd
  rw [h, portOf_mod] at hm
  have h2 := congrArg Prod.snd h
  simp only [portOf, portCell] at hd hm h2
  have hβ : β = β' := Fin.ext (by have := β.isLt; have := β'.isLt; omega)
  have hp := hinj (Prod.ext (Fin.ext (by omega)) h2)
  simp only [Prod.mk.injEq] at hp
  rw [hβ, Fin.cons_right_injective _ hp.1, Fin.cons_right_injective _ hp.2]

lemma baseOf_portOf (hbase : ∀ p, base3 (port3 p) = false) (e : Digit d q) :
    baseOf d q base3 (portOf d q port3 e) = false := by
  have hr := (portCell d q port3 e).1.isLt
  rw [baseOf, portOf_mod, planeTab, ite_eq_right (by omega), ite_eq_right (by omega), extTab,
    dite_eq_left (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact hbase (Fin.cons false e.2.1, Fin.cons false e.2.2)

lemma not_mem_port (digits : Finset (Digit d q)) {k : ℕ}
    (hk : k < q * planeLen d) (h : k % planeLen d < 2 * (d + 2)) (win : Fin (d + 3) → Bool) :
    (⟨k, hk⟩, win) ∉ digits.image (portOf d q port3) := by
  intro hmem
  obtain ⟨e, -, he⟩ := Finset.mem_image.1 hmem
  have := planeLen_eq d
  have hm := portOf_mod d q port3 e
  rw [he] at hm
  dsimp only at hm
  omega

lemma mem_port (digits : Finset (Digit d q)) {k : ℕ}
    (hk : k < q * planeLen d) (h1 : 2 * (d + 2) ≤ k % planeLen d)
    (h3 : k % planeLen d - 2 * (d + 2) < 2 ^ (d + 2) - 1) (win : Fin (d + 3) → Bool) :
    (⟨k, hk⟩, win) ∈ digits.image (portOf d q port3) ↔
      (⟨k % planeLen d - 2 * (d + 2), h3⟩, win) ∈
        (allowedOf d (dig d q digits) (q - 1 - k / planeLen d)).image port3 := by
  have hP := planeLen_eq d
  have hkd : k / planeLen d < q := (Nat.div_lt_iff_lt_mul (by omega)).2 hk
  constructor
  · intro hmem
    obtain ⟨⟨β, u, v⟩, he, heq⟩ := Finset.mem_image.1 hmem
    have hm := portOf_mod d q port3 (β, u, v)
    have hd := portOf_div d q port3 (β, u, v)
    rw [heq] at hm hd
    dsimp only [portCell] at hm hd
    refine Finset.mem_image.2 ⟨(Fin.cons false u, Fin.cons false v),
      Finset.mem_image.2 ⟨(u, v), ?_, rfl⟩, Prod.ext (Fin.ext (by dsimp only; omega)) ?_⟩
    · have hβ : q - 1 - k / planeLen d = β.val := by have := β.isLt; omega
      simp [hβ, dig, he]
    · have h2 := congrArg Prod.snd heq
      simp only [portOf] at h2
      exact h2
  · intro hmem
    obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.1 hmem
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 hp
    have hβ : q - 1 - k / planeLen d < q := by
      generalize k / planeLen d = t at hkd ⊢; omega
    have huv' := (Finset.mem_filter.1 huv).2
    rw [dig, dite_eq_left hβ, decide_eq_true_iff] at huv'
    refine Finset.mem_image.2 ⟨(⟨q - 1 - k / planeLen d, hβ⟩, u, v), huv', ?_⟩
    refine Prod.ext (Fin.ext ?_) ?_
    · show (q - 1 - (q - 1 - k / planeLen d)) * planeLen d +
          (2 * (d + 2) + (port3 (Fin.cons false u, Fin.cons false v)).1.val) = k
      rw [hpeq, show q - 1 - (q - 1 - k / planeLen d) = k / planeLen d by
        generalize k / planeLen d = t at hkd ⊢; omega]
      dsimp only
      rw [show 2 * (d + 2) + (k % planeLen d - 2 * (d + 2)) = k % planeLen d by omega,
        Nat.div_add_mod']
    · show (port3 (Fin.cons false u, Fin.cons false v)).2 = win
      rw [hpeq]

lemma tab_eq (digits : Finset (Digit d q)) (k : ℕ)
    (hk : k < q * planeLen d) :
    extTab (d + 1) (q * planeLen d) (fun i win => baseOf d q base3 (i, win) ||
        decide ((i, win) ∈ digits.image (portOf d q port3))) k =
      globalTab d (2 ^ (d + 2) - 1)
        (fun β => segOf d base3 port3 (allowedOf d (dig d q digits) β)) q k := by
  funext win
  have hP := planeLen_eq d
  have hr : k % planeLen d < planeLen d := Nat.mod_lt _ (by omega)
  simp only [extTab, dite_eq_left hk, globalTab, baseOf]
  unfold planeTab
  split_ifs with h1 h2
  · simp [not_mem_port d q port3 digits hk (by omega) win]
  · simp [not_mem_port d q port3 digits hk (by omega) win]
  · have h3 : k % planeLen d - 2 * (d + 2) < 2 ^ (d + 2) - 1 := by omega
    simp only [segOf, extTab, dite_eq_left h3, mem_port d q port3 digits hk (by omega) h3]

lemma hF_of (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (h388 : Transfers d base3 port3)
    (β : ℕ) (u : Fin d → Bool) (G : State (d + 1) → ℕ) :
    ∑ m, walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 (allowedOf d dg β))
      (pack d false u) m * G m =
      G (pack d false u) + ∑ v, if dg β u v = true then G (pack d true v) else 0 := by
  unfold Transfers at h388
  simp only [h388, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hset : Finset.univ.filter (fun m : State (d + 1) => pack d false u 0 = false ∧ m 0 = true ∧
      ((fun j : Fin (d + 1) => pack d false u j.succ), (fun j : Fin (d + 1) => m j.succ)) ∈
        allowedOf d dg β) = (Finset.univ.filter fun v => dg β u v = true).image (pack d true) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, allowedOf, pack,
      Fin.cons_zero, Fin.cons_succ, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hm0, a, b, hab, ha, hb⟩
      refine ⟨b, ?_, ?_⟩
      · rwa [← Fin.cons_right_injective _ ha]
      · rw [← Fin.cons_self_tail m, hm0]
        exact congrArg _ hb
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by simp, u, v, hv, rfl, by funext j; simp⟩
  rw [hset, Finset.sum_image fun x _ y _ h => ((pack_inj d).1 h).2]

lemma hT_of (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (h388 : Transfers d base3 port3)
    (β : ℕ) (u : Fin d → Bool) (m : State (d + 1)) :
    walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 (allowedOf d dg β)) (pack d true u) m =
      if pack d true u = m then 1 else 0 := by
  unfold Transfers at h388
  simp [h388, pack_zero]

end Final

end PEqualNP.Outside.L_lib_836_aux

open PEqualNP.Outside.L_lib_836_aux in
theorem PEqualNP.Outside.L_lib_836 :
∀ d q : Nat,
  let w := d+2
  let plane := 2*w + (2^w-1)
  let L := q*plane
  let n := L+w
  let D := Fin d → Bool
  let E := Fin q × D × D
  let S := Fin L × (Fin (w+1) → Bool)
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.succ_pos (d+1)) (Nat.le_add_left _ _))⟩ : Fin n)
  let pack := fun (tag : Bool) (payload : D) => (Fin.cases tag (Fin.cases false payload) : Fin w → Bool)
  ∃ (base : S → Bool) (port : E → S),
    Function.Injective port ∧ (∀ e, base (port e) = false) ∧
    (∀ e, (port e).1.val / plane = q-1-e.1.val) ∧
    ∀ digits : Finset E, ∀ (a b : Bool) (u v : D),
      let weight := (Finset.univ : Finset (Fin q)).sum
        (fun bit => if (bit,u,v) ∈ digits then 2^bit.val else 0)
      (Finset.univ.filter (fun x : Fin n → Bool =>
        (∀ j : Fin w, x (loc j.val) = pack a u j ∧ x (loc (L+j.val)) = pack b v j) ∧
        ∀ i : Fin L,
          let s : S := (i, fun off => x (loc (i.val+off.val)))
          base s = true ∨ s ∈ digits.image port)).card =
        if a = b then (if u = v then (if a then 2^q else 1) else 0)
        else if a then 0 else weight := by
  intro d q
  dsimp only
  obtain ⟨base3, port3, hinj3, hbase3, h388⟩ := seg388 d
  refine ⟨baseOf d q base3, portOf d q port3, portOf_injective d q port3 hinj3,
    baseOf_portOf d q base3 port3 hbase3, portOf_div d q port3, fun digits a b u v => ?_⟩
  have hcard := card_mod (d + 1) (q * planeLen d) (fun i win => baseOf d q base3 (i, win) ||
    decide ((i, win) ∈ digits.image (portOf d q port3))) (pack d a u) (pack d b v)
  rw [walks_congr (d + 1) _ _ _ (fun k hk => tab_eq d q base3 port3 digits k hk),
    main_count d _ _ (dig d q digits) (hF_of d base3 port3 _ h388)
      (hT_of d base3 port3 _ h388)] at hcard
  refine Eq.trans ?_ (hcard.trans ?_)
  · congr 1
    apply Finset.filter_congr
    intro x _
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rfl
  · rw [← Fin.sum_univ_eq_sum_range]
    simp [dig]
