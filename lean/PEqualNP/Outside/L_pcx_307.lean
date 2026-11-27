import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_307

open PEqualNP.ProofComplexity

private abbrev Raw (n b : ℕ) : Type := (i : Fin n) × Fin b

private def rawParity {n b : ℕ} (y : Raw n b → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin b)).filter (fun j => y ⟨i, j⟩ = true)).card)

private def vecParity {b : ℕ} (z : Fin b → Bool) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin b)).filter (fun j => z j = true)).card)

private def liftAxP {n b : ℕ} (F : Set (Clause (Fin n))) (A : Clause (Raw n b)) : Prop :=
  ∃ C ∈ F, ∃ y : Raw n b → Bool, (∀ lit ∈ C, rawParity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (Raw n b)).filter (fun r => r.1 ∈ C.image Prod.fst)).image
      (fun r => (r, !(y r)))

private def treeShape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

private def refutesP {n b : ℕ} (F : Set (Clause (Fin n))) (H K width : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b)),
    treeShape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H ∧ (line p).card ≤ width) ∧
    (N \ J).card ≤ K ∧ (∀ p ∈ N \ J, liftAxP F (line p)) ∧
    ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

private def bal (base m : ℕ) : ℕ :=
  let d := Nat.clog 2 m
  (2 ^ d - m) * base ^ (d - 1) + (2 * m - 2 ^ d) * base ^ d

private def badCycle {n : ℕ} (E : Fin n → Fin n → Bool → Prop) (m : ℕ) : Prop :=
  ∃ (v : ℕ → Fin n) (s : ℕ → Bool), v 0 = v m ∧
    Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i + 1)) (s i)

private def edgeFormula {n : ℕ} (E : Fin n → Fin n → Bool → Prop) : Set (Clause (Fin n)) :=
  {C | ∃ u v s a, E u v s ∧ C = {(u, !a), (v, a ^^ s)}}

private theorem clog_two_eq {k m : ℕ} (h1 : 2 ^ k < m) (h2 : m ≤ 2 ^ (k + 1)) :
    Nat.clog 2 m = k + 1 := by
  apply le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by decide)).mpr h2
  · by_contra hlt
    have hle : Nat.clog 2 m ≤ k := by omega
    have hmp := (Nat.clog_le_iff_le_pow (by decide)).mp hle
    omega

private theorem clog_two_double {g : ℕ} (hg : 1 ≤ g) :
    Nat.clog 2 (2 * g) = Nat.clog 2 g + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by decide), Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_right 2 (Nat.le_pow_clog (b := 2) (by decide) g)
  · by_contra hlt
    have hle : Nat.clog 2 (2 * g) ≤ Nat.clog 2 g := by omega
    have h1 := (Nat.clog_le_iff_le_pow (by decide)).mp hle
    cases hd : Nat.clog 2 g with
    | zero =>
      rw [hd] at h1
      simp at h1
      omega
    | succ d' =>
      have hgt1 : 1 < g := by
        by_contra hle1
        have hg1 : g = 1 := by omega
        subst hg1
        rw [Nat.clog_one_right] at hd
        omega
      have hpred := Nat.pow_pred_clog_lt_self 2 hgt1
      rw [hd] at hpred h1
      simp only [Nat.pred_succ] at hpred
      rw [Nat.pow_succ, Nat.mul_comm] at h1
      omega

private theorem bal_one (base : ℕ) : bal base 1 = 1 := by
  simp [bal, Nat.clog_one_right]

private theorem bal_eq_linear (base k m : ℕ) (h1 : 2 ^ k ≤ m) (h2 : m ≤ 2 ^ (k + 1)) :
    bal base m = (2 ^ (k + 1) - m) * base ^ k + (2 * m - 2 ^ (k + 1)) * base ^ (k + 1) := by
  by_cases heq : m = 2 ^ k
  · subst heq
    have hcl : Nat.clog 2 (2 ^ k) = k := Nat.clog_pow 2 k (by decide)
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    dsimp only [bal]
    rw [hcl, hp]
    have hsub1 : 2 ^ k - 2 ^ k = 0 := Nat.sub_self _
    have hsub2 : 2 * 2 ^ k - 2 ^ k = 2 ^ k := by omega
    have hsub3 : 2 * 2 ^ k - 2 * 2 ^ k = 0 := Nat.sub_self _
    rw [hsub1, hsub2, hsub3]
    simp
  · have hlt : 2 ^ k < m := by omega
    have hcl : Nat.clog 2 m = k + 1 := clog_two_eq hlt h2
    dsimp only [bal]
    rw [hcl]
    simp

private theorem bal_step {base : ℕ} (hb : 1 ≤ base) {m : ℕ} (hm : 1 ≤ m) :
    bal base (m + 1) = bal base m + (2 * base - 1) * base ^ (Nat.log 2 m) := by
  set k := Nat.log 2 m
  have h1 : 2 ^ k ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) m
  have hb1 := bal_eq_linear base k m h1 (by omega)
  have hb2 := bal_eq_linear base k (m + 1) (by omega) (by omega)
  rw [hb1, hb2]
  set p := 2 ^ (k + 1)
  set q := base ^ k
  have hpow : base ^ (k + 1) = q * base := Nat.pow_succ base k
  rw [hpow]
  have h2m : p ≤ 2 * m := by
    have : p = 2 * 2 ^ k := by dsimp only [p]; rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have ha1 : p - m = (p - (m + 1)) + 1 := by omega
  have ha2 : 2 * (m + 1) - p = (2 * m - p) + 2 := by omega
  rw [ha1, ha2]
  have hdist1 : (p - (m + 1) + 1) * q = (p - (m + 1)) * q + q := by rw [Nat.add_mul, Nat.one_mul]
  have hdist2 : (2 * m - p + 2) * (q * base) = (2 * m - p) * (q * base) + 2 * (q * base) := by
    rw [Nat.add_mul]
  have hdist3 : (2 * base - 1) * q = 2 * (q * base) - q := by
    have hle : 1 ≤ 2 * base := by omega
    rw [Nat.sub_mul, Nat.one_mul]
    have hm1 : 2 * base * q = 2 * (q * base) := by rw [Nat.mul_assoc, Nat.mul_comm base q]
    rw [hm1]
  have hqle : q ≤ 2 * (q * base) := by
    have hqb : q ≤ q * base := Nat.le_mul_of_pos_right q (by omega)
    omega
  rw [hdist1, hdist2, hdist3]
  omega

private theorem bal_mono {base : ℕ} (hb : 1 ≤ base) {m1 m2 : ℕ} (h1 : 1 ≤ m1) (hle : m1 ≤ m2) :
    bal base m1 ≤ bal base m2 := by
  induction hle with
  | refl => exact le_refl _
  | @step k hk ih =>
    have hk1 : 1 ≤ k := h1.trans hk
    rw [bal_step hb hk1]
    omega

private theorem bal_convex_step {base : ℕ} (hb : 1 ≤ base) {a c : ℕ} (ha : 1 ≤ a) (hac : a + 2 ≤ c) :
    bal base (a + 1) + bal base (c - 1) ≤ bal base a + bal base c := by
  have hc1 : 1 ≤ c - 1 := by omega
  have hceq : c = (c - 1) + 1 := by omega
  have hstep1 := bal_step hb ha
  have hstep2 := bal_step hb hc1
  rw [← hceq] at hstep2
  have hlog : Nat.log 2 a ≤ Nat.log 2 (c - 1) := Nat.log_mono_right (by omega)
  have hpow : base ^ (Nat.log 2 a) ≤ base ^ (Nat.log 2 (c - 1)) := Nat.pow_le_pow_right hb hlog
  have hmul : (2 * base - 1) * base ^ (Nat.log 2 a) ≤ (2 * base - 1) * base ^ (Nat.log 2 (c - 1)) :=
    Nat.mul_le_mul_left _ hpow
  omega

private theorem bal_split_eq {base : ℕ} {m : ℕ} (hm : 2 ≤ m) :
    bal base m = base * (bal base (m / 2) + bal base (m - m / 2)) := by
  by_cases hm2 : m = 2
  · subst hm2
    have hcl2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by decide)
    dsimp only [bal]
    rw [hcl2]
    simp [Nat.clog_one_right, Nat.mul_comm]
  · have hm3 : 3 ≤ m := by omega
    set d := Nat.clog 2 m
    have hd2 : 2 ≤ d := by
      by_contra hlt
      have hdle : d ≤ 1 := by omega
      have hle := (Nat.clog_le_iff_le_pow (by decide)).mp hdle
      omega
    set k := d - 1
    have hk1 : 1 ≤ k := by omega
    have hdk : d = k + 1 := by omega
    have hlt : 2 ^ k < m := by
      have hp := Nat.pow_pred_clog_lt_self 2 (by omega : 1 < m)
      simpa [d, k] using hp
    have hle : m ≤ 2 ^ (k + 1) := by
      have hp := Nat.le_pow_clog (b := 2) (by decide) m
      simpa [d, hdk] using hp
    set l1 := m / 2
    set l2 := m - l1
    have hp2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.pow_succ, Nat.mul_comm]
    have hp2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hl1_lo : 2 ^ (k - 1) ≤ l1 := by omega
    have hl1_hi : l1 ≤ 2 ^ k := by omega
    have hl2_lo : 2 ^ (k - 1) ≤ l2 := by omega
    have hl2_hi : l2 ≤ 2 ^ k := by omega
    have hksub : (k - 1) + 1 = k := by omega
    have hbm := bal_eq_linear base k m (by omega) hle
    have hbl1 := bal_eq_linear base (k - 1) l1 hl1_lo (by rw [hksub]; exact hl1_hi)
    have hbl2 := bal_eq_linear base (k - 1) l2 hl2_lo (by rw [hksub]; exact hl2_hi)
    rw [hksub] at hbl1 hbl2
    rw [hbm, hbl1, hbl2]
    have hpow1 : base ^ k = base * base ^ (k - 1) := by
      conv_lhs => rw [← hksub, Nat.pow_succ, Nat.mul_comm]
    have hpow2 : base ^ (k + 1) = base * base ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hs1 : (2 ^ k - l1) + (2 ^ k - l2) = 2 ^ (k + 1) - m := by omega
    have hs2 : (2 * l1 - 2 ^ k) + (2 * l2 - 2 ^ k) = 2 * m - 2 ^ (k + 1) := by omega
    rw [← hs1, ← hs2, hpow2, hpow1]
    ring

private theorem bal_jensen_aux {base : ℕ} (hb : 1 ≤ base) :
    ∀ dist a c : ℕ, 1 ≤ a → 1 ≤ c → (a ≤ c → c - a ≤ dist) → (c ≤ a → a - c ≤ dist) →
      bal base ((a + c) / 2) + bal base (a + c - (a + c) / 2) ≤ bal base a + bal base c := by
  intro dist
  induction dist with
  | zero =>
    intro a c _ _ h1 h2
    have heq : a = c := by omega
    subst heq
    have hdiv : (a + a) / 2 = a := by omega
    have hrem : a + a - a = a := by omega
    rw [hdiv, hrem]
  | succ d ih =>
    intro a c ha hc h1 h2
    by_cases hclose : (a ≤ c ∧ c - a ≤ 1) ∨ (c ≤ a ∧ a - c ≤ 1)
    · rcases hclose with ⟨hle, hdiff⟩ | ⟨hle, hdiff⟩
      · have hdiv : (a + c) / 2 = a := by omega
        have hrem : a + c - a = c := by omega
        rw [hdiv, hrem]
      · have hdiv : (a + c) / 2 = c := by omega
        have hrem : a + c - c = a := by omega
        rw [hdiv, hrem, Nat.add_comm]
    · by_cases hlt : a + 2 ≤ c
      · have hstep := bal_convex_step hb ha hlt
        have hsum : (a + 1) + (c - 1) = a + c := by omega
        have hih := ih (a + 1) (c - 1) (by omega) (by omega) (by omega) (by omega)
        rw [hsum] at hih
        omega
      · have hgt : c + 2 ≤ a := by omega
        have hstep := bal_convex_step hb hc hgt
        have hsum : (c + 1) + (a - 1) = a + c := by omega
        have hih := ih (c + 1) (a - 1) (by omega) (by omega) (by omega) (by omega)
        rw [hsum] at hih
        omega

private theorem bal_subadd {base : ℕ} (hb : 1 ≤ base) {m1 m2 : ℕ} (h1 : 1 ≤ m1) (h2 : 1 ≤ m2) :
    bal base (m1 + m2) ≤ base * (bal base m1 + bal base m2) := by
  rw [bal_split_eq (by omega : 2 ≤ m1 + m2)]
  apply Nat.mul_le_mul_left
  exact bal_jensen_aux hb (m1 + m2) m1 m2 h1 h2 (by omega) (by omega)

private def xorPrefix (s : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xorPrefix s k ^^ s k

private theorem xorPrefix_eq_true_iff_odd (s : ℕ → Bool) (m : ℕ) :
    xorPrefix s m = true ↔ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
  induction m with
  | zero => simp [xorPrefix]
  | succ m ih =>
    have hfilt : (Finset.range (m + 1)).filter (fun i => s i = true) =
        if s m = true then insert m ((Finset.range m).filter (fun i => s i = true))
        else (Finset.range m).filter (fun i => s i = true) := by
      rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : m ∉ (Finset.range m).filter (fun i => s i = true) := by simp
    rw [hfilt, xorPrefix]
    cases hsm : s m
    · simp only [Bool.false_eq_true, ite_false, Bool.xor_false]
      exact ih
    · simp only [ite_true, Finset.card_insert_of_notMem hnotmem, Bool.xor_true]
      constructor
      · intro hnot
        have hf : xorPrefix s m = false := by cases hc : xorPrefix s m <;> simp_all
        have hneven : ¬ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
          rw [← ih, hf]; decide
        rcases Nat.even_or_odd (((Finset.range m).filter (fun i => s i = true)).card) with he | ho
        · rcases he with ⟨k, hk⟩
          exact ⟨k, by omega⟩
        · exact absurd ho hneven
      · rintro ⟨k, hk⟩
        cases hc : xorPrefix s m
        · rfl
        · rcases ih.mp hc with ⟨j, hj⟩
          omega

private theorem xorPrefix_sub (s : ℕ → Bool) {i j : ℕ} (hij : i ≤ j) :
    xorPrefix s j = (xorPrefix s i ^^ xorPrefix (fun t => s (i + t)) (j - i)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp [xorPrefix]
  | succ d ih =>
    have heq : i + (d + 1) = (i + d) + 1 := by omega
    rw [heq, xorPrefix, xorPrefix, ih (Nat.le_add_right i d), Bool.xor_assoc]

private def HasEdge {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (s : Bool) : Prop :=
  (u, v, s) ∈ es ∨ (v, u, s) ∈ es

private def WalkIn {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (d : ℕ) : Prop :=
  ∃ (vs : ℕ → Fin n) (ss : ℕ → Bool),
    vs 0 = u ∧ vs d = v ∧ ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)

private def Connected {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) : Prop :=
  ∃ d : ℕ, WalkIn es u v d

private theorem connected_refl {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u : Fin n) :
    Connected es u u :=
  ⟨0, fun _ => u, fun _ => false, rfl, rfl, fun _ hi => by omega⟩

private theorem connected_step {n : ℕ} (es : List (Fin n × Fin n × Bool)) {u v w : Fin n} {s : Bool}
    (huv : Connected es u v) (hvw : HasEdge es v w s) : Connected es u w := by
  rcases huv with ⟨d, vs, ss, hv0, hvd, hstep⟩
  refine ⟨d + 1, fun i => if i ≤ d then vs i else w, fun i => if i < d then ss i else s,
    by simp [hv0], by simp, ?_⟩
  intro i hi
  by_cases hid : i < d
  · have h1 : i ≤ d := by omega
    have h2 : i + 1 ≤ d := by omega
    simp only [h1, h2, hid, ite_true]
    exact hstep i hid
  · have hieq : i = d := by omega
    rw [hieq]
    simp only [Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
      show ¬ (d < d) by omega, hvd]
    exact hvw

private theorem walk_eval {n : ℕ} {es : List (Fin n × Fin n × Bool)} {φ : Fin n → Bool}
    (hφ : ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2)
    {vs : ℕ → Fin n} {ss : ℕ → Bool} (d : ℕ)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    (φ (vs 0) ^^ φ (vs d)) = xorPrefix ss d := by
  induction d with
  | zero => simp [xorPrefix]
  | succ d ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast : (φ (vs d) ^^ φ (vs (d + 1))) = ss d := by
      rcases hstep d (Nat.lt_succ_self d) with h1 | h2
      · exact hφ _ h1
      · have h := hφ _ h2
        rw [Bool.xor_comm] at h
        exact h
    rw [xorPrefix, ← hprev, ← hlast]
    cases φ (vs 0) <;> cases φ (vs d) <;> cases φ (vs (d + 1)) <;> rfl

private theorem shortest_walk_nodup {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    ∀ p q : ℕ, p ≤ d → q ≤ d → vs p = vs q → p = q := by
  intro p q hp hq hpq
  by_contra hne
  wlog hlt : p < q generalizing p q
  · exact this q p hq hp hpq.symm (Ne.symm hne) (by omega)
  let d' := d - (q - p)
  have hd' : d' < d := by omega
  apply hmin d' hd'
  refine ⟨fun i => if i ≤ p then vs i else vs (i + (q - p)),
    fun i => if i < p then ss i else ss (i + (q - p)), ?_, ?_, ?_⟩
  · simp [hv0]
  · by_cases hdp : d' ≤ p
    · have hqd : q = d ∧ p = d' := by omega
      simp only [hdp, ite_true]
      rw [← hqd.2, hpq, hqd.1, hvd]
    · simp only [hdp, ite_false]
      have : d' + (q - p) = d := by omega
      rw [this, hvd]
  · intro i hi
    by_cases hip : i < p
    · have h1 : i ≤ p := by omega
      have h2 : i + 1 ≤ p := by omega
      simp only [h1, h2, hip, ite_true]
      exact hstep i (by omega)
    · by_cases hieq : i = p
      · subst hieq
        simp only [Nat.le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false,
          show ¬ (i < i) by omega]
        have h1 : i + 1 + (q - i) = q + 1 := by omega
        have h2 : i + (q - i) = q := by omega
        rw [h1, h2, hpq]
        exact hstep q (by omega)
      · have h1 : ¬ (i ≤ p) := by omega
        have h2 : ¬ (i + 1 ≤ p) := by omega
        have h3 : ¬ (i < p) := by omega
        simp only [h1, h2, h3, ite_false]
        have h4 : i + 1 + (q - p) = (i + (q - p)) + 1 := by omega
        rw [h4]
        exact hstep (i + (q - p)) (by omega)

private theorem shortest_walk_le_len {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    d ≤ es.length := by
  have hinj := shortest_walk_nodup hmin hv0 hvd hstep
  have hex : ∀ i : Fin d, ∃ k : Fin es.length,
      es[k.val] = (vs i.val, vs (i.val + 1), ss i.val) ∨
      es[k.val] = (vs (i.val + 1), vs i.val, ss i.val) := by
    intro i
    rcases hstep i.val i.isLt with h1 | h2
    · rcases List.mem_iff_getElem.mp h1 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inl hget⟩
    · rcases List.mem_iff_getElem.mp h2 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inr hget⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    have hi := hf i
    have hj := hf j
    rw [hij] at hi
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have heq := hi.symm.trans hj
      exact Fin.ext (hinj i.val j.val (by omega) (by omega) (congrArg Prod.fst heq))
    · have heq := hi.symm.trans hj
      have e1 := hinj i.val (j.val + 1) (by omega) (by omega) (congrArg Prod.fst heq)
      have e2 := hinj (i.val + 1) j.val (by omega) (by omega) (congrArg (fun x => x.2.1) heq)
      omega
    · have heq := hi.symm.trans hj
      have e1 := hinj (i.val + 1) j.val (by omega) (by omega) (congrArg Prod.fst heq)
      have e2 := hinj i.val (j.val + 1) (by omega) (by omega) (congrArg (fun x => x.2.1) heq)
      omega
    · have heq := hi.symm.trans hj
      have e1 := hinj (i.val + 1) (j.val + 1) (by omega) (by omega) (congrArg Prod.fst heq)
      exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa using hcard

private theorem consistent_or_bad {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v s, E u v s → E v u s) (es : List (Fin n × Fin n × Bool))
    (hE : ∀ e ∈ es, E e.1 e.2.1 e.2.2) :
    (∃ φ : Fin n → Bool, ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2) ∨
    (∃ j ≤ es.length, badCycle E j) := by
  classical
  induction es with
  | nil =>
    left
    exact ⟨fun _ => false, fun _ h => by simp at h⟩
  | cons e rest ih =>
    rcases e with ⟨u, v, s⟩
    have hE_e : E u v s := hE (u, v, s) (by simp)
    have hE_rest : ∀ e' ∈ rest, E e'.1 e'.2.1 e'.2.2 := fun e' he' => hE e' (by simp [he'])
    rcases ih hE_rest with ⟨φ, hφ⟩ | ⟨j, hj, hbad⟩
    · by_cases hconn : Connected rest u v
      · by_cases hsat : (φ u ^^ φ v) = s
        · left
          refine ⟨φ, fun e' he' => ?_⟩
          simp only [List.mem_cons] at he'
          rcases he' with rfl | hr
          · exact hsat
          · exact hφ e' hr
        · right
          let d := Nat.find hconn
          have hd_walk : WalkIn rest u v d := Nat.find_spec hconn
          have hd_min : ∀ d' < d, ¬ WalkIn rest u v d' := fun d' hd' => Nat.find_min hconn hd'
          rcases hd_walk with ⟨vs, ss, hv0, hvd, hstep⟩
          have hd_le : d ≤ rest.length := shortest_walk_le_len hd_min hv0 hvd hstep
          have hpar := walk_eval hφ d hstep
          rw [hv0, hvd] at hpar
          refine ⟨d + 1, by simp; omega, ?_⟩
          let vs' : ℕ → Fin n := fun i => if i ≤ d then vs i else u
          let ss' : ℕ → Bool := fun i => if i < d then ss i else s
          refine ⟨vs', ss', by simp [vs', hv0], ?_, ?_⟩
          · rw [← xorPrefix_eq_true_iff_odd]
            have hpre : xorPrefix ss' d = xorPrefix ss d := by
              have hgen : ∀ k ≤ d, xorPrefix ss' k = xorPrefix ss k := by
                intro k hk
                induction k with
                | zero => rfl
                | succ k ihk =>
                  simp only [xorPrefix, ihk (by omega), ss', show k < d by omega, ite_true]
              exact hgen d (Nat.le_refl d)
            rw [xorPrefix, hpre]
            simp only [ss', show ¬ (d < d) by omega, ite_false]
            rw [← hpar]
            cases hc : (φ u ^^ φ v) <;> cases hs : s <;> simp_all
          · intro i hi
            by_cases hid : i < d
            · simp only [vs', ss', show i ≤ d by omega, show i + 1 ≤ d by omega, hid, ite_true]
              rcases hstep i hid with h1 | h2
              · exact hE_rest _ h1
              · exact hsym _ _ _ (hE_rest _ h2)
            · have hieq : i = d := by omega
              subst hieq
              simp only [vs', ss', Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
                show ¬ (d < d) by omega, hvd]
              exact hsym u v s hE_e
      · left
        let delta : Bool := (φ u ^^ φ v) ^^ s
        let φ' : Fin n → Bool := fun z => if Connected rest u z then φ z ^^ delta else φ z
        refine ⟨φ', fun e' he' => ?_⟩
        simp only [List.mem_cons] at he'
        rcases he' with rfl | hr
        · simp only [φ', connected_refl rest u, ite_true, hconn, ite_false, delta]
          cases φ u <;> cases φ v <;> cases s <;> rfl
        · rcases e' with ⟨x, y, s'⟩
          have hxy : Connected rest u x ↔ Connected rest u y :=
            ⟨fun hx => connected_step rest hx (Or.inl hr),
             fun hy => connected_step rest hy (Or.inr hr)⟩
          have hbase : (φ x ^^ φ y) = s' := hφ (x, y, s') hr
          dsimp only [φ']
          by_cases hcx : Connected rest u x
          · have hcy : Connected rest u y := hxy.mp hcx
            simp only [hcx, hcy, ite_true, ← hbase]
            cases φ x <;> cases φ y <;> cases delta <;> rfl
          · have hcy : ¬ Connected rest u y := fun h => hcx (hxy.mpr h)
            simp only [hcx, hcy, ite_false]
            exact hbase
    · right
      exact ⟨j, by simp; omega, hbad⟩

private theorem shortest_bad_nodup {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (g : ℕ) (hmin : ∀ j < g, ¬ badCycle E j)
    {v : ℕ → Fin n} {s : ℕ → Bool} (hv : v 0 = v g)
    (hodd : Odd (((Finset.range g).filter (fun i => s i = true)).card))
    (hE : ∀ i < g, E (v i) (v (i + 1)) (s i)) :
    ∀ a c : ℕ, a < g → c < g → v a = v c → a = c := by
  intro a c ha hc hvac
  by_contra hne
  wlog hlt : a < c generalizing a c
  · exact this c a hc ha hvac.symm (Ne.symm hne) (by omega)
  have hpar_g : xorPrefix s g = true := (xorPrefix_eq_true_iff_odd s g).mpr hodd
  cases hmid : xorPrefix (fun t => s (a + t)) (c - a)
  · set m' := g - (c - a)
    have hm'_lt : m' < g := by omega
    apply hmin m' hm'_lt
    let v' : ℕ → Fin n := fun t => if t ≤ a then v t else v (t + (c - a))
    let s' : ℕ → Bool := fun t => if t < a then s t else s (t + (c - a))
    refine ⟨v', s', ?_, ?_, ?_⟩
    · have h1 : ¬ (m' ≤ a) := by omega
      have h2 : m' + (c - a) = g := by omega
      simp only [v', Nat.zero_le, ite_true, h1, ite_false, h2, hv]
    · rw [← xorPrefix_eq_true_iff_odd]
      have hpre : xorPrefix s' a = xorPrefix s a := by
        have hgen : ∀ k ≤ a, xorPrefix s' k = xorPrefix s k := by
          intro k hk
          induction k with
          | zero => rfl
          | succ k ih =>
            simp only [xorPrefix, ih (by omega), s', show k < a by omega, ite_true]
        exact hgen a (Nat.le_refl a)
      have htail : xorPrefix (fun t => s' (a + t)) (m' - a) =
          xorPrefix (fun t => s (c + t)) (g - c) := by
        have hlen : m' - a = g - c := by omega
        rw [hlen]
        have hgen : ∀ k, xorPrefix (fun t => s' (a + t)) k = xorPrefix (fun t => s (c + t)) k := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
            simp only [xorPrefix, ih, s', show ¬ (a + k < a) by omega, ite_false]
            have hidx : a + k + (c - a) = c + k := by omega
            rw [hidx]
        exact hgen (g - c)
      rw [xorPrefix_sub s' (by omega : a ≤ m'), hpre, htail]
      have hg1 := xorPrefix_sub s (by omega : c ≤ g)
      have hg2 := xorPrefix_sub s (by omega : a ≤ c)
      rw [hg2, hmid, Bool.xor_false] at hg1
      rw [← hg1, hpar_g]
    · intro i hi
      by_cases hia : i < a
      · simp only [v', s', show i ≤ a by omega, show i + 1 ≤ a by omega, hia, ite_true]
        exact hE i (by omega)
      · by_cases hieq : i = a
        · subst hieq
          simp only [v', s', Nat.le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false,
            show ¬ (i < i) by omega]
          have h1 : i + 1 + (c - i) = c + 1 := by omega
          have h2 : i + (c - i) = c := by omega
          rw [h1, h2, hvac]
          exact hE c (by omega)
        · simp only [v', s', show ¬ (i ≤ a) by omega, show ¬ (i + 1 ≤ a) by omega,
            show ¬ (i < a) by omega, ite_false]
          have h1 : i + 1 + (c - a) = (i + (c - a)) + 1 := by omega
          rw [h1]
          exact hE (i + (c - a)) (by omega)
  · apply hmin (c - a) (by omega)
    refine ⟨fun t => v (a + t), fun t => s (a + t), ?_,
      (xorPrefix_eq_true_iff_odd _ _).mp hmid, fun t ht => ?_⟩
    · simp only [Nat.add_zero, show a + (c - a) = c by omega, hvac]
    · dsimp only
      have h1 : a + (t + 1) = (a + t) + 1 := by omega
      rw [h1]
      exact hE (a + t) (by omega)

private theorem parity_flip_bit {b : ℕ} (z : Fin b → Bool) (j : Fin b) :
    vecParity (Function.update z j true) = !(vecParity (Function.update z j false)) := by
  unfold vecParity
  set S0 := (Finset.univ : Finset (Fin b)).filter (fun k => Function.update z j false k = true)
  set S1 := (Finset.univ : Finset (Fin b)).filter (fun k => Function.update z j true k = true)
  have hj0 : j ∉ S0 := by simp [S0]
  have hS1 : S1 = insert j S0 := by
    ext k
    simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update, hk]
  rw [hS1, Finset.card_insert_of_notMem hj0]
  rcases Nat.even_or_odd S0.card with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hno : ¬ Odd S0.card := by rintro ⟨m, hm⟩; omega
    have ho : Odd (S0.card + 1) := ⟨k, by omega⟩
    simp [hno, ho]
  · have ho : Odd S0.card := ⟨k, hk⟩
    have hno : ¬ Odd (S0.card + 1) := by rintro ⟨m, hm⟩; omega
    simp [ho, hno]

private theorem rawParity_update_same {n b : ℕ} (y : Raw n b → Bool) (i : Fin n) (j : Fin b) :
    rawParity (Function.update y ⟨i, j⟩ true) i = !(rawParity (Function.update y ⟨i, j⟩ false) i) := by
  have h1 : rawParity (Function.update y ⟨i, j⟩ true) i =
      vecParity (Function.update (fun k => y ⟨i, k⟩) j true) := by
    unfold rawParity vecParity
    apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update]
    by_cases hk : k = j
    · subst hk; simp
    · have hne : (⟨i, k⟩ : Raw n b) ≠ ⟨i, j⟩ := by intro h; exact hk (by simpa using h)
      simp [hk, hne]
  have h2 : rawParity (Function.update y ⟨i, j⟩ false) i =
      vecParity (Function.update (fun k => y ⟨i, k⟩) j false) := by
    unfold rawParity vecParity
    apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update]
    by_cases hk : k = j
    · subst hk; simp
    · have hne : (⟨i, k⟩ : Raw n b) ≠ ⟨i, j⟩ := by intro h; exact hk (by simpa using h)
      simp [hk, hne]
  rw [h1, h2]
  exact parity_flip_bit _ j

private theorem rawParity_update_ne {n b : ℕ} (y : Raw n b → Bool) {i i' : Fin n} (hne : i' ≠ i)
    (j : Fin b) (val : Bool) :
    rawParity (Function.update y ⟨i, j⟩ val) i' = rawParity y i' := by
  unfold rawParity
  apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
  ext k
  simp [Function.update, hne]

private theorem rawParity_eq_of_block_eq {n b : ℕ} {y1 y2 : Raw n b → Bool} {i : Fin n}
    (h : ∀ j : Fin b, y1 ⟨i, j⟩ = y2 ⟨i, j⟩) : rawParity y1 i = rawParity y2 i := by
  unfold rawParity
  apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
  ext j
  simp [h j]

private def subLeaves (N J : Finset (List Bool)) (p : List Bool) : Finset (List Bool) :=
  (N \ J).filter (fun q => p <+: q)

private theorem shape_prefix_inner {N J : Finset (List Bool)} (hs : treeShape N J)
    (p rest : List Bool) (hne : rest ≠ []) (hmem : p ++ rest ∈ N) : p ∈ J := by
  induction rest using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton r bit ih =>
    rw [← List.append_assoc] at hmem
    have hpr := hs.2.2.1 (p ++ r) bit hmem
    cases r with
    | nil => simpa using hpr
    | cons c cs => exact ih (by simp) (hs.2.1 hpr)

private theorem subLeaves_leaf {N J : Finset (List Bool)} (hs : treeShape N J)
    {p : List Bool} (hp : p ∈ N) (hni : p ∉ J) : subLeaves N J p = {p} := by
  ext q
  simp only [subLeaves, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hqn, _⟩, ⟨rest, rfl⟩⟩
    cases rest with
    | nil => simp
    | cons bit bs => exact absurd (shape_prefix_inner hs p (bit :: bs) (by simp) hqn) hni
  · rintro rfl
    exact ⟨⟨hp, hni⟩, List.prefix_refl _⟩

private theorem subLeaves_split {N J : Finset (List Bool)} {p : List Bool} (hp : p ∈ J) :
    subLeaves N J p = subLeaves N J (p ++ [false]) ∪ subLeaves N J (p ++ [true]) := by
  ext q
  simp only [subLeaves, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hq, ⟨rest, rfl⟩⟩
    cases rest with
    | nil => simp at hq; exact absurd hp hq.2
    | cons bit bs =>
      cases bit
      · left; exact ⟨hq, ⟨bs, by simp⟩⟩
      · right; exact ⟨hq, ⟨bs, by simp⟩⟩
  · rintro (⟨hq, ⟨rest, rfl⟩⟩ | ⟨hq, ⟨rest, rfl⟩⟩)
    · exact ⟨hq, ⟨false :: rest, by simp⟩⟩
    · exact ⟨hq, ⟨true :: rest, by simp⟩⟩

private theorem subLeaves_disjoint (N J : Finset (List Bool)) (p : List Bool) :
    Disjoint (subLeaves N J (p ++ [false])) (subLeaves N J (p ++ [true])) := by
  rw [Finset.disjoint_left]
  intro q h1 h2
  rcases (Finset.mem_filter.mp h1).2 with ⟨r1, hr1⟩
  rcases (Finset.mem_filter.mp h2).2 with ⟨r2, hr2⟩
  rw [← hr1] at hr2
  simp at hr2

private theorem shape_maxLen {N J : Finset (List Bool)} :
    ∃ H : ℕ, ∀ p ∈ N, p.length ≤ H := by
  classical
  by_cases hne : N.Nonempty
  · refine ⟨(N.image List.length).max' (hne.image _), fun p hp => ?_⟩
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  · refine ⟨0, fun p hp => absurd ⟨p, hp⟩ hne⟩

private theorem subLeaves_nonempty {N J : Finset (List Bool)} (hs : treeShape N J)
    {H : ℕ} (hH : ∀ p ∈ N, p.length ≤ H) :
    ∀ d : ℕ, ∀ p ∈ N, H - p.length ≤ d → (subLeaves N J p).Nonempty := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have hlen : p.length = H := by have := hH p hp; omega
    have hni : p ∉ J := by
      intro hpj
      have hf := (hs.2.2.2 p hpj).1
      have hfl := hH (p ++ [false]) hf
      simp [hlen] at hfl
    rw [subLeaves_leaf hs hp hni]
    exact Finset.singleton_nonempty p
  | succ d ih =>
    intro p hp hd
    by_cases hpj : p ∈ J
    · have hf := (hs.2.2.2 p hpj).1
      rw [subLeaves_split hpj]
      rcases ih (p ++ [false]) hf (by simp; omega) with ⟨q, hq⟩
      exact ⟨q, Finset.mem_union_left _ hq⟩
    · rw [subLeaves_leaf hs hp hpj]
      exact Finset.singleton_nonempty p

private theorem shape_leaves_le_pow {N J : Finset (List Bool)} (hs : treeShape N J)
    {H : ℕ} (hH : ∀ p ∈ N \ J, p.length ≤ H) :
    ∀ d : ℕ, ∀ p ∈ N, H - p.length ≤ d → (subLeaves N J p).card ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have hni : p ∉ J := by
      intro hpj
      rcases shape_maxLen (N := N) (J := J) with ⟨Hm, hHm⟩
      rcases subLeaves_nonempty hs hHm Hm (p ++ [false]) (hs.2.2.2 p hpj).1 (by omega) with ⟨q, hq⟩
      have hql := hH q (Finset.mem_filter.mp hq).1
      rcases (Finset.mem_filter.mp hq).2 with ⟨r, rfl⟩
      simp at hql
      omega
    rw [subLeaves_leaf hs hp hni]
    simp
  | succ d ih =>
    intro p hp hd
    by_cases hpj : p ∈ J
    · rcases hs.2.2.2 p hpj with ⟨hf, ht⟩
      rw [subLeaves_split hpj]
      have h1 := ih (p ++ [false]) hf (by simp; omega)
      have h2 := ih (p ++ [true]) ht (by simp; omega)
      have hu := Finset.card_union_le (subLeaves N J (p ++ [false])) (subLeaves N J (p ++ [true]))
      rw [Nat.pow_succ]
      omega
    · rw [subLeaves_leaf hs hp hpj]
      simp only [Finset.card_singleton]
      exact Nat.one_le_two_pow

private theorem bal_tree_le {base : ℕ} (hb : 1 ≤ base) {N J : Finset (List Bool)}
    (hs : treeShape N J) :
    bal base (N \ J).card ≤ ∑ l ∈ N \ J, base ^ l.length := by
  rcases shape_maxLen (N := N) (J := J) with ⟨H, hH⟩
  have hgen : ∀ d : ℕ, ∀ p ∈ N, H - p.length ≤ d →
      bal base (subLeaves N J p).card ≤ ∑ l ∈ subLeaves N J p, base ^ (l.length - p.length) := by
    intro d
    induction d with
    | zero =>
      intro p hp hd
      have hlen : p.length = H := by have := hH p hp; omega
      have hni : p ∉ J := by
        intro hpj
        have hfl := hH (p ++ [false]) (hs.2.2.2 p hpj).1
        simp [hlen] at hfl
      rw [subLeaves_leaf hs hp hni]
      simp [bal_one]
    | succ d ih =>
      intro p hp hd
      by_cases hpj : p ∈ J
      · rcases hs.2.2.2 p hpj with ⟨hf, ht⟩
        have hdisj := subLeaves_disjoint N J p
        have hne1 := Finset.card_pos.mpr (subLeaves_nonempty hs hH H (p ++ [false]) hf (by omega))
        have hne2 := Finset.card_pos.mpr (subLeaves_nonempty hs hH H (p ++ [true]) ht (by omega))
        rw [subLeaves_split hpj, Finset.card_union_of_disjoint hdisj,
          Finset.sum_union hdisj]
        have hsum_c : ∀ c : Bool,
            ∑ l ∈ subLeaves N J (p ++ [c]), base ^ (l.length - p.length) =
            base * ∑ l ∈ subLeaves N J (p ++ [c]), base ^ (l.length - (p ++ [c]).length) := by
          intro c
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rcases (Finset.mem_filter.mp hl).2 with ⟨r, rfl⟩
          have hsub : (p ++ [c] ++ r).length - p.length =
              ((p ++ [c] ++ r).length - (p ++ [c]).length) + 1 := by simp; omega
          rw [hsub, Nat.pow_succ, Nat.mul_comm]
        rw [hsum_c false, hsum_c true, ← Nat.mul_add]
        have h1 := ih (p ++ [false]) hf (by simp; omega)
        have h2 := ih (p ++ [true]) ht (by simp; omega)
        calc bal base ((subLeaves N J (p ++ [false])).card + (subLeaves N J (p ++ [true])).card)
            ≤ base * (bal base (subLeaves N J (p ++ [false])).card +
                bal base (subLeaves N J (p ++ [true])).card) := bal_subadd hb hne1 hne2
          _ ≤ base * ((∑ l ∈ subLeaves N J (p ++ [false]), base ^ (l.length - (p ++ [false]).length)) +
                (∑ l ∈ subLeaves N J (p ++ [true]), base ^ (l.length - (p ++ [true]).length))) := by
              exact Nat.mul_le_mul_left base (Nat.add_le_add h1 h2)
      · rw [subLeaves_leaf hs hp hpj]
        simp [bal_one]
  have hroot := hgen H [] hs.1 (by simp)
  have hsub : subLeaves N J [] = N \ J := by ext q; simp [subLeaves]
  rw [hsub] at hroot
  simpa using hroot

private def agrees {n : ℕ} (x : Fin n → Bool) (ask : List Bool → Fin n) (p : List Bool) : Prop :=
  ∀ k (hk : k < p.length), x (ask (p.take k)) = p[k]

private theorem agrees_nil {n : ℕ} (x : Fin n → Bool) (ask : List Bool → Fin n) :
    agrees x ask [] := fun _ hk => by simp at hk

private theorem agrees_append_singleton {n : ℕ} (x : Fin n → Bool) (ask : List Bool → Fin n)
    (p : List Bool) (c : Bool) :
    agrees x ask (p ++ [c]) ↔ agrees x ask p ∧ x (ask p) = c := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have h1 := h k (by simp; omega)
      have htake : (p ++ [c]).take k = p.take k := by
        rw [List.take_append_of_le_length (by omega)]
      have hget : (p ++ [c])[k]'(by simp; omega) = p[k] := by
        rw [List.getElem_append_left hk]
      rwa [htake, hget] at h1
    · have h1 := h p.length (by simp)
      have htake : (p ++ [c]).take p.length = p := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hget : (p ++ [c])[p.length]'(by simp) = c := by simp
      rwa [htake, hget] at h1
  · rintro ⟨hp, hxc⟩ k hk
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hlt : k < p.length
    · have htake : (p ++ [c]).take k = p.take k := List.take_append_of_le_length (by omega)
      have hget : (p ++ [c])[k]'(by simp; omega) = p[k] := List.getElem_append_left hlt
      rw [htake, hget]
      exact hp k hlt
    · have heq : k = p.length := by omega
      subst heq
      have htake : (p ++ [c]).take p.length = p := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hget : (p ++ [c])[p.length]'(by simp) = c := by simp
      rw [htake, hget]
      exact hxc

private theorem agrees_cons {n : ℕ} (x : Fin n → Bool) (i : Fin n)
    (askL askR : List Bool → Fin n) (bit : Bool) (q : List Bool) :
    let ask : List Bool → Fin n := fun p => match p with
      | [] => i
      | false :: rest => askL rest
      | true :: rest => askR rest
    agrees x ask (bit :: q) ↔ x i = bit ∧ agrees x (if bit = false then askL else askR) q := by
  intro ask
  constructor
  · intro h
    refine ⟨?_, fun k hk => ?_⟩
    · have h0 := h 0 (by simp)
      simpa [ask] using h0
    · have h1 := h (k + 1) (by simp; omega)
      cases bit <;> simpa [ask] using h1
  · rintro ⟨hxi, hq⟩ k hk
    cases k with
    | zero => simpa [ask] using hxi
    | succ k' =>
      have hk' : k' < q.length := by simp at hk; omega
      have h1 := hq k' hk'
      cases bit <;> simpa [ask] using h1

private theorem shape_glue {NL JL NR JR : Finset (List Bool)}
    (hsL : treeShape NL JL) (hsR : treeShape NR JR) :
    treeShape
      (insert ([] : List Bool) (NL.image (false :: ·) ∪ NR.image (true :: ·)))
      (insert ([] : List Bool) (JL.image (false :: ·) ∪ JR.image (true :: ·))) := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, hsL.2.1 hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hsR.2.1 hq, rfl⟩)
  · intro p bit hp
    cases p with
    | nil => exact Finset.mem_insert_self _ _
    | cons b rest =>
      simp only [List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      cases b
      · simp only [reduceCtorEq, false_or] at hp
        rcases hp with ⟨q, hq, heq⟩ | ⟨q, _, heq⟩
        · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
          subst hqeq
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨rest, hsL.2.2.1 rest bit hq, rfl⟩))
        · cases heq
      · simp only [reduceCtorEq, false_or] at hp
        rcases hp with ⟨q, _, heq⟩ | ⟨q, hq, heq⟩
        · cases heq
        · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
          subst hqeq
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨rest, hsR.2.2.1 rest bit hq, rfl⟩))
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.nil_append]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], hsL.1, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], hsR.1, rfl⟩))⟩
    · rcases hsL.2.2.2 q hq with ⟨hf, ht⟩
      simp only [List.cons_append]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩))⟩
    · rcases hsR.2.2.2 q hq with ⟨hf, ht⟩
      simp only [List.cons_append]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩))⟩

private theorem sdiff_glue (NL JL NR JR : Finset (List Bool)) :
    (insert ([] : List Bool) (NL.image (false :: ·) ∪ NR.image (true :: ·))) \
    (insert ([] : List Bool) (JL.image (false :: ·) ∪ JR.image (true :: ·))) =
    (NL \ JL).image (false :: ·) ∪ (NR \ JR).image (true :: ·) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  cases p with
  | nil => simp
  | cons b rest => cases b <;> simp

private theorem disj_cons_image (A B : Finset (List Bool)) :
    Disjoint (A.image (false :: ·)) (B.image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro p h1 h2
  rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨_, _, heq⟩
  cases heq

private theorem base_dt_leaves_lb {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v s, E u v s → E v u s)
    (g : ℕ) (hg : badCycle E g) (hmin : ∀ j < g, ¬ badCycle E j)
    (N0 J0 : Finset (List Bool)) (ask : List Bool → Fin n)
    (hs : treeShape N0 J0)
    (hleaf : ∀ l ∈ N0 \ J0, ∃ C ∈ edgeFormula E, ∀ x : Fin n → Bool, agrees x ask l → ¬ ClauseSat x C) :
    2 * g ≤ (N0 \ J0).card := by
  classical
  have hroot_in : [] ∈ J0 := by
    by_contra hni
    rcases hleaf [] (Finset.mem_sdiff.mpr ⟨hs.1, hni⟩) with ⟨C, ⟨u, v, s, a, _, rfl⟩, hns⟩
    apply hns (fun _ => !a) (agrees_nil _ _)
    exact ⟨(u, !a), by simp, rfl⟩
  rcases shape_maxLen (N := N0) (J := J0) with ⟨H0, hH0⟩
  have hfollow : ∀ d : ℕ, ∀ (ψ : Fin n → Bool) (p : List Bool),
      p ∈ N0 → H0 - p.length ≤ d → agrees ψ ask p →
      ∃ l ∈ subLeaves N0 J0 p, agrees ψ ask l := by
    intro d
    induction d with
    | zero =>
      intro ψ p hp hd hag
      have hlen : p.length = H0 := by have := hH0 p hp; omega
      have hni : p ∉ J0 := by
        intro hpj
        have hfl := hH0 (p ++ [false]) (hs.2.2.2 p hpj).1
        simp [hlen] at hfl
      exact ⟨p, by rw [subLeaves_leaf hs hp hni]; simp, hag⟩
    | succ d ih =>
      intro ψ p hp hd hag
      by_cases hpj : p ∈ J0
      · set c := ψ (ask p)
        have hpc : p ++ [c] ∈ N0 := by
          cases hc : c
          · exact (hs.2.2.2 p hpj).1
          · exact (hs.2.2.2 p hpj).2
        have hag' : agrees ψ ask (p ++ [c]) := (agrees_append_singleton ψ ask p c).mpr ⟨hag, rfl⟩
        rcases ih ψ (p ++ [c]) hpc (by simp; omega) hag' with ⟨l, hl, hagl⟩
        refine ⟨l, ?_, hagl⟩
        rw [subLeaves_split hpj]
        cases hc : c
        · rw [hc] at hl; exact Finset.mem_union_left _ hl
        · rw [hc] at hl; exact Finset.mem_union_right _ hl
      · exact ⟨p, by rw [subLeaves_leaf hs hp hpj]; simp, hag⟩
  have hbranch_lb : ∀ bit : Bool, g ≤ (subLeaves N0 J0 [bit]).card := by
    intro bit
    have hbit_mem : [bit] ∈ N0 := by
      cases bit
      · simpa using (hs.2.2.2 [] hroot_in).1
      · simpa using (hs.2.2.2 [] hroot_in).2
    have hchoose : ∀ l : List Bool, ∃ e : Fin n × Fin n × Bool,
        l ∈ subLeaves N0 J0 [bit] →
        E e.1 e.2.1 e.2.2 ∧ ∃ a : Bool, ∀ x : Fin n → Bool,
          agrees x ask l → ¬ ClauseSat x {(e.1, !a), (e.2.1, a ^^ e.2.2)} := by
      intro l
      by_cases hl : l ∈ subLeaves N0 J0 [bit]
      · have hlm := (Finset.mem_filter.mp hl).1
        rcases hleaf l hlm with ⟨C, ⟨u, v, s, a, hEuv, rfl⟩, hns⟩
        exact ⟨(u, v, s), fun _ => ⟨hEuv, a, hns⟩⟩
      · exact ⟨(ask [], ask [], false), fun h => absurd h hl⟩
    choose f hf using hchoose
    let es := (subLeaves N0 J0 [bit]).toList.map f
    have hE_es : ∀ e ∈ es, E e.1 e.2.1 e.2.2 := by
      intro e he
      rcases List.mem_map.mp he with ⟨l, hl, rfl⟩
      exact (hf l (Finset.mem_toList.mp hl)).1
    rcases consistent_or_bad E hsym es hE_es with ⟨φ, hφ⟩ | ⟨j, hj, hbad⟩
    · exfalso
      let ψ : Fin n → Bool := if φ (ask []) = bit then φ else fun z => !(φ z)
      have hψ0 : ψ (ask []) = bit := by
        dsimp only [ψ]
        split_ifs with h
        · exact h
        · cases h1 : φ (ask []) <;> cases h2 : bit <;> simp_all
      have hψE : ∀ e ∈ es, (ψ e.1 ^^ ψ e.2.1) = e.2.2 := by
        intro e he
        have h1 := hφ e he
        dsimp only [ψ]
        split_ifs
        · exact h1
        · cases φ e.1 <;> cases φ e.2.1 <;> simpa using h1
      have hag_bit : agrees ψ ask [bit] := by
        have := (agrees_append_singleton ψ ask [] bit).mpr ⟨agrees_nil ψ ask, hψ0⟩
        simpa using this
      rcases hfollow H0 ψ [bit] hbit_mem (by omega) hag_bit with ⟨l, hl, hagl⟩
      rcases (hf l hl).2 with ⟨a, hns⟩
      have hpar := hψE (f l) (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩)
      apply hns ψ hagl
      by_cases h1 : ψ (f l).1 = !a
      · exact ⟨((f l).1, !a), by simp, h1⟩
      · refine ⟨((f l).2.1, a ^^ (f l).2.2), by simp, ?_⟩
        cases hu : ψ (f l).1 <;> cases hv : ψ (f l).2.1 <;> cases ha : a <;> cases hs' : (f l).2.2 <;>
          simp [hu, hv, ha, hs'] at h1 hpar ⊢
    · have hjge : g ≤ j := by
        by_contra hlt
        exact hmin j (by omega) hbad
      have hlen : es.length = (subLeaves N0 J0 [bit]).card := by simp [es]
      omega
  have h1 := hbranch_lb false
  have h2 := hbranch_lb true
  have hsub : subLeaves N0 J0 [false] ∪ subLeaves N0 J0 [true] ⊆ N0 \ J0 := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hdisj : Disjoint (subLeaves N0 J0 [false]) (subLeaves N0 J0 [true]) := by
    simpa using subLeaves_disjoint N0 J0 []
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  omega

private theorem resolvent_falsify_left {V : Type} [DecidableEq V] {C D R : Clause V} {v : V}
    (h1 : (v, true) ∈ C) (h2 : (v, false) ∈ D) (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    {y : V → Bool} (hyR : ¬ ClauseSat y R) (hyv : y v = false) : ¬ ClauseSat y C := by
  rintro ⟨l, hlC, hyl⟩
  by_cases hlv : l = (v, true)
  · subst hlv; simp only at hyl; rw [hyv] at hyl; cases hyl
  · exact hyR ⟨l, hR ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlC⟩), hyl⟩

private theorem resolvent_falsify_right {V : Type} [DecidableEq V] {C D R : Clause V} {v : V}
    (h1 : (v, true) ∈ C) (h2 : (v, false) ∈ D) (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    {y : V → Bool} (hyR : ¬ ClauseSat y R) (hyv : y v = true) : ¬ ClauseSat y D := by
  rintro ⟨l, hlD, hyl⟩
  by_cases hlv : l = (v, false)
  · subst hlv; simp only at hyl; rw [hyv] at hyl; cases hyl
  · exact hyR ⟨l, hR ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlD⟩), hyl⟩

private def closedBlocks {n b : ℕ} (D : Finset (Raw n b)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j : Fin b, (⟨i, j⟩ : Raw n b) ∈ D)

private def openBitCount {n b : ℕ} (D : Finset (Raw n b)) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin b => (⟨i, j⟩ : Raw n b) ∈ D)).card

private def openTotal {n b : ℕ} (D : Finset (Raw n b)) : ℕ :=
  ∑ i ∈ Finset.univ \ closedBlocks D, openBitCount D i

private theorem openBitCount_insert_same {n b : ℕ} (D : Finset (Raw n b)) (i : Fin n) (j : Fin b)
    (hnot : (⟨i, j⟩ : Raw n b) ∉ D) :
    openBitCount (insert ⟨i, j⟩ D) i = openBitCount D i + 1 := by
  unfold openBitCount
  have hfilt : Finset.univ.filter (fun k : Fin b => (⟨i, k⟩ : Raw n b) ∈ insert ⟨i, j⟩ D) =
      insert j (Finset.univ.filter (fun k : Fin b => (⟨i, k⟩ : Raw n b) ∈ D)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro (heq | hmem)
      · left; simpa using heq
      · right; exact hmem
    · rintro (rfl | hmem)
      · left; rfl
      · right; exact hmem
  rw [hfilt, Finset.card_insert_of_notMem]
  simp [hnot]

private theorem openBitCount_insert_ne {n b : ℕ} (D : Finset (Raw n b)) {i i' : Fin n}
    (hne : i' ≠ i) (j : Fin b) :
    openBitCount (insert ⟨i, j⟩ D) i' = openBitCount D i' := by
  unfold openBitCount
  congr 1
  ext k
  simp [hne]

private theorem mem_closedBlocks_iff_card {n b : ℕ} (D : Finset (Raw n b)) (i : Fin n) :
    i ∈ closedBlocks D ↔ openBitCount D i = b := by
  unfold closedBlocks openBitCount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have : Finset.univ.filter (fun j : Fin b => (⟨i, j⟩ : Raw n b) ∈ D) = Finset.univ := by
      ext j; simp [h j]
    rw [this]; simp
  · intro hc j
    have heq : Finset.univ.filter (fun k : Fin b => (⟨i, k⟩ : Raw n b) ∈ D) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hc)
    have : j ∈ Finset.univ.filter (fun k : Fin b => (⟨i, k⟩ : Raw n b) ∈ D) := by rw [heq]; simp
    exact (Finset.mem_filter.mp this).2

private theorem project_tree {n b : ℕ} (hn : 0 < n) (hb : 0 < b)
    (F : Set (Clause (Fin n))) (H : ℕ)
    (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b))
    (hs : treeShape N J)
    (hH : ∀ p ∈ N, p.length ≤ H)
    (hax : ∀ p ∈ N \ J, liftAxP F (line p))
    (hres : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ (d : ℕ) (p : List Bool), p ∈ N → H - p.length ≤ d →
      ∀ (D : Finset (Raw n b)) (val : Raw n b → Bool),
        (∀ y : Raw n b → Bool, (∀ r ∈ D, y r = val r) → ¬ ClauseSat y (line p)) →
        ∃ (N0 J0 : Finset (List Bool)) (ask : List Bool → Fin n),
          treeShape N0 J0 ∧
          (∀ l ∈ N0 \ J0, p.length + b * l.length ≤ H + openTotal D) ∧
          (∑ l ∈ N0 \ J0, (2 ^ (b - 1)) ^ l.length ≤ 2 ^ openTotal D * (subLeaves N J p).card) ∧
          (∀ l ∈ N0 \ J0, ∃ C ∈ F, ∀ x : Fin n → Bool,
            (∀ i ∈ closedBlocks D, x i = rawParity val i) →
            agrees x ask l → ¬ ClauseSat x C) := by
  classical
  intro d
  induction d with
  | zero =>
    intro p hp hd D val hinv
    have hlen : p.length = H := by have := hH p hp; omega
    have hni : p ∉ J := by
      intro hpj
      have hfl := hH (p ++ [false]) (hs.2.2.2 p hpj).1
      simp [hlen] at hfl
    rcases hax p (Finset.mem_sdiff.mpr ⟨hp, hni⟩) with ⟨C, hCF, y0, hy0, hlp⟩
    have hblock : ∀ lit ∈ C, lit.1 ∈ closedBlocks D ∧ rawParity val lit.1 = rawParity y0 lit.1 := by
      intro lit hlit
      have hmemD : ∀ j : Fin b, (⟨lit.1, j⟩ : Raw n b) ∈ D := by
        intro j
        by_contra hnot
        have hlit_in : (⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)) ∈ line p := by
          rw [hlp]
          exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨lit, hlit, rfl⟩⟩, rfl⟩
        apply hinv (Function.update val ⟨lit.1, j⟩ (!(y0 ⟨lit.1, j⟩)))
        · intro r hr
          have hne : r ≠ ⟨lit.1, j⟩ := fun h => hnot (h ▸ hr)
          simp [Function.update, hne]
        · exact ⟨(⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)), hlit_in, by simp⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemD⟩, ?_⟩
      apply rawParity_eq_of_block_eq
      intro j
      have hlit_in : (⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)) ∈ line p := by
        rw [hlp]
        exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨lit, hlit, rfl⟩⟩, rfl⟩
      have hns := hinv val (fun _ _ => rfl)
      have hne : val ⟨lit.1, j⟩ ≠ !(y0 ⟨lit.1, j⟩) := fun heq => hns ⟨_, hlit_in, heq⟩
      cases h1 : val ⟨lit.1, j⟩ <;> cases h2 : y0 ⟨lit.1, j⟩ <;> simp_all
    refine ⟨{[]}, ∅, fun _ => ⟨0, hn⟩, ⟨by simp, by simp, fun q bit hq => by
        rw [Finset.mem_singleton] at hq
        have := congrArg List.length hq
        simp at this, fun q hq => by simp at hq⟩, ?_, ?_, ?_⟩
    · intro l hl
      simp only [Finset.sdiff_empty, Finset.mem_singleton] at hl
      subst hl
      simp; omega
    · rw [subLeaves_leaf hs hp hni]
      simp only [Finset.sdiff_empty, Finset.sum_singleton, List.length_nil, pow_zero,
        Finset.card_singleton, Nat.mul_one]
      exact Nat.one_le_two_pow
    · intro l hl
      simp only [Finset.sdiff_empty, Finset.mem_singleton] at hl
      subst hl
      refine ⟨C, hCF, fun x hx _ => ?_⟩
      rintro ⟨lit, hlit, hxl⟩
      rcases hblock lit hlit with ⟨hcl, hpeq⟩
      have hx1 := hx lit.1 hcl
      rw [hx1, hpeq] at hxl
      exact hy0 lit hlit hxl
  | succ d ih =>
    intro p hp hd D val hinv
    by_cases hpj : p ∈ J
    · rcases hs.2.2.2 p hpj with ⟨hf, ht⟩
      rcases hres p hpj with ⟨v, hv1, hv2, hReq⟩
      by_cases hvD : v ∈ D
      · cases hval : val v
        · have hinvF : ∀ y : Raw n b → Bool, (∀ r ∈ D, y r = val r) → ¬ ClauseSat y (line (p ++ [false])) := by
            intro y hy
            exact resolvent_falsify_left hv1 hv2 hReq (hinv y hy) (by rw [hy v hvD, hval])
          rcases ih (p ++ [false]) hf (by simp; omega) D val hinvF with
            ⟨N0, J0, ask, hs0, hH0, hK0, hS0⟩
          refine ⟨N0, J0, ask, hs0, ?_, ?_, hS0⟩
          · intro l hl
            have := hH0 l hl
            simp at this
            omega
          · have hle : (subLeaves N J (p ++ [false])).card ≤ (subLeaves N J p).card := by
              rw [subLeaves_split hpj]
              exact Finset.card_le_card Finset.subset_union_left
            exact hK0.trans (Nat.mul_le_mul_left _ hle)
        · have hinvT : ∀ y : Raw n b → Bool, (∀ r ∈ D, y r = val r) → ¬ ClauseSat y (line (p ++ [true])) := by
            intro y hy
            exact resolvent_falsify_right hv1 hv2 hReq (hinv y hy) (by rw [hy v hvD, hval])
          rcases ih (p ++ [true]) ht (by simp; omega) D val hinvT with
            ⟨N0, J0, ask, hs0, hH0, hK0, hS0⟩
          refine ⟨N0, J0, ask, hs0, ?_, ?_, hS0⟩
          · intro l hl
            have := hH0 l hl
            simp at this
            omega
          · have hle : (subLeaves N J (p ++ [true])).card ≤ (subLeaves N J p).card := by
              rw [subLeaves_split hpj]
              exact Finset.card_le_card Finset.subset_union_right
            exact hK0.trans (Nat.mul_le_mul_left _ hle)
      · rcases v with ⟨i, j⟩
        set D' := insert (⟨i, j⟩ : Raw n b) D
        set val0 := Function.update val ⟨i, j⟩ false
        set val1 := Function.update val ⟨i, j⟩ true
        have hi_not_cl : i ∉ closedBlocks D := by
          intro hcl
          exact hvD ((Finset.mem_filter.mp hcl).2 j)
        have hki_lt : openBitCount D i < b := by
          have hle : openBitCount D i ≤ b := by
            have := Finset.card_le_univ (Finset.univ.filter (fun k : Fin b => (⟨i, k⟩ : Raw n b) ∈ D))
            simpa [openBitCount] using this
          have hne : openBitCount D i ≠ b := fun heq => hi_not_cl ((mem_closedBlocks_iff_card D i).mpr heq)
          omega
        have hinv0 : ∀ y : Raw n b → Bool, (∀ r ∈ D', y r = val0 r) →
            ¬ ClauseSat y (line (p ++ [false])) := by
          intro y hy
          have hyD : ∀ r ∈ D, y r = val r := by
            intro r hr
            have hne : r ≠ ⟨i, j⟩ := fun h => hvD (h ▸ hr)
            have := hy r (Finset.mem_insert_of_mem hr)
            simpa [val0, Function.update, hne] using this
          have hyv : y ⟨i, j⟩ = false := by
            simpa [val0] using hy ⟨i, j⟩ (Finset.mem_insert_self _ _)
          exact resolvent_falsify_left hv1 hv2 hReq (hinv y hyD) hyv
        have hinv1 : ∀ y : Raw n b → Bool, (∀ r ∈ D', y r = val1 r) →
            ¬ ClauseSat y (line (p ++ [true])) := by
          intro y hy
          have hyD : ∀ r ∈ D, y r = val r := by
            intro r hr
            have hne : r ≠ ⟨i, j⟩ := fun h => hvD (h ▸ hr)
            have := hy r (Finset.mem_insert_of_mem hr)
            simpa [val1, Function.update, hne] using this
          have hyv : y ⟨i, j⟩ = true := by
            simpa [val1] using hy ⟨i, j⟩ (Finset.mem_insert_self _ _)
          exact resolvent_falsify_right hv1 hv2 hReq (hinv y hyD) hyv
        have hsub_add : (subLeaves N J p).card =
            (subLeaves N J (p ++ [false])).card + (subLeaves N J (p ++ [true])).card := by
          rw [subLeaves_split hpj, Finset.card_union_of_disjoint (subLeaves_disjoint N J p)]
        by_cases hclose : openBitCount D i + 1 < b
        · have hcl_eq : closedBlocks D' = closedBlocks D := by
            ext i'
            rw [mem_closedBlocks_iff_card, mem_closedBlocks_iff_card]
            by_cases hi' : i' = i
            · rw [hi']
              dsimp only [D']
              rw [openBitCount_insert_same D i j hvD]
              omega
            · dsimp only [D']
              rw [openBitCount_insert_ne D hi' j]
          have hR_eq : openTotal D' = openTotal D + 1 := by
            unfold openTotal
            rw [hcl_eq]
            have hi_in : i ∈ Finset.univ \ closedBlocks D :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi_not_cl⟩
            rw [← Finset.add_sum_erase _ _ hi_in, ← Finset.add_sum_erase _ _ hi_in]
            rw [openBitCount_insert_same D i j hvD]
            have hrest : ∑ x ∈ (Finset.univ \ closedBlocks D).erase i, openBitCount D' x =
                ∑ x ∈ (Finset.univ \ closedBlocks D).erase i, openBitCount D x := by
              apply Finset.sum_congr rfl
              intro x hx
              exact openBitCount_insert_ne D (Finset.mem_erase.mp hx).1 j
            rw [hrest]
            omega
          by_cases hcmp : (subLeaves N J (p ++ [false])).card ≤ (subLeaves N J (p ++ [true])).card
          · rcases ih (p ++ [false]) hf (by simp; omega) D' val0 hinv0 with
              ⟨N0, J0, ask, hs0, hH0, hK0, hS0⟩
            refine ⟨N0, J0, ask, hs0, ?_, ?_, ?_⟩
            · intro l hl
              have := hH0 l hl
              rw [hR_eq] at this
              simp at this
              omega
            · rw [hR_eq, Nat.pow_succ] at hK0
              calc ∑ l ∈ N0 \ J0, (2 ^ (b - 1)) ^ l.length
                  ≤ 2 ^ openTotal D * 2 * (subLeaves N J (p ++ [false])).card := hK0
                _ = 2 ^ openTotal D * (2 * (subLeaves N J (p ++ [false])).card) := by
                    rw [Nat.mul_assoc]
                _ ≤ 2 ^ openTotal D * (subLeaves N J p).card := by
                    apply Nat.mul_le_mul_left; omega
            · intro l hl
              rcases hS0 l hl with ⟨C, hCF, hC⟩
              refine ⟨C, hCF, fun x hx hag => hC x (fun i' hi' => ?_) hag⟩
              rw [hcl_eq] at hi'
              have hne : i' ≠ i := fun heq => hi_not_cl (heq ▸ hi')
              rw [rawParity_update_ne val hne j false]
              exact hx i' hi'
          · rcases ih (p ++ [true]) ht (by simp; omega) D' val1 hinv1 with
              ⟨N0, J0, ask, hs0, hH0, hK0, hS0⟩
            refine ⟨N0, J0, ask, hs0, ?_, ?_, ?_⟩
            · intro l hl
              have := hH0 l hl
              rw [hR_eq] at this
              simp at this
              omega
            · rw [hR_eq, Nat.pow_succ] at hK0
              calc ∑ l ∈ N0 \ J0, (2 ^ (b - 1)) ^ l.length
                  ≤ 2 ^ openTotal D * 2 * (subLeaves N J (p ++ [true])).card := hK0
                _ = 2 ^ openTotal D * (2 * (subLeaves N J (p ++ [true])).card) := by
                    rw [Nat.mul_assoc]
                _ ≤ 2 ^ openTotal D * (subLeaves N J p).card := by
                    apply Nat.mul_le_mul_left; omega
            · intro l hl
              rcases hS0 l hl with ⟨C, hCF, hC⟩
              refine ⟨C, hCF, fun x hx hag => hC x (fun i' hi' => ?_) hag⟩
              rw [hcl_eq] at hi'
              have hne : i' ≠ i := fun heq => hi_not_cl (heq ▸ hi')
              rw [rawParity_update_ne val hne j true]
              exact hx i' hi'
        · have hki_eq : openBitCount D i = b - 1 := by omega
          have hcl_eq : closedBlocks D' = insert i (closedBlocks D) := by
            ext i'
            rw [Finset.mem_insert, mem_closedBlocks_iff_card, mem_closedBlocks_iff_card]
            by_cases hi' : i' = i
            · rw [hi']
              dsimp only [D']
              rw [openBitCount_insert_same D i j hvD]
              simp [hki_eq, show b - 1 + 1 = b by omega]
            · dsimp only [D']
              rw [openBitCount_insert_ne D hi' j]
              simp [hi']
          have hR_eq : openTotal D = openTotal D' + (b - 1) := by
            unfold openTotal
            have hi_in : i ∈ Finset.univ \ closedBlocks D :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi_not_cl⟩
            have hsdiff : Finset.univ \ closedBlocks D' = (Finset.univ \ closedBlocks D).erase i := by
              ext x
              rw [hcl_eq]
              simp [and_comm]
            rw [hsdiff, ← Finset.add_sum_erase _ _ hi_in, hki_eq]
            have hrest : ∑ x ∈ (Finset.univ \ closedBlocks D).erase i, openBitCount D' x =
                ∑ x ∈ (Finset.univ \ closedBlocks D).erase i, openBitCount D x := by
              apply Finset.sum_congr rfl
              intro x hx
              exact openBitCount_insert_ne D (Finset.mem_erase.mp hx).1 j
            rw [hrest]
            omega
          rcases ih (p ++ [false]) hf (by simp; omega) D' val0 hinv0 with
            ⟨Nf, Jf, askf, hsf, hHf, hKf, hSf⟩
          rcases ih (p ++ [true]) ht (by simp; omega) D' val1 hinv1 with
            ⟨Nt, Jt, askt, hst, hHt, hKt, hSt⟩
          have hpar_flip : rawParity val1 i = !(rawParity val0 i) := rawParity_update_same val i j
          have hcombine : ∀ (NL JL NR JR : Finset (List Bool)) (askL askR : List Bool → Fin n)
              (kf kt : ℕ),
              treeShape NL JL → treeShape NR JR →
              (∀ l ∈ NL \ JL, p.length + 1 + b * l.length ≤ H + openTotal D') →
              (∀ l ∈ NR \ JR, p.length + 1 + b * l.length ≤ H + openTotal D') →
              (∑ l ∈ NL \ JL, (2 ^ (b - 1)) ^ l.length ≤ 2 ^ openTotal D' * kf) →
              (∑ l ∈ NR \ JR, (2 ^ (b - 1)) ^ l.length ≤ 2 ^ openTotal D' * kt) →
              kf + kt = (subLeaves N J p).card →
              (∀ l ∈ NL \ JL, ∃ C ∈ F, ∀ x : Fin n → Bool,
                (∀ i' ∈ closedBlocks D, x i' = rawParity val i') →
                x i = false → agrees x askL l → ¬ ClauseSat x C) →
              (∀ l ∈ NR \ JR, ∃ C ∈ F, ∀ x : Fin n → Bool,
                (∀ i' ∈ closedBlocks D, x i' = rawParity val i') →
                x i = true → agrees x askR l → ¬ ClauseSat x C) →
              ∃ (N0 J0 : Finset (List Bool)) (ask : List Bool → Fin n),
                treeShape N0 J0 ∧
                (∀ l ∈ N0 \ J0, p.length + b * l.length ≤ H + openTotal D) ∧
                (∑ l ∈ N0 \ J0, (2 ^ (b - 1)) ^ l.length ≤ 2 ^ openTotal D * (subLeaves N J p).card) ∧
                (∀ l ∈ N0 \ J0, ∃ C ∈ F, ∀ x : Fin n → Bool,
                  (∀ i' ∈ closedBlocks D, x i' = rawParity val i') →
                  agrees x ask l → ¬ ClauseSat x C) := by
            intro NL JL NR JR askL askR kf kt hsL hsR hHL hHR hKL hKR hkadd hSL hSR
            let N0 := insert ([] : List Bool) (NL.image (false :: ·) ∪ NR.image (true :: ·))
            let J0 := insert ([] : List Bool) (JL.image (false :: ·) ∪ JR.image (true :: ·))
            let ask : List Bool → Fin n := fun q => match q with
              | [] => i
              | false :: rest => askL rest
              | true :: rest => askR rest
            refine ⟨N0, J0, ask, shape_glue hsL hsR, ?_, ?_, ?_⟩
            · intro l hl
              rw [sdiff_glue] at hl
              rcases Finset.mem_union.mp hl with h1 | h2
              · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
                have := hHL q hq
                simp only [List.length_cons]
                have hm : b * (q.length + 1) = b * q.length + b := Nat.mul_succ b q.length
                omega
              · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
                have := hHR q hq
                simp only [List.length_cons]
                have hm : b * (q.length + 1) = b * q.length + b := Nat.mul_succ b q.length
                omega
            · rw [sdiff_glue, Finset.sum_union (disj_cons_image _ _),
                Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2),
                Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)]
              have hsum1 : ∑ q ∈ NL \ JL, (2 ^ (b - 1)) ^ (false :: q).length =
                  2 ^ (b - 1) * ∑ q ∈ NL \ JL, (2 ^ (b - 1)) ^ q.length := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q _
                simp [Nat.pow_succ, Nat.mul_comm]
              have hsum2 : ∑ q ∈ NR \ JR, (2 ^ (b - 1)) ^ (true :: q).length =
                  2 ^ (b - 1) * ∑ q ∈ NR \ JR, (2 ^ (b - 1)) ^ q.length := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q _
                simp [Nat.pow_succ, Nat.mul_comm]
              rw [hsum1, hsum2, ← Nat.mul_add]
              calc 2 ^ (b - 1) * ((∑ q ∈ NL \ JL, (2 ^ (b - 1)) ^ q.length) +
                      (∑ q ∈ NR \ JR, (2 ^ (b - 1)) ^ q.length))
                  ≤ 2 ^ (b - 1) * (2 ^ openTotal D' * kf + 2 ^ openTotal D' * kt) :=
                    Nat.mul_le_mul_left _ (Nat.add_le_add hKL hKR)
                _ = 2 ^ (b - 1) * 2 ^ openTotal D' * (kf + kt) := by rw [← Nat.mul_add, ← Nat.mul_assoc]
                _ = 2 ^ openTotal D * (subLeaves N J p).card := by
                    rw [hkadd, hR_eq, Nat.pow_add, Nat.mul_comm (2 ^ openTotal D') (2 ^ (b - 1))]
            · intro l hl
              rw [sdiff_glue] at hl
              rcases Finset.mem_union.mp hl with h1 | h2
              · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
                rcases hSL q hq with ⟨C, hCF, hC⟩
                refine ⟨C, hCF, fun x hx hag => ?_⟩
                have hc := (agrees_cons x i askL askR false q).mp hag
                exact hC x hx hc.1 (by simpa using hc.2)
              · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
                rcases hSR q hq with ⟨C, hCF, hC⟩
                refine ⟨C, hCF, fun x hx hag => ?_⟩
                have hc := (agrees_cons x i askL askR true q).mp hag
                exact hC x hx hc.1 (by simpa using hc.2)
          have hval0_agree : ∀ x : Fin n → Bool,
              (∀ i' ∈ closedBlocks D, x i' = rawParity val i') →
              x i = rawParity val0 i →
              ∀ i' ∈ closedBlocks D', x i' = rawParity val0 i' := by
            intro x hx hxi i' hi'
            rw [hcl_eq, Finset.mem_insert] at hi'
            rcases hi' with rfl | hi'
            · exact hxi
            · have hne : i' ≠ i := fun h => hi_not_cl (h ▸ hi')
              rw [rawParity_update_ne val hne j false]
              exact hx i' hi'
          have hval1_agree : ∀ x : Fin n → Bool,
              (∀ i' ∈ closedBlocks D, x i' = rawParity val i') →
              x i = rawParity val1 i →
              ∀ i' ∈ closedBlocks D', x i' = rawParity val1 i' := by
            intro x hx hxi i' hi'
            rw [hcl_eq, Finset.mem_insert] at hi'
            rcases hi' with rfl | hi'
            · exact hxi
            · have hne : i' ≠ i := fun h => hi_not_cl (h ▸ hi')
              rw [rawParity_update_ne val hne j true]
              exact hx i' hi'
          cases hp0 : rawParity val0 i
          · have hp1 : rawParity val1 i = true := by rw [hpar_flip, hp0]; rfl
            exact hcombine Nf Jf Nt Jt askf askt
              (subLeaves N J (p ++ [false])).card (subLeaves N J (p ++ [true])).card
              hsf hst (by intro l hl; simpa using hHf l hl) (by intro l hl; simpa using hHt l hl)
              hKf hKt hsub_add.symm
              (fun l hl => let ⟨C, hCF, hC⟩ := hSf l hl;
                ⟨C, hCF, fun x hx hxi hag => hC x (hval0_agree x hx (by rw [hp0]; exact hxi)) hag⟩)
              (fun l hl => let ⟨C, hCF, hC⟩ := hSt l hl;
                ⟨C, hCF, fun x hx hxi hag => hC x (hval1_agree x hx (by rw [hp1]; exact hxi)) hag⟩)
          · have hp1 : rawParity val1 i = false := by rw [hpar_flip, hp0]; rfl
            exact hcombine Nt Jt Nf Jf askt askf
              (subLeaves N J (p ++ [true])).card (subLeaves N J (p ++ [false])).card
              hst hsf (by intro l hl; simpa using hHt l hl) (by intro l hl; simpa using hHf l hl)
              hKt hKf (by omega)
              (fun l hl => let ⟨C, hCF, hC⟩ := hSt l hl;
                ⟨C, hCF, fun x hx hxi hag => hC x (hval1_agree x hx (by rw [hp1]; exact hxi)) hag⟩)
              (fun l hl => let ⟨C, hCF, hC⟩ := hSf l hl;
                ⟨C, hCF, fun x hx hxi hag => hC x (hval0_agree x hx (by rw [hp0]; exact hxi)) hag⟩)
    · rcases hax p (Finset.mem_sdiff.mpr ⟨hp, hpj⟩) with ⟨C, hCF, y0, hy0, hlp⟩
      have hblock : ∀ lit ∈ C, lit.1 ∈ closedBlocks D ∧ rawParity val lit.1 = rawParity y0 lit.1 := by
        intro lit hlit
        have hmemD : ∀ j : Fin b, (⟨lit.1, j⟩ : Raw n b) ∈ D := by
          intro j
          by_contra hnot
          have hlit_in : (⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)) ∈ line p := by
            rw [hlp]
            exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨lit, hlit, rfl⟩⟩, rfl⟩
          apply hinv (Function.update val ⟨lit.1, j⟩ (!(y0 ⟨lit.1, j⟩)))
          · intro r hr
            have hne : r ≠ ⟨lit.1, j⟩ := fun h => hnot (h ▸ hr)
            simp [Function.update, hne]
          · exact ⟨(⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)), hlit_in, by simp⟩
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemD⟩, ?_⟩
        apply rawParity_eq_of_block_eq
        intro j
        have hlit_in : (⟨lit.1, j⟩, !(y0 ⟨lit.1, j⟩)) ∈ line p := by
          rw [hlp]
          exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨lit, hlit, rfl⟩⟩, rfl⟩
        have hns := hinv val (fun _ _ => rfl)
        have hne : val ⟨lit.1, j⟩ ≠ !(y0 ⟨lit.1, j⟩) := fun heq => hns ⟨_, hlit_in, heq⟩
        cases h1 : val ⟨lit.1, j⟩ <;> cases h2 : y0 ⟨lit.1, j⟩ <;> simp_all
      refine ⟨{[]}, ∅, fun _ => ⟨0, hn⟩, ⟨by simp, by simp, fun q bit hq => by
          rw [Finset.mem_singleton] at hq
          have := congrArg List.length hq
          simp at this, fun q hq => by simp at hq⟩, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Finset.sdiff_empty, Finset.mem_singleton] at hl
        subst hl
        have := hH p hp
        simp; omega
      · rw [subLeaves_leaf hs hp hpj]
        simp only [Finset.sdiff_empty, Finset.sum_singleton, List.length_nil, pow_zero,
          Finset.card_singleton, Nat.mul_one]
        exact Nat.one_le_two_pow
      · intro l hl
        simp only [Finset.sdiff_empty, Finset.mem_singleton] at hl
        subst hl
        refine ⟨C, hCF, fun x hx _ => ?_⟩
        rintro ⟨lit, hlit, hxl⟩
        rcases hblock lit hlit with ⟨hcl, hpeq⟩
        have hx1 := hx lit.1 hcl
        rw [hx1, hpeq] at hxl
        exact hy0 lit hlit hxl

private def fullBlocks {n b : ℕ} (A : Clause (Raw n b)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j : Fin b, (⟨i, j⟩, false) ∈ A ∨ (⟨i, j⟩, true) ∈ A)

private theorem width_lb_g1 {n b : ℕ} (hb : 0 < b) (E : Fin n → Fin n → Bool → Prop)
    {H K width : ℕ} (href : refutesP (b := b) (edgeFormula E) H K width) : b ≤ width := by
  rcases href with ⟨N, J, line, hs, _, hbound, _, hax, _⟩
  rcases subLeaves_nonempty hs (fun p hp => (hbound p hp).1) H [] hs.1 (by simp) with ⟨p, hp⟩
  have hps := (Finset.mem_filter.mp hp).1
  have hpn := (Finset.mem_sdiff.mp hps).1
  rcases hax p hps with ⟨C, ⟨u, v, s, a, _, rfl⟩, y, _, hlp⟩
  have hinj : Function.Injective (fun j : Fin b => ((⟨u, j⟩ : Raw n b), !(y ⟨u, j⟩))) := by
    intro j1 j2 h
    have h1 := congrArg Prod.fst h
    simpa using h1
  have hsub : Finset.univ.image (fun j : Fin b => ((⟨u, j⟩ : Raw n b), !(y ⟨u, j⟩))) ⊆ line p := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨j, _, rfl⟩
    rw [hlp]
    exact Finset.mem_image.mpr ⟨⟨u, j⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(u, !a), by simp, rfl⟩⟩, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.trans (hbound p hpn).2

private theorem no_neg_self_loop {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hnb1 : ¬ badCycle E 1) (u : Fin n) : ¬ E u u true := by
  intro hE
  apply hnb1
  refine ⟨fun _ => u, fun _ => true, rfl, ?_, fun _ _ => hE⟩
  have : (Finset.range 1).filter (fun _ => true = true) = {0} := by decide
  rw [this]
  exact ⟨0, by simp⟩

private theorem no_opp_parallel {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hsym : ∀ u v s, E u v s → E v u s)
    (hnb2 : ¬ badCycle E 2) (u v : Fin n) : ¬ (E u v false ∧ E u v true) := by
  rintro ⟨hf, ht⟩
  apply hnb2
  refine ⟨fun i => if i = 1 then v else u, fun i => if i = 0 then false else true, by simp, ?_, ?_⟩
  · have : (Finset.range 2).filter (fun i => (if i = 0 then false else true) = true) = {1} := by decide
    rw [this]
    exact ⟨0, by simp⟩
  · intro i hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · simpa using hf
    · simpa using hsym u v true ht

private theorem width_lb_g2 {n b : ℕ} (hb : 0 < b) (E : Fin n → Fin n → Bool → Prop)
    (hnb1 : ¬ badCycle E 1) {H K width : ℕ}
    (href : refutesP (b := b) (edgeFormula E) H K width) : 2 * b ≤ width := by
  rcases href with ⟨N, J, line, hs, _, hbound, _, hax, _⟩
  rcases subLeaves_nonempty hs (fun p hp => (hbound p hp).1) H [] hs.1 (by simp) with ⟨p, hp⟩
  have hps := (Finset.mem_filter.mp hp).1
  have hpn := (Finset.mem_sdiff.mp hps).1
  rcases hax p hps with ⟨C, ⟨u, v, s, a, hEuv, rfl⟩, y, hy, hlp⟩
  have huv : u ≠ v := by
    intro heq
    subst heq
    have h1 := hy (u, !a) (by simp)
    have h2 := hy (u, a ^^ s) (by simp)
    cases hs' : s
    · rw [hs', Bool.xor_false] at h2
      cases hp' : rawParity y u <;> cases a <;> simp_all
    · rw [hs'] at hEuv
      exact no_neg_self_loop hnb1 u hEuv
  let S1 := Finset.univ.image (fun j : Fin b => ((⟨u, j⟩ : Raw n b), !(y ⟨u, j⟩)))
  let S2 := Finset.univ.image (fun j : Fin b => ((⟨v, j⟩ : Raw n b), !(y ⟨v, j⟩)))
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    rcases Finset.mem_image.mp h1 with ⟨j1, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j2, _, heq⟩
    exact huv (congrArg Sigma.fst (congrArg Prod.fst heq)).symm
  have hsub : S1 ∪ S2 ⊆ line p := by
    intro l hl
    rw [hlp]
    rcases Finset.mem_union.mp hl with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u, j⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(u, !a), by simp, rfl⟩⟩, rfl⟩
    · rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨v, j⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(v, a ^^ s), by simp, rfl⟩⟩, rfl⟩
  have hinj1 : Function.Injective (fun j : Fin b => ((⟨u, j⟩ : Raw n b), !(y ⟨u, j⟩))) :=
    fun _ _ h => by simpa using congrArg Prod.fst h
  have hinj2 : Function.Injective (fun j : Fin b => ((⟨v, j⟩ : Raw n b), !(y ⟨v, j⟩))) :=
    fun _ _ h => by simpa using congrArg Prod.fst h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2,
    Finset.card_univ, Fintype.card_fin] at hcard
  have hw := (hbound p hpn).2
  omega

private theorem width_lb_g3 {n b : ℕ} (hb : 0 < b) (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v s, E u v s → E v u s)
    (hnb1 : ¬ badCycle E 1) (hnb2 : ¬ badCycle E 2)
    {H K width : ℕ} (href : refutesP (b := b) (edgeFormula E) H K width) :
    3 * b - 1 ≤ width := by
  classical
  by_contra hlt
  have hw_le : width ≤ 3 * b - 2 := by omega
  rcases href with ⟨N, J, line, hs, hempty, hbound, _, hax, hres⟩
  let Good : Clause (Raw n b) → Prop := fun A =>
    ∃ y : Raw n b → Bool, ¬ ClauseSat y A ∧
      ∀ u ∈ fullBlocks A, ∀ v ∈ fullBlocks A, ∀ s : Bool, E u v s →
        (rawParity y u ^^ rawParity y v) = s
  have hroot_good : Good (line []) := by
    rw [hempty]
    refine ⟨fun _ => false, by rintro ⟨_, hm, _⟩; simp at hm, fun u hu => ?_⟩
    have h0 := (Finset.mem_filter.mp hu).2 ⟨0, hb⟩
    simp at h0
  have hleaf_bad : ∀ p ∈ N \ J, ¬ Good (line p) := by
    intro p hp ⟨y, hny, hsatE⟩
    rcases hax p hp with ⟨C, ⟨u, v, s, a, hEuv, rfl⟩, y0, hy0, hlp⟩
    have hu_full : u ∈ fullBlocks (line p) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, fun j => ?_⟩
      have hmem : (⟨u, j⟩, !(y0 ⟨u, j⟩)) ∈ line p := by
        rw [hlp]
        exact Finset.mem_image.mpr ⟨⟨u, j⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(u, !a), by simp, rfl⟩⟩, rfl⟩
      cases hc : !(y0 ⟨u, j⟩)
      · left; rwa [hc] at hmem
      · right; rwa [hc] at hmem
    have hv_full : v ∈ fullBlocks (line p) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, fun j => ?_⟩
      have hmem : (⟨v, j⟩, !(y0 ⟨v, j⟩)) ∈ line p := by
        rw [hlp]
        exact Finset.mem_image.mpr ⟨⟨v, j⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(v, a ^^ s), by simp, rfl⟩⟩, rfl⟩
      cases hc : !(y0 ⟨v, j⟩)
      · left; rwa [hc] at hmem
      · right; rwa [hc] at hmem
    have hpu : rawParity y u = rawParity y0 u := by
      apply rawParity_eq_of_block_eq
      intro j
      have hmem : (⟨u, j⟩, !(y0 ⟨u, j⟩)) ∈ line p := by
        rw [hlp]
        exact Finset.mem_image.mpr ⟨⟨u, j⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(u, !a), by simp, rfl⟩⟩, rfl⟩
      have hne : y ⟨u, j⟩ ≠ !(y0 ⟨u, j⟩) := fun h => hny ⟨_, hmem, h⟩
      cases h1 : y ⟨u, j⟩ <;> cases h2 : y0 ⟨u, j⟩ <;> simp_all
    have hpv : rawParity y v = rawParity y0 v := by
      apply rawParity_eq_of_block_eq
      intro j
      have hmem : (⟨v, j⟩, !(y0 ⟨v, j⟩)) ∈ line p := by
        rw [hlp]
        exact Finset.mem_image.mpr ⟨⟨v, j⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(v, a ^^ s), by simp, rfl⟩⟩, rfl⟩
      have hne : y ⟨v, j⟩ ≠ !(y0 ⟨v, j⟩) := fun h => hny ⟨_, hmem, h⟩
      cases h1 : y ⟨v, j⟩ <;> cases h2 : y0 ⟨v, j⟩ <;> simp_all
    have h1 := hy0 (u, !a) (by simp)
    have h2 := hy0 (v, a ^^ s) (by simp)
    have h3 := hsatE u hu_full v hv_full s hEuv
    rw [hpu, hpv] at h3
    cases hpu' : rawParity y0 u <;> cases hpv' : rawParity y0 v <;> cases a <;> cases s <;>
      simp_all
  have hstep_good : ∀ p ∈ J, Good (line p) →
      Good (line (p ++ [false])) ∨ Good (line (p ++ [true])) := by
    intro p hpj ⟨y, hny, hsatE⟩
    set A := line p
    set A0 := line (p ++ [false])
    set A1 := line (p ++ [true])
    have hA_card : A.card ≤ 3 * b - 2 := (hbound p (hs.2.1 hpj)).2.trans hw_le
    rcases hres p hpj with ⟨x, hx0, hx1, hReq⟩
    rcases x with ⟨w, j⟩
    have hA0_sub : ∀ l ∈ A0, l = (⟨w, j⟩, true) ∨ l ∈ A := by
      intro l hl
      by_cases heq : l = (⟨w, j⟩, true)
      · exact Or.inl heq
      · right
        dsimp only [A]
        rw [hReq]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hl⟩)
    have hA1_sub : ∀ l ∈ A1, l = (⟨w, j⟩, false) ∨ l ∈ A := by
      intro l hl
      by_cases heq : l = (⟨w, j⟩, false)
      · exact Or.inl heq
      · right
        dsimp only [A]
        rw [hReq]
        exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨heq, hl⟩)
    have hfull0_sub : fullBlocks A0 ⊆ insert w (fullBlocks A) := by
      intro i hi
      rw [Finset.mem_insert]
      by_cases hiw : i = w
      · exact Or.inl hiw
      · right
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j' => ?_⟩
        have hne : (⟨i, j'⟩ : Raw n b) ≠ ⟨w, j⟩ := fun h => hiw (congrArg Sigma.fst h)
        rcases (Finset.mem_filter.mp hi).2 j' with h | h
        · left
          rcases hA0_sub _ h with heq | hm
          · exact absurd (congrArg Prod.fst heq) hne
          · exact hm
        · right
          rcases hA0_sub _ h with heq | hm
          · exact absurd (congrArg Prod.fst heq) hne
          · exact hm
    have hfull1_sub : fullBlocks A1 ⊆ insert w (fullBlocks A) := by
      intro i hi
      rw [Finset.mem_insert]
      by_cases hiw : i = w
      · exact Or.inl hiw
      · right
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j' => ?_⟩
        have hne : (⟨i, j'⟩ : Raw n b) ≠ ⟨w, j⟩ := fun h => hiw (congrArg Sigma.fst h)
        rcases (Finset.mem_filter.mp hi).2 j' with h | h
        · left
          rcases hA1_sub _ h with heq | hm
          · exact absurd (congrArg Prod.fst heq) hne
          · exact hm
        · right
          rcases hA1_sub _ h with heq | hm
          · exact absurd (congrArg Prod.fst heq) hne
          · exact hm
    by_cases hsub_both : fullBlocks A0 ⊆ fullBlocks A ∧ fullBlocks A1 ⊆ fullBlocks A
    · cases hyx : y ⟨w, j⟩
      · left
        refine ⟨y, resolvent_falsify_left hx0 hx1 hReq hny hyx, fun u hu v hv s hE =>
          hsatE u (hsub_both.1 hu) v (hsub_both.1 hv) s hE⟩
      · right
        refine ⟨y, resolvent_falsify_right hx0 hx1 hReq hny hyx, fun u hu v hv s hE =>
          hsatE u (hsub_both.2 hu) v (hsub_both.2 hv) s hE⟩
    · have hw_not_A : w ∉ fullBlocks A := by
        intro hwA
        apply hsub_both
        have hins : insert w (fullBlocks A) = fullBlocks A := Finset.insert_eq_of_mem hwA
        exact ⟨hins ▸ hfull0_sub, hins ▸ hfull1_sub⟩
      have hx_not_A : (⟨w, j⟩, false) ∉ A ∧ (⟨w, j⟩, true) ∉ A := by
        by_contra hmem
        apply hsub_both
        have hmx : (⟨w, j⟩, false) ∈ A ∨ (⟨w, j⟩, true) ∈ A := by tauto
        constructor
        · intro i hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j' => ?_⟩
          by_cases hpair : (⟨i, j'⟩ : Raw n b) = ⟨w, j⟩
          · rwa [hpair]
          · rcases (Finset.mem_filter.mp hi).2 j' with h | h
            · rcases hA0_sub _ h with heq | hm
              · exact absurd (congrArg Prod.fst heq) hpair
              · exact Or.inl hm
            · rcases hA0_sub _ h with heq | hm
              · exact absurd (congrArg Prod.fst heq) hpair
              · exact Or.inr hm
        · intro i hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun j' => ?_⟩
          by_cases hpair : (⟨i, j'⟩ : Raw n b) = ⟨w, j⟩
          · rwa [hpair]
          · rcases (Finset.mem_filter.mp hi).2 j' with h | h
            · rcases hA1_sub _ h with heq | hm
              · exact absurd (congrArg Prod.fst heq) hpair
              · exact Or.inl hm
            · rcases hA1_sub _ h with heq | hm
              · exact absurd (congrArg Prod.fst heq) hpair
              · exact Or.inr hm
      have hw_other_in_A : ∀ j' : Fin b, j' ≠ j → (⟨w, j'⟩ : Raw n b) ∈ A.image Prod.fst := by
        have hw_in_one : w ∈ fullBlocks A0 ∨ w ∈ fullBlocks A1 := by
          by_contra hneither
          push_neg at hneither
          apply hsub_both
          constructor
          · intro i hi
            rcases Finset.mem_insert.mp (hfull0_sub hi) with rfl | hm
            · exact absurd hi hneither.1
            · exact hm
          · intro i hi
            rcases Finset.mem_insert.mp (hfull1_sub hi) with rfl | hm
            · exact absurd hi hneither.2
            · exact hm
        intro j' hj'
        have hne : (⟨w, j'⟩ : Raw n b) ≠ ⟨w, j⟩ := fun h => hj' (by simpa using h)
        rcases hw_in_one with hw0 | hw1
        · rcases (Finset.mem_filter.mp hw0).2 j' with h | h
          · rcases hA0_sub _ h with heq | hm
            · exact absurd (congrArg Prod.fst heq) hne
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
          · rcases hA0_sub _ h with heq | hm
            · exact absurd (congrArg Prod.fst heq) hne
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
        · rcases (Finset.mem_filter.mp hw1).2 j' with h | h
          · rcases hA1_sub _ h with heq | hm
            · exact absurd (congrArg Prod.fst heq) hne
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
          · rcases hA1_sub _ h with heq | hm
            · exact absurd (congrArg Prod.fst heq) hne
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
      have hfull_le1 : (fullBlocks A).card ≤ 1 := by
        let Vfull : Finset (Raw n b) := (fullBlocks A).biUnion (fun i =>
          Finset.univ.image (fun j' : Fin b => (⟨i, j'⟩ : Raw n b)))
        let Vw : Finset (Raw n b) := (Finset.univ.erase j).image (fun j' : Fin b => (⟨w, j'⟩ : Raw n b))
        have hdisjV : Disjoint Vfull Vw := by
          rw [Finset.disjoint_left]
          intro r h1 h2
          rcases Finset.mem_biUnion.mp h1 with ⟨i, hi, hr1⟩
          rcases Finset.mem_image.mp hr1 with ⟨j1, _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨j2, _, heq⟩
          have hiw : i = w := (congrArg Sigma.fst heq).symm
          exact hw_not_A (hiw ▸ hi)
        have hsubV : Vfull ∪ Vw ⊆ A.image Prod.fst := by
          intro r hr
          rcases Finset.mem_union.mp hr with h1 | h2
          · rcases Finset.mem_biUnion.mp h1 with ⟨i, hi, hr1⟩
            rcases Finset.mem_image.mp hr1 with ⟨j', _, rfl⟩
            rcases (Finset.mem_filter.mp hi).2 j' with hm | hm
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
            · exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
          · rcases Finset.mem_image.mp h2 with ⟨j', hj', rfl⟩
            exact hw_other_in_A j' (Finset.mem_erase.mp hj').1
        have hcard_Vfull : Vfull.card = (fullBlocks A).card * b := by
          rw [Finset.card_biUnion]
          · have hper : ∀ i ∈ fullBlocks A,
                (Finset.univ.image (fun j' : Fin b => (⟨i, j'⟩ : Raw n b))).card = b := by
              intro i _
              rw [Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)]
              simp
            rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
          · intro i1 _ i2 _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro r h1 h2
            rcases Finset.mem_image.mp h1 with ⟨j1, _, rfl⟩
            rcases Finset.mem_image.mp h2 with ⟨j2, _, heq⟩
            exact hne (congrArg Sigma.fst heq).symm
        have hcard_Vw : Vw.card = b - 1 := by
          rw [Finset.card_image_of_injective _ (fun _ _ h => by simpa using h),
            Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
        have hle1 := Finset.card_le_card hsubV
        rw [Finset.card_union_of_disjoint hdisjV, hcard_Vfull, hcard_Vw] at hle1
        have hle2 := Finset.card_image_le (f := Prod.fst) (s := A)
        have htot : (fullBlocks A).card * b + (b - 1) ≤ 3 * b - 2 := hle1.trans (hle2.trans hA_card)
        by_contra hge2
        have h2 : 2 ≤ (fullBlocks A).card := by omega
        have hmul : 2 * b ≤ (fullBlocks A).card * b := Nat.mul_le_mul_right b h2
        omega
      let y0 := Function.update y ⟨w, j⟩ false
      let y1 := Function.update y ⟨w, j⟩ true
      have hy0A : ¬ ClauseSat y0 A := by
        rintro ⟨l, hlA, hyl⟩
        have hne : l.1 ≠ ⟨w, j⟩ := by
          intro heq
          rcases l with ⟨r, pol⟩
          simp only at heq
          subst heq
          cases pol
          · exact hx_not_A.1 hlA
          · exact hx_not_A.2 hlA
        rw [show y0 l.1 = y l.1 by simp [y0, Function.update, hne]] at hyl
        exact hny ⟨l, hlA, hyl⟩
      have hy1A : ¬ ClauseSat y1 A := by
        rintro ⟨l, hlA, hyl⟩
        have hne : l.1 ≠ ⟨w, j⟩ := by
          intro heq
          rcases l with ⟨r, pol⟩
          simp only at heq
          subst heq
          cases pol
          · exact hx_not_A.1 hlA
          · exact hx_not_A.2 hlA
        rw [show y1 l.1 = y l.1 by simp [y1, Function.update, hne]] at hyl
        exact hny ⟨l, hlA, hyl⟩
      have hny0_A0 : ¬ ClauseSat y0 A0 := resolvent_falsify_left hx0 hx1 hReq hy0A (by simp [y0])
      have hny1_A1 : ¬ ClauseSat y1 A1 := resolvent_falsify_right hx0 hx1 hReq hy1A (by simp [y1])
      have hflip : rawParity y1 w = !(rawParity y0 w) := rawParity_update_same y w j
      by_cases hemp : fullBlocks A = ∅
      · left
        refine ⟨y0, hny0_A0, fun u hu v hv s hE => ?_⟩
        have huw : u = w := by
          have := hfull0_sub hu; rw [hemp] at this; exact Finset.mem_singleton.mp this
        have hvw : v = w := by
          have := hfull0_sub hv; rw [hemp] at this; exact Finset.mem_singleton.mp this
        rw [huw, hvw] at hE ⊢
        cases s
        · simp
        · exact absurd hE (no_neg_self_loop hnb1 w)
      · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hfull_eq : fullBlocks A = {u0} := by
          ext i
          simp only [Finset.mem_singleton]
          constructor
          · intro hi
            by_contra hne
            have hsub2 : ({u0, i} : Finset (Fin n)) ⊆ fullBlocks A := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hu0
              · exact hi
            have hc := Finset.card_le_card hsub2
            rw [Finset.card_pair (Ne.symm hne)] at hc
            omega
          · rintro rfl; exact hu0
        have hu0_ne_w : u0 ≠ w := fun h => hw_not_A (h ▸ hu0)
        let pw : Bool := if E u0 w true then !(rawParity y u0) else rawParity y u0
        have hcheck_edges : ∀ (yc : Raw n b → Bool),
            rawParity yc u0 = rawParity y u0 → rawParity yc w = pw →
            ∀ u ∈ insert w (fullBlocks A), ∀ v ∈ insert w (fullBlocks A), ∀ s : Bool, E u v s →
              (rawParity yc u ^^ rawParity yc v) = s := by
          intro yc hcu hcw u hu v hv s hE
          rw [hfull_eq] at hu hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          have hpair : ∀ s' : Bool, E u0 w s' → (rawParity yc u0 ^^ rawParity yc w) = s' := by
            intro s' hEs'
            rw [hcu, hcw]
            cases s'
            · have hnt : ¬ E u0 w true := fun ht => no_opp_parallel hsym hnb2 u0 w ⟨hEs', ht⟩
              simp [pw, hnt]
            · simp [pw, hEs']
          rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at hE ⊢
          · cases s
            · simp
            · exact absurd hE (no_neg_self_loop hnb1 w)
          · rw [Bool.xor_comm]
            exact hpair s (hsym w u0 s hE)
          · exact hpair s hE
          · cases s
            · simp
            · exact absurd hE (no_neg_self_loop hnb1 u0)
        by_cases hp0 : rawParity y0 w = pw
        · left
          refine ⟨y0, hny0_A0, fun u hu v hv s hE =>
            hcheck_edges y0 (rawParity_update_ne y hu0_ne_w j false) hp0
              u (hfull0_sub hu) v (hfull0_sub hv) s hE⟩
        · right
          have hp1 : rawParity y1 w = pw := by
            rw [hflip]
            cases h0 : rawParity y0 w <;> cases hp : pw <;> simp_all
          refine ⟨y1, hny1_A1, fun u hu v hv s hE =>
            hcheck_edges y1 (rawParity_update_ne y hu0_ne_w j true) hp1
              u (hfull1_sub hu) v (hfull1_sub hv) s hE⟩
  have hreach : ∀ d : ℕ, ∀ p ∈ N, H - p.length ≤ d → Good (line p) →
      ∃ l ∈ N \ J, Good (line l) := by
    intro d
    induction d with
    | zero =>
      intro p hp hd hg
      have hlen : p.length = H := by have := (hbound p hp).1; omega
      have hni : p ∉ J := by
        intro hpj
        have hfl := (hbound (p ++ [false]) (hs.2.2.2 p hpj).1).1
        simp [hlen] at hfl
      exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hni⟩, hg⟩
    | succ d ih =>
      intro p hp hd hg
      by_cases hpj : p ∈ J
      · rcases hstep_good p hpj hg with hg0 | hg1
        · exact ih (p ++ [false]) (hs.2.2.2 p hpj).1 (by simp; omega) hg0
        · exact ih (p ++ [true]) (hs.2.2.2 p hpj).2 (by simp; omega) hg1
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpj⟩, hg⟩
  rcases hreach H [] hs.1 (by simp) hroot_good with ⟨l, hl, hgl⟩
  exact hleaf_bad l hl hgl

private theorem lower_bounds {n b : ℕ} (hn : 0 < n) (hb : 0 < b)
    (E : Fin n → Fin n → Bool → Prop) (hsym : ∀ u v s, E u v s → E v u s)
    (g H K width : ℕ) (hg : badCycle E g) (hmin : ∀ j < g, ¬ badCycle E j)
    (href : refutesP (b := b) (edgeFormula E) H K width) :
    b * Nat.clog 2 (2 * g) ≤ H ∧ bal (2 ^ (b - 1)) (2 * g) ≤ K ∧
      (if g = 1 then b else if g = 2 then 2 * b else 3 * b - 1) ≤ width := by
  have hg_pos : 1 ≤ g := by
    by_contra h0
    have : g = 0 := by omega
    subst this
    rcases hg with ⟨_, _, _, hodd, _⟩
    simp at hodd
  rcases href with ⟨N, J, line, hs, hempty, hbound, hK, hax, hres⟩
  have hproj := project_tree hn hb (edgeFormula E) H N J line hs
    (fun p hp => (hbound p hp).1) hax hres H [] hs.1 (by simp) ∅ (fun _ => false)
    (fun y _ => by rw [hempty]; rintro ⟨_, hm, _⟩; simp at hm)
  have hcl_empty : closedBlocks (∅ : Finset (Raw n b)) = ∅ := by
    ext i
    simp only [closedBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_forall]
    exact ⟨⟨0, hb⟩, by simp⟩
  have hR_zero : openTotal (∅ : Finset (Raw n b)) = 0 := by
    simp [openTotal, openBitCount]
  rcases hproj with ⟨N0, J0, ask, hs0, hH0, hK0, hS0⟩
  rw [hR_zero] at hH0 hK0
  have hS0' : ∀ l ∈ N0 \ J0, ∃ C ∈ edgeFormula E, ∀ x : Fin n → Bool, agrees x ask l → ¬ ClauseSat x C := by
    intro l hl
    rcases hS0 l hl with ⟨C, hCF, hC⟩
    exact ⟨C, hCF, fun x hag => hC x (fun i hi => by rw [hcl_empty] at hi; simp at hi) hag⟩
  have h2g : 2 * g ≤ (N0 \ J0).card := base_dt_leaves_lb E hsym g hg hmin N0 J0 ask hs0 hS0'
  have hlen_div : ∀ l ∈ N0 \ J0, l.length ≤ H / b := by
    intro l hl
    have h1 := hH0 l hl
    simp only [List.length_nil, Nat.zero_add, Nat.add_zero] at h1
    rw [Nat.le_div_iff_mul_le hb, Nat.mul_comm]
    exact h1
  have hpow := shape_leaves_le_pow hs0 hlen_div (H / b) [] hs0.1 (by simp)
  have hsub0 : subLeaves N0 J0 [] = N0 \ J0 := by ext q; simp [subLeaves]
  rw [hsub0] at hpow
  have hclog : Nat.clog 2 (2 * g) ≤ H / b :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (h2g.trans hpow)
  have hH_ok : b * Nat.clog 2 (2 * g) ≤ H := by
    have := (Nat.le_div_iff_mul_le hb).mp hclog
    rw [Nat.mul_comm] at this
    exact this
  have hbase_pos : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
  have hsub_root : subLeaves N J [] = N \ J := by ext q; simp [subLeaves]
  rw [hsub_root] at hK0
  simp only [pow_zero, Nat.one_mul] at hK0
  have hK_ok : bal (2 ^ (b - 1)) (2 * g) ≤ K :=
    (bal_mono hbase_pos (by omega) h2g).trans
      ((bal_tree_le hbase_pos hs0).trans (hK0.trans hK))
  have href' : refutesP (b := b) (edgeFormula E) H K width :=
    ⟨N, J, line, hs, hempty, hbound, hK, hax, hres⟩
  have hW_ok : (if g = 1 then b else if g = 2 then 2 * b else 3 * b - 1) ≤ width := by
    split_ifs with hg1 hg2
    · exact width_lb_g1 hb E href'
    · exact width_lb_g2 hb E (hmin 1 (by omega)) href'
    · exact width_lb_g3 hb E hsym (hmin 1 (by omega)) (hmin 2 (by omega)) href'
  exact ⟨hH_ok, hK_ok, hW_ok⟩

private def upperClause {n b : ℕ} (u : Fin n) (r : ℕ) (z : Fin b → Bool) : Clause (Raw n b) :=
  (Finset.univ.filter (fun j : Fin b => r ≤ j.val)).image (fun j => ((⟨u, j⟩ : Raw n b), !(z j)))

private def blockClause {n b : ℕ} (u : Fin n) (z : Fin b → Bool) : Clause (Raw n b) :=
  upperClause u 0 z

private theorem upperClause_top {n b : ℕ} (u : Fin n) (z : Fin b → Bool) :
    upperClause u b z = ∅ := by
  ext l
  simp only [upperClause, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_exists, not_and]
  intro j hj _
  have := j.isLt
  omega

private theorem upperClause_card {n b : ℕ} (u : Fin n) (r : ℕ) (hr : r ≤ b) (z : Fin b → Bool) :
    (upperClause u r z).card ≤ b - r := by
  unfold upperClause
  refine (Finset.card_image_le).trans ?_
  have hsub : (Finset.univ.filter (fun j : Fin b => r ≤ j.val)).image Fin.val ⊆ Finset.Ico r b := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at h1
  exact h1

private theorem blockClause_card {n b : ℕ} (u : Fin n) (z : Fin b → Bool) :
    (blockClause u z).card ≤ b := by
  simpa [blockClause] using upperClause_card u 0 (Nat.zero_le b) z

private theorem mem_upperClause_fst_eq {n b : ℕ} {u : Fin n} {r : ℕ} {z : Fin b → Bool}
    {l : Literal (Raw n b)} (hl : l ∈ upperClause u r z) : l.1.1 = u := by
  rcases Finset.mem_image.mp hl with ⟨_, _, rfl⟩
  rfl

private theorem upperClause_step_res {n b : ℕ} (u : Fin n) (t : ℕ) (ht : t < b)
    (C0 C1 : Clause (Raw n b))
    (hC0 : ∀ l ∈ C0, l.1.1 ≠ u) (hC1 : ∀ l ∈ C1, l.1.1 ≠ u)
    (z : Fin b → Bool) :
    IsResolvent
      (C0 ∪ upperClause u t (Function.update z ⟨t, ht⟩ false))
      (C1 ∪ upperClause u t (Function.update z ⟨t, ht⟩ true))
      ((C0 ∪ C1) ∪ upperClause u (t + 1) z) := by
  set jt : Fin b := ⟨t, ht⟩
  set z0 := Function.update z jt false
  set z1 := Function.update z jt true
  refine ⟨⟨u, jt⟩, ?_, ?_, ?_⟩
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨jt, ?_, by simp [z0]⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl t⟩
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨jt, ?_, by simp [z1]⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl t⟩
  · have hnot0 : ((⟨u, jt⟩ : Raw n b), true) ∉ C0 := fun h => hC0 _ h rfl
    have hnot1 : ((⟨u, jt⟩ : Raw n b), false) ∉ C1 := fun h => hC1 _ h rfl
    have he0 : (upperClause u t z0).erase (⟨u, jt⟩, true) = upperClause u (t + 1) z := by
      ext l
      simp only [Finset.mem_erase, upperClause, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, ⟨j, hj, rfl⟩⟩
        have hjne : j ≠ jt := by
          intro heq
          subst heq
          apply hne
          simp [z0]
        have hgt : t + 1 ≤ j.val := by
          have : j.val ≠ t := fun hv => hjne (Fin.ext hv)
          omega
        exact ⟨j, hgt, by simp [z0, Function.update, hjne]⟩
      · rintro ⟨j, hj, rfl⟩
        have hjne : j ≠ jt := fun heq => by have := congrArg Fin.val heq; simp [jt] at this; omega
        refine ⟨?_, ⟨j, by omega, by simp [z0, Function.update, hjne]⟩⟩
        intro heq
        exact hjne (by simpa using congrArg Prod.fst heq)
    have he1 : (upperClause u t z1).erase (⟨u, jt⟩, false) = upperClause u (t + 1) z := by
      ext l
      simp only [Finset.mem_erase, upperClause, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, ⟨j, hj, rfl⟩⟩
        have hjne : j ≠ jt := by
          intro heq
          subst heq
          apply hne
          simp [z1]
        have hgt : t + 1 ≤ j.val := by
          have : j.val ≠ t := fun hv => hjne (Fin.ext hv)
          omega
        exact ⟨j, hgt, by simp [z1, Function.update, hjne]⟩
      · rintro ⟨j, hj, rfl⟩
        have hjne : j ≠ jt := fun heq => by have := congrArg Fin.val heq; simp [jt] at this; omega
        refine ⟨?_, ⟨j, by omega, by simp [z1, Function.update, hjne]⟩⟩
        intro heq
        exact hjne (by simpa using congrArg Prod.fst heq)
    rw [Finset.erase_union_distrib, Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem hnot0, Finset.erase_eq_of_notMem hnot1, he0, he1]
    ext l
    simp only [Finset.mem_union]
    tauto

private def joinRec {n b : ℕ} (u : Fin n) (C0 C1 : Clause (Raw n b))
    (sub : (Fin b → Bool) → Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Raw n b))) :
    (r : ℕ) → r ≤ b → (Fin b → Bool) →
      Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Raw n b))
  | 0, _, z => sub z
  | t + 1, hr, z =>
    let jt : Fin b := ⟨t, by omega⟩
    let TL := joinRec u C0 C1 sub t (by omega) (Function.update z jt false)
    let TR := joinRec u C0 C1 sub t (by omega) (Function.update z jt true)
    (insert [] (TL.1.image (false :: ·) ∪ TR.1.image (true :: ·)),
     insert [] (TL.2.1.image (false :: ·) ∪ TR.2.1.image (true :: ·)),
     fun p => match p with
       | [] => (C0 ∪ C1) ∪ upperClause u (t + 1) z
       | false :: rest => TL.2.2 rest
       | true :: rest => TR.2.2 rest)

private theorem joinRec_spec {n b : ℕ} (hb : 0 < b) (F : Set (Clause (Fin n)))
    (u : Fin n) (C0 C1 : Clause (Raw n b))
    (hC0 : ∀ l ∈ C0, l.1.1 ≠ u) (hC1 : ∀ l ∈ C1, l.1.1 ≠ u)
    (flag : Bool) (h0 h1 k0 k1 W : ℕ)
    (hW_inner : (C0 ∪ C1).card + (b - 1) ≤ W)
    (sub : (Fin b → Bool) → Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Raw n b)))
    (hsub : ∀ z : Fin b → Bool,
      let T := sub z
      treeShape T.1 T.2.1 ∧
      T.2.2 [] = (if vecParity z = flag then C0 else C1) ∪ blockClause u z ∧
      (∀ p ∈ T.1, p.length ≤ (if vecParity z = flag then h0 else h1) ∧ (T.2.2 p).card ≤ W) ∧
      (T.1 \ T.2.1).card = (if vecParity z = flag then k0 else k1) ∧
      (∀ p ∈ T.1 \ T.2.1, liftAxP F (T.2.2 p)) ∧
      (∀ p ∈ T.2.1, IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p))) :
    ∀ (r : ℕ) (hr : r ≤ b) (hpos : 1 ≤ r) (z : Fin b → Bool),
      let T := joinRec u C0 C1 sub r hr z
      treeShape T.1 T.2.1 ∧
      T.2.2 [] = (C0 ∪ C1) ∪ upperClause u r z ∧
      (∀ p ∈ T.1, p.length ≤ r + max h0 h1 ∧ (T.2.2 p).card ≤ W) ∧
      (T.1 \ T.2.1).card = 2 ^ (r - 1) * (k0 + k1) ∧
      (∀ p ∈ T.1 \ T.2.1, liftAxP F (T.2.2 p)) ∧
      (∀ p ∈ T.2.1, IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p)) := by
  intro r
  induction r with
  | zero => intro _ hpos; omega
  | succ t ih =>
    intro hr _ z
    set jt : Fin b := ⟨t, by omega⟩
    set z0 := Function.update z jt false
    set z1 := Function.update z jt true
    set TL := joinRec u C0 C1 sub t (by omega) z0
    set TR := joinRec u C0 C1 sub t (by omega) z1
    have hjoin_eq : joinRec u C0 C1 sub (t + 1) hr z =
        (insert [] (TL.1.image (false :: ·) ∪ TR.1.image (true :: ·)),
         insert [] (TL.2.1.image (false :: ·) ∪ TR.2.1.image (true :: ·)),
         fun p => match p with
           | [] => (C0 ∪ C1) ∪ upperClause u (t + 1) z
           | false :: rest => TL.2.2 rest
           | true :: rest => TR.2.2 rest) := rfl
    rw [hjoin_eq]
    dsimp only
    have hroot_card : ((C0 ∪ C1) ∪ upperClause u (t + 1) z).card ≤ W := by
      have h1 := Finset.card_union_le (C0 ∪ C1) (upperClause u (t + 1) z)
      have h2 := upperClause_card u (t + 1) hr z
      omega
    cases t with
    | zero =>
      have hTL := hsub z0
      have hTR := hsub z1
      have hflip : vecParity z1 = !(vecParity z0) := parity_flip_bit z ⟨0, hb⟩
      have hres_root : IsResolvent (TL.2.2 []) (TR.2.2 []) ((C0 ∪ C1) ∪ upperClause u 1 z) := by
        change IsResolvent ((sub z0).2.2 []) ((sub z1).2.2 []) ((C0 ∪ C1) ∪ upperClause u 1 z)
        rw [hTL.2.1, hTR.2.1]
        by_cases hp : vecParity z0 = flag
        · have hp1 : vecParity z1 ≠ flag := by rw [hflip, hp]; cases flag <;> decide
          simp only [hp, ite_true, hp1, ite_false]
          exact upperClause_step_res u 0 hb C0 C1 hC0 hC1 z
        · have hp1 : vecParity z1 = flag := by
            rw [hflip]; cases h0' : vecParity z0 <;> cases flag <;> simp_all
          simp only [hp, ite_false, hp1, ite_true]
          have h := upperClause_step_res u 0 hb C1 C0 hC1 hC0 z
          rwa [Finset.union_comm C1 C0] at h
      have hleaf_sum : (TL.1 \ TL.2.1).card + (TR.1 \ TR.2.1).card = k0 + k1 := by
        change ((sub z0).1 \ (sub z0).2.1).card + ((sub z1).1 \ (sub z1).2.1).card = k0 + k1
        rw [hTL.2.2.2.1, hTR.2.2.2.1]
        by_cases hp : vecParity z0 = flag
        · have hp1 : vecParity z1 ≠ flag := by rw [hflip, hp]; cases flag <;> decide
          simp [hp, hp1]
        · have hp1 : vecParity z1 = flag := by
            rw [hflip]; cases h0' : vecParity z0 <;> cases flag <;> simp_all
          simp [hp, hp1, Nat.add_comm]
      refine ⟨shape_glue hTL.1 hTR.1, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact ⟨by simp, hroot_card⟩
        · have hq' := hTL.2.2.1 q hq
          refine ⟨?_, hq'.2⟩
          simp only [List.length_cons]
          split_ifs at hq' <;> omega
        · have hq' := hTR.2.2.1 q hq
          refine ⟨?_, hq'.2⟩
          simp only [List.length_cons]
          split_ifs at hq' <;> omega
      · rw [sdiff_glue, Finset.card_union_of_disjoint (disj_cons_image _ _),
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
          hleaf_sum]
        simp
      · intro p hp
        rw [sdiff_glue] at hp
        rcases Finset.mem_union.mp hp with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
          exact hTL.2.2.2.2.1 q hq
        · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
          exact hTR.2.2.2.2.1 q hq
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · simpa using hres_root
        · exact hTL.2.2.2.2.2 q hq
        · exact hTR.2.2.2.2.2 q hq
    | succ t' =>
      have hTL := ih (by omega) (by omega) z0
      have hTR := ih (by omega) (by omega) z1
      have hC01 : ∀ l ∈ C0 ∪ C1, l.1.1 ≠ u := fun l hl =>
        (Finset.mem_union.mp hl).elim (hC0 l) (hC1 l)
      have hres_root : IsResolvent (TL.2.2 []) (TR.2.2 []) ((C0 ∪ C1) ∪ upperClause u (t' + 2) z) := by
        rw [hTL.2.1, hTR.2.1]
        have h := upperClause_step_res u (t' + 1) (by omega) (C0 ∪ C1) (C0 ∪ C1) hC01 hC01 z
        simpa [Finset.union_idempotent] using h
      refine ⟨shape_glue hTL.1 hTR.1, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact ⟨by simp, hroot_card⟩
        · have hq' := hTL.2.2.1 q hq
          exact ⟨by simp; omega, hq'.2⟩
        · have hq' := hTR.2.2.1 q hq
          exact ⟨by simp; omega, hq'.2⟩
      · rw [sdiff_glue, Finset.card_union_of_disjoint (disj_cons_image _ _),
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
          hTL.2.2.2.1, hTR.2.2.2.1]
        simp only [Nat.add_sub_cancel]
        rw [Nat.pow_succ]
        ring
      · intro p hp
        rw [sdiff_glue] at hp
        rcases Finset.mem_union.mp hp with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
          exact hTL.2.2.2.2.1 q hq
        · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
          exact hTR.2.2.2.2.1 q hq
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · simpa using hres_root
        · exact hTL.2.2.2.2.2 q hq
        · exact hTR.2.2.2.2.2 q hq

private def buildSeg {n b : ℕ} (v : ℕ → Fin n) (s : ℕ → Bool) (init : Bool) :
    (len : ℕ) → ℕ → (Fin b → Bool) → (Fin b → Bool) →
      Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Raw n b))
  | 0, i, yi, yj => ({[]}, ∅, fun _ => blockClause (v i) yi ∪ blockClause (v i) yj)
  | 1, i, yi, yj => ({[]}, ∅, fun _ => blockClause (v i) yi ∪ blockClause (v (i + 1)) yj)
  | len + 2, i, yi, yj =>
    let total := len + 2
    let l1 := total / 2
    let l2 := total - l1
    let k := i + l1
    have hl1 : l1 < total := by omega
    have hl2 : l2 < total := by omega
    let flag := !(init ^^ xorPrefix s k)
    joinRec (v k) (blockClause (v i) yi) (blockClause (v (i + total)) yj)
      (fun z => if vecParity z = flag then buildSeg v s init l1 i yi z
                else buildSeg v s init l2 k z yj)
      b (le_refl b) (fun _ => false)
termination_by len => len

private theorem buildSeg_spec {n b : ℕ} (hb : 0 < b) (E : Fin n → Fin n → Bool → Prop)
    (v : ℕ → Fin n) (s : ℕ → Bool) (g : ℕ)
    (hv : v 0 = v g)
    (hodd : Odd (((Finset.range g).filter (fun i => s i = true)).card))
    (hmin : ∀ j < g, ¬ badCycle E j)
    (hE : ∀ i < g, E (v i) (v (i + 1)) (s i))
    (init : Bool) :
    ∀ len : ℕ, 1 ≤ len → ∀ i : ℕ, i + len ≤ g →
      ∀ yi yj : Fin b → Bool,
        vecParity yi = (init ^^ xorPrefix s i) →
        vecParity yj = !(init ^^ xorPrefix s (i + len)) →
        (v i = v (i + len) → yi = yj) →
        let T := buildSeg v s init len i yi yj
        treeShape T.1 T.2.1 ∧
        T.2.2 [] = blockClause (v i) yi ∪ blockClause (v (i + len)) yj ∧
        (∀ p ∈ T.1, p.length ≤ b * Nat.clog 2 len ∧
          (T.2.2 p).card ≤ (if len = 1 then (blockClause (v i) yi ∪ blockClause (v (i + 1)) yj).card
                            else if len = 2 ∧ v i = v (i + len) then 2 * b
                            else 3 * b - 1)) ∧
        (T.1 \ T.2.1).card = bal (2 ^ (b - 1)) len ∧
        (∀ p ∈ T.1 \ T.2.1, liftAxP (edgeFormula E) (T.2.2 p)) ∧
        (∀ p ∈ T.2.1, IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p)) := by
  classical
  have hnodup := shortest_bad_nodup E g hmin hv hodd hE
  intro len
  induction len using Nat.strong_induction_on with
  | ind len ih =>
    intro hlen1 i hile yi yj hyi hyj hsame
    match len with
    | 0 => omega
    | 1 =>
      have h1_eq : buildSeg v s init 1 i yi yj =
          ({[]}, ∅, fun _ => blockClause (v i) yi ∪ blockClause (v (i + 1)) yj) := by
        conv_lhs => rw [buildSeg]
      rw [h1_eq]
      dsimp only
      refine ⟨⟨by simp, by simp, fun p bit hp => by
          rw [Finset.mem_singleton] at hp
          have := congrArg List.length hp
          simp at this, fun p hp => by simp at hp⟩, rfl, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton.mp hp]
        simp
      · simp [bal_one]
      · intro p _
        set a := init ^^ xorPrefix s i
        let C : Clause (Fin n) := {(v i, !a), (v (i + 1), a ^^ s i)}
        let y : Raw n b → Bool := fun r =>
          if r.1 = v i then yi r.2 else if r.1 = v (i + 1) then yj r.2 else false
        have hy_vi : ∀ j : Fin b, y ⟨v i, j⟩ = yi j := fun j => by simp [y]
        have hy_vi1 : ∀ j : Fin b, y ⟨v (i + 1), j⟩ = yj j := by
          intro j
          by_cases heq : v (i + 1) = v i
          · simp only [y, heq, ite_true]
            exact congrFun (hsame heq.symm) j
          · simp [y, heq]
        have hp_vi : rawParity y (v i) = a := by
          have : rawParity y (v i) = vecParity yi := by
            unfold rawParity vecParity
            apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
            ext j; simp [hy_vi j]
          rw [this, hyi]
        have hp_vi1 : rawParity y (v (i + 1)) = !(a ^^ s i) := by
          have : rawParity y (v (i + 1)) = vecParity yj := by
            unfold rawParity vecParity
            apply congrArg (fun S : Finset (Fin b) => decide (Odd S.card))
            ext j; simp [hy_vi1 j]
          rw [this, hyj, xorPrefix]
          simp [a]
        refine ⟨C, ⟨v i, v (i + 1), s i, a, hE i (by omega), rfl⟩, y, ?_, ?_⟩
        · intro lit hlit
          simp only [C, Finset.mem_insert, Finset.mem_singleton] at hlit
          rcases hlit with rfl | rfl
          · dsimp only; rw [hp_vi]; cases a <;> decide
          · dsimp only; rw [hp_vi1]; cases a ^^ s i <;> decide
        · ext l
          simp only [blockClause, upperClause, Nat.zero_le, Finset.filter_true,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            C, Finset.image_insert, Finset.image_singleton, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
            · exact ⟨⟨v i, j⟩, Or.inl rfl, by simp [hy_vi j]⟩
            · exact ⟨⟨v (i + 1), j⟩, Or.inr rfl, by simp [hy_vi1 j]⟩
          · rintro ⟨⟨u, j⟩, rfl | rfl, rfl⟩
            · left; exact ⟨j, by simp [hy_vi j]⟩
            · right; exact ⟨j, by simp [hy_vi1 j]⟩
      · intro p hp; simp at hp
    | len' + 2 =>
      set total := len' + 2
      set l1 := total / 2
      set l2 := total - l1
      set k := i + l1
      set flag := !(init ^^ xorPrefix s k)
      have hl1_pos : 1 ≤ l1 := by omega
      have hl2_pos : 1 ≤ l2 := by omega
      have hl1_lt : l1 < total := by omega
      have hl2_lt : l2 < total := by omega
      have hk_lt_g : k < g := by omega
      have hk_pos : 0 < k := by omega
      have hvk_ne_vi : v k ≠ v i := fun heq => by
        have := hnodup k i hk_lt_g (by omega) heq
        omega
      have hvk_ne_vj : v k ≠ v (i + total) := by
        intro heq
        by_cases hjg : i + total < g
        · have := hnodup k (i + total) hk_lt_g hjg heq
          omega
        · have hjeq : i + total = g := by omega
          rw [hjeq, ← hv] at heq
          have := hnodup k 0 hk_lt_g (by omega) heq
          omega
      set C0 := blockClause (v i) yi
      set C1 := blockClause (v (i + total)) yj
      have hC0_disj : ∀ l ∈ C0, l.1.1 ≠ v k := fun l hl heq =>
        hvk_ne_vi (heq.symm.trans (mem_upperClause_fst_eq hl))
      have hC1_disj : ∀ l ∈ C1, l.1.1 ≠ v k := fun l hl heq =>
        hvk_ne_vj (heq.symm.trans (mem_upperClause_fst_eq hl))
      set W := if total = 2 ∧ v i = v (i + total) then 2 * b else 3 * b - 1
      have hW_inner : (C0 ∪ C1).card + (b - 1) ≤ W := by
        dsimp only [W]
        split_ifs with h2eq
        · rcases h2eq with ⟨_, hveq⟩
          have hy_eq : yi = yj := hsame hveq
          have hCeq : C0 = C1 := by simp [C0, C1, hveq, hy_eq]
          rw [hCeq, Finset.union_idempotent]
          have hc : C1.card ≤ b := blockClause_card (v (i + total)) yj
          omega
        · have hc : (C0 ∪ C1).card ≤ b + b := (Finset.card_union_le C0 C1).trans
            (Nat.add_le_add (blockClause_card (v i) yi) (blockClause_card (v (i + total)) yj))
          omega
      set sub := fun z : Fin b → Bool =>
        if vecParity z = flag then buildSeg v s init l1 i yi z
        else buildSeg v s init l2 k z yj
      have hsub_spec : ∀ z : Fin b → Bool,
          let T := sub z
          treeShape T.1 T.2.1 ∧
          T.2.2 [] = (if vecParity z = flag then C0 else C1) ∪ blockClause (v k) z ∧
          (∀ p ∈ T.1, p.length ≤ (if vecParity z = flag then b * Nat.clog 2 l1 else b * Nat.clog 2 l2) ∧
            (T.2.2 p).card ≤ W) ∧
          (T.1 \ T.2.1).card = (if vecParity z = flag then bal (2 ^ (b - 1)) l1 else bal (2 ^ (b - 1)) l2) ∧
          (∀ p ∈ T.1 \ T.2.1, liftAxP (edgeFormula E) (T.2.2 p)) ∧
          (∀ p ∈ T.2.1, IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p)) := by
        intro z
        dsimp only [sub]
        split_ifs with hz
        · have h1 := ih l1 hl1_lt hl1_pos i (by omega) yi z hyi hz (fun heq => absurd heq.symm hvk_ne_vi)
          refine ⟨h1.1, h1.2.1, fun p hp => ⟨(h1.2.2.1 p hp).1, (h1.2.2.1 p hp).2.trans ?_⟩,
            h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2⟩
          dsimp only [W]
          have hpair : (blockClause (v i) yi ∪ blockClause (v (i + 1)) z).card ≤ b + b :=
            (Finset.card_union_le _ _).trans
              (Nat.add_le_add (blockClause_card _ _) (blockClause_card _ _))
          split_ifs <;> omega
        · have hz' : vecParity z = (init ^^ xorPrefix s k) := by
            revert hz
            dsimp only [flag]
            cases vecParity z <;> cases (init ^^ xorPrefix s k) <;> decide
          have hk_add : k + l2 = i + total := by omega
          have h2 := ih l2 hl2_lt hl2_pos k (by omega) z yj hz' (by rw [hk_add]; exact hyj)
            (fun heq => absurd (hk_add ▸ heq) hvk_ne_vj)
          refine ⟨h2.1, ?_, fun p hp => ⟨(h2.2.2.1 p hp).1, (h2.2.2.1 p hp).2.trans ?_⟩,
            h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2⟩
          · rw [h2.2.1, hk_add, Finset.union_comm]
          · dsimp only [W]
            have hpair : (blockClause (v k) z ∪ blockClause (v (k + 1)) yj).card ≤ b + b :=
              (Finset.card_union_le _ _).trans
                (Nat.add_le_add (blockClause_card _ _) (blockClause_card _ _))
            split_ifs <;> omega
      have hjoin := joinRec_spec hb (edgeFormula E) (v k) C0 C1 hC0_disj hC1_disj flag
        (b * Nat.clog 2 l1) (b * Nat.clog 2 l2)
        (bal (2 ^ (b - 1)) l1) (bal (2 ^ (b - 1)) l2) W hW_inner sub hsub_spec
        b (le_refl b) hb (fun _ => false)
      have hT_eq : buildSeg v s init total i yi yj =
          joinRec (v k) C0 C1 sub b (le_refl b) (fun _ => false) := by
        conv_lhs => rw [buildSeg]
      rw [hT_eq]
      have hcl_bound : b + max (b * Nat.clog 2 l1) (b * Nat.clog 2 l2) ≤ b * Nat.clog 2 total := by
        set d := Nat.clog 2 total
        have hd1 : 1 ≤ d := by
          by_contra h0
          have : d = 0 := by omega
          have hle := Nat.le_pow_clog (b := 2) (by decide) total
          rw [show Nat.clog 2 total = 0 from this] at hle
          simp at hle; omega
        have htot_le : total ≤ 2 ^ d := Nat.le_pow_clog (b := 2) (by decide) total
        have hp2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
          have : d = (d - 1) + 1 := by omega
          conv_lhs => rw [this, Nat.pow_succ, Nat.mul_comm]
        have hl1_c : Nat.clog 2 l1 ≤ d - 1 :=
          (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
        have hl2_c : Nat.clog 2 l2 ≤ d - 1 :=
          (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
        have hm1 : b * Nat.clog 2 l1 ≤ b * (d - 1) := Nat.mul_le_mul_left b hl1_c
        have hm2 : b * Nat.clog 2 l2 ≤ b * (d - 1) := Nat.mul_le_mul_left b hl2_c
        have hm : max (b * Nat.clog 2 l1) (b * Nat.clog 2 l2) ≤ b * (d - 1) := max_le hm1 hm2
        have hbd : b + b * (d - 1) = b * d := by
          have : d = (d - 1) + 1 := by omega
          conv_rhs => rw [this, Nat.mul_succ, Nat.add_comm]
        omega
      refine ⟨hjoin.1, ?_, ?_, ?_, hjoin.2.2.2.2.1, hjoin.2.2.2.2.2⟩
      · rw [hjoin.2.1, upperClause_top, Finset.union_empty]
      · intro p hp
        have hp' := hjoin.2.2.1 p hp
        have hne1 : total ≠ 1 := by omega
        simp only [hne1, ite_false]
        exact ⟨hp'.1.trans hcl_bound, hp'.2⟩
      · rw [hjoin.2.2.2.1, bal_split_eq (by omega : 2 ≤ total)]

private theorem upper_construction {n b : ℕ} (hb : 0 < b)
    (E : Fin n → Fin n → Bool → Prop)
    (g H K width : ℕ) (hg : badCycle E g) (hmin : ∀ j < g, ¬ badCycle E j)
    (hH : b * Nat.clog 2 (2 * g) ≤ H)
    (hK : bal (2 ^ (b - 1)) (2 * g) ≤ K)
    (hW : (if g = 1 then b else if g = 2 then 2 * b else 3 * b - 1) ≤ width) :
    refutesP (b := b) (edgeFormula E) H K width := by
  rcases hg with ⟨v, s, hv, hodd, hE⟩
  have hg_pos : 1 ≤ g := by
    by_contra h0
    have : g = 0 := by omega
    subst this
    simp at hodd
  have hpar_g : xorPrefix s g = true := (xorPrefix_eq_true_iff_odd s g).mpr hodd
  set W0 := if g = 1 then b else if g = 2 then 2 * b else 3 * b - 1
  have hW_inner : ((∅ : Clause (Raw n b)) ∪ ∅).card + (b - 1) ≤ W0 := by
    dsimp only [W0]
    split_ifs <;> simp <;> omega
  set sub := fun z : Fin b → Bool => buildSeg v s (vecParity z) g 0 z z
  have hsub_spec : ∀ z : Fin b → Bool,
      let T := sub z
      treeShape T.1 T.2.1 ∧
      T.2.2 [] = (if vecParity z = false then (∅ : Clause (Raw n b)) else ∅) ∪ blockClause (v 0) z ∧
      (∀ p ∈ T.1, p.length ≤ (if vecParity z = false then b * Nat.clog 2 g else b * Nat.clog 2 g) ∧
        (T.2.2 p).card ≤ W0) ∧
      (T.1 \ T.2.1).card = (if vecParity z = false then bal (2 ^ (b - 1)) g else bal (2 ^ (b - 1)) g) ∧
      (∀ p ∈ T.1 \ T.2.1, liftAxP (edgeFormula E) (T.2.2 p)) ∧
      (∀ p ∈ T.2.1, IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p)) := by
    intro z
    have hseg := buildSeg_spec hb E v s g hv hodd hmin hE (vecParity z) g hg_pos 0 (by omega) z z
      (by simp [xorPrefix])
      (by simp [hpar_g])
      (fun _ => rfl)
    refine ⟨hseg.1, ?_, fun p hp => ?_, ?_, hseg.2.2.2.2.1, hseg.2.2.2.2.2⟩
    · rw [hseg.2.1]
      simp only [Nat.zero_add, ← hv, Finset.union_idempotent, ite_self, Finset.empty_union]
    · have hp' := hseg.2.2.1 p hp
      refine ⟨by simpa using hp'.1, hp'.2.trans ?_⟩
      dsimp only [W0]
      simp only [Nat.zero_add, ← hv]
      by_cases hg1 : g = 1
      · subst hg1
        simp only [ite_true]
        rw [← hv, Finset.union_idempotent]
        exact blockClause_card (v 0) z
      · by_cases hg2 : g = 2
        · simp [hg1, hg2]
        · simp [hg1, hg2]
    · simpa using hseg.2.2.2.1
  have htop := joinRec_spec hb (edgeFormula E) (v 0) ∅ ∅ (by simp) (by simp) false
    (b * Nat.clog 2 g) (b * Nat.clog 2 g)
    (bal (2 ^ (b - 1)) g) (bal (2 ^ (b - 1)) g) W0 hW_inner sub hsub_spec
    b (le_refl b) hb (fun _ => false)
  set T := joinRec (v 0) ∅ ∅ sub b (le_refl b) (fun _ => false)
  refine ⟨T.1, T.2.1, T.2.2, htop.1, ?_, ?_, ?_, htop.2.2.2.2.1, htop.2.2.2.2.2⟩
  · rw [htop.2.1, upperClause_top]
    simp
  · intro p hp
    have hp' := htop.2.2.1 p hp
    have hlen : b + max (b * Nat.clog 2 g) (b * Nat.clog 2 g) = b * Nat.clog 2 (2 * g) := by
      rw [max_self, clog_two_double hg_pos, Nat.mul_succ, Nat.add_comm]
    exact ⟨hp'.1.trans (hlen.le.trans hH), hp'.2.trans hW⟩
  · rw [htop.2.2.2.1]
    have hbal : bal (2 ^ (b - 1)) (2 * g) =
        2 ^ (b - 1) * (bal (2 ^ (b - 1)) g + bal (2 ^ (b - 1)) g) := by
      have hsp := bal_split_eq (base := 2 ^ (b - 1)) (m := 2 * g) (by omega)
      have hd1 : (2 * g) / 2 = g := by omega
      have hd2 : 2 * g - g = g := by omega
      rw [hd1, hd2] at hsp
      exact hsp
    rw [← hbal]
    exact hK

end PEqualNP.Outside.L_pcx_307

theorem PEqualNP.Outside.L_pcx_307 : ∀ (n : ℕ) (hn : 0 < n) (b : ℕ), 0 < b →
  let w := fun _ : Fin n => b
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H K width : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
      shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H ∧ (line p).card ≤ width) ∧ (N \ J).card ≤ K ∧
      (∀ p ∈ N \ J, liftAx F (line p)) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
        (line (p ++ [false])) (line (p ++ [true])) (line p)
  let base := 2^(b-1)
  let balanced := fun m : ℕ =>
    let d := Nat.clog 2 m
    (2^d-m)*base^(d-1) + (2*m-2^d)*base^d
  ∀ (E : Fin n → Fin n → Bool → Prop), (∀ u v s, E u v s → E v u s) →
    let bad := fun m : ℕ => ∃ (v : ℕ → Fin n) (s : ℕ → Bool), v 0 = v m ∧
      Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
      ∀ i < m, E (v i) (v (i+1)) (s i)
    let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C |
      ∃ u v s a, E u v s ∧ C = {(u,!a),(v,a ^^ s)}}
    ∀ (g H K width : ℕ), bad g → (∀ j < g, ¬ bad j) →
      Iff (refutes F H K width) (b*Nat.clog 2 (2*g) ≤ H ∧ balanced (2*g) ≤ K ∧
        (if g = 1 then b else if g = 2 then 2*b else 3*b-1) ≤ width) := by
  intro n hn b hb w Raw parity liftAx shape refutes base balanced E hsym bad F g H K width hg hmin
  constructor
  · exact PEqualNP.Outside.L_pcx_307.lower_bounds hn hb E hsym g H K width hg hmin
  · rintro ⟨hH, hK, hW⟩
    exact PEqualNP.Outside.L_pcx_307.upper_construction hb E g H K width hg hmin hH hK hW
