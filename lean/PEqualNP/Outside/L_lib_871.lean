import PEqualNP.Defs
import PEqualNP.Outside.L_lib_542
import PEqualNP.Outside.L_lib_540

namespace PEqualNP.Outside.L_lib_871

open Classical

def loc (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ hn⟩

def window (n w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) : Fin (w + 1) → Bool :=
  fun j => x (loc n hn (i.val + j.val))

lemma loc_add_mod (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    loc n hn (a + b) = loc n hn ((a % n) + b) := by
  apply Fin.ext
  change (a + b) % n = (a % n + b) % n
  rw [Nat.add_mod a b n, Nat.add_mod (a % n) b n, Nat.mod_mod]

lemma case_n_eq_1 (w : ℕ) (hw : 0 < w) :
    let n := 1
    let hn : 0 < n := Nat.one_pos
    let D := 2^w
    let B := min (2^n) (min (n*D) (D*D))
    let cut := max 1 (min (n-1) (max w (n-w)))
    let Pat := Fin (w+1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc' := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc' (i.val+j.val))) = true)).card
    let Slot := Fin n × Pat
    ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
      B ≤ 64*M ∧ Function.Injective port ∧
      (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
      ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
        total (fun i pat => if i.val < cut then
          (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
          (if addr ∈ enabled then 1 else 0) := by
  intro n hn D B cut Pat Row Tab loc' total Slot
  let p0 : Pat := fun _ => false
  let base : Tab := fun _ _ => false
  let port : Fin 1 → Slot := fun _ => (⟨0, hn⟩, p0)
  let query : Fin 1 → Tab := fun _ _ _ => true
  refine ⟨1, base, port, query, ?_, ?_, ?_, ?_⟩
  · have hB : B ≤ 2 := le_trans (min_le_left _ _) (by norm_num)
    omega
  · intro a b _
    exact Fin.ext (by omega)
  · intro bit
    refine ⟨?_, rfl⟩
    simp only [cut, port]
    omega
  · intro enabled addr
    let x0 : Fin 1 → Bool := fun _ => false
    have hx0_win : (fun j : Fin (w + 1) => x0 (loc' (0 + j.val))) = p0 := rfl
    by_cases hmem : addr ∈ enabled
    · rw [if_pos hmem]
      have hfilt : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun x =>
          ∀ i : Fin 1, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = {x0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          have h0 := h ⟨0, hn⟩
          have hcut : (⟨0, hn⟩ : Fin 1).val < cut := by simp [cut]
          simp only [hcut, ↓reduceIte, base, Bool.false_or, decide_eq_true_eq, Finset.mem_image] at h0
          rcases h0 with ⟨b, _, hb⟩
          have hp := (Prod.mk.inj hb).2
          funext k
          have hk0 : k = ⟨0, hn⟩ := Fin.ext (by omega)
          rw [hk0]
          have hval := congrFun hp ⟨0, Nat.zero_lt_succ w⟩
          simpa [port, p0, loc'] using hval
        · intro hx
          subst hx
          intro i
          have hi0 : i = ⟨0, hn⟩ := Fin.ext (by omega)
          rw [hi0]
          have hcut : (⟨0, hn⟩ : Fin 1).val < cut := by simp [cut]
          simp only [hcut, ↓reduceIte, base, Bool.false_or, decide_eq_true_eq, Finset.mem_image]
          refine ⟨addr, hmem, ?_⟩
          apply Prod.ext rfl
          funext j
          rfl
      change (Finset.filter _ Finset.univ).card = 1
      rw [hfilt, Finset.card_singleton]
    · rw [if_neg hmem]
      have hfilt : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun x =>
          ∀ i : Fin 1, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _
        intro h
        have h0 := h ⟨0, hn⟩
        have hcut : (⟨0, hn⟩ : Fin 1).val < cut := by simp [cut]
        simp only [hcut, ↓reduceIte, base, Bool.false_or, decide_eq_true_eq, Finset.mem_image] at h0
        rcases h0 with ⟨b, hb_mem, _⟩
        have hb_eq : b = addr := Fin.ext (by omega)
        rw [hb_eq] at hb_mem
        exact hmem hb_mem
      change (Finset.filter _ Finset.univ).card = 0
      rw [hfilt, Finset.card_empty]

lemma case_small_n (n w : ℕ) (hn2 : 2 ≤ n) (hnw : n ≤ w + 1) :
    let hn : 0 < n := by omega
    let D := 2^w
    let B := min (2^n) (min (n*D) (D*D))
    let cut := max 1 (min (n-1) (max w (n-w)))
    let Pat := Fin (w+1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc' := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc' (i.val+j.val))) = true)).card
    let Slot := Fin n × Pat
    ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
      B ≤ 64*M ∧ Function.Injective port ∧
      (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
      ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
        total (fun i pat => if i.val < cut then
          (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
          (if addr ∈ enabled then 1 else 0) := by
  intro hn D B cut Pat Row Tab loc' total Slot
  have hcut : cut = n - 1 := by
    have : n - 1 ≤ max w (n - w) := by omega
    simp only [cut, min_eq_left this]
    omega
  have hcard_eq : Fintype.card (Fin n → Bool) = 2 ^ n := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let e : Fin (2 ^ n) ≃ (Fin n → Bool) := (Fintype.equivFinOfCardEq hcard_eq).symm
  let base : Tab := fun i _ => decide (i.val ≠ 0)
  let port : Fin (2 ^ n) → Slot := fun bit => (⟨0, hn⟩, window n w hn (e bit) ⟨0, hn⟩)
  let query : Fin (2 ^ n) → Tab := fun addr i pat => decide (pat = window n w hn (e addr) i)
  have hwin0_inj : ∀ x y : Fin n → Bool, window n w hn x ⟨0, hn⟩ = window n w hn y ⟨0, hn⟩ → x = y := by
    intro x y h
    funext k
    have hk := congrFun h ⟨k.val, by omega⟩
    have hloc : loc n hn k.val = k := Fin.ext (by simp [loc, Nat.mod_eq_of_lt k.isLt])
    simpa [window, hloc] using hk
  refine ⟨2 ^ n, base, port, query, ?_, ?_, ?_, ?_⟩
  · have hB : B ≤ 2 ^ n := min_le_left _ _
    omega
  · intro a b hab
    exact e.injective (hwin0_inj (e a) (e b) (Prod.mk.inj hab).2)
  · intro bit
    refine ⟨?_, ?_⟩
    · simp [port, hcut]; omega
    · simp [port, base]
  · intro enabled addr
    have hlast_pin : ∀ x : Fin n → Bool,
        window n w hn x ⟨n - 1, by omega⟩ = window n w hn (e addr) ⟨n - 1, by omega⟩ → x = e addr := by
      intro x h
      funext k
      let jv := (k.val + 1) % n
      have hjv : jv < n := Nat.mod_lt _ hn
      have hk := congrFun h ⟨jv, by omega⟩
      have hloc : loc n hn ((n - 1) + jv) = k := by
        apply Fin.ext
        change ((n - 1) + (k.val + 1) % n) % n = k.val
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : n - 1 + (k.val + 1) = k.val + n := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      simpa [window, hloc] using hk
    have hloc_eq : ∀ x (i : Fin n), (fun j : Fin (w + 1) => x (loc' (i.val + j.val))) = window n w hn x i :=
      fun _ _ => rfl
    by_cases hmem : addr ∈ enabled
    · rw [if_pos hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = {e addr} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          have hlast := h ⟨n - 1, by omega⟩
          have hnot : ¬ (n - 1 < cut) := by rw [hcut]; omega
          simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hlast
          exact hlast_pin x hlast
        · intro hx
          subst hx
          intro i
          by_cases hic : i.val < cut
          · simp only [hic, ↓reduceIte, base]
            by_cases hi0 : i.val = 0
            · have hi_eq : i = ⟨0, hn⟩ := Fin.ext hi0
              rw [hi_eq]
              simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq,
                Finset.mem_image]
              exact ⟨addr, hmem, rfl⟩
            · simp [hi0]
          · simp only [hic, ↓reduceIte, query, decide_eq_true_eq]
            rfl
      change (Finset.filter _ Finset.univ).card = 1
      rw [hfilt, Finset.card_singleton]
    · rw [if_neg hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ h
        have hlast := h ⟨n - 1, by omega⟩
        have hnot : ¬ (n - 1 < cut) := by rw [hcut]; omega
        simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hlast
        have hx : x = e addr := hlast_pin x hlast
        subst hx
        have h0 := h ⟨0, hn⟩
        have hcut0 : (⟨0, hn⟩ : Fin n).val < cut := by dsimp only; rw [hcut]; omega
        simp only [hcut0, ↓reduceIte, base, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
          decide_eq_true_eq, Finset.mem_image] at h0
        rcases h0 with ⟨b, hb_mem, hb_eq⟩
        have hba : b = addr := e.injective (hwin0_inj (e b) (e addr) (Prod.mk.inj hb_eq).2)
        rw [hba] at hb_mem
        exact hmem hb_mem
      change (Finset.filter _ Finset.univ).card = 0
      rw [hfilt, Finset.card_empty]

lemma suffix_pins_word (n w : ℕ) (hnw : w + 2 ≤ n) (hn2w : n < 2 * w) :
    let hn : 0 < n := by omega
    ∀ (x target : Fin n → Bool),
      (∀ i : Fin n, w ≤ i.val → window n w hn x i = window n w hn target i) →
      x = target := by
  intro hn x target h
  funext k
  by_cases hkw : k.val < w
  · have hrow := h ⟨n - 1, by omega⟩ (show w ≤ (⟨n - 1, by omega⟩ : Fin n).val by dsimp only; omega)
    have hj : k.val + 1 < w + 1 := by omega
    have hpt := congrFun hrow ⟨k.val + 1, hj⟩
    have hloc : loc n hn (n - 1 + (k.val + 1)) = k := by
      apply Fin.ext
      change (n - 1 + (k.val + 1)) % n = k.val
      have hsum : n - 1 + (k.val + 1) = k.val + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
    simpa [window, hloc] using hpt
  · have hrow := h ⟨w, by omega⟩ (le_rfl)
    have hj : k.val - w < w + 1 := by omega
    have hpt := congrFun hrow ⟨k.val - w, hj⟩
    have hloc : loc n hn (w + (k.val - w)) = k := by
      apply Fin.ext
      change (w + (k.val - w)) % n = k.val
      have hsum : w + (k.val - w) = k.val := by omega
      rw [hsum, Nat.mod_eq_of_lt k.isLt]
    simpa [window, hloc] using hpt

lemma case_mid_small (n w : ℕ) (hnw : w + 2 ≤ n) (hn2w : n < 2 * w) (hsmall : n ≤ w + 7) :
    let hn : 0 < n := by omega
    let D := 2^w
    let B := min (2^n) (min (n*D) (D*D))
    let cut := max 1 (min (n-1) (max w (n-w)))
    let Pat := Fin (w+1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc' := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc' (i.val+j.val))) = true)).card
    let Slot := Fin n × Pat
    ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
      B ≤ 64*M ∧ Function.Injective port ∧
      (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
      ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
        total (fun i pat => if i.val < cut then
          (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
          (if addr ∈ enabled then 1 else 0) := by
  intro hn D B cut Pat Row Tab loc' total Slot
  have hcut : cut = w := by
    have h1 : n - w ≤ w := by omega
    have h2 : w ≤ n - 1 := by omega
    simp only [cut, max_eq_left h1, min_eq_right h2]
    omega
  have hcard_pat : Fintype.card Pat = 2 ^ (w + 1) := by
    simp [Pat, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let e : Fin (2 ^ (w + 1)) ≃ Pat := (Fintype.equivFinOfCardEq hcard_pat).symm
  let word : Fin (2 ^ (w + 1)) → (Fin n → Bool) := fun addr k =>
    if hk : k.val < w + 1 then e addr ⟨k.val, hk⟩ else false
  let base : Tab := fun i _ => decide (i.val ≠ 0)
  let port : Fin (2 ^ (w + 1)) → Slot := fun bit => (⟨0, hn⟩, e bit)
  let query : Fin (2 ^ (w + 1)) → Tab := fun addr i pat => decide (pat = window n w hn (word addr) i)
  have hwin0_word : ∀ addr, window n w hn (word addr) ⟨0, hn⟩ = e addr := by
    intro addr
    funext j
    have hloc : loc n hn j.val = ⟨j.val, by omega⟩ :=
      Fin.ext (by simp [loc, Nat.mod_eq_of_lt (by omega : j.val < n)])
    dsimp only [window]
    rw [Nat.zero_add, hloc]
    have hj : (⟨j.val, by omega⟩ : Fin n).val < w + 1 := j.isLt
    simp only [word, hj, ↓reduceDIte]
  refine ⟨2 ^ (w + 1), base, port, query, ?_, ?_, ?_, ?_⟩
  · have hpow : 2 ^ n ≤ 2 ^ (w + 7) := Nat.pow_le_pow_right (by omega) hsmall
    have hpow2 : 2 ^ (w + 7) = 64 * 2 ^ (w + 1) := by
      rw [show w + 7 = (w + 1) + 6 by omega, pow_add]
      simp only [pow_succ, pow_zero]
      ring
    have hB : B ≤ 2 ^ n := min_le_left _ _
    omega
  · intro a b hab
    exact e.injective (Prod.mk.inj hab).2
  · intro bit
    refine ⟨?_, ?_⟩
    · simp [port, hcut]; omega
    · simp [port, base]
  · intro enabled addr
    by_cases hmem : addr ∈ enabled
    · rw [if_pos hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = {word addr} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          apply suffix_pins_word n w hnw hn2w x (word addr)
          intro i hiw
          have hnot : ¬ (i.val < cut) := by omega
          have hi := h i
          simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hi
          exact hi
        · intro hx
          subst hx
          intro i
          by_cases hic : i.val < cut
          · simp only [hic, ↓reduceIte, base]
            by_cases hi0 : i.val = 0
            · have hi_eq : i = ⟨0, hn⟩ := Fin.ext hi0
              rw [hi_eq]
              simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq,
                Finset.mem_image]
              refine ⟨addr, hmem, ?_⟩
              apply Prod.ext
              · rfl
              · exact (hwin0_word addr).symm
            · simp [hi0]
          · simp only [hic, ↓reduceIte, query, decide_eq_true_eq]
            rfl
      change (Finset.filter _ Finset.univ).card = 1
      rw [hfilt, Finset.card_singleton]
    · rw [if_neg hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ h
        have hx : x = word addr := by
          apply suffix_pins_word n w hnw hn2w x (word addr)
          intro i hiw
          have hnot : ¬ (i.val < cut) := by omega
          have hi := h i
          simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hi
          exact hi
        subst hx
        have h0 := h ⟨0, hn⟩
        have hcut0 : (⟨0, hn⟩ : Fin n).val < cut := by dsimp only; rw [hcut]; omega
        simp only [hcut0, ↓reduceIte, base, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
          decide_eq_true_eq, Finset.mem_image] at h0
        rcases h0 with ⟨b, hb_mem, hb_eq⟩
        have heb : e b = e addr := (Prod.mk.inj hb_eq).2.trans (hwin0_word addr)
        have hba : b = addr := e.injective heb
        rw [hba] at hb_mem
        exact hmem hb_mem
      change (Finset.filter _ Finset.univ).card = 0
      rw [hfilt, Finset.card_empty]

lemma two_mul_le_pow_sub_three (m : ℕ) (hm : 8 ≤ m) : 2 * m ≤ 2 ^ (m - 3) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show m + 1 - 3 = (m - 3) + 1 by omega, pow_succ]
    omega

lemma exists_pow_ge (m : ℕ) : ∃ t : ℕ, m ≤ 2 ^ t :=
  ⟨m, Nat.le_of_lt Nat.lt_two_pow_self⟩

lemma case_mid_large (n w : ℕ) (hnw : w + 2 ≤ n) (hn2w : n < 2 * w) (hlarge : w + 8 ≤ n) :
    let hn : 0 < n := by omega
    let D := 2^w
    let B := min (2^n) (min (n*D) (D*D))
    let cut := max 1 (min (n-1) (max w (n-w)))
    let Pat := Fin (w+1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc' := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc' (i.val+j.val))) = true)).card
    let Slot := Fin n × Pat
    ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
      B ≤ 64*M ∧ Function.Injective port ∧
      (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
      ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
        total (fun i pat => if i.val < cut then
          (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
          (if addr ∈ enabled then 1 else 0) := by
  intro hn D B cut Pat Row Tab loc' total Slot
  have hw9 : 9 ≤ w := by omega
  have hn17 : 17 ≤ n := by omega
  have hcut : cut = w := by
    have h1 : n - w ≤ w := by omega
    have h2 : w ≤ n - 1 := by omega
    simp only [cut, max_eq_left h1, min_eq_right h2]
    omega
  let h := n - w - 1
  let t0 := Nat.find (exists_pow_ge (2 * n))
  let t := max h t0
  have ht0_spec : 2 * n ≤ 2 ^ t0 := Nat.find_spec (exists_pow_ge (2 * n))
  have ht0_pos : 0 < t0 := by
    by_contra h0
    have : t0 = 0 := by omega
    rw [this, pow_zero] at ht0_spec
    omega
  have ht0_min : 2 ^ (t0 - 1) < 2 * n := by
    by_contra hge
    exact Nat.find_min (exists_pow_ge (2 * n)) (by omega : t0 - 1 < t0) (by omega)
  have ht0_upper : 2 ^ t0 < 4 * n := by
    have hpow : 2 ^ t0 = 2 * 2 ^ (t0 - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht0_pos, pow_succ, mul_comm]
    omega
  have ht0_le_n3 : t0 ≤ n - 3 := by
    by_contra hgt
    have hle : n - 3 < t0 := by omega
    exact Nat.find_min (exists_pow_ge (2 * n)) hle (two_mul_le_pow_sub_three n (by omega))
  have h_le_t : h ≤ t := le_max_left h t0
  have ht_le_n3 : t + 3 ≤ n := by omega
  have h2n_le_pow_t : 2 * n ≤ 2 ^ t :=
    le_trans ht0_spec (Nat.pow_le_pow_right (by omega) (le_max_right h t0))
  let sites : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < w)
  have hsites_card : sites.card = w := by
    rw [← Finset.card_range w]
    refine Finset.card_bij (fun (i : Fin n) _ => i.val) ?_ ?_ ?_
    · intro i hi
      simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_range.mpr hi
    · intro i1 _ i2 _ heq; exact Fin.ext heq
    · intro m hm
      simp only [Finset.mem_range] at hm
      exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  obtain ⟨pool, owner, hpool_card, hpool_uniq⟩ :=
    PEqualNP.Outside.L_lib_542 n h t hn h_le_t ht_le_n3 h2n_le_pow_t sites
  have hpool_ge : w * 2 ^ (n - t - 3) ≤ pool.card := by
    have hsum := Finset.card_eq_sum_card_fiberwise (f := owner)
      (s := (Finset.univ : Finset (↥pool))) (t := (Finset.univ : Finset (↥sites))) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_coe] at hsum
    have hle_sum : ∑ i : ↥sites, 2 ^ (n - t - 3) ≤ ∑ i : ↥sites, ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card :=
      Finset.sum_le_sum (fun i _ => hpool_card i)
    rw [← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hsites_card, smul_eq_mul] at hle_sum
    exact hle_sum
  have hB_le : B ≤ 64 * pool.card := by
    by_cases hth : t = h
    · have hnt3 : n - t - 3 = w - 2 := by omega
      have hB1 : B ≤ n * D := le_trans (min_le_right _ _) (min_le_left _ _)
      have hD_split : D = 4 * 2 ^ (w - 2) := by
        change 2 ^ w = 4 * 2 ^ (w - 2)
        rw [show w = (w - 2) + 2 by omega, pow_add]
        norm_num
        ring
      rw [hnt3] at hpool_ge
      calc B ≤ n * D := hB1
        _ ≤ (2 * w) * D := Nat.mul_le_mul_right D (le_of_lt hn2w)
        _ = 8 * (w * 2 ^ (w - 2)) := by rw [hD_split]; ring
        _ ≤ 64 * (w * 2 ^ (w - 2)) := by omega
        _ ≤ 64 * pool.card := Nat.mul_le_mul_left 64 hpool_ge
    · have htt0 : t = t0 := by omega
      have hB1 : B ≤ 2 ^ n := min_le_left _ _
      have hpow_split : 2 ^ n = 2 ^ (n - t0 - 3) * 8 * 2 ^ t0 := by
        have h8 : (8 : ℕ) = 2 ^ 3 := by decide
        rw [h8, ← pow_add, ← pow_add]
        congr 1
        omega
      have hmul_pow : 2 ^ t0 * B ≤ 2 ^ t0 * (64 * pool.card) := by
        calc 2 ^ t0 * B ≤ 2 ^ t0 * 2 ^ n := Nat.mul_le_mul_left (2 ^ t0) hB1
          _ ≤ (4 * n) * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) (le_of_lt ht0_upper)
          _ ≤ (8 * w) * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) (by omega)
          _ = 2 ^ t0 * (64 * (w * 2 ^ (n - t0 - 3))) := by rw [hpow_split]; ring
          _ ≤ 2 ^ t0 * (64 * pool.card) := by
              rw [htt0] at hpool_ge
              exact Nat.mul_le_mul_left (2 ^ t0) (Nat.mul_le_mul_left 64 hpool_ge)
      exact Nat.le_of_mul_le_mul_left hmul_pow (Nat.two_pow_pos t0)
  let M := pool.card
  let e : Fin M ≃ ↥pool := (Fintype.equivFinOfCardEq (Fintype.card_coe pool)).symm
  let port : Fin M → Slot := fun bit =>
    ((owner (e bit)).val, window n w hn (e bit).val (owner (e bit)).val)
  let base : Tab := fun i pat => decide (∀ bit : Fin M, port bit ≠ (i, pat))
  let query : Fin M → Tab := fun addr i pat => decide (pat = window n w hn (e addr).val i)
  have hport_inj : Function.Injective port := by
    intro a b hab
    have howner : (owner (e a)).val = (owner (e b)).val := (Prod.mk.inj hab).1
    have hwin : window n w hn (e a).val (owner (e a)).val =
        window n w hn (e b).val (owner (e b)).val := (Prod.mk.inj hab).2
    have heq_pool : e a = e b := by
      apply hpool_uniq (e a) (e b)
      intro j
      have hj : j.val < w + 1 := by omega
      have hpt := congrFun hwin ⟨j.val, hj⟩
      simpa [window, loc, howner] using hpt
    exact e.injective heq_pool
  refine ⟨M, base, port, query, hB_le, hport_inj, ?_, ?_⟩
  · intro bit
    refine ⟨?_, ?_⟩
    · have hmem := (owner (e bit)).property
      simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rw [hcut]; exact hmem
    · simp only [base, decide_eq_false_iff_not, not_forall, not_not]
      exact ⟨bit, rfl⟩
  · intro enabled addr
    by_cases hmem : addr ∈ enabled
    · rw [if_pos hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = {(e addr).val} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          apply suffix_pins_word n w hnw hn2w x (e addr).val
          intro i hiw
          have hnot : ¬ (i.val < cut) := by omega
          have hi := h i
          simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hi
          exact hi
        · intro hx
          subst hx
          intro i
          by_cases hic : i.val < cut
          · simp only [hic, ↓reduceIte]
            by_cases hi_own : i = (owner (e addr)).val
            · rw [hi_own]
              apply Bool.or_eq_true_iff.mpr
              right
              simp only [decide_eq_true_eq, Finset.mem_image]
              exact ⟨addr, hmem, rfl⟩
            · apply Bool.or_eq_true_iff.mpr
              left
              simp only [base, decide_eq_true_eq]
              intro bit hbit
              have howner : (owner (e bit)).val = i := (Prod.mk.inj hbit).1
              have hwin : window n w hn (e bit).val (owner (e bit)).val =
                  window n w hn (e addr).val i := (Prod.mk.inj hbit).2
              have heq_pool : e bit = e addr := by
                apply hpool_uniq (e bit) (e addr)
                intro j
                have hj : j.val < w + 1 := by omega
                have hpt := congrFun hwin ⟨j.val, hj⟩
                simpa [window, loc, howner] using hpt
              have hba : bit = addr := e.injective heq_pool
              rw [hba] at howner
              exact hi_own howner.symm
          · simp only [hic, ↓reduceIte, query, decide_eq_true_eq]
            rfl
      change (Finset.filter _ Finset.univ).card = 1
      rw [hfilt, Finset.card_singleton]
    · rw [if_neg hmem]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
          ∀ i : Fin n, (if i.val < cut then (base i (fun j => x (loc' (i.val + j.val))) ||
            decide ((i, fun j => x (loc' (i.val + j.val))) ∈ enabled.image port))
            else query addr i (fun j => x (loc' (i.val + j.val)))) = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ h
        have hx : x = (e addr).val := by
          apply suffix_pins_word n w hnw hn2w x (e addr).val
          intro i hiw
          have hnot : ¬ (i.val < cut) := by omega
          have hi := h i
          simp only [hnot, ↓reduceIte, query, decide_eq_true_eq] at hi
          exact hi
        subst hx
        have hown := h (owner (e addr)).val
        have hown_cut : (owner (e addr)).val.val < cut := by
          have hprop := (owner (e addr)).property
          simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and] at hprop
          omega
        simp only [hown_cut, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_image] at hown
        rcases hown with hbase | ⟨bit, hbit_mem, hbit_eq⟩
        · simp only [base, decide_eq_true_eq] at hbase
          exact hbase addr rfl
        · have hba : bit = addr := hport_inj hbit_eq
          rw [hba] at hbit_mem
          exact hmem hbit_mem
      change (Finset.filter _ Finset.univ).card = 0
      rw [hfilt, Finset.card_empty]

lemma case_large_n (n w : ℕ) (hw : 0 < w) (hn2w : 2 * w ≤ n) :
    let hn : 0 < n := by omega
    let D := 2^w
    let B := min (2^n) (min (n*D) (D*D))
    let cut := max 1 (min (n-1) (max w (n-w)))
    let Pat := Fin (w+1) → Bool
    let Row := Pat → Bool
    let Tab := Fin n → Row
    let loc' := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let total := fun (table : Tab) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, table i (fun j => x (loc' (i.val+j.val))) = true)).card
    let Slot := Fin n × Pat
    ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
      B ≤ 64*M ∧ Function.Injective port ∧
      (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
      ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
        total (fun i pat => if i.val < cut then
          (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
          (if addr ∈ enabled then 1 else 0) := by
  intro hn D B cut Pat Row Tab loc' total Slot
  let d := w - 1
  let L := n - w
  have hw_eq : w = d + 1 := by omega
  have hL_ge : w ≤ L := by omega
  have hn_eq : L + d + 1 = n := by omega
  have hcut : cut = L := by
    have h1 : w ≤ n - w := by omega
    have h2 : n - w ≤ n - 1 := by omega
    simp only [cut, max_eq_right h1, min_eq_right h2]
    omega
  obtain ⟨m, edge, base540, port540, hm_bound, hedge_inj, hedge_disj, h540⟩ :=
    PEqualNP.Outside.L_lib_540 d L (by omega)
  have h540_f := h540 false
  rcases h540_f with ⟨hport_inj, hbase_false, hcount⟩
  let port : Fin m → Slot := fun bit =>
    (⟨(port540 false bit).1.val, by omega⟩, fun off => (port540 false bit).2 ⟨off.val, by omega⟩)
  let base : Tab := fun i pat =>
    if hi : i.val < L then base540 (⟨i.val, hi⟩, fun off => pat ⟨off.val, by omega⟩) else true
  let query : Fin m → Tab := fun addr i pat =>
    (if i.val = L then decide (∀ pos : Fin w, pat ⟨pos.val, by omega⟩ = (edge addr).2 ⟨pos.val, by omega⟩) else true) &&
    (if i.val = n - 1 then decide (∀ pos : Fin w, pat ⟨pos.val + 1, by omega⟩ = (edge addr).1 ⟨pos.val, by omega⟩) else true)
  refine ⟨m, base, port, query, ?_, ?_, ?_, ?_⟩
  · have hD_eq : D = 2 ^ (d + 1) := by simp [D, hw_eq]
    have hB1 : B ≤ min (n * D) (D * D) := min_le_right _ _
    have hn_le : n ≤ 2 * L := by omega
    have hm1 : min (n * D) (D * D) ≤ 2 * (D * min L D) := by
      rcases le_total L D with hLD | hDL
      · rw [min_eq_left hLD]
        calc min (n * D) (D * D) ≤ n * D := min_le_left _ _
          _ ≤ (2 * L) * D := Nat.mul_le_mul_right D hn_le
          _ = 2 * (D * L) := by ring
      · rw [min_eq_right hDL]
        calc min (n * D) (D * D) ≤ D * D := min_le_right _ _
          _ ≤ 2 * (D * D) := by omega
    rw [← hD_eq] at hm_bound
    omega
  · intro a b hab
    apply hport_inj
    apply Prod.ext
    · exact Fin.ext (congrArg (fun s : Slot => s.1.val) hab)
    · funext off
      have := congrFun (Prod.mk.inj hab).2 ⟨off.val, by omega⟩
      exact this
  · intro bit
    refine ⟨?_, ?_⟩
    · simp only [port, hcut]; exact (port540 false bit).1.isLt
    · simp only [port, base]
      have hlt : (port540 false bit).1.val < L := (port540 false bit).1.isLt
      simp only [hlt, ↓reduceDIte]
      have := hbase_false bit
      convert this using 2
  · intro enabled addr
    let x_end : Fin (d + 1) → Bool := fun pos => (edge addr).1 pos
    let y_end : Fin (d + 1) → Bool := fun pos => (edge addr).2 pos
    have hcnt := hcount enabled x_end y_end
    have hne_xy : x_end ≠ y_end := hedge_disj addr addr
    have hex_iff : (∃ j ∈ enabled, edge j = (x_end, y_end)) ↔ addr ∈ enabled := by
      constructor
      · rintro ⟨j, hj, heq⟩
        have hja : j = addr := hedge_inj heq
        rw [hja] at hj; exact hj
      · intro h
        exact ⟨addr, h, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, hex_iff] at hcnt
    rw [if_neg hne_xy, Nat.zero_add] at hcnt
    rw [← hcnt]
    refine Finset.card_bij (fun (x : Fin n → Bool) _ => fun k : Fin (L + d + 1) => x ⟨k.val, by omega⟩) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      constructor
      · intro pos
        have hpos_val : pos.val < d + 1 := pos.isLt
        have hL_lt : L < n := by omega
        have hn1_lt : n - 1 < n := by omega
        have hqL := hx ⟨L, hL_lt⟩
        have hqn1 := hx ⟨n - 1, hn1_lt⟩
        have hnotL : ¬ (L < cut) := by omega
        have hnotn1 : ¬ (n - 1 < cut) := by omega
        simp only [hnotL, ↓reduceIte, query, Bool.and_eq_true, decide_eq_true_eq] at hqL
        simp only [hnotn1, ↓reduceIte, query, Bool.and_eq_true, decide_eq_true_eq] at hqn1
        have hqL' := hqL.1 ⟨pos.val, by omega⟩
        have hqn1' := hqn1.2 ⟨pos.val, by omega⟩
        have hof1 : (Fin.ofNat (L + d + 1) pos.val).val = (loc' (0 + pos.val)).val := by
          simp [Fin.ofNat, loc', hn_eq]
        have hof2 : (Fin.ofNat (L + d + 1) (L + pos.val)).val = (loc' (L + pos.val)).val := by
          simp [Fin.ofNat, loc', hn_eq]
        have hloc_n1 : loc' (n - 1 + (pos.val + 1)) = loc' (0 + pos.val) := by
          apply Fin.ext
          change (n - 1 + (pos.val + 1)) % n = (0 + pos.val) % n
          rw [show n - 1 + (pos.val + 1) = pos.val + n by omega, Nat.add_mod_right, Nat.zero_add]
        constructor
        · convert hqn1' using 1
          · congr 1; apply Fin.ext; rw [hof1, hloc_n1]
        · convert hqL' using 1
          · congr 1; apply Fin.ext; exact hof2
      · intro i
        have hi_cut : i.val < cut := by omega
        have hxi := hx ⟨i.val, by omega⟩
        simp only [hi_cut, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_image] at hxi
        rcases hxi with hbase | ⟨bit, hbit_mem, hbit_eq⟩
        · left
          simp only [base, show i.val < L by omega, ↓reduceDIte] at hbase
          convert hbase using 2
          apply Prod.ext
          · exact Fin.ext rfl
          · funext off
            dsimp only
            congr 1; apply Fin.ext; simp [Fin.ofNat, loc', hn_eq]
        · right
          rw [Finset.mem_image]
          refine ⟨bit, hbit_mem, ?_⟩
          apply Prod.ext
          · exact Fin.ext (congrArg (fun s : Slot => s.1.val) hbit_eq)
          · funext off
            have hpt := congrFun (Prod.mk.inj hbit_eq).2 ⟨off.val, by omega⟩
            convert hpt using 2
            apply Fin.ext; simp [Fin.ofNat, loc', hn_eq]
    · intro x1 _ x2 _ heq
      funext k
      exact congrFun heq ⟨k.val, by omega⟩
    · intro word hword
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword
      refine ⟨fun k => word ⟨k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro i
        by_cases hic : i.val < cut
        · simp only [hic, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_image]
          have hiL : i.val < L := by omega
          rcases hword.2 ⟨i.val, hiL⟩ with hbase | hmem
          · left
            simp only [base, hiL, ↓reduceDIte]
            convert hbase using 2
            apply Prod.ext
            · exact Fin.ext rfl
            · funext off
              dsimp only
              congr 1; apply Fin.ext; simp [Fin.ofNat, loc', hn_eq]
          · right
            rw [Finset.mem_image] at hmem
            rcases hmem with ⟨bit, hbit_mem, hbit_eq⟩
            refine ⟨bit, hbit_mem, ?_⟩
            apply Prod.ext
            · exact Fin.ext (congrArg (fun s : Fin L × (Fin (d + 1 + 1) → Bool) => s.1.val) hbit_eq)
            · funext off
              have hpt := congrFun (Prod.mk.inj hbit_eq).2 ⟨off.val, by omega⟩
              dsimp only
              convert hpt using 2
              apply Fin.ext; simp [Fin.ofNat, loc', hn_eq]
        · simp only [hic, ↓reduceIte, query, Bool.and_eq_true]
          constructor
          · split_ifs with hiL
            · rw [decide_eq_true_eq]
              intro pos
              have hp := (hword.1 ⟨pos.val, by omega⟩).2
              convert hp using 2
              apply Fin.ext; simp [Fin.ofNat, loc', hn_eq, hiL]
            · rfl
          · split_ifs with hin1
            · rw [decide_eq_true_eq]
              intro pos
              have hp := (hword.1 ⟨pos.val, by omega⟩).1
              have hloc_n1 : loc' (n - 1 + (pos.val + 1)) = loc' (0 + pos.val) := by
                apply Fin.ext
                change (n - 1 + (pos.val + 1)) % n = (0 + pos.val) % n
                rw [show n - 1 + (pos.val + 1) = pos.val + n by omega, Nat.add_mod_right, Nat.zero_add]
              convert hp using 2
              apply Fin.ext
              rw [hin1, hloc_n1]
              simp [Fin.ofNat, loc', hn_eq]
            · rfl
      · funext k
        rfl

end PEqualNP.Outside.L_lib_871

theorem PEqualNP.Outside.L_lib_871 : (∀ (n w : Nat) (hn : 0 < n), 0 < w →
  let D := 2^w
  let B := min (2^n) (min (n*D) (D*D))
  let cut := max 1 (min (n-1) (max w (n-w)))
  let Pat := Fin (w+1) → Bool
  let Row := Pat → Bool
  let Tab := Fin n → Row
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let total := fun (table : Tab) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, table i (fun j => x (loc (i.val+j.val))) = true)).card
  let Slot := Fin n × Pat
  ∃ (M : Nat) (base : Tab) (port : Fin M → Slot) (query : Fin M → Tab),
    B ≤ 64*M ∧ Function.Injective port ∧
    (∀ bit, (port bit).1.val < cut ∧ base (port bit).1 (port bit).2 = false) ∧
    ∀ enabled : Finset (Fin M), ∀ addr : Fin M,
      total (fun i pat => if i.val < cut then
        (base i pat || decide ((i,pat) ∈ enabled.image port)) else query addr i pat) =
        (if addr ∈ enabled then 1 else 0)) := by
  intro n w hn hw
  by_cases hn1 : n = 1
  · subst hn1
    exact PEqualNP.Outside.L_lib_871.case_n_eq_1 w hw
  · by_cases hnw : n ≤ w + 1
    · exact PEqualNP.Outside.L_lib_871.case_small_n n w (by omega) hnw
    · by_cases hn2w : 2 * w ≤ n
      · exact PEqualNP.Outside.L_lib_871.case_large_n n w hw hn2w
      · by_cases hsmall : n ≤ w + 7
        · exact PEqualNP.Outside.L_lib_871.case_mid_small n w (by omega) (by omega) hsmall
        · exact PEqualNP.Outside.L_lib_871.case_mid_large n w (by omega) (by omega) (by omega)
