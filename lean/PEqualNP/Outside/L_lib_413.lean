import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_413_aux

theorem card_agree (n : ℕ) (H : Finset (Fin n)) (w : Fin n → Bool) :
    (Finset.univ.filter (fun v : Fin n → Bool => ∀ j ∈ H, v j = w j)).card = 2 ^ (n - H.card) := by
  have e : (Finset.univ.filter (fun v : Fin n → Bool => ∀ j ∈ H, v j = w j))
      = Fintype.piFinset (fun j => if j ∈ H then ({w j} : Finset Bool) else Finset.univ) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hv j
      by_cases hj : j ∈ H
      · simp [hj, hv j hj]
      · simp [hj]
    · intro hv j hj
      have := hv j
      simpa [hj] using this
  have hc : ∀ j : Fin n, (if j ∈ H then ({w j} : Finset Bool) else Finset.univ).card
      = if j ∈ H then 1 else 2 := by
    intro j
    split_ifs <;> simp
  have hcompl : (Finset.univ.filter (fun j : Fin n => ¬ j ∈ H)) = Hᶜ := by
    ext j
    simp
  rw [e, Fintype.card_piFinset]
  simp only [hc]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hcompl, Finset.card_compl,
    Fintype.card_fin]

theorem pow_ineq (x m : ℕ) : x ^ m * (x + m) ≤ (x + 1) ^ m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : (x + 1) * (x + m) = x * (x + (m + 1)) + m := by ring
    have h1 : x * (x + (m + 1)) ≤ (x + 1) * (x + m) := by omega
    calc x ^ (m + 1) * (x + (m + 1)) = x ^ m * (x * (x + (m + 1))) := by ring
      _ ≤ x ^ m * ((x + 1) * (x + m)) := Nat.mul_le_mul_left _ h1
      _ = (x + 1) * (x ^ m * (x + m)) := by ring
      _ ≤ (x + 1) * ((x + 1) ^ m * x) := Nat.mul_le_mul_left _ ih
      _ = (x + 1) ^ (m + 1) * x := by ring

theorem two_pow_le (x : ℕ) (hx : 0 < x) : 2 * x ^ x ≤ (x + 1) ^ x := by
  have h := pow_ineq x x
  have h2 : 2 * x ^ x * x ≤ (x + 1) ^ x * x := by
    calc 2 * x ^ x * x = x ^ x * (x + x) := by ring
      _ ≤ (x + 1) ^ x * x := h
  exact Nat.le_of_mul_le_mul_right h2 hx

theorem two_pow_succ_le (x : ℕ) : 2 * x ^ (x + 1) ≤ (x + 1) ^ (x + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h := pow_ineq x (x + 1)
    have h2 : 2 * x ^ (x + 1) * x ≤ (x + 1) ^ (x + 1) * x := by
      calc 2 * x ^ (x + 1) * x = x ^ (x + 1) * (x + x) := by ring
        _ ≤ x ^ (x + 1) * (x + (x + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ (x + 1) ^ (x + 1) * x := h
    exact Nat.le_of_mul_le_mul_right h2 hx


theorem averaging (n h : ℕ) (hn : h ≤ n) (R : Finset (Finset (Fin n) × (Fin n → Bool)))
    (hR : ∀ τ ∈ R, τ.1.card = h) :
    ∃ v : Fin n → Bool, R.card ≤ 2 ^ h * (R.filter (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card := by
  by_contra hcon
  have hlt : ∀ v : Fin n → Bool,
      2 ^ h * (R.filter (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card < R.card := by
    intro v
    by_contra hv
    exact hcon ⟨v, not_lt.mp hv⟩
  have hsum : ∑ v : Fin n → Bool, (R.filter (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card
      = R.card * 2 ^ (n - h) := by
    have e1 : ∀ v : Fin n → Bool, (R.filter (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card
        = ∑ τ ∈ R, (if ∀ j ∈ τ.1, v j = τ.2 j then 1 else 0) := fun v => Finset.card_filter _ _
    rw [Finset.sum_congr rfl (fun v _ => e1 v), Finset.sum_comm]
    have e2 : ∀ τ ∈ R, (∑ v : Fin n → Bool, (if ∀ j ∈ τ.1, v j = τ.2 j then 1 else 0)) = 2 ^ (n - h) := by
      intro τ hτ
      rw [← Finset.card_filter, card_agree, hR τ hτ]
    rw [Finset.sum_congr rfl e2, Finset.sum_const, smul_eq_mul]
  have hbig : ∑ v : Fin n → Bool, 2 ^ h * (R.filter (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card
      < ∑ _v : Fin n → Bool, R.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => hlt v)
  rw [← Finset.mul_sum, hsum, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hbig
  have hcardW : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hpow : 2 ^ h * 2 ^ (n - h) = 2 ^ n := by rw [← pow_add]; congr 1; omega
  rw [hcardW] at hbig
  have : 2 ^ h * (R.card * 2 ^ (n - h)) = 2 ^ n * R.card := by rw [← hpow]; ring
  omega

theorem greedy (n h : ℕ) (hn : h ≤ n) (Tg : Finset (Finset (Fin n) × (Fin n → Bool)))
    (hTg : ∀ τ ∈ Tg, τ.1.card = h) (N : ℕ) :
    ∃ pool : Finset (Fin n → Bool), pool.card ≤ N ∧
      (2 ^ h) ^ N * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card
        ≤ (2 ^ h - 1) ^ N * Tg.card := by
  induction N with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨pool, hcard, hbound⟩ := ih
    obtain ⟨v, hv⟩ := averaging n h hn (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j))
      (fun τ hτ => hTg τ (Finset.mem_filter.mp hτ).1)
    refine ⟨insert v pool, (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hcard), ?_⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j))
      (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)
    have hsub : (Tg.filter (fun τ => ∀ u ∈ insert v pool, ¬ ∀ j ∈ τ.1, u j = τ.2 j))
        ⊆ (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).filter
            (fun τ => ¬ ∀ j ∈ τ.1, v j = τ.2 j) := by
      intro τ hτ
      rw [Finset.mem_filter] at hτ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hτ.1, fun u hu => hτ.2 u (Finset.mem_insert_of_mem hu)⟩, ?_⟩
      exact hτ.2 v (Finset.mem_insert_self _ _)
    have hle := Finset.card_le_card hsub
    have hmul : (2 ^ h - 1) * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card
        = 2 ^ h * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card
          - (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card := by
      rw [Nat.sub_mul, one_mul]
    have hstep : 2 ^ h * (Tg.filter (fun τ => ∀ u ∈ insert v pool, ¬ ∀ j ∈ τ.1, u j = τ.2 j)).card
        ≤ (2 ^ h - 1) * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card := by
      have h1 := Nat.mul_le_mul_left (2 ^ h) hle
      have h2 : 2 ^ h * ((Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).filter
            (fun τ => ∀ j ∈ τ.1, v j = τ.2 j)).card
          + 2 ^ h * ((Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).filter
            (fun τ => ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card
          = 2 ^ h * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card := by
        rw [← Nat.mul_add, hsplit]
      omega
    calc (2 ^ h) ^ (N + 1) * (Tg.filter (fun τ => ∀ u ∈ insert v pool, ¬ ∀ j ∈ τ.1, u j = τ.2 j)).card
        = (2 ^ h) ^ N * (2 ^ h * (Tg.filter (fun τ => ∀ u ∈ insert v pool, ¬ ∀ j ∈ τ.1, u j = τ.2 j)).card) := by ring
      _ ≤ (2 ^ h) ^ N * ((2 ^ h - 1) * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card) :=
          Nat.mul_le_mul_left _ hstep
      _ = (2 ^ h - 1) * ((2 ^ h) ^ N * (Tg.filter (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card) := by ring
      _ ≤ (2 ^ h - 1) * ((2 ^ h - 1) ^ N * Tg.card) := Nat.mul_le_mul_left _ hbound
      _ = (2 ^ h - 1) ^ (N + 1) * Tg.card := by ring

theorem uncovered_large (n h : ℕ) (pool : Finset (Fin n → Bool)) (H : Finset (Fin n)) (hH : H.card = h)
    (w : Fin n → Bool) (hw : ∀ v ∈ pool, ¬ ∀ j ∈ H, v j = w j) :
    2 ^ (n - h) ≤ (((Finset.powersetCard h (Finset.univ : Finset (Fin n))) ×ˢ
        (Finset.univ : Finset (Fin n → Bool))).filter
        (fun τ => ∀ v ∈ pool, ¬ ∀ j ∈ τ.1, v j = τ.2 j)).card := by
  have hc := card_agree n H w
  rw [hH] at hc
  rw [← hc]
  refine Finset.card_le_card_of_injOn (fun w' => (H, w')) ?_ ?_
  · intro w' hw'
    have hag : ∀ j ∈ H, w' j = w j := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hH⟩, Finset.mem_univ _⟩, ?_⟩)
    intro v hv hcov
    exact hw v hv (fun j hj => (hcov j hj).trans (hag j hj))
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).2

theorem numeric (n h t : ℕ) (ht : t = 1 + h * (1 + Nat.clog 2 (n + 1))) :
    (2 ^ h - 1) ^ (2 ^ h * t) * (n.choose h * 2 ^ h) < (2 ^ h) ^ (2 ^ h * t) := by
  have hX : n.choose h * 2 ^ h < 2 ^ t := by
    have h1 : n.choose h ≤ n ^ h := Nat.choose_le_pow n h
    have h2 : n ≤ 2 ^ Nat.clog 2 (n + 1) :=
      (Nat.le_succ n).trans (Nat.le_pow_clog (by norm_num) (n + 1))
    have h3 : n ^ h ≤ (2 ^ Nat.clog 2 (n + 1)) ^ h := Nat.pow_le_pow_left h2 h
    have hpos : 0 < (2 ^ Nat.clog 2 (n + 1)) ^ h * 2 ^ h := by positivity
    calc n.choose h * 2 ^ h ≤ (2 ^ Nat.clog 2 (n + 1)) ^ h * 2 ^ h := Nat.mul_le_mul_right _ (h1.trans h3)
      _ < 2 * ((2 ^ Nat.clog 2 (n + 1)) ^ h * 2 ^ h) := by omega
      _ = 2 ^ t := by rw [ht]; ring
  have htpos : 0 < t := by omega
  obtain ⟨x, hx⟩ : ∃ x, 2 ^ h = x + 1 := ⟨2 ^ h - 1, by have : 0 < 2 ^ h := by positivity
                                                        omega⟩
  rw [hx] at hX ⊢
  rw [Nat.add_sub_cancel]
  have key : 2 ^ t * x ^ ((x + 1) * t) ≤ (x + 1) ^ ((x + 1) * t) := by
    have := Nat.pow_le_pow_left (two_pow_succ_le x) t
    rwa [mul_pow, ← pow_mul, ← pow_mul] at this
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · have hne : (0 + 1) * t ≠ 0 := by omega
    rw [zero_pow hne]
    simp
  · calc x ^ ((x + 1) * t) * (n.choose h * (x + 1)) < x ^ ((x + 1) * t) * 2 ^ t :=
          (Nat.mul_lt_mul_left (pow_pos hxpos _)).mpr hX
      _ = 2 ^ t * x ^ ((x + 1) * t) := mul_comm _ _
      _ ≤ (x + 1) ^ ((x + 1) * t) := key

theorem exists_pool (n h : ℕ) (hn : h ≤ n) :
    ∃ pool : Finset (Fin n → Bool), pool.card ≤ 2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1))) ∧
      ∀ (H : Finset (Fin n)), H.card ≤ h → ∀ w : Fin n → Bool, ∃ v ∈ pool, ∀ j ∈ H, v j = w j := by
  obtain ⟨pool, hcard, hbound⟩ := greedy n h hn
    ((Finset.powersetCard h (Finset.univ : Finset (Fin n))) ×ˢ (Finset.univ : Finset (Fin n → Bool)))
    (fun τ hτ => (Finset.mem_powersetCard.mp (Finset.mem_product.mp hτ).1).2)
    (2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1))))
  refine ⟨pool, hcard, ?_⟩
  intro H hH w
  obtain ⟨H', hHH', _, hH'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ H) hH
    (by simpa using hn)
  by_contra hcon
  have hunc : ∀ v ∈ pool, ¬ ∀ j ∈ H', v j = w j := by
    intro v hv hcov
    exact hcon ⟨v, hv, fun j hj => hcov j (hHH' hj)⟩
  have hlarge := uncovered_large n h pool H' hH' w hunc
  have hTg : (((Finset.powersetCard h (Finset.univ : Finset (Fin n))) ×ˢ
      (Finset.univ : Finset (Fin n → Bool)))).card = n.choose h * 2 ^ n := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    simp
  have hnum := numeric n h _ rfl
  have h1 := (Nat.mul_le_mul_left _ hlarge).trans hbound
  rw [hTg] at h1
  have hpow : 2 ^ n = 2 ^ h * 2 ^ (n - h) := by rw [← pow_add]; congr 1; omega
  have h2 : (2 ^ h) ^ (2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1)))) * 2 ^ (n - h)
      ≤ ((2 ^ h - 1) ^ (2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1)))) * (n.choose h * 2 ^ h)) * 2 ^ (n - h) := by
    calc _ ≤ _ := h1
      _ = _ := by rw [hpow]; ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
  exact absurd h3 (not_le.mpr hnum)

theorem pool_main (n h : ℕ) (hn : h ≤ n) :
    ∃ pool : Finset (Fin n → Bool),
      pool.card ≤ min (2 ^ n) (2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1)))) ∧
      ∀ (H : Finset (Fin n)), H.card ≤ h → ∀ w : Fin n → Bool, ∃ v ∈ pool, ∀ j ∈ H, v j = w j := by
  by_cases hbig : 2 ^ n ≤ 2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1)))
  · refine ⟨Finset.univ, ?_, fun H _ w => ⟨w, Finset.mem_univ _, fun j _ => rfl⟩⟩
    have hc : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
    rw [hc]
    exact le_min le_rfl hbig
  · obtain ⟨pool, hcard, hcov⟩ := exists_pool n h hn
    exact ⟨pool, le_min (hcard.trans (le_of_lt (not_le.mp hbig))) hcard, hcov⟩

theorem step_indep (n k : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ k) (r : (Fin n → Bool) → Bool)
    (hr : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → r x = r y) (z : Fin n → Bool) (hz : r z = false)
    (A : Finset (Fin n → Bool))
    (hA : ∀ w ∈ A, ∀ u : Fin n → Bool, (∀ j, j ∉ S → u j = w j) → u ∈ A) :
    (A.filter (fun w => r w = true)).card * 2 ^ k ≤ A.card * (2 ^ k - 1) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun w => r w = true)
  have himg : A.image (fun w : Fin n → Bool => fun j => if j ∈ S then z j else w j)
      ⊆ A.filter (fun w => ¬ r w = true) := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_filter.mpr ⟨hA w hw _ (fun j hj => by simp [hj]), ?_⟩
    have : r (fun j => if j ∈ S then z j else w j) = r z := hr _ _ (fun j hj => by simp [hj])
    rw [this, hz]
    simp
  have hfib : ∀ b ∈ A.image (fun w : Fin n → Bool => fun j => if j ∈ S then z j else w j),
      (A.filter (fun w : Fin n → Bool => (fun j => if j ∈ S then z j else w j) = b)).card ≤ 2 ^ S.card := by
    intro b _
    have hsub : (A.filter (fun w : Fin n → Bool => (fun j => if j ∈ S then z j else w j) = b))
        ⊆ Finset.univ.filter (fun w : Fin n → Bool => ∀ j ∈ Sᶜ, w j = b j) := by
      intro w hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩
      have hjS : j ∉ S := Finset.mem_compl.mp hj
      have := congrFun (Finset.mem_filter.mp hw).2 j
      simpa [hjS] using this
    have hcard := card_agree n Sᶜ b
    have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hexp : n - Sᶜ.card = S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    rw [hexp] at hcard
    exact (Finset.card_le_card hsub).trans (le_of_eq hcard)
  have h1 := Finset.card_le_mul_card_image A (2 ^ S.card) hfib
  have h2 := Nat.mul_le_mul_left (2 ^ S.card) (Finset.card_le_card himg)
  have h3 : 2 ^ S.card ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hS
  have h4 := Nat.mul_le_mul_right (A.filter (fun w => ¬ r w = true)).card h3
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by have : 0 < 2 ^ k := by positivity
                                                        omega⟩
  rw [hq] at h4 ⊢
  rw [Nat.add_sub_cancel, ← hsplit]
  have h5 : (A.filter (fun w => r w = true)).card ≤ q * (A.filter (fun w => ¬ r w = true)).card := by
    nlinarith [h1, h2, h4, hsplit]
  nlinarith [h5]

theorem packing_count (n k m : ℕ) (scope : Fin m → Finset (Fin n)) (row : Fin m → (Fin n → Bool) → Bool)
    (hsc : ∀ i, (scope i).card ≤ k)
    (hrow : ∀ i x y, (∀ j ∈ scope i, x j = y j) → row i x = row i y)
    (Q : Finset (Fin m)) (hdisj : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (scope i) (scope j))
    (hnf : ∀ i ∈ Q, ∃ z, row i z = false) :
    (Finset.univ.filter (fun w : Fin n → Bool => ∀ i ∈ Q, row i w = true)).card * (2 ^ k) ^ Q.card
      ≤ 2 ^ n * (2 ^ k - 1) ^ Q.card := by
  induction Q using Finset.induction_on with
  | empty => simp
  | insert i Q hi ih =>
    have ih' := ih (fun a ha b hb hab => hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
      (fun a ha => hnf a (Finset.mem_insert_of_mem ha))
    obtain ⟨z, hz⟩ := hnf i (Finset.mem_insert_self _ _)
    have heq : (Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ insert i Q, row i' w = true))
        = (Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true)).filter
            (fun w => row i w = true) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert]
      exact and_comm
    have hstep := step_indep n k (scope i) (hsc i) (row i) (hrow i) z hz
      (Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true))
      (by
        intro w hw u hu
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i' hi' => ?_⟩
        have hne : i ≠ i' := fun h => hi (h ▸ hi')
        have hd := hdisj i (Finset.mem_insert_self _ _) i' (Finset.mem_insert_of_mem hi') hne
        rw [hrow i' u w (fun j hj => hu j (fun hjs => (Finset.disjoint_left.mp hd) hjs hj))]
        exact (Finset.mem_filter.mp hw).2 i' hi')
    rw [heq, Finset.card_insert_of_notMem hi]
    calc ((Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true)).filter
            (fun w => row i w = true)).card * (2 ^ k) ^ (Q.card + 1)
        = (((Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true)).filter
            (fun w => row i w = true)).card * 2 ^ k) * (2 ^ k) ^ Q.card := by ring
      _ ≤ ((Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true)).card * (2 ^ k - 1))
            * (2 ^ k) ^ Q.card := Nat.mul_le_mul_right _ hstep
      _ = ((Finset.univ.filter (fun w : Fin n → Bool => ∀ i' ∈ Q, row i' w = true)).card * (2 ^ k) ^ Q.card)
            * (2 ^ k - 1) := by ring
      _ ≤ (2 ^ n * (2 ^ k - 1) ^ Q.card) * (2 ^ k - 1) := Nat.mul_le_mul_right _ ih'
      _ = 2 ^ n * (2 ^ k - 1) ^ (Q.card + 1) := by ring

theorem exp_bound (x a t : ℕ) (hx : 0 < x) (h : (x + 1) ^ t ≤ 2 ^ a * x ^ t) : t ≤ a * x := by
  by_contra hcon
  obtain ⟨s, hs⟩ : ∃ s, t = a * x + (s + 1) := ⟨t - a * x - 1, by omega⟩
  subst hs
  have h1 : (2 * x ^ x) ^ a ≤ ((x + 1) ^ x) ^ a := Nat.pow_le_pow_left (two_pow_le x hx) a
  have h2 : x ^ (s + 1) < (x + 1) ^ (s + 1) :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self x) (Nat.succ_ne_zero s)
  have h3 : 2 ^ a * x ^ (a * x + (s + 1)) < (x + 1) ^ (a * x + (s + 1)) := by
    calc 2 ^ a * x ^ (a * x + (s + 1)) = (2 * x ^ x) ^ a * x ^ (s + 1) := by ring
      _ ≤ ((x + 1) ^ x) ^ a * x ^ (s + 1) := Nat.mul_le_mul_right _ h1
      _ < ((x + 1) ^ x) ^ a * (x + 1) ^ (s + 1) := (Nat.mul_lt_mul_left (by positivity)).mpr h2
      _ = (x + 1) ^ (a * x + (s + 1)) := by ring
  exact absurd h (not_le.mpr h3)

theorem packing_le (n k a m : ℕ) (hk : 0 < k) (scope : Fin m → Finset (Fin n))
    (row : Fin m → (Fin n → Bool) → Bool)
    (hsc : ∀ i, (scope i).card ≤ k)
    (hrow : ∀ i x y, (∀ j ∈ scope i, x j = y j) → row i x = row i y)
    (Q : Finset (Fin m)) (hdisj : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (scope i) (scope j))
    (hnf : ∀ i ∈ Q, ∃ z, row i z = false)
    (G : Finset (Fin n → Bool)) (hG : ∀ w ∈ G, ∀ i, row i w = true)
    (hdens : 2 ^ n ≤ 2 ^ a * G.card) :
    Q.card ≤ a * (2 ^ k - 1) := by
  have hcount := packing_count n k m scope row hsc hrow Q hdisj hnf
  have hsub : G ⊆ Finset.univ.filter (fun w : Fin n → Bool => ∀ i ∈ Q, row i w = true) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i _ => hG w hw i⟩
  have hGc := Finset.card_le_card hsub
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨x, hx⟩ : ∃ x, 2 ^ k = x + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hx] at hcount ⊢
  rw [Nat.add_sub_cancel] at hcount ⊢
  have hxpos : 0 < x := by omega
  apply exp_bound x a Q.card hxpos
  have h1 : 2 ^ n * (x + 1) ^ Q.card ≤ 2 ^ n * (2 ^ a * x ^ Q.card) := by
    calc 2 ^ n * (x + 1) ^ Q.card ≤ (2 ^ a * G.card) * (x + 1) ^ Q.card := Nat.mul_le_mul_right _ hdens
      _ ≤ (2 ^ a * (Finset.univ.filter (fun w : Fin n → Bool => ∀ i ∈ Q, row i w = true)).card)
            * (x + 1) ^ Q.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hGc)
      _ = 2 ^ a * ((Finset.univ.filter (fun w : Fin n → Bool => ∀ i ∈ Q, row i w = true)).card
            * (x + 1) ^ Q.card) := by ring
      _ ≤ 2 ^ a * (2 ^ n * x ^ Q.card) := Nat.mul_le_mul_left _ hcount
      _ = 2 ^ n * (2 ^ a * x ^ Q.card) := by ring
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

theorem exists_max_packing (n m : ℕ) (scope : Fin m → Finset (Fin n)) (NF : Finset (Fin m)) :
    ∃ Q : Finset (Fin m), Q ⊆ NF ∧ (∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (scope i) (scope j)) ∧
      ∀ i ∈ NF, i ∉ Q → ∃ j ∈ Q, ¬ Disjoint (scope i) (scope j) := by
  classical
  obtain ⟨Q, hQ, hmax⟩ := Finset.exists_max_image
    (NF.powerset.filter (fun Q => ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (scope i) (scope j)))
    Finset.card ⟨∅, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hQ
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  intro i hi hiQ
  by_contra hcon
  have hall : ∀ j ∈ Q, Disjoint (scope i) (scope j) := by
    intro j hj
    by_contra hd
    exact hcon ⟨j, hj, hd⟩
  have hins : insert i Q ∈ NF.powerset.filter
      (fun Q => ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (scope i) (scope j)) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hi hQ.1, ?_⟩
    intro b hb c hc hbc
    rw [Finset.mem_insert] at hb hc
    rcases hb with rfl | hb <;> rcases hc with rfl | hc
    · exact absurd rfl hbc
    · exact hall c hc
    · exact (hall b hb).symm
    · exact hQ.2 b hb c hc hbc
  have hle := hmax _ hins
  rw [Finset.card_insert_of_notMem hiQ] at hle
  omega

theorem active_le (n k d m : ℕ) (scope : Fin m → Finset (Fin n)) (hsc : ∀ i, (scope i).card ≤ k)
    (hocc : ∀ bit : Fin n, (Finset.univ.filter (fun i => bit ∈ scope i)).card ≤ d)
    (NF Q : Finset (Fin m))
    (hmax : ∀ i ∈ NF, i ∉ Q → ∃ j ∈ Q, ¬ Disjoint (scope i) (scope j)) :
    (NF.biUnion scope).card ≤ k * Q.card * (1 + (d - 1) * (k - 1)) := by
  have hU : (Q.biUnion scope).card ≤ Q.card * k := Finset.card_biUnion_le_card_mul Q scope k (fun i _ => hsc i)
  have hmeet : ∀ i ∈ NF \ Q, ∃ b, b ∈ scope i ∧ b ∈ Q.biUnion scope := by
    intro i hi
    obtain ⟨hiNF, hiQ⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨j, hj, hnd⟩ := hmax i hiNF hiQ
    obtain ⟨b, hb1, hb2⟩ := Finset.not_disjoint_iff.mp hnd
    exact ⟨b, hb1, Finset.mem_biUnion.mpr ⟨j, hj, hb2⟩⟩
  have hsub : NF.biUnion scope ⊆ Q.biUnion scope ∪ (NF \ Q).biUnion (fun i => scope i \ Q.biUnion scope) := by
    intro b hb
    obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
    by_cases hbU : b ∈ Q.biUnion scope
    · exact Finset.mem_union_left _ hbU
    · have hiQ : i ∉ Q := fun h => hbU (Finset.mem_biUnion.mpr ⟨i, h, hbi⟩)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiQ⟩, Finset.mem_sdiff.mpr ⟨hbi, hbU⟩⟩)
  have hnew : ∀ i ∈ NF \ Q, (scope i \ Q.biUnion scope).card ≤ k - 1 := by
    intro i hi
    obtain ⟨b, hb1, hb2⟩ := hmeet i hi
    have hs : scope i \ Q.biUnion scope ⊆ (scope i).erase b := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_sdiff.mp hc
      exact Finset.mem_erase.mpr ⟨fun h => hc2 (h ▸ hb2), hc1⟩
    have := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hb1] at this
    have := hsc i
    omega
  have hR : (NF \ Q).card ≤ (Q.biUnion scope).card * (d - 1) := by
    have hsubR : NF \ Q ⊆ (Q.biUnion scope).biUnion
        (fun b => (Finset.univ.filter (fun i => b ∈ scope i)).filter (fun i => i ∉ Q)) := by
      intro i hi
      obtain ⟨b, hb1, hb2⟩ := hmeet i hi
      exact Finset.mem_biUnion.mpr ⟨b, hb2, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb1⟩, (Finset.mem_sdiff.mp hi).2⟩⟩
    refine (Finset.card_le_card hsubR).trans (Finset.card_biUnion_le_card_mul _ _ _ ?_)
    intro b hb
    obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
    have hs : (Finset.univ.filter (fun i => b ∈ scope i)).filter (fun i => i ∉ Q)
        ⊆ (Finset.univ.filter (fun i => b ∈ scope i)).erase j := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_erase.mpr ⟨fun h => hc2 (h ▸ hj), hc1⟩
    have := Finset.card_le_card hs
    have hjm : j ∈ Finset.univ.filter (fun i => b ∈ scope i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbj⟩
    rw [Finset.card_erase_of_mem hjm] at this
    have := hocc b
    omega
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_biUnion_le_card_mul (NF \ Q) (fun i => scope i \ Q.biUnion scope) (k - 1) hnew
  have h3 : (NF \ Q).card * (k - 1) ≤ (Q.biUnion scope).card * (d - 1) * (k - 1) :=
    Nat.mul_le_mul_right _ hR
  calc (NF.biUnion scope).card
      ≤ (Q.biUnion scope).card + (Q.biUnion scope).card * (d - 1) * (k - 1) := by omega
    _ = (Q.biUnion scope).card * (1 + (d - 1) * (k - 1)) := by ring
    _ ≤ (Q.card * k) * (1 + (d - 1) * (k - 1)) := Nat.mul_le_mul_right _ hU
    _ = k * Q.card * (1 + (d - 1) * (k - 1)) := by ring

theorem recover (n k d a m : ℕ) (hk : 0 < k) (scope : Fin m → Finset (Fin n))
    (row : Fin m → (Fin n → Bool) → Bool)
    (hsc : ∀ i, (scope i).card ≤ k)
    (hocc : ∀ bit : Fin n, (Finset.univ.filter (fun i => bit ∈ scope i)).card ≤ d)
    (hrow : ∀ i x y, (∀ j ∈ scope i, x j = y j) → row i x = row i y)
    (G : Finset (Fin n → Bool)) (hG : ∀ w ∈ G, ∀ i, row i w = true)
    (hdens : 2 ^ n ≤ 2 ^ a * G.card)
    (x : Fin n → Bool) (hx : ∀ i, row i x = true) (T : Finset (Fin n)) (hT : T.card ≤ k) :
    ∃ H : Finset (Fin n), H.card ≤ k + k * (a * (2 ^ k - 1)) * (1 + (d - 1) * (k - 1)) ∧ T ⊆ H ∧
      ∀ v : Fin n → Bool, (∀ j ∈ H, v j = x j) → ∀ i, row i v = true := by
  obtain ⟨NF, hNF⟩ : ∃ NF : Finset (Fin m), ∀ i, i ∈ NF ↔ ∃ z, row i z = false :=
    ⟨Finset.univ.filter (fun i => ∃ z, row i z = false), fun i => by simp⟩
  obtain ⟨Q, hQ, hdisj, hmax⟩ := exists_max_packing n m scope NF
  have hQp : Q.card ≤ a * (2 ^ k - 1) := packing_le n k a m hk scope row hsc hrow Q hdisj
    (fun i hi => (hNF i).mp (hQ hi)) G hG hdens
  have hact := active_le n k d m scope hsc hocc NF Q hmax
  refine ⟨NF.biUnion scope ∪ T, ?_, Finset.subset_union_right, ?_⟩
  · have h1 := Finset.card_union_le (NF.biUnion scope) T
    have h2 : k * Q.card * (1 + (d - 1) * (k - 1)) ≤ k * (a * (2 ^ k - 1)) * (1 + (d - 1) * (k - 1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQp)
    omega
  · intro v hv i
    by_cases hi : ∃ z, row i z = false
    · have hiNF : i ∈ NF := (hNF i).mpr hi
      rw [hrow i v x (fun j hj => hv j (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hiNF, hj⟩)))]
      exact hx i
    · by_contra hne
      exact hi ⟨v, by simpa using hne⟩

end PEqualNP.Outside.L_lib_413_aux

theorem PEqualNP.Outside.L_lib_413 : (∀ (n k d a : ℕ), 0 < k → k ≤ n →
  let W := Fin n → Bool
  let agrees := fun (S : Finset (Fin n)) (u v : W) => ∀ j ∈ S, u j = v j
  let p := a * (2 ^ k - 1)
  let h := min n (k + k * p * (1 + (d - 1) * (k - 1)))
  ∃ pool : Finset W,
    pool.card ≤ min (2 ^ n) (2 ^ h * (1 + h * (1 + Nat.clog 2 (n + 1)))) ∧
    ∀ (m : ℕ) (scope : Fin m → Finset (Fin n)) (row : Fin m → W → Bool),
      (∀ i, (scope i).card ≤ k) →
      (∀ bit : Fin n, (Finset.univ.filter (fun i => bit ∈ scope i)).card ≤ d) →
      (∀ i x y, agrees (scope i) x y → row i x = row i y) →
      let good := fun z : W => ∀ i, row i z = true
      let learned := fun w : W => ∀ T : Finset (Fin n), T.card ≤ k →
        ∃ v ∈ pool, good v ∧ agrees T v w
      (∀ x, learned x → good x) ∧
      (2 ^ n ≤ 2 ^ a * (Finset.univ.filter good).card → ∀ x, good x → learned x)) := by
  intro n k d a hk hkn
  dsimp only
  obtain ⟨pool, hcard, huniv⟩ := PEqualNP.Outside.L_lib_413_aux.pool_main n
    (min n (k + k * (a * (2 ^ k - 1)) * (1 + (d - 1) * (k - 1)))) (min_le_left _ _)
  refine ⟨pool, hcard, ?_⟩
  intro m scope row hsc hocc hrow
  refine ⟨?_, ?_⟩
  · intro x hx i
    obtain ⟨v, _, hgood, hag⟩ := hx (scope i) (hsc i)
    rw [hrow i x v (fun j hj => (hag j hj).symm)]
    exact hgood i
  · intro hdens x hx T hT
    have key := fun hG => PEqualNP.Outside.L_lib_413_aux.recover n k d a m hk scope row hsc hocc hrow
      _ hG hdens x hx T hT
    obtain ⟨H, hH, hTH, hgood⟩ := key (fun w hw i => (Finset.mem_filter.mp hw).2 i)
    have hHn : H.card ≤ n := by
      have := Finset.card_le_univ H
      simpa using this
    obtain ⟨v, hv, hag⟩ := huniv H (le_min hHn hH) x
    exact ⟨v, hv, hgood v hag, fun j hj => hag j (hTH hj)⟩
