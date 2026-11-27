import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_530

theorem kraftFwd (m : ℕ) (c : Fin m → List Bool)
    (hc : ∀ i j, (∃ tail : List Bool, c j = c i ++ tail) → i = j) :
    (∑ i, (1 / (2:ℝ)) ^ (c i).length) ≤ 1 := by
  have hinj : Function.Injective c :=
    fun i j h => hc i j ⟨[], by rw [List.append_nil]; exact h.symm⟩
  have hpf : InformationTheory.IsPrefixFree
      ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) := by
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    obtain ⟨t, ht⟩ := hxy
    rw [hc i j ⟨t, ht.symm⟩]
  have h := hpf.finsetSum_one_div_card_pow_length_le_one
  rw [Finset.sum_image (fun x _ y _ h => hinj h)] at h
  simpa using h

theorem card_bad (n : ℕ) (u : List Bool) (hk : u.length ≤ n) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => u <+: List.ofFn w)).card ≤
      2 ^ (n - u.length) := by
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin n → Bool)).filter (fun w => u <+: List.ofFn w))
    (t := (Finset.univ : Finset (Fin (n - u.length) → Bool)))
    (fun w => fun t : Fin (n - u.length) =>
      w ⟨u.length + t.val, by have h0 := t.isLt; omega⟩)
    (fun _ _ => Finset.mem_univ _)
    (by
      intro w hw w' hw' heq
      have hp : u <+: List.ofFn w := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
      have hp' : u <+: List.ofFn w' := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
      funext s
      by_cases hs : s.val < u.length
      · have e1 := hp.getElem hs
        have e2 := hp'.getElem hs
        simp only [List.getElem_ofFn, Fin.eta] at e1 e2
        exact e1.symm.trans e2
      · have h6 := congrFun heq ⟨s.val - u.length, by have h0 := s.isLt; omega⟩
        have e3 : u.length + (s.val - u.length) = s.val := by omega
        simp only [e3, Fin.eta] at h6
        exact h6)
  simpa using h

theorem exists_word (m : ℕ) (s : Finset (Fin m)) (c : Fin m → List Bool) (n : ℕ)
    (hlen : ∀ j ∈ s, (c j).length ≤ n)
    (hk : (∑ j ∈ s, (1 / (2:ℝ)) ^ (c j).length) + (1 / (2:ℝ)) ^ n ≤ 1) :
    ∃ w : Fin n → Bool, ∀ j ∈ s, ¬ c j <+: List.ofFn w := by
  by_contra hcon
  have hcon' : ∀ w : Fin n → Bool, ∃ j ∈ s, c j <+: List.ofFn w := by
    intro w
    by_contra h
    exact hcon ⟨w, fun j hj hp => h ⟨j, hj, hp⟩⟩
  have hsub : (Finset.univ : Finset (Fin n → Bool)) ⊆
      s.biUnion (fun j => (Finset.univ : Finset (Fin n → Bool)).filter
        (fun w => c j <+: List.ofFn w)) := by
    intro w _
    obtain ⟨j, hj, hp⟩ := hcon' w
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := s)
    (t := fun j => (Finset.univ : Finset (Fin n → Bool)).filter (fun w => c j <+: List.ofFn w))
  have h3 : (∑ j ∈ s, ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun w => c j <+: List.ofFn w)).card) ≤ ∑ j ∈ s, 2 ^ (n - (c j).length) :=
    Finset.sum_le_sum (fun j hj => card_bad n (c j) (hlen j hj))
  have h4 : (2:ℕ) ^ n ≤ ∑ j ∈ s, 2 ^ (n - (c j).length) := by
    have h0 : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
    rw [← h0]; exact h1.trans (h2.trans h3)
  have h5 : ((∑ j ∈ s, 2 ^ (n - (c j).length) : ℕ) : ℝ) =
      (2:ℝ)^n * ∑ j ∈ s, (1 / (2:ℝ)) ^ (c j).length := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hle := hlen j hj
    push_cast
    rw [one_div, inv_pow, ← div_eq_mul_inv, eq_div_iff (by positivity), ← pow_add,
      Nat.sub_add_cancel hle]
  have h6 : (((2:ℕ)^n : ℕ) : ℝ) ≤ ((∑ j ∈ s, 2 ^ (n - (c j).length) : ℕ) : ℝ) := by
    exact_mod_cast h4
  rw [h5] at h6
  have h7 : (2:ℝ)^n * (1 / (2:ℝ)) ^ n = 1 := by rw [← mul_pow]; norm_num
  have h8 : (0:ℝ) < 2^n := by positivity
  have h9 := mul_le_mul_of_nonneg_left hk h8.le
  rw [mul_add, h7, mul_one] at h9
  push_cast at h6
  linarith

theorem kraftConv (m : ℕ) (l : Fin m → ℕ) (I : Finset (Fin m)) :
    (∑ i ∈ I, (1 / (2:ℝ)) ^ (l i)) ≤ 1 →
    ∃ c : Fin m → List Bool, (∀ i ∈ I, (c i).length = l i) ∧
      ∀ i ∈ I, ∀ j ∈ I, c i <+: c j → i = j := by
  induction I using Finset.induction_on_max_value l with
  | empty => intro _; exact ⟨fun _ => [], by simp, by simp⟩
  | insert a s ha hmax ih =>
    intro hsum
    rw [Finset.sum_insert ha] at hsum
    have hnn : 0 ≤ (1 / (2:ℝ)) ^ (l a) := by positivity
    obtain ⟨c, hlen, hpf⟩ := ih (by linarith)
    obtain ⟨w, hw⟩ := exists_word m s c (l a)
      (fun j hj => by rw [hlen j hj]; exact hmax j hj) (by
        have h0 : (∑ j ∈ s, (1 / (2:ℝ)) ^ (c j).length) = ∑ j ∈ s, (1 / (2:ℝ)) ^ (l j) :=
          Finset.sum_congr rfl (fun j hj => by rw [hlen j hj])
        rw [h0]; linarith)
    refine ⟨Function.update c a (List.ofFn w), ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with hia | hi'
      · rw [hia, Function.update_self, List.length_ofFn]
      · have hia : i ≠ a := fun h => ha (h ▸ hi')
        rw [Function.update_of_ne hia]; exact hlen i hi'
    · intro i hi j hj hp
      rcases Finset.mem_insert.mp hi with hia | hi' <;>
        rcases Finset.mem_insert.mp hj with hja | hj'
      · rw [hia, hja]
      · exfalso
        have hja : j ≠ a := fun h => ha (h ▸ hj')
        rw [hia, Function.update_self, Function.update_of_ne hja] at hp
        have hle : (c j).length ≤ (List.ofFn w).length := by
          rw [List.length_ofFn, hlen j hj']; exact hmax j hj'
        have heq := hp.eq_of_length_le hle
        exact hw j hj' ⟨[], by rw [List.append_nil, heq]⟩
      · exfalso
        have hia : i ≠ a := fun h => ha (h ▸ hi')
        rw [hja, Function.update_self, Function.update_of_ne hia] at hp
        exact hw i hi' hp
      · have hia : i ≠ a := fun h => ha (h ▸ hi')
        have hja : j ≠ a := fun h => ha (h ▸ hj')
        rw [Function.update_of_ne hia, Function.update_of_ne hja] at hp
        exact hpf i hi' j hj' hp

theorem main (m h : ℕ) (p : Fin h → Fin m → ℝ) (e : Fin m → ℝ) (hm : 0 < m) (_hh : 0 < h)
    (hp : ∀ j i, 0 < p j i) (_hsum : ∀ j, (∑ i, p j i) = 1)
    (he : ∀ i, (∀ j, p j i ≤ e i) ∧ ∃ j, p j i = e i) :
    (∀ i j, p j i ≤ (∑ i, e i)*(e i/(∑ i, e i))) ∧ (∑ i, e i/(∑ i, e i)) = 1 ∧
    (∀ q : Fin m → ℝ, (∀ i, 0 < q i) → (∑ i, q i) = 1 → ∃ i j, (∑ i, e i)*q i ≤ p j i) ∧
    (∀ c : Fin m → List Bool, (∀ i j, (∃ tail : List Bool, c j = c i ++ tail) → i = j) →
      ∃ i j, (∑ i, e i) ≤ p j i * (2:ℝ)^(c i).length) ∧
    ∃ c : Fin m → List Bool, (∀ i j, (∃ tail : List Bool, c j = c i ++ tail) → i = j) ∧
      ∀ i j, p j i * (2:ℝ)^(c i).length < 2*(∑ i, e i) := by
  have hepos : ∀ i, 0 < e i := fun i => by
    obtain ⟨j, hj⟩ := (he i).2
    rw [← hj]; exact hp j i
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hZ : 0 < ∑ i, e i := Finset.sum_pos (fun i _ => hepos i) hne
  have hZe : ∀ i, e i ≤ ∑ k, e k := fun i =>
    Finset.single_le_sum (fun k _ => (hepos k).le) (Finset.mem_univ i)
  generalize hZdef : (∑ i, e i) = Z at hZ hZe ⊢
  have key : ∀ q : Fin m → ℝ, (∑ i, q i) ≤ 1 → ∃ i, Z * q i ≤ e i := by
    intro q hq
    by_contra hcon
    have hlt : ∀ i ∈ (Finset.univ : Finset (Fin m)), e i < Z * q i := fun i _ => by
      by_contra h0; exact hcon ⟨i, not_lt.mp h0⟩
    have h1 := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [← Finset.mul_sum, hZdef] at h1
    nlinarith [mul_le_mul_of_nonneg_left hq hZ.le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [mul_div_cancel₀ _ hZ.ne']
    exact (he i).1 j
  · rw [← Finset.sum_div, hZdef, div_self hZ.ne']
  · intro q _ hq
    obtain ⟨i, hi⟩ := key q hq.le
    obtain ⟨j, hj⟩ := (he i).2
    exact ⟨i, j, by rw [hj]; exact hi⟩
  · intro c hc
    have hk := kraftFwd m c hc
    obtain ⟨i, hi⟩ := key (fun i => (1 / (2:ℝ)) ^ (c i).length) hk
    obtain ⟨j, hj⟩ := (he i).2
    refine ⟨i, j, ?_⟩
    rw [hj]
    have h2 : (0:ℝ) < 2 ^ (c i).length := by positivity
    have h3 : (1 / (2:ℝ)) ^ (c i).length * 2 ^ (c i).length = 1 := by
      rw [← mul_pow]; norm_num
    have h4 := mul_le_mul_of_nonneg_right hi h2.le
    rw [mul_assoc, h3, mul_one] at h4
    exact h4
  · have hl : ∀ i, ∃ n : ℕ, Z / e i ≤ (2:ℝ) ^ n ∧ (2:ℝ) ^ n < 2 * (Z / e i) := by
      intro i
      classical
      have hex : ∃ n : ℕ, Z / e i ≤ (2:ℝ) ^ n := by
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Z / e i) (by norm_num : (1:ℝ) < 2)
        exact ⟨n, hn.le⟩
      have h1Z : 1 ≤ Z / e i := by
        rw [le_div_iff₀ (hepos i), one_mul]; exact hZe i
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]; linarith
      · have h1 := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
        have h2 : (2:ℝ) ^ (Nat.find hex) = 2 * 2 ^ (Nat.find hex - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hpos]
        rw [h2]; linarith [not_le.mp h1]
    choose l hl1 hl2 using hl
    have hkraft : (∑ i ∈ (Finset.univ : Finset (Fin m)), (1 / (2:ℝ)) ^ (l i)) ≤ 1 := by
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)), (1 / (2:ℝ)) ^ (l i) ≤ e i / Z := by
        intro i _
        have h1 := hl1 i
        rw [div_le_iff₀ (hepos i)] at h1
        rw [one_div, inv_pow, ← one_div, div_le_div_iff₀ (by positivity) hZ]
        linarith
      calc (∑ i ∈ (Finset.univ : Finset (Fin m)), (1 / (2:ℝ)) ^ (l i))
          ≤ ∑ i, e i / Z := Finset.sum_le_sum hterm
        _ = 1 := by rw [← Finset.sum_div, hZdef, div_self hZ.ne']
    obtain ⟨c, hlen, hpf⟩ := kraftConv m l Finset.univ hkraft
    refine ⟨c, ?_, ?_⟩
    · intro i j ⟨t, ht⟩
      exact hpf i (Finset.mem_univ _) j (Finset.mem_univ _) ⟨t, ht.symm⟩
    · intro i j
      rw [hlen i (Finset.mem_univ _)]
      have h1 := hl2 i
      have h2 := (he i).1 j
      have h3 : e i * (2 * (Z / e i)) = 2 * Z := by
        have h0 := (hepos i).ne'
        field_simp
      calc p j i * 2 ^ (l i) ≤ e i * 2 ^ (l i) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ < e i * (2 * (Z / e i)) := mul_lt_mul_of_pos_left h1 (hepos i)
        _ = 2 * Z := h3

end PEqualNP.Outside.L_lib_530

theorem PEqualNP.Outside.L_lib_530 : ∀ (m h : ℕ) (p : Fin h → Fin m → ℝ) (e : Fin m → ℝ), 0 < m → 0 < h →
  (∀ j i, 0 < p j i) → (∀ j, (∑ i, p j i) = 1) →
  (∀ i, (∀ j, p j i ≤ e i) ∧ ∃ j, p j i = e i) →
  let prefixCode := fun (code : Fin m → List Bool) =>
    ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
  let Z := ∑ i, e i
  (∀ i j, p j i ≤ Z*(e i/Z)) ∧ (∑ i, e i/Z) = 1 ∧
  (∀ q : Fin m → ℝ, (∀ i, 0 < q i) → (∑ i, q i) = 1 →
    ∃ i j, Z*q i ≤ p j i) ∧
  (∀ c, prefixCode c → ∃ i j, Z ≤ p j i * (2:ℝ)^(c i).length) ∧
  ∃ c, prefixCode c ∧ ∀ i j, p j i * (2:ℝ)^(c i).length < 2*Z := by
  intro m h p e hm hh hp hsum he
  exact PEqualNP.Outside.L_lib_530.main m h p e hm hh hp hsum he
