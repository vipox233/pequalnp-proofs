import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48148_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

private lemma nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

private lemma sum_choose_mul_two_pow (s : ℕ) :
    ∑ i ∈ Finset.range (s + 1), Nat.choose s i * 2 ^ (s - i) = 3 ^ s := by
  have h := add_pow (1 : ℕ) 2 s
  simpa [Nat.add_comm, Nat.mul_comm] using h.symm

private lemma arith_bound (n e s : ℕ) (h : 3 * (2 * n + e + 1) ≤ s) :
    n * 2 ^ n * (∑ i ∈ Finset.range e, Nat.choose s i) < 2 ^ s := by
  have hes : e ≤ s := by omega
  have h1 : 2 ^ s * (∑ i ∈ Finset.range e, Nat.choose s i) ≤ 2 ^ e * 3 ^ s := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range e, 2 ^ s * Nat.choose s i
        ≤ ∑ i ∈ Finset.range e, 2 ^ e * (Nat.choose s i * 2 ^ (s - i)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          have hpow : 2 ^ s ≤ 2 ^ e * 2 ^ (s - i) := by
            rw [← pow_add]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          calc 2 ^ s * Nat.choose s i
              ≤ (2 ^ e * 2 ^ (s - i)) * Nat.choose s i := Nat.mul_le_mul_right _ hpow
            _ = 2 ^ e * (Nat.choose s i * 2 ^ (s - i)) := by ring
      _ = 2 ^ e * ∑ i ∈ Finset.range e, Nat.choose s i * 2 ^ (s - i) := by rw [Finset.mul_sum]
      _ ≤ 2 ^ e * ∑ i ∈ Finset.range (s + 1), Nat.choose s i * 2 ^ (s - i) := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      _ = 2 ^ e * 3 ^ s := by rw [sum_choose_mul_two_pow]
  have h2 : n * 2 ^ n * 2 ^ e < 2 ^ (2 * n + e + 1) := by
    have hn : n < 2 ^ n := nat_lt_two_pow n
    have hmul : n * 2 ^ n * 2 ^ e < 2 ^ n * 2 ^ n * 2 ^ e := by
      apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
      exact Nat.mul_lt_mul_of_pos_right hn (by positivity)
    have hpow : 2 ^ n * 2 ^ n * 2 ^ e ≤ 2 ^ (2 * n + e + 1) := by
      rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k := 2 * n + e + 1 with hk_def
  have hkpos : 0 < k := by omega
  have h3 : 2 ^ k * 3 ^ s < 4 ^ s := by
    have hstep1 : 2 ^ k * 3 ^ (3 * k) < 4 ^ (3 * k) := by
      have ha : 2 ^ k * 3 ^ (3 * k) = 54 ^ k := by
        rw [pow_mul, ← mul_pow]; norm_num
      have hb : 4 ^ (3 * k) = 64 ^ k := by
        rw [pow_mul]; norm_num
      rw [ha, hb]
      exact Nat.pow_lt_pow_left (by norm_num) (by omega)
    have hstep2 : 3 ^ (s - 3 * k) ≤ 4 ^ (s - 3 * k) :=
      Nat.pow_le_pow_left (by norm_num) _
    have hs1 : 3 ^ s = 3 ^ (3 * k) * 3 ^ (s - 3 * k) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    have hs2 : 4 ^ s = 4 ^ (3 * k) * 4 ^ (s - 3 * k) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    rw [hs1, hs2, ← mul_assoc]
    exact Nat.mul_lt_mul_of_lt_of_le hstep1 hstep2 (by positivity)
  have h4 : (n * 2 ^ n * (∑ i ∈ Finset.range e, Nat.choose s i)) * 2 ^ s < 2 ^ s * 2 ^ s := by
    calc (n * 2 ^ n * (∑ i ∈ Finset.range e, Nat.choose s i)) * 2 ^ s
        = n * 2 ^ n * (2 ^ s * (∑ i ∈ Finset.range e, Nat.choose s i)) := by ring
      _ ≤ n * 2 ^ n * (2 ^ e * 3 ^ s) := Nat.mul_le_mul_left _ h1
      _ = (n * 2 ^ n * 2 ^ e) * 3 ^ s := by ring
      _ ≤ 2 ^ k * 3 ^ s := Nat.mul_le_mul_right _ (le_of_lt h2)
      _ < 4 ^ s := h3
      _ = 2 ^ s * 2 ^ s := by rw [← mul_pow]; norm_num
  exact Nat.lt_of_mul_lt_mul_right h4

private def Causal {r : ℕ} (P : (Fin r → Bool) → Fin r → Bool) : Prop :=
  ∀ c₁ c₂ a, (∀ b < a, c₁ b = c₂ b) → P c₁ a = P c₂ a

private lemma causal_tail {r : ℕ} {P : (Fin (r + 1) → Bool) → Fin (r + 1) → Bool}
    (hP : Causal P) (v : Bool) :
    Causal (fun (c' : Fin r → Bool) (i : Fin r) => P (Fin.cons v c') i.succ) := by
  intro c₁ c₂ a h
  apply hP
  intro b hb
  cases b using Fin.cases with
  | zero => simp [Fin.cons]
  | succ b' =>
    simp only [Fin.cons_succ]
    exact h b' (Fin.succ_lt_succ_iff.mp hb)

private def PrefixFew :
    ∀ {r : ℕ}, ℕ → ℕ → Bool → ((Fin r → Bool) → Fin r → Bool) → (Fin r → Bool) → Prop
  | 0, s, e, _, _, _ => s = 0 ∧ 0 < e
  | _ + 1, s, e, target, P, c =>
    if P c 0 = true then
      match s with
      | 0 => 0 < e
      | s' + 1 =>
        if c 0 = target then
          0 < e ∧ PrefixFew s' (e - 1) target (fun c' i => P (Fin.cons (c 0) c') i.succ) (fun i => c i.succ)
        else
          PrefixFew s' e target (fun c' i => P (Fin.cons (c 0) c') i.succ) (fun i => c i.succ)
    else
      PrefixFew s e target (fun c' i => P (Fin.cons (c 0) c') i.succ) (fun i => c i.succ)

private lemma prefixFew_zero_false :
    ∀ {r : ℕ} (s : ℕ) (target : Bool) (P : (Fin r → Bool) → Fin r → Bool) (c : Fin r → Bool),
      ¬ PrefixFew s 0 target P c := by
  intro r
  induction r with
  | zero => intro s target P c; simp [PrefixFew]
  | succ r ih =>
    intro s target P c h
    unfold PrefixFew at h
    by_cases h1 : P c 0 = true
    · rw [if_pos h1] at h
      cases s with
      | zero => simp at h
      | succ s' =>
        dsimp only at h
        by_cases h2 : c 0 = target
        · rw [if_pos h2] at h; omega
        · rw [if_neg h2] at h; exact ih s' target _ _ h
    · rw [if_neg h1] at h
      exact ih s target _ _ h

private lemma sum_choose_pascal (s' e' : ℕ) :
    (∑ i ∈ Finset.range e', Nat.choose s' i) + (∑ i ∈ Finset.range (e' + 1), Nat.choose s' i) =
    ∑ i ∈ Finset.range (e' + 1), Nat.choose (s' + 1) i := by
  induction e' with
  | zero => simp
  | succ e' ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := e' + 1), Finset.sum_range_succ (n := e' + 1)]
    have hpas : Nat.choose (s' + 1) (e' + 1) = Nat.choose s' e' + Nat.choose s' (e' + 1) :=
      Nat.choose_succ_succ s' e'
    omega

private lemma card_prefixFew_le :
    ∀ (r s e : ℕ) (target : Bool) (P : (Fin r → Bool) → Fin r → Bool),
      Causal P →
      ∀ [DecidablePred (PrefixFew s e target P)],
      (Finset.univ.filter (PrefixFew s e target P)).card * 2 ^ s ≤
        (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro s e target P _ _
    cases s with
    | zero =>
      cases e with
      | zero => simp [PrefixFew]
      | succ e' =>
        have hle : (Finset.univ.filter (PrefixFew 0 (e' + 1) target P)).card ≤ 1 := by
          calc (Finset.univ.filter (PrefixFew 0 (e' + 1) target P)).card
              ≤ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.card_filter_le _ _
            _ = 1 := by simp
        have hsum : 1 ≤ ∑ i ∈ Finset.range (e' + 1), Nat.choose 0 i := by
          rw [Finset.sum_range_succ']
          simp
        simpa using le_trans hle hsum
    | succ s' =>
      simp [PrefixFew]
  | succ r ih =>
    intro s e target P hP _
    classical
    let fT : (Fin r → Bool) ↪ (Fin (r + 1) → Bool) :=
      ⟨fun c' => Fin.cons target c', fun a b h => by
        funext i; have := congrFun h i.succ; simpa using this⟩
    let fF : (Fin r → Bool) ↪ (Fin (r + 1) → Bool) :=
      ⟨fun c' => Fin.cons (!target) c', fun a b h => by
        funext i; have := congrFun h i.succ; simpa using this⟩
    let S := Finset.univ.filter (PrefixFew s e target P)
    let ST := Finset.univ.filter (fun c' : Fin r → Bool => PrefixFew s e target P (Fin.cons target c'))
    let SF := Finset.univ.filter (fun c' : Fin r → Bool => PrefixFew s e target P (Fin.cons (!target) c'))
    have hsplit : S.card = ST.card + SF.card := by
      have hdisj : Disjoint (ST.map fT) (SF.map fF) := by
        rw [Finset.disjoint_left]
        intro x hxT hxF
        rcases Finset.mem_map.mp hxT with ⟨a, _, rfl⟩
        rcases Finset.mem_map.mp hxF with ⟨b, _, hb⟩
        have h0 : (!target) = target := congrFun hb 0
        cases target <;> simp at h0
      have hunion : S = (ST.map fT) ∪ (SF.map fF) := by
        ext c
        simp only [S, ST, SF, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
          true_and, fT, fF, Function.Embedding.coeFn_mk]
        constructor
        · intro hc
          by_cases h0 : c 0 = target
          · left
            have hceq : Fin.cons target (fun i => c i.succ) = c := by
              funext j; cases j using Fin.cases with
              | zero => simp [h0]
              | succ i => simp
            exact ⟨fun i => c i.succ, by rwa [hceq], hceq⟩
          · right
            have h0' : c 0 = !target := by cases hc0 : c 0 <;> cases target <;> simp_all
            have hceq : Fin.cons (!target) (fun i => c i.succ) = c := by
              funext j; cases j using Fin.cases with
              | zero => simp [h0']
              | succ i => simp
            exact ⟨fun i => c i.succ, by rwa [hceq], hceq⟩
        · rintro (⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩) <;> exact hc'
      rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
    let b0 := P (fun _ => false) 0
    have hb0 : ∀ c : Fin (r + 1) → Bool, P c 0 = b0 := by
      intro c; exact hP c (fun _ => false) 0 (fun b hb => absurd hb (Fin.not_lt_zero b))
    let PT := fun (c' : Fin r → Bool) (i : Fin r) => P (Fin.cons target c') i.succ
    let PF := fun (c' : Fin r → Bool) (i : Fin r) => P (Fin.cons (!target) c') i.succ
    have hPT : Causal PT := causal_tail hP target
    have hPF : Causal PF := causal_tail hP (!target)
    change S.card * 2 ^ s ≤ (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ (r + 1)
    cases hbb : b0 with
    | false =>
      have hST : ST = Finset.univ.filter (PrefixFew s e target PT) := by
        ext c'
        simp only [ST, Finset.mem_filter, Finset.mem_univ, true_and]
        conv_lhs => unfold PrefixFew
        rw [hb0, hbb]
        simp [PT]
      have hSF : SF = Finset.univ.filter (PrefixFew s e target PF) := by
        ext c'
        simp only [SF, Finset.mem_filter, Finset.mem_univ, true_and]
        conv_lhs => unfold PrefixFew
        rw [hb0, hbb]
        simp [PF]
      rw [hsplit, hST, hSF, add_mul, pow_succ]
      have ihT := ih s e target PT hPT
      have ihF := ih s e target PF hPF
      linarith
    | true =>
      cases s with
      | zero =>
        cases e with
        | zero =>
          have h0 : S = ∅ := by
            ext c; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false]
            exact prefixFew_zero_false 0 target P c
          rw [h0]; simp
        | succ e' =>
          have hle : S.card ≤ 2 ^ (r + 1) := by
            calc S.card ≤ (Finset.univ : Finset (Fin (r + 1) → Bool)).card := Finset.card_filter_le _ _
              _ = 2 ^ (r + 1) := by simp
          have hsum : 1 ≤ ∑ i ∈ Finset.range (e' + 1), Nat.choose 0 i := by
            rw [Finset.sum_range_succ']; simp
          simpa using le_trans hle (Nat.le_mul_of_pos_left _ hsum)
      | succ s' =>
        cases e with
        | zero =>
          have h0 : S = ∅ := by
            ext c; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false]
            exact prefixFew_zero_false (s' + 1) target P c
          rw [h0]; simp
        | succ e' =>
          have hST : ST = Finset.univ.filter (PrefixFew s' e' target PT) := by
            ext c'
            simp only [ST, Finset.mem_filter, Finset.mem_univ, true_and]
            conv_lhs => unfold PrefixFew
            rw [hb0, hbb]
            simp [PT]
          have hSF : SF = Finset.univ.filter (PrefixFew s' (e' + 1) target PF) := by
            ext c'
            simp only [SF, Finset.mem_filter, Finset.mem_univ, true_and]
            conv_lhs => unfold PrefixFew
            rw [hb0, hbb]
            have hne : (!target) ≠ target := by cases target <;> simp
            simp [PF, hne]
          rw [hsplit, hST, hSF]
          have ihT := ih s' e' target PT hPT
          have ihF := ih s' (e' + 1) target PF hPF
          have hpas := sum_choose_pascal s' e'
          calc ((Finset.univ.filter (PrefixFew s' e' target PT)).card +
                (Finset.univ.filter (PrefixFew s' (e' + 1) target PF)).card) * 2 ^ (s' + 1)
              = 2 * ((Finset.univ.filter (PrefixFew s' e' target PT)).card * 2 ^ s' +
                  (Finset.univ.filter (PrefixFew s' (e' + 1) target PF)).card * 2 ^ s') := by
                rw [pow_succ]; ring
            _ ≤ 2 * ((∑ i ∈ Finset.range e', Nat.choose s' i) * 2 ^ r +
                  (∑ i ∈ Finset.range (e' + 1), Nat.choose s' i) * 2 ^ r) := by
                exact Nat.mul_le_mul_left 2 (Nat.add_le_add ihT ihF)
            _ = ((∑ i ∈ Finset.range e', Nat.choose s' i) +
                  (∑ i ∈ Finset.range (e' + 1), Nat.choose s' i)) * 2 ^ (r + 1) := by
                rw [pow_succ]; ring
            _ = (∑ i ∈ Finset.range (e' + 1), Nat.choose (s' + 1) i) * 2 ^ (r + 1) := by
                rw [hpas]

private lemma exists_kth_elem {r : ℕ} (H : Finset (Fin r)) {k : ℕ} (hk : k < H.card) :
    ∃ a ∈ H, (H.filter (fun i => i < a)).card = k := by
  let f := H.orderEmbOfFin rfl
  let idx : Fin H.card := ⟨k, hk⟩
  refine ⟨f idx, Finset.orderEmbOfFin_mem H rfl idx, ?_⟩
  have hmap : (Finset.Iio idx).map f.toEmbedding = H.filter (fun i => i < f idx) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem H rfl j, f.strictMono hj⟩
    · rintro ⟨hx, hlt⟩
      have hmem : x ∈ Set.range f := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      rcases hmem with ⟨j, rfl⟩
      exact ⟨j, f.lt_iff_lt.mp hlt, rfl⟩
  rw [← hmap, Finset.card_map, Fin.card_Iio]

private lemma prefixFew_of_hits :
    ∀ {r : ℕ} (s e : ℕ) (target : Bool) (P : (Fin r → Bool) → Fin r → Bool) (c : Fin r → Bool),
      s < (Finset.univ.filter (fun a : Fin r => P c a = true)).card →
      (∀ a_last : Fin r, P c a_last = true →
        (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true)).card = s →
        (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true ∧ c a = target)).card < e) →
      PrefixFew s e target P c := by
  intro r
  induction r with
  | zero =>
    intro s e target P c hlt _
    simp at hlt
  | succ r ih =>
    intro s e target P c hlt hbound
    let P' := fun (c' : Fin r → Bool) (i : Fin r) => P (Fin.cons (c 0) c') i.succ
    let c' : Fin r → Bool := fun i => c i.succ
    have hcc : Fin.cons (c 0) c' = c := by
      funext j; cases j using Fin.cases <;> simp [c']
    have hP'_eq : ∀ i : Fin r, P' c' i = P c i.succ := by
      intro i; simp [P', hcc]
    let H := Finset.univ.filter (fun a : Fin (r + 1) => P c a = true)
    let H' := Finset.univ.filter (fun i : Fin r => P' c' i = true)
    change s < H.card at hlt
    have hH_card : H.card = (if P c 0 = true then 1 else 0) + H'.card := by
      let emb : Fin r ↪ Fin (r + 1) := ⟨Fin.succ, Fin.succ_injective r⟩
      have hsub : H'.map emb = H.erase 0 := by
        ext a
        simp only [H', H, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, emb, Function.Embedding.coeFn_mk]
        cases a using Fin.cases with
        | zero => simp
        | succ i =>
          simp [Fin.succ_inj, hP'_eq]
      by_cases h0 : P c 0 = true
      · have hmem : (0 : Fin (r + 1)) ∈ H := by simp [H, h0]
        rw [if_pos h0, ← Finset.card_map emb, hsub, Finset.card_erase_of_mem hmem]
        have hpos : 0 < H.card := Finset.card_pos.mpr ⟨0, hmem⟩
        omega
      · have hmem : (0 : Fin (r + 1)) ∉ H := by simp [H, h0]
        rw [if_neg h0, zero_add, ← Finset.card_map emb, hsub, Finset.erase_eq_of_notMem hmem]
    unfold PrefixFew
    by_cases h0 : P c 0 = true
    · rw [if_pos h0]
      cases s with
      | zero =>
        have hb := hbound 0 h0 (by simp)
        simpa using hb
      | succ s' =>
        dsimp only
        have hlt' : s' < H'.card := by rw [if_pos h0] at hH_card; omega
        have hshift : ∀ a' : Fin r,
            (Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true)).card =
            1 + (Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true)).card := by
          intro a'
          let A := Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true)
          let A' := Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true)
          let emb : Fin r ↪ Fin (r + 1) := ⟨Fin.succ, Fin.succ_injective r⟩
          have hsub : A'.map emb = A.erase 0 := by
            ext a
            simp only [A', A, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase, emb, Function.Embedding.coeFn_mk]
            cases a using Fin.cases with
            | zero => simp
            | succ i => simp [Fin.succ_inj, Fin.succ_lt_succ_iff, hP'_eq]
          have hmem : (0 : Fin (r + 1)) ∈ A := by simp [A, h0, Fin.succ_pos]
          change A.card = 1 + A'.card
          rw [← Finset.card_map emb, hsub, Finset.card_erase_of_mem hmem]
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨0, hmem⟩
          omega
        have hshift_m : ∀ a' : Fin r,
            (Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true ∧ c a = target)).card =
            (if c 0 = target then 1 else 0) +
            (Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true ∧ c' i = target)).card := by
          intro a'
          let B := Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true ∧ c a = target)
          let B' := Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true ∧ c' i = target)
          let emb : Fin r ↪ Fin (r + 1) := ⟨Fin.succ, Fin.succ_injective r⟩
          have hsub : B'.map emb = B.erase 0 := by
            ext a
            simp only [B', B, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase, emb, Function.Embedding.coeFn_mk]
            cases a using Fin.cases with
            | zero => simp
            | succ i => simp [Fin.succ_inj, Fin.succ_lt_succ_iff, hP'_eq, c']
          change B.card = (if c 0 = target then 1 else 0) + B'.card
          by_cases hc0 : c 0 = target
          · have hmem : (0 : Fin (r + 1)) ∈ B := by simp [B, h0, hc0, Fin.succ_pos]
            rw [if_pos hc0, ← Finset.card_map emb, hsub, Finset.card_erase_of_mem hmem]
            have hpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hmem⟩
            omega
          · have hmem : (0 : Fin (r + 1)) ∉ B := by simp [B, hc0]
            rw [if_neg hc0, zero_add, ← Finset.card_map emb, hsub, Finset.erase_eq_of_notMem hmem]
        by_cases hc0 : c 0 = target
        · simp only [hc0, ↓reduceIte]
          obtain ⟨a', ha'_mem, hcard'⟩ := exists_kth_elem H' hlt'
          have ha' : P' c' a' = true := by simpa [H'] using ha'_mem
          have hfilt_eq : H'.filter (fun i => i < a') =
              Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true) := by
            ext i; simp [H', and_comm]
          rw [hfilt_eq] at hcard'
          have hP'_eq' : (fun c' i => P (Fin.cons target c') i.succ) = P' := by
            funext c'' i; simp [P', hc0]
          rw [hP'_eq']
          refine ⟨?_, ih s' (e - 1) target P' c' hlt' ?_⟩
          · have hb := hbound a'.succ (by rwa [← hP'_eq]) (by rw [hshift]; omega)
            rw [hshift_m, if_pos hc0] at hb
            omega
          · intro a₁ ha₁ hcard₁
            have hb := hbound a₁.succ (by rwa [← hP'_eq]) (by rw [hshift]; omega)
            rw [hshift_m, if_pos hc0] at hb
            omega
        · simp only [hc0, ↓reduceIte]
          apply ih s' e target P' c' hlt'
          intro a₁ ha₁ hcard₁
          have hb := hbound a₁.succ (by rwa [← hP'_eq]) (by rw [hshift]; omega)
          rw [hshift_m, if_neg hc0] at hb
          omega
    · rw [if_neg h0]
      have hlt' : s < H'.card := by rw [if_neg h0] at hH_card; omega
      apply ih s e target P' c' hlt'
      intro a' ha' hcard'
      have hshift :
          (Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true)).card =
          (Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true)).card := by
        let A := Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true)
        let A' := Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true)
        let emb : Fin r ↪ Fin (r + 1) := ⟨Fin.succ, Fin.succ_injective r⟩
        have hsub : A'.map emb = A := by
          ext a
          simp only [A', A, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            emb, Function.Embedding.coeFn_mk]
          cases a using Fin.cases with
          | zero => simp [h0]
          | succ i => simp [Fin.succ_lt_succ_iff, hP'_eq]
        change A.card = A'.card
        rw [← hsub, Finset.card_map]
      have hshift_m :
          (Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true ∧ c a = target)).card =
          (Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true ∧ c' i = target)).card := by
        let B := Finset.univ.filter (fun a : Fin (r + 1) => a < a'.succ ∧ P c a = true ∧ c a = target)
        let B' := Finset.univ.filter (fun i : Fin r => i < a' ∧ P' c' i = true ∧ c' i = target)
        let emb : Fin r ↪ Fin (r + 1) := ⟨Fin.succ, Fin.succ_injective r⟩
        have hsub : B'.map emb = B := by
          ext a
          simp only [B', B, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            emb, Function.Embedding.coeFn_mk]
          cases a using Fin.cases with
          | zero => simp [h0]
          | succ i => simp [Fin.succ_lt_succ_iff, hP'_eq, c']
        change B.card = B'.card
        rw [← hsub, Finset.card_map]
      have hb := hbound a'.succ (by rwa [← hP'_eq]) (by rw [hshift]; exact hcard')
      rwa [hshift_m] at hb

section PackHelpers

variable {n r : ℕ} (edge : Fin n → Fin n → Bool) (f : Finset (Fin r × Fin n) → (Fin r × Fin n) → Bool)

private def blockOf (y : Finset (Fin r × Fin n)) (a : Fin r) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (a, i) ∈ y)

private def alphaOf (x : Finset (Fin n)) : ℕ :=
  (x.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge i k = false)).sup Finset.card

private def packOf : ℕ → Finset (Fin r × Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin r × Fin n) → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset (Fin r × Fin n)) (k : Fin r × Fin n),
      prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)

private lemma packOf_mono {m : ℕ} {u v : Finset (Fin r × Fin n)}
    (hu : packOf f m u) (huv : u ⊆ v) : packOf f m v := by
  cases m with
  | zero => trivial
  | succ m =>
    rcases hu with ⟨u', v', k, hp, h1, h2, h3, h4⟩
    exact ⟨u', v', k, hp, h1, h2.trans huv, h3, h4⟩

private lemma exists_max_indep (x : Finset (Fin n)) :
    ∃ I ⊆ x, (∀ i ∈ I, ∀ k ∈ I, edge i k = false) ∧ I.card = alphaOf edge x := by
  let S := x.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge i k = false)
  have hne : S.Nonempty := ⟨∅, by simp [S]⟩
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image S Finset.card hne
  have hI_sub : I ⊆ x := Finset.mem_powerset.mp (Finset.mem_filter.mp hI_mem).1
  have hI_ind : ∀ i ∈ I, ∀ k ∈ I, edge i k = false := (Finset.mem_filter.mp hI_mem).2
  have hI_eq : I.card = alphaOf edge x := by
    apply le_antisymm
    · exact Finset.le_sup (f := Finset.card) hI_mem
    · exact Finset.sup_le (fun z hz => hI_max z hz)
  exact ⟨I, hI_sub, hI_ind, hI_eq⟩

private lemma alphaOf_mono {x y : Finset (Fin n)} (hxy : x ⊆ y) :
    alphaOf edge x ≤ alphaOf edge y := by
  apply Finset.sup_mono
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_powerset] at hz ⊢
  exact ⟨hz.1.trans hxy, hz.2⟩

private lemma alphaOf_insert_le (x : Finset (Fin n)) (j : Fin n) :
    alphaOf edge (insert j x) ≤ alphaOf edge x + 1 := by
  obtain ⟨I, hI_sub, hI_ind, hI_eq⟩ := exists_max_indep edge (insert j x)
  have hsub : I.erase j ⊆ x := by
    intro i hi
    have h1 := hI_sub (Finset.mem_of_mem_erase hi)
    have h2 := Finset.ne_of_mem_erase hi
    simpa [h2] using h1
  have hind : ∀ i ∈ I.erase j, ∀ k ∈ I.erase j, edge i k = false :=
    fun i hi k hk => hI_ind i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk)
  have hle : (I.erase j).card ≤ alphaOf edge x :=
    Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hind⟩)
  have hcard : I.card ≤ (I.erase j).card + 1 := by
    by_cases hj : j ∈ I
    · rw [Finset.card_erase_of_mem hj]; have := Finset.card_pos.mpr ⟨j, hj⟩; omega
    · rw [Finset.erase_eq_of_notMem hj]; omega
  omega

private lemma alphaOf_empty : alphaOf edge (∅ : Finset (Fin n)) = 0 := by
  simp [alphaOf]

private lemma packOf_indep
    (h_indep : ∀ (y : Finset (Fin r × Fin n)) (a : Fin r) (i : Fin n),
      ((a, i) ∉ y ∧ ∀ k ∈ blockOf y a, edge k i = false) → f y (a, i) = true)
    (h_in : ∀ (y : Finset (Fin r × Fin n)) (a : Fin r) (i : Fin n),
      (a, i) ∈ y → f y (a, i) = false)
    (a : Fin r) (u : Finset (Fin r × Fin n)) (hu_empty : blockOf u a = ∅)
    (I : Finset (Fin n)) (hI : ∀ i ∈ I, ∀ k ∈ I, edge i k = false)
    {m : ℕ} (hm : packOf f m u) :
    packOf f (m + I.card) (u ∪ I.image (fun i => (a, i))) := by
  induction I using Finset.induction_on with
  | empty => simpa using hm
  | @insert i I' hi ih =>
    have hI' : ∀ x ∈ I', ∀ k ∈ I', edge x k = false :=
      fun x hx k hk => hI x (Finset.mem_insert_of_mem hx) k (Finset.mem_insert_of_mem hk)
    have hprev := ih hI'
    rw [Finset.card_insert_of_notMem hi, ← Nat.add_assoc]
    let u' := u ∪ I'.image (fun k => (a, k))
    let v' := u ∪ (insert i I').image (fun k => (a, k))
    have hsub : u' ⊆ v' := Finset.union_subset_union_right (Finset.image_subset_image (Finset.subset_insert i I'))
    have hnotmem : (a, i) ∉ u' := by
      simp only [u', Finset.mem_union, Finset.mem_image, Prod.mk.injEq, true_and, not_or, not_exists]
      refine ⟨?_, fun k hk => hi (hk.2 ▸ hk.1)⟩
      intro hmem
      have : i ∈ blockOf u a := by simp [blockOf, hmem]
      rw [hu_empty] at this
      exact Finset.notMem_empty i this
    have hmem_v : (a, i) ∈ v' := by
      simp only [v', Finset.mem_union, Finset.mem_image]
      right; exact ⟨i, Finset.mem_insert_self i I', rfl⟩
    have hblock : ∀ k ∈ blockOf u' a, edge k i = false := by
      intro k hk
      simp only [blockOf, u', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, Prod.mk.injEq] at hk
      rcases hk with hku | ⟨k', hk', hk_eq⟩
      · have : k ∈ blockOf u a := by simp [blockOf, hku]
        rw [hu_empty] at this
        exact absurd this (Finset.notMem_empty k)
      · rw [← hk_eq]; exact hI k' (Finset.mem_insert_of_mem hk') i (Finset.mem_insert_self i I')
    exact ⟨u', v', (a, i), hprev, hsub, Finset.Subset.refl _, h_indep u' a i ⟨hnotmem, hblock⟩, h_in v' a i hmem_v⟩

end PackHelpers

private lemma wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x =
    Circuit.wires ⟨gs₂, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    have : (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gs).length =
        x.length + gs.length := ih
    omega

private lemma wires_getD_append_left (gs₁ gs₂ : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs₁.length) :
    (Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x).getD i false =
    (Circuit.wires ⟨gs₁, 0⟩ x).getD i false := by
  rw [wires_append]
  induction gs₂ using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs₂ g ih =>
    let w := Circuit.wires ⟨gs₂, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x)
    have hlen : i < w.length := by
      simp only [w, wires_length]; omega
    have hstep : Circuit.wires ⟨gs₂ ++ [g], 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) =
        w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)] := by
      simp [w, Circuit.wires, List.foldl_append]
    rw [hstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private lemma wires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.wires ⟨gs ++ [g], 0⟩ x).getD (x.length + gs.length) false =
    g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false) := by
  let w := Circuit.wires ⟨gs, 0⟩ x
  have hlen : w.length = x.length + gs.length := wires_length gs x
  have hstep : Circuit.wires ⟨gs ++ [g], 0⟩ x =
      w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)] := by
    simp [w, Circuit.wires, List.foldl_append]
  rw [hstep, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _)]
  simp [w]

private lemma notCount_append (gs₁ gs₂ : List Gate) (o₁ o₂ o : ℕ) :
    notCount ⟨gs₁ ++ gs₂, o⟩ = notCount ⟨gs₁, o₁⟩ + notCount ⟨gs₂, o₂⟩ := by
  simp [notCount, List.filter_append, List.length_append]

private lemma fanInTwo_append {gs₁ gs₂ : List Gate} {o₁ o₂ o : ℕ}
    (h1 : FanInTwo ⟨gs₁, o₁⟩) (h2 : FanInTwo ⟨gs₂, o₂⟩) :
    FanInTwo ⟨gs₁ ++ gs₂, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

private lemma readsBack_append {m : ℕ} {gs₁ gs₂ : List Gate} {o₁ o₂ o : ℕ}
    (h1 : ReadsBack m ⟨gs₁, o₁⟩)
    (h2 : ∀ j < gs₂.length, ∀ i ∈ (gateAt ⟨gs₂, o₂⟩ j).inputs, i < m + gs₁.length + j) :
    ReadsBack m ⟨gs₁ ++ gs₂, o⟩ := by
  intro j hj i hi
  simp only [gateAt, List.getD_eq_getElem?_getD] at hi
  by_cases hj1 : j < gs₁.length
  · rw [List.getElem?_append_left hj1] at hi
    exact h1 j hj1 i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
  · have hge : gs₁.length ≤ j := by omega
    rw [List.getElem?_append_right hge] at hi
    have hj2 : j - gs₁.length < gs₂.length := by simp at hj; omega
    have h := h2 (j - gs₁.length) hj2 i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
    omega

private def remapWire (inN : ℕ) (inMap : ℕ → ℕ) (base : ℕ) (w : ℕ) : ℕ :=
  if w < inN then inMap w else base + (w - inN)

private def remapGates (inN : ℕ) (inMap : ℕ → ℕ) (base : ℕ) (gs : List Gate) : List Gate :=
  gs.map (fun g => ⟨g.op, g.inputs.map (remapWire inN inMap base)⟩)

private lemma remapGates_length (inN : ℕ) (inMap : ℕ → ℕ) (base : ℕ) (gs : List Gate) :
    (remapGates inN inMap base gs).length = gs.length := by
  simp [remapGates]

private lemma remapGates_notCount (inN : ℕ) (inMap : ℕ → ℕ) (base : ℕ) (gs : List Gate) (o : ℕ) :
    notCount ⟨remapGates inN inMap base gs, o⟩ = notCount ⟨gs, o⟩ := by
  simp [notCount, remapGates, List.filter_map, Function.comp_def]

private lemma remapGates_fanInTwo {inN : ℕ} {inMap : ℕ → ℕ} {base : ℕ} {C : Circuit}
    (hF : FanInTwo C) (o : ℕ) :
    FanInTwo ⟨remapGates inN inMap base C.gates, o⟩ := by
  intro g hg
  simp only [remapGates, List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  obtain ⟨hop, hlen⟩ := hF g₀ hg₀
  exact ⟨hop, by simpa using hlen⟩

private lemma remapGates_readsBack {m inN : ℕ} {inMap : ℕ → ℕ} {gs₁ : List Gate} {C : Circuit}
    (hRB : ReadsBack inN C) (hin : ∀ w < inN, inMap w < m + gs₁.length) :
    ∀ j < (remapGates inN inMap (m + gs₁.length) C.gates).length,
      ∀ i ∈ (gateAt ⟨remapGates inN inMap (m + gs₁.length) C.gates, 0⟩ j).inputs,
        i < m + gs₁.length + j := by
  intro j hj i hi
  rw [remapGates_length] at hj
  simp only [gateAt, remapGates, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, List.mem_map] at hi
  rcases hi with ⟨w, hw, rfl⟩
  have hw_lt : w < inN + j := hRB j hj w (by
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hw)
  unfold remapWire
  split_ifs with hlt
  · exact lt_of_lt_of_le (hin w hlt) (Nat.le_add_right _ _)
  · omega

private lemma remapGates_eval {inN : ℕ} {inMap : ℕ → ℕ}
    (gs₁ : List Gate) (C : Circuit) (xD xC : List Bool)
    (hxC : xC.length = inN)
    (hRB : ReadsBack inN C)
    (hin_lt : ∀ w < inN, inMap w < xD.length + gs₁.length)
    (hin_val : ∀ w < inN, (Circuit.wires ⟨gs₁, 0⟩ xD).getD (inMap w) false = xC.getD w false) :
    ∀ w < inN + C.gates.length,
      (Circuit.wires ⟨gs₁ ++ remapGates inN inMap (xD.length + gs₁.length) C.gates, 0⟩ xD).getD
        (remapWire inN inMap (xD.length + gs₁.length) w) false =
      (Circuit.wires C xC).getD w false := by

  obtain ⟨gates, out⟩ := C
  induction gates using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, add_zero] at hw
    simp only [remapGates, List.map_nil, List.append_nil, remapWire, if_pos hw, Circuit.wires,
      List.foldl_nil]
    exact hin_val w hw
  | append_singleton gs g ih =>
    have hRB_gs : ReadsBack inN ⟨gs, out⟩ := by
      intro j hj i hi
      dsimp only at hj
      have hj' : j < (gs ++ [g]).length := by simp; omega
      have h := hRB j hj' i
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hj] at h
      exact h (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
    have ih' := ih hRB_gs
    let base := xD.length + gs₁.length
    let rg := remapGates inN inMap base gs
    let g' : Gate := ⟨g.op, g.inputs.map (remapWire inN inMap base)⟩
    have hrm_eq : remapGates inN inMap base (gs ++ [g]) = rg ++ [g'] := by
      simp [remapGates, rg, g']
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hw_old : w < inN + gs.length
    · have hrem_lt : remapWire inN inMap base w < xD.length + (gs₁ ++ rg).length := by
        simp only [List.length_append, rg, remapGates_length]
        unfold remapWire
        split_ifs with hlt
        · exact lt_of_lt_of_le (hin_lt w hlt) (by omega)
        · omega
      rw [hrm_eq, ← List.append_assoc, wires_getD_append_left (gs₁ ++ rg) [g'] xD hrem_lt]
      have hC_old : (Circuit.wires ⟨gs ++ [g], out⟩ xC).getD w false =
          (Circuit.wires ⟨gs, out⟩ xC).getD w false := by
        have hlen : w < xC.length + gs.length := by omega
        exact wires_getD_append_left gs [g] xC hlen
      rw [hC_old]
      exact ih' w hw_old
    · have hw_eq : w = inN + gs.length := by omega
      subst hw_eq
      have hrem_eq : remapWire inN inMap base (inN + gs.length) = xD.length + (gs₁ ++ rg).length := by
        simp only [remapWire, show ¬ (inN + gs.length < inN) by omega, ↓reduceIte,
          Nat.add_sub_cancel_left, List.length_append, rg, remapGates_length, base]
        omega
      rw [hrm_eq, ← List.append_assoc, hrem_eq, wires_snoc_last (gs₁ ++ rg) g' xD]
      have hC_last : (Circuit.wires ⟨gs ++ [g], out⟩ xC).getD (inN + gs.length) false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, out⟩ xC).getD i false) := by
        rw [← hxC]
        exact wires_snoc_last gs g xC
      rw [hC_last]
      congr 1
      simp only [g', List.map_map]
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < inN + gs.length := by
        have h := hRB gs.length (by simp) u
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at h
        exact h hu
      exact ih' u hu_lt

private def voteStepGates (s : ℕ) (wTrue wVote base : ℕ) (T : Fin (s + 1) → ℕ) : List Gate :=
  (List.ofFn (fun k : Fin (s + 1) =>
    let prevLo := if hk : k.val = 0 then wTrue else T ⟨k.val - 1, by omega⟩
    let prevHi := T k
    let andW := base + 2 * k.val
    [⟨GateOp.and, [prevLo, wVote]⟩, ⟨GateOp.or, [prevHi, andW]⟩])).flatten

private def voteStepNext (s base : ℕ) : Fin (s + 1) → ℕ :=
  fun k => base + 2 * k.val + 1

private lemma voteStepGates_length (s wTrue wVote base : ℕ) (T : Fin (s + 1) → ℕ) :
    (voteStepGates s wTrue wVote base T).length = 2 * (s + 1) := by
  simp only [voteStepGates, List.length_flatten, List.map_ofFn]
  change (List.ofFn (fun _ : Fin (s + 1) => 2)).sum = 2 * (s + 1)
  rw [List.sum_ofFn]
  simp [Nat.mul_comm]

private lemma voteStepGates_notCount (s wTrue wVote base : ℕ) (T : Fin (s + 1) → ℕ) (o : ℕ) :
    notCount ⟨voteStepGates s wTrue wVote base T, o⟩ = 0 := by
  simp only [notCount, List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro g hg
  simp only [voteStepGates, List.mem_flatten, List.mem_ofFn] at hg
  rcases hg with ⟨l, ⟨k, rfl⟩, hgl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgl
  rcases hgl with rfl | rfl <;> simp

private lemma voteStepGates_fanInTwo (s wTrue wVote base : ℕ) (T : Fin (s + 1) → ℕ) (o : ℕ) :
    FanInTwo ⟨voteStepGates s wTrue wVote base T, o⟩ := by
  intro g hg
  simp only [voteStepGates, List.mem_flatten, List.mem_ofFn] at hg
  rcases hg with ⟨l, ⟨k, rfl⟩, hgl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgl
  rcases hgl with rfl | rfl <;> simp

private lemma voteStepGates_getElem (s wTrue wVote base : ℕ) (T : Fin (s + 1) → ℕ) (j : ℕ)
    (hj : j < 2 * (s + 1)) :
    (voteStepGates s wTrue wVote base T).getD j ⟨GateOp.or, []⟩ =
    if j % 2 = 0 then
      let k : Fin (s + 1) := ⟨j / 2, by omega⟩
      let prevLo := if hk : k.val = 0 then wTrue else T ⟨k.val - 1, by omega⟩
      ⟨GateOp.and, [prevLo, wVote]⟩
    else
      let k : Fin (s + 1) := ⟨j / 2, by omega⟩
      ⟨GateOp.or, [T k, base + 2 * k.val]⟩ := by
  have hflat : ∀ (m : ℕ) (f : Fin m → Gate × Gate) (i : ℕ) (hi : i < 2 * m),
      ((List.ofFn (fun k : Fin m => [(f k).1, (f k).2])).flatten).getD i ⟨GateOp.or, []⟩ =
      if i % 2 = 0 then (f ⟨i / 2, by omega⟩).1 else (f ⟨i / 2, by omega⟩).2 := by
    intro m
    induction m with
    | zero => intro _ _ hi; omega
    | succ m ih =>
      intro f i hi
      rw [List.ofFn_succ, List.flatten_cons]
      cases i with
      | zero => simp
      | succ i =>
        cases i with
        | zero => simp
        | succ i' =>
          have h1 : ([(f 0).1, (f 0).2] ++ (List.ofFn (fun k : Fin m => [(f k.succ).1, (f k.succ).2])).flatten).getD (i' + 2) ⟨GateOp.or, []⟩ =
            ((List.ofFn (fun k : Fin m => [(f k.succ).1, (f k.succ).2])).flatten).getD i' ⟨GateOp.or, []⟩ := by
            simp [List.getD_eq_getElem?_getD]
          rw [h1, ih (fun k => f k.succ) i' (by omega)]
          have hmod : (i' + 2) % 2 = i' % 2 := by omega
          have hdiv : (i' + 2) / 2 = i' / 2 + 1 := by omega
          simp only [hmod, hdiv]
          split_ifs <;> rfl
  exact hflat (s + 1) (fun k =>
    (⟨GateOp.and, [if hk : k.val = 0 then wTrue else T ⟨k.val - 1, by omega⟩, wVote]⟩,
     ⟨GateOp.or, [T k, base + 2 * k.val]⟩)) j hj

private lemma voteStepGates_readsBack {m s wTrue wVote : ℕ} {gs₁ : List Gate} {T : Fin (s + 1) → ℕ}
    (hwT : wTrue < m + gs₁.length) (hwV : wVote < m + gs₁.length)
    (hT : ∀ k : Fin (s + 1), T k < m + gs₁.length) :
    ∀ j < (voteStepGates s wTrue wVote (m + gs₁.length) T).length,
      ∀ i ∈ (gateAt ⟨voteStepGates s wTrue wVote (m + gs₁.length) T, 0⟩ j).inputs,
        i < m + gs₁.length + j := by
  intro j hj i hi
  rw [voteStepGates_length] at hj
  simp only [gateAt] at hi
  rw [voteStepGates_getElem s wTrue wVote (m + gs₁.length) T j hj] at hi
  split_ifs at hi with hmod
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · split_ifs
      · omega
      · have := hT ⟨j / 2 - 1, by omega⟩; omega
    · omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := hT ⟨j / 2, by omega⟩; omega
    · omega

private lemma voteStepGates_eval {s wTrue wVote : ℕ} (gs₁ : List Gate) (x : List Bool)
    (T : Fin (s + 1) → ℕ)
    (hwT : wTrue < x.length + gs₁.length)
    (hwV : wVote < x.length + gs₁.length)
    (hT : ∀ k : Fin (s + 1), T k < x.length + gs₁.length)
    (hwT_val : (Circuit.wires ⟨gs₁, 0⟩ x).getD wTrue false = true) :
    ∀ k : Fin (s + 1),
      (Circuit.wires ⟨gs₁ ++ voteStepGates s wTrue wVote (x.length + gs₁.length) T, 0⟩ x).getD
        (voteStepNext s (x.length + gs₁.length) k) false =
      ((Circuit.wires ⟨gs₁, 0⟩ x).getD (T k) false ||
        ((if hk : k.val = 0 then true else (Circuit.wires ⟨gs₁, 0⟩ x).getD (T ⟨k.val - 1, by omega⟩) false) &&
          (Circuit.wires ⟨gs₁, 0⟩ x).getD wVote false)) := by
  intro k
  set base := x.length + gs₁.length
  set vg := voteStepGates s wTrue wVote base T
  have hvlen : vg.length = 2 * (s + 1) := voteStepGates_length s wTrue wVote base T

  have hk2 : 2 * k.val + 1 < vg.length := by omega
  have hsplit : vg = vg.take (2 * k.val + 2) ++ vg.drop (2 * k.val + 2) := (List.take_append_drop _ _).symm
  have htake_len : (vg.take (2 * k.val + 2)).length = 2 * k.val + 2 := List.length_take_of_le (by omega)
  have htake_snoc : vg.take (2 * k.val + 2) = vg.take (2 * k.val + 1) ++ [vg[2 * k.val + 1]'hk2] := by
    rw [List.take_succ_eq_append_getElem hk2]
  have htake_snoc0 : vg.take (2 * k.val + 1) = vg.take (2 * k.val) ++ [vg[2 * k.val]'(by omega)] := by
    rw [List.take_succ_eq_append_getElem (by omega)]
  have htarget_lt : voteStepNext s base k < x.length + (gs₁ ++ vg.take (2 * k.val + 2)).length := by
    simp [voteStepNext, List.length_append, htake_len, base]; omega
  rw [hsplit, ← List.append_assoc, wires_getD_append_left (gs₁ ++ vg.take (2 * k.val + 2)) _ x htarget_lt]

  have hor_idx : voteStepNext s base k = x.length + (gs₁ ++ vg.take (2 * k.val + 1)).length := by
    simp [voteStepNext, List.length_append, List.length_take_of_le (show 2 * k.val + 1 ≤ vg.length by omega), base]
    omega
  rw [htake_snoc, ← List.append_assoc, hor_idx, wires_snoc_last]
  have hgate_or : vg[2 * k.val + 1]'hk2 = ⟨GateOp.or, [T k, base + 2 * k.val]⟩ := by
    have h := voteStepGates_getElem s wTrue wVote base T (2 * k.val + 1) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] at h
    have hmod : (2 * k.val + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
    simp only [hmod, ↓reduceIte, hdiv, Fin.eta] at h
    exact h
  rw [hgate_or]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]

  have hTk_val : (Circuit.wires ⟨gs₁ ++ vg.take (2 * k.val + 1), 0⟩ x).getD (T k) false =
      (Circuit.wires ⟨gs₁, 0⟩ x).getD (T k) false :=
    wires_getD_append_left gs₁ _ x (hT k)

  have hand_idx : base + 2 * k.val = x.length + (gs₁ ++ vg.take (2 * k.val)).length := by
    have hlen_t : (vg.take (2 * k.val)).length = 2 * k.val := List.length_take_of_le (by rw [hvlen]; omega)
    rw [List.length_append, hlen_t]
    change x.length + gs₁.length + 2 * k.val = x.length + (gs₁.length + 2 * k.val)
    omega
  have hgate_and : vg[2 * k.val]'(by omega) =
      ⟨GateOp.and, [if hk : k.val = 0 then wTrue else T ⟨k.val - 1, by omega⟩, wVote]⟩ := by
    have h := voteStepGates_getElem s wTrue wVote base T (2 * k.val) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 * k.val < vg.length by rw [hvlen]; omega), Option.getD_some] at h
    have hmod : (2 * k.val) % 2 = 0 := by omega
    have hdiv : (2 * k.val) / 2 = k.val := by omega
    simp only [hmod, ↓reduceIte, hdiv] at h
    exact h
  have hand_val : (Circuit.wires ⟨gs₁ ++ vg.take (2 * k.val + 1), 0⟩ x).getD (base + 2 * k.val) false =
      ((if hk : k.val = 0 then true else (Circuit.wires ⟨gs₁, 0⟩ x).getD (T ⟨k.val - 1, by omega⟩) false) &&
        (Circuit.wires ⟨gs₁, 0⟩ x).getD wVote false) := by
    rw [htake_snoc0, ← List.append_assoc, hand_idx, wires_snoc_last, hgate_and]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    have hV : (Circuit.wires ⟨gs₁ ++ vg.take (2 * k.val), 0⟩ x).getD wVote false =
        (Circuit.wires ⟨gs₁, 0⟩ x).getD wVote false :=
      wires_getD_append_left gs₁ _ x hwV
    rw [hV]
    split_ifs with hk0
    · rw [wires_getD_append_left gs₁ _ x hwT, hwT_val]
    · rw [wires_getD_append_left gs₁ _ x (hT ⟨k.val - 1, by omega⟩)]
  rw [hTk_val, hand_val]

end PEqualNP.Outside.L_meta_48148_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_48148 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n e s : Nat) (edge : Fin n → Fin n → Bool),
  (∀ i, edge i i = false) → (∀ i k, edge i k = edge k i) →
  (n*2^n*(∑ i ∈ Finset.range e, Nat.choose s i) < 2^s ∨ 3*(2*n+e+1) ≤ s) →
  let r := 2*s+1
  let V := Fin r × Fin n
  let X := Finset (Fin n)
  let Y := Finset V
  let block := fun (y : Y) a => Finset.univ.filter (fun i : Fin n => (a,i) ∈ y)
  let alpha := fun (x : X) =>
    (x.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge i k = false)).sup Finset.card
  let gain := fun x j => decide (alpha (insert j x) = alpha x + 1)
  let input := fun (y : Y) =>
    (List.ofFn (fun a : Fin r => List.ofFn (fun i : Fin n => decide ((a,i) ∈ y)))).flatten ++ [false,true]
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : V → Fin (r*n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (r*n+2) C →
    C.output < r*n+2+C.size →
    let f := fun y k => (C.wires (input y)).getD (tap k).val false
    let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Y) (k : V), prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        f u k = true ∧ f v k = false)
    (∀ (y : Y) (a : Fin r) (i : Fin n),
      ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge k i = false) → f y (a,i) = true) →
    (∀ (y : Y) (a : Fin r) (i : Fin n), (a,i) ∈ y → f y (a,i) = false) →
    (∀ y, ¬ pack ((∑ a : Fin r, alpha (block y a)) + e + 1) y) →
    let query := fun (c : Fin r → Bool) (x : X) (j : Fin n) (a : Fin r) =>
      (Finset.univ : Y).filter (fun p =>
        (p.1 < a ∧ (p.2 ∈ x ∨ (c p.1 = true ∧ p.2 = j))) ∨ (p.1 = a ∧ p.2 ∈ x))
    let vote := fun c x j => decide (s <
      (Finset.univ.filter (fun a : Fin r => f (query c x j a) (a,j) = true)).card)
    ∃ c, (∀ x j, vote c x j = gain x j) ∧
      ∀ j, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧
        D.output < n+2+D.size ∧ D.size ≤ r*(C.size+2*(s+1)) ∧
        PEqualNP.NotBracket.notCount D ≤ r*PEqualNP.NotBracket.notCount C ∧
        ∀ (x : X), D.eval (List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]) = vote c x j) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.NotBracket PEqualNP.Outside.L_meta_48148_aux in
  intro n e s edge hirr hsym hbound r V X Y block alpha gain input C tap hFan hRB hOut f pack h_indep h_in h_nopack query vote
  classical
  have hblock_eq : ∀ y a, block y a = blockOf y a := fun y a => by ext i; simp [block, blockOf]
  have halpha_eq : ∀ x, alpha x = alphaOf edge x := fun x => by
    simp only [alpha, alphaOf]; congr 1; ext z; simp
  have hpack_eq : ∀ m y, pack m y ↔ packOf f m y := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
      intro y
      exact exists_congr fun u => exists_congr fun v => exists_congr fun k =>
        and_congr (ih u) Iff.rfl
  have hgain_eq : ∀ x j, gain x j = decide (alphaOf edge (insert j x) = alphaOf edge x + 1) := by
    intro x j
    apply Bool.eq_iff_iff.mpr
    simp only [gain, decide_eq_true_eq, halpha_eq]
    have hins : @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) fun a b => Classical.propDecidable (a = b)) j x =
        insert j x := by
      ext i
      rw [@Finset.mem_insert _ (fun a b => Classical.propDecidable (a = b)), Finset.mem_insert]
    rw [hins]
  have h_indep' : ∀ (y : Finset (Fin r × Fin n)) (a : Fin r) (i : Fin n),
      ((a, i) ∉ y ∧ ∀ k ∈ blockOf y a, edge k i = false) → f y (a, i) = true := by
    intro y a i h; exact h_indep y a i ⟨h.1, by simpa [hblock_eq] using h.2⟩
  have h_nopack' : ∀ y : Finset (Fin r × Fin n),
      ¬ packOf f ((∑ a : Fin r, alphaOf edge (blockOf y a)) + e + 1) y := by
    intro y hp
    apply h_nopack y
    have hsum_eq : (∑ a : Fin r, alpha (block y a)) + e + 1 =
        (∑ a : Fin r, alphaOf edge (blockOf y a)) + e + 1 := by
      simp only [hblock_eq, halpha_eq]
    rw [hsum_eq]
    exact (hpack_eq _ y).mpr hp

  have hcount : n * 2 ^ n * (∑ i ∈ Finset.range e, Nat.choose s i) < 2 ^ s := by
    rcases hbound with h1 | h2
    · exact h1
    · exact arith_bound n e s h2

  have hbad_card : ∀ (x : Finset (Fin n)) (j : Fin n),
      (Finset.univ.filter (fun c : Fin r → Bool => vote c x j ≠ gain x j)).card * 2 ^ s ≤
      (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ r := by
    intro x j

    have hq_causal : ∀ c₁ c₂ a, (∀ b < a, c₁ b = c₂ b) → query c₁ x j a = query c₂ x j a := by
      intro c₁ c₂ a hc
      ext ⟨p1, p2⟩
      simp only [query, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hlt : p1 < a
      · simp [hlt, hc p1 hlt]
      · simp [hlt]

    let yPrefix : (Fin r → Bool) → ℕ → Finset (Fin r × Fin n) :=
      fun c k => (Finset.univ : Finset (Fin r × Fin n)).filter (fun p =>
        p.1.val < k ∧ (p.2 ∈ x ∨ (c p.1 = true ∧ p.2 = j)))
    have hyPrefix_block_ge : ∀ c k (a : Fin r), k ≤ a.val → blockOf (yPrefix c k) a = ∅ := by
      intro c k a hka
      ext i; simp only [blockOf, yPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_and]; omega
    have hyPrefix_sub_query : ∀ c (a : Fin r), yPrefix c a.val ⊆ query c x j a := by
      intro c a ⟨p1, p2⟩ hp
      simp only [yPrefix, query, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact Or.inl ⟨hp.1, hp.2⟩
    have hquery_sub_yPrefix : ∀ c (a : Fin r), query c x j a ⊆ yPrefix c (a.val + 1) := by
      intro c a ⟨p1, p2⟩ hp
      simp only [yPrefix, query, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨hlt, h2⟩ | ⟨rfl, h2⟩
      · exact ⟨by exact Nat.lt_succ_of_lt hlt, h2⟩
      · exact ⟨Nat.lt_succ_self _, Or.inl h2⟩

    by_cases hgain : gain x j = true
    ·
      have hα_eq : alphaOf edge (insert j x) = alphaOf edge x + 1 := by
        simpa [hgain_eq] using hgain
      have hj_notin : j ∉ x := by
        intro hjx
        rw [Finset.insert_eq_of_mem hjx] at hα_eq
        omega
      obtain ⟨I', hI'_sub, hI'_ind, hI'_card⟩ := exists_max_indep edge (insert j x)
      have hj_in_I' : j ∈ I' := by
        by_contra hjn
        have hsub : I' ⊆ x := by
          intro i hi
          have h1 := hI'_sub hi
          have hne : i ≠ j := fun heq => hjn (heq ▸ hi)
          simpa [hne] using h1
        have hle : I'.card ≤ alphaOf edge x :=
          Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hI'_ind⟩)
        omega
      let I := I'.erase j
      have hI_sub : I ⊆ x := by
        intro i hi
        have h1 := hI'_sub (Finset.mem_of_mem_erase hi)
        have hne := Finset.ne_of_mem_erase hi
        simpa [hne] using h1
      have hI_ind : ∀ i ∈ I, ∀ k ∈ I, edge i k = false :=
        fun i hi k hk => hI'_ind i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk)
      have hI_j : ∀ k ∈ I, edge k j = false :=
        fun k hk => hI'_ind k (Finset.mem_of_mem_erase hk) j hj_in_I'
      have hI_card : I.card = alphaOf edge x := by
        rw [Finset.card_erase_of_mem hj_in_I', hI'_card, hα_eq]; omega
      let P : (Fin r → Bool) → Fin r → Bool := fun c a => !(f (query c x j a) (a, j))
      have hP_causal : Causal P := by
        intro c₁ c₂ a hc; simp only [P, hq_causal c₁ c₂ a hc]
      have hsub_pf : Finset.univ.filter (fun c : Fin r → Bool => vote c x j ≠ gain x j) ⊆
          Finset.univ.filter (PrefixFew s e false P) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        have hv_false : vote c x j = false := by rw [hgain] at hc; cases hv : vote c x j <;> simp_all
        have hlt_hits : s < (Finset.univ.filter (fun a : Fin r => P c a = true)).card := by
          have hnot : ¬ (s < (Finset.univ.filter (fun a : Fin r => f (query c x j a) (a, j) = true)).card) := by
            have hle : (Finset.univ.filter (fun a : Fin r => f (query c x j a) (a, j) = true)).card ≤ s := by
              convert (by simpa [vote] using hv_false)
            exact Nat.not_lt.mpr hle
          have hcomp : (Finset.univ.filter (fun a : Fin r => f (query c x j a) (a, j) = true)).card +
              (Finset.univ.filter (fun a : Fin r => P c a = true)).card = r := by
            have h1 : Finset.univ.filter (fun a : Fin r => P c a = true) =
                Finset.univ.filter (fun a : Fin r => ¬ (f (query c x j a) (a, j) = true)) := by
              ext a; simp [P]
            rw [h1, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
          omega
        apply prefixFew_of_hits s e false P c hlt_hits
        intro a_last ha_last _

        have hpack_prefix : ∀ k ≤ r,
            packOf f ((∑ a ∈ Finset.univ.filter (fun a : Fin r => a.val < k), alphaOf edge (blockOf (yPrefix c k) a)) +
              (Finset.univ.filter (fun a : Fin r => a.val < k ∧ P c a = true ∧ c a = false)).card) (yPrefix c k) := by
          intro k hk
          induction k with
          | zero => simp [packOf]
          | succ k ih =>
            have hk' : k < r := by omega
            let a : Fin r := ⟨k, hk'⟩
            have hih := ih (by omega)

            have hblock_old : ∀ b : Fin r, b.val < k →
                blockOf (yPrefix c (k + 1)) b = blockOf (yPrefix c k) b := by
              intro b hb
              ext i; simp only [blockOf, yPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor <;> intro h <;> exact ⟨by omega, h.2⟩
            have hsum_split :
                (∑ b ∈ Finset.univ.filter (fun b : Fin r => b.val < k + 1), alphaOf edge (blockOf (yPrefix c (k + 1)) b)) =
                (∑ b ∈ Finset.univ.filter (fun b : Fin r => b.val < k), alphaOf edge (blockOf (yPrefix c k) b)) +
                alphaOf edge (blockOf (yPrefix c (k + 1)) a) := by
              have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1) =
                  insert a (Finset.univ.filter (fun b : Fin r => b.val < k)) := by
                ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                  Fin.ext_iff, a]; omega
              have hna : a ∉ Finset.univ.filter (fun b : Fin r => b.val < k) := by simp [a]
              rw [hfilt, Finset.sum_insert hna, add_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro b hb
              rw [hblock_old b (by simpa using hb)]
            have hcard_split :
                (Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = false)).card =
                (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false)).card +
                (if P c a = true ∧ c a = false then 1 else 0) := by
              by_cases hpa : P c a = true ∧ c a = false
              · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = false) =
                    insert a (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false)) := by
                  ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, a]
                  constructor
                  · rintro ⟨hlt, h2⟩
                    by_cases hbk : b.val = k
                    · exact Or.inl hbk
                    · exact Or.inr ⟨by omega, h2⟩
                  · rintro (rfl | ⟨hlt, h2⟩)
                    · exact ⟨Nat.lt_succ_self _, hpa⟩
                    · exact ⟨by omega, h2⟩
                have hna : a ∉ Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false) := by
                  simp [a]
                rw [hfilt, Finset.card_insert_of_notMem hna, if_pos hpa]
              · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = false) =
                    Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false) := by
                  ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · rintro ⟨hlt, h2⟩
                    by_cases hbk : b.val = k
                    · have hba : b = a := Fin.ext hbk
                      exact absurd (hba ▸ h2) hpa
                    · exact ⟨by omega, h2⟩
                  · rintro ⟨hlt, h2⟩; exact ⟨by omega, h2⟩
                rw [hfilt, if_neg hpa, add_zero]
            rw [hsum_split, hcard_split]

            have hstepI := packOf_indep edge f h_indep' h_in a (yPrefix c k) (hyPrefix_block_ge c k a (le_refl _)) I hI_ind hih
            rw [hI_card] at hstepI
            let uI := yPrefix c k ∪ I.image (fun i => (a, i))
            have huI_sub_q : uI ⊆ query c x j a := by
              intro ⟨p1, p2⟩ hp
              simp only [uI, Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hp
              rcases hp with hp | ⟨i, hi, rfl, rfl⟩
              · exact hyPrefix_sub_query c a hp
              · simp [query, hI_sub hi]
            have hblock_a : blockOf (yPrefix c (k + 1)) a = if c a = true then insert j x else x := by
              ext i; simp only [blockOf, yPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hca : c a = true <;> simp [hca, a] <;> tauto
            by_cases hca : c a = true
            ·
              have hα_a : alphaOf edge (blockOf (yPrefix c (k + 1)) a) = alphaOf edge x + 1 := by
                rw [hblock_a, if_pos hca, hα_eq]
              have hno_extra : ¬ (P c a = true ∧ c a = false) := by simp [hca]
              rw [hα_a, if_neg hno_extra, add_zero]
              have hnotmem : (a, j) ∉ uI := by
                simp only [uI, Finset.mem_union, Finset.mem_image, Prod.mk.injEq, true_and, not_or, not_exists]
                refine ⟨?_, fun i hi => hj_notin (hi.2 ▸ hI_sub hi.1)⟩
                simp [yPrefix, a]
              have hblock_uI : ∀ i ∈ blockOf uI a, edge i j = false := by
                intro i hi
                simp only [blockOf, uI, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                  Finset.mem_image, Prod.mk.injEq] at hi
                rcases hi with h1 | ⟨i', hi', hi_eq⟩
                · simp [yPrefix, a] at h1
                · rw [← hi_eq]; exact hI_j i' hi'
              have hpack_plus : packOf f ((∑ b ∈ Finset.univ.filter (fun b : Fin r => b.val < k),
                    alphaOf edge (blockOf (yPrefix c k) b)) +
                  (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false)).card +
                  alphaOf edge x + 1) (yPrefix c (k + 1)) :=
                ⟨uI, insert (a, j) uI, (a, j), hstepI, Finset.subset_insert _ _,
                  (fun p hp => by
                    rcases Finset.mem_insert.mp hp with rfl | hp'
                    · simp [yPrefix, a, hca]
                    · exact hquery_sub_yPrefix c a (huI_sub_q hp')),
                  h_indep' uI a j ⟨hnotmem, hblock_uI⟩,
                  h_in (insert (a, j) uI) a j (Finset.mem_insert_self _ _)⟩
              convert hpack_plus using 1; ring
            ·
              have hca_f : c a = false := by cases hc0 : c a <;> simp_all
              have hα_a : alphaOf edge (blockOf (yPrefix c (k + 1)) a) = alphaOf edge x := by
                rw [hblock_a, if_neg hca]
              rw [hα_a]
              by_cases hpa : P c a = true
              · rw [if_pos ⟨hpa, hca_f⟩]
                have hf_false : f (query c x j a) (a, j) = false := by simpa [P] using hpa
                have hnotmem : (a, j) ∉ uI := by
                  simp only [uI, Finset.mem_union, Finset.mem_image, Prod.mk.injEq, true_and, not_or, not_exists]
                  refine ⟨?_, fun i hi => hj_notin (hi.2 ▸ hI_sub hi.1)⟩
                  simp [yPrefix, a]
                have hblock_uI : ∀ i ∈ blockOf uI a, edge i j = false := by
                  intro i hi
                  simp only [blockOf, uI, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                    Finset.mem_image, Prod.mk.injEq] at hi
                  rcases hi with h1 | ⟨i', hi', hi_eq⟩
                  · simp [yPrefix, a] at h1
                  · rw [← hi_eq]; exact hI_j i' hi'
                have hpack_plus : packOf f ((∑ b ∈ Finset.univ.filter (fun b : Fin r => b.val < k),
                      alphaOf edge (blockOf (yPrefix c k) b)) +
                    (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = false)).card +
                    alphaOf edge x + 1) (yPrefix c (k + 1)) :=
                  ⟨uI, query c x j a, (a, j), hstepI, huI_sub_q, hquery_sub_yPrefix c a,
                    h_indep' uI a j ⟨hnotmem, hblock_uI⟩, hf_false⟩
                convert hpack_plus using 1; ring
              · rw [if_neg (by simp [hpa]), add_zero]
                have hpack_same := packOf_mono f hstepI (huI_sub_q.trans (hquery_sub_yPrefix c a))
                convert hpack_same using 1; ring

        have hpref := hpack_prefix a_last.val (le_of_lt a_last.isLt)
        have hstepI := packOf_indep edge f h_indep' h_in a_last (yPrefix c a_last.val)
          (hyPrefix_block_ge c a_last.val a_last (le_refl _)) I hI_ind hpref
        rw [hI_card] at hstepI
        let uI := yPrefix c a_last.val ∪ I.image (fun i => (a_last, i))
        have huI_sub_q : uI ⊆ query c x j a_last := by
          intro ⟨p1, p2⟩ hp
          simp only [uI, Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hp
          rcases hp with hp | ⟨i, hi, rfl, rfl⟩
          · exact hyPrefix_sub_query c a_last hp
          · simp [query, hI_sub hi]
        have hnotmem : (a_last, j) ∉ uI := by
          simp only [uI, Finset.mem_union, Finset.mem_image, Prod.mk.injEq, true_and, not_or, not_exists]
          refine ⟨?_, fun i hi => hj_notin (hi.2 ▸ hI_sub hi.1)⟩
          simp [yPrefix]
        have hblock_uI : ∀ i ∈ blockOf uI a_last, edge i j = false := by
          intro i hi
          simp only [blockOf, uI, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_image, Prod.mk.injEq] at hi
          rcases hi with h1 | ⟨i', hi', hi_eq⟩
          · simp [yPrefix] at h1
          · rw [← hi_eq]; exact hI_j i' hi'
        have hf_last : f (query c x j a_last) (a_last, j) = false := by simpa [P] using ha_last
        have hpack_final : packOf f ((∑ a ∈ Finset.univ.filter (fun a : Fin r => a.val < a_last.val),
              alphaOf edge (blockOf (yPrefix c a_last.val) a)) +
            (Finset.univ.filter (fun a : Fin r => a.val < a_last.val ∧ P c a = true ∧ c a = false)).card +
            alphaOf edge x + 1) (query c x j a_last) :=
          ⟨uI, query c x j a_last, (a_last, j), hstepI, huI_sub_q, Finset.Subset.refl _,
            h_indep' uI a_last j ⟨hnotmem, hblock_uI⟩, hf_last⟩

        have hsum_q : ∑ a : Fin r, alphaOf edge (blockOf (query c x j a_last) a) =
            (∑ a ∈ Finset.univ.filter (fun a : Fin r => a.val < a_last.val),
              alphaOf edge (blockOf (yPrefix c a_last.val) a)) + alphaOf edge x := by
          have hblock_lt : ∀ a : Fin r, a < a_last →
              blockOf (query c x j a_last) a = blockOf (yPrefix c a_last.val) a := by
            intro a ha
            ext i; simp only [blockOf, query, yPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
            have hne : a ≠ a_last := ne_of_lt ha
            simp [ha, hne, Fin.lt_def.mp ha]
          have hblock_eq : blockOf (query c x j a_last) a_last = x := by
            ext i; simp [blockOf, query]
          have hblock_gt : ∀ a : Fin r, a_last < a → blockOf (query c x j a_last) a = ∅ := by
            intro a ha
            ext i; simp only [blockOf, query, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false]
            have h1 : ¬ (a < a_last) := not_lt.mpr (le_of_lt ha)
            have h2 : a ≠ a_last := ne_of_gt ha
            simp [h1, h2]
          have hsplit : (Finset.univ : Finset (Fin r)) =
              insert a_last (Finset.univ.filter (fun a : Fin r => a.val < a_last.val)) ∪
              Finset.univ.filter (fun a : Fin r => a_last < a) := by
            ext a; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_insert, Finset.mem_filter,
              true_and, true_iff, Fin.lt_def]
            omega
          have hdisj : Disjoint (insert a_last (Finset.univ.filter (fun a : Fin r => a.val < a_last.val)))
              (Finset.univ.filter (fun a : Fin r => a_last < a)) := by
            rw [Finset.disjoint_left]
            intro a ha1 ha2
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha1 ha2
            omega
          have hna : a_last ∉ Finset.univ.filter (fun a : Fin r => a.val < a_last.val) := by simp
          conv_lhs => rw [hsplit]
          rw [Finset.sum_union hdisj, Finset.sum_insert hna]
          have hzero : ∑ a ∈ Finset.univ.filter (fun a : Fin r => a_last < a),
              alphaOf edge (blockOf (query c x j a_last) a) = 0 := by
            apply Finset.sum_eq_zero
            intro a ha
            rw [hblock_gt a (by simpa using ha), alphaOf_empty]
          rw [hzero, add_zero, hblock_eq, add_comm]
          apply congrArg (· + alphaOf edge x)
          apply Finset.sum_congr rfl
          intro a ha
          rw [hblock_lt a (Fin.lt_def.mpr (by simpa using ha))]
        have hnop := h_nopack' (query c x j a_last)
        rw [hsum_q] at hnop
        by_contra hge
        have hge' : e ≤ (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true ∧ c a = false)).card :=
          Nat.le_of_not_lt hge
        have hcard_eq : (Finset.univ.filter (fun a : Fin r => a.val < a_last.val ∧ P c a = true ∧ c a = false)).card =
            (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true ∧ c a = false)).card := rfl

        have hpack_down : ∀ {m₁ m₂ : ℕ} {y : Finset (Fin r × Fin n)},
            m₁ ≤ m₂ → packOf f m₂ y → packOf f m₁ y := by
          intro m₁ m₂
          induction m₂ generalizing m₁ with
          | zero => intro y hle _; cases Nat.eq_zero_of_le_zero hle; trivial
          | succ m₂ ih =>
            intro y hle hp
            rcases Nat.eq_or_lt_of_le hle with rfl | hlt
            · exact hp
            · rcases hp with ⟨u, v, k, hpu, huv, hvy, _, _⟩
              exact packOf_mono f (ih (by omega) hpu) (huv.trans hvy)
        exact hnop (hpack_down (by omega) hpack_final)
      calc (Finset.univ.filter (fun c : Fin r → Bool => vote c x j ≠ gain x j)).card * 2 ^ s
          ≤ (Finset.univ.filter (PrefixFew s e false P)).card * 2 ^ s :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub_pf)
        _ ≤ (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ r :=
            card_prefixFew_le r s e false P hP_causal
    ·
      have hα_eq : alphaOf edge (insert j x) = alphaOf edge x := by
        have hne : alphaOf edge (insert j x) ≠ alphaOf edge x + 1 := by simpa [hgain_eq] using hgain
        have hle := alphaOf_insert_le edge x j
        have hge := alphaOf_mono edge (Finset.subset_insert j x)
        omega
      obtain ⟨I, hI_sub, hI_ind, hI_card⟩ := exists_max_indep edge x
      let P : (Fin r → Bool) → Fin r → Bool := fun c a => f (query c x j a) (a, j)
      have hP_causal : Causal P := by
        intro c₁ c₂ a hc; simp only [P, hq_causal c₁ c₂ a hc]
      have hsub_pf : Finset.univ.filter (fun c : Fin r → Bool => vote c x j ≠ gain x j) ⊆
          Finset.univ.filter (PrefixFew s e true P) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        have hv_true : vote c x j = true := by
          have hg_f : gain x j = false := by cases hg : gain x j <;> simp_all
          rw [hg_f] at hc; cases hv : vote c x j <;> simp_all
        have hlt_hits : s < (Finset.univ.filter (fun a : Fin r => P c a = true)).card := by
          convert (by simpa [vote, P] using hv_true)
        apply prefixFew_of_hits s e true P c hlt_hits
        intro a_last ha_last _
        have hpack_prefix : ∀ k ≤ r,
            packOf f (k * alphaOf edge x +
              (Finset.univ.filter (fun a : Fin r => a.val < k ∧ P c a = true ∧ c a = true)).card) (yPrefix c k) := by
          intro k hk
          induction k with
          | zero => simp [packOf]
          | succ k ih =>
            have hk' : k < r := by omega
            let a : Fin r := ⟨k, hk'⟩
            have hih := ih (by omega)
            have hcard_split :
                (Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = true)).card =
                (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = true)).card +
                (if P c a = true ∧ c a = true then 1 else 0) := by
              by_cases hpa : P c a = true ∧ c a = true
              · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = true) =
                    insert a (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = true)) := by
                  ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, a]
                  constructor
                  · rintro ⟨hlt, h2⟩
                    by_cases hbk : b.val = k
                    · exact Or.inl hbk
                    · exact Or.inr ⟨by omega, h2⟩
                  · rintro (rfl | ⟨hlt, h2⟩)
                    · exact ⟨Nat.lt_succ_self _, hpa⟩
                    · exact ⟨by omega, h2⟩
                have hna : a ∉ Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = true) := by
                  simp [a]
                rw [hfilt, Finset.card_insert_of_notMem hna, if_pos hpa]
              · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ P c b = true ∧ c b = true) =
                    Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = true) := by
                  ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · rintro ⟨hlt, h2⟩
                    by_cases hbk : b.val = k
                    · have hba : b = a := Fin.ext hbk
                      exact absurd (hba ▸ h2) hpa
                    · exact ⟨by omega, h2⟩
                  · rintro ⟨hlt, h2⟩; exact ⟨by omega, h2⟩
                rw [hfilt, if_neg hpa, add_zero]
            rw [hcard_split]
            have hstepI := packOf_indep edge f h_indep' h_in a (yPrefix c k) (hyPrefix_block_ge c k a (le_refl _)) I hI_ind hih
            rw [hI_card] at hstepI
            have huI_sub_q : yPrefix c k ∪ I.image (fun i => (a, i)) ⊆ query c x j a := by
              intro ⟨p1, p2⟩ hp
              simp only [Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hp
              rcases hp with hp | ⟨i, hi, rfl, rfl⟩
              · exact hyPrefix_sub_query c a hp
              · simp [query, hI_sub hi]
            have hpack_q := packOf_mono f hstepI huI_sub_q
            by_cases hpa : P c a = true ∧ c a = true
            · rw [if_pos hpa]
              have hsub_next : insert (a, j) (query c x j a) ⊆ yPrefix c (k + 1) := by
                intro p hp
                rcases Finset.mem_insert.mp hp with rfl | hp'
                · simp [yPrefix, a, hpa.2]
                · exact hquery_sub_yPrefix c a hp'
              have hpack_plus : packOf f (k * alphaOf edge x +
                  (Finset.univ.filter (fun b : Fin r => b.val < k ∧ P c b = true ∧ c b = true)).card +
                  alphaOf edge x + 1) (yPrefix c (k + 1)) :=
                ⟨query c x j a, insert (a, j) (query c x j a), (a, j), hpack_q,
                  Finset.subset_insert _ _, hsub_next, hpa.1,
                  h_in (insert (a, j) (query c x j a)) a j (Finset.mem_insert_self _ _)⟩
              convert hpack_plus using 1; ring
            · rw [if_neg hpa, add_zero]
              have hpack_same := packOf_mono f hpack_q (hquery_sub_yPrefix c a)
              convert hpack_same using 1; ring
        have hpref := hpack_prefix a_last.val (le_of_lt a_last.isLt)
        have hstepI := packOf_indep edge f h_indep' h_in a_last (yPrefix c a_last.val)
          (hyPrefix_block_ge c a_last.val a_last (le_refl _)) I hI_ind hpref
        rw [hI_card] at hstepI
        have huI_sub_q : yPrefix c a_last.val ∪ I.image (fun i => (a_last, i)) ⊆ query c x j a_last := by
          intro ⟨p1, p2⟩ hp
          simp only [Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hp
          rcases hp with hp | ⟨i, hi, rfl, rfl⟩
          · exact hyPrefix_sub_query c a_last hp
          · simp [query, hI_sub hi]
        have hpack_q := packOf_mono f hstepI huI_sub_q
        let yFin := insert (a_last, j) (query c x j a_last)
        have hpack_final : packOf f (a_last.val * alphaOf edge x +
            (Finset.univ.filter (fun a : Fin r => a.val < a_last.val ∧ P c a = true ∧ c a = true)).card +
            alphaOf edge x + 1) yFin :=
          ⟨query c x j a_last, yFin, (a_last, j), hpack_q, Finset.subset_insert _ _,
            Finset.Subset.refl _, ha_last, h_in yFin a_last j (Finset.mem_insert_self _ _)⟩
        have hsum_yFin : ∑ a : Fin r, alphaOf edge (blockOf yFin a) = (a_last.val + 1) * alphaOf edge x := by
          have hblock_le : ∀ a : Fin r, a ≤ a_last → alphaOf edge (blockOf yFin a) = alphaOf edge x := by
            intro a ha
            by_cases hlt : a < a_last
            · by_cases hca : c a = true
              · have hb : blockOf yFin a = insert j x := by
                  ext i; simp only [blockOf, yFin, query, Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_insert, Prod.mk.injEq]
                  have hne : a ≠ a_last := ne_of_lt hlt
                  simp [hlt, hne, hca]; tauto
                rw [hb, hα_eq]
              · have hb : blockOf yFin a = x := by
                  ext i; simp only [blockOf, yFin, query, Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_insert, Prod.mk.injEq]
                  have hne : a ≠ a_last := ne_of_lt hlt
                  simp [hlt, hne, hca]
                rw [hb]
            · have heq : a = a_last := le_antisymm ha (not_lt.mp hlt)
              subst heq
              have hb : blockOf yFin a = insert j x := by
                ext i; simp only [blockOf, yFin, query, Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_insert, Prod.mk.injEq]
                simp
              rw [hb, hα_eq]
          have hblock_gt : ∀ a : Fin r, a_last < a → blockOf yFin a = ∅ := by
            intro a ha
            ext i; simp only [blockOf, yFin, query, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert, Prod.mk.injEq, Finset.notMem_empty, iff_false]
            have h1 : ¬ (a < a_last) := not_lt.mpr (le_of_lt ha)
            have h2 : a ≠ a_last := ne_of_gt ha
            simp [h1, h2]
          have hsplit : (Finset.univ : Finset (Fin r)) =
              Finset.univ.filter (fun a : Fin r => a ≤ a_last) ∪
              Finset.univ.filter (fun a : Fin r => a_last < a) := by
            ext a; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            exact le_or_gt a a_last
          have hdisj : Disjoint (Finset.univ.filter (fun a : Fin r => a ≤ a_last))
              (Finset.univ.filter (fun a : Fin r => a_last < a)) := by
            rw [Finset.disjoint_left]
            intro a h1 h2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            exact not_lt.mpr h1 h2
          conv_lhs => rw [hsplit]
          rw [Finset.sum_union hdisj]
          have hzero : ∑ a ∈ Finset.univ.filter (fun a : Fin r => a_last < a),
              alphaOf edge (blockOf yFin a) = 0 := by
            apply Finset.sum_eq_zero; intro a ha; rw [hblock_gt a (by simpa using ha), alphaOf_empty]
          rw [hzero, add_zero]
          have hsum_const : ∑ a ∈ Finset.univ.filter (fun a : Fin r => a ≤ a_last),
              alphaOf edge (blockOf yFin a) =
              (Finset.univ.filter (fun a : Fin r => a ≤ a_last)).card * alphaOf edge x := by
            rw [Finset.sum_congr rfl (fun a ha => hblock_le a (by simpa using ha)), Finset.sum_const, smul_eq_mul]
          rw [hsum_const]
          have hcard_le : (Finset.univ.filter (fun a : Fin r => a ≤ a_last)).card = a_last.val + 1 := by
            have hIic : Finset.univ.filter (fun a : Fin r => a ≤ a_last) = Finset.Iic a_last := by
              ext a; simp
            rw [hIic, Fin.card_Iic]
          rw [hcard_le]
        have hnop := h_nopack' yFin
        rw [hsum_yFin] at hnop
        by_contra hge
        have hge' : e ≤ (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true ∧ c a = true)).card :=
          Nat.le_of_not_lt hge
        have hpack_down : ∀ {m₁ m₂ : ℕ} {y : Finset (Fin r × Fin n)},
            m₁ ≤ m₂ → packOf f m₂ y → packOf f m₁ y := by
          intro m₁ m₂
          induction m₂ generalizing m₁ with
          | zero => intro y hle _; cases Nat.eq_zero_of_le_zero hle; trivial
          | succ m₂ ih =>
            intro y hle hp
            rcases Nat.eq_or_lt_of_le hle with rfl | hlt
            · exact hp
            · rcases hp with ⟨u, v, k, hpu, huv, hvy, _, _⟩
              exact packOf_mono f (ih (by omega) hpu) (huv.trans hvy)
        have hcard_eq : (Finset.univ.filter (fun a : Fin r => a.val < a_last.val ∧ P c a = true ∧ c a = true)).card =
            (Finset.univ.filter (fun a : Fin r => a < a_last ∧ P c a = true ∧ c a = true)).card := rfl
        exact hnop (hpack_down (by
          have h1 : (a_last.val + 1) * alphaOf edge x = a_last.val * alphaOf edge x + alphaOf edge x := by ring
          omega) hpack_final)
      calc (Finset.univ.filter (fun c : Fin r → Bool => vote c x j ≠ gain x j)).card * 2 ^ s
          ≤ (Finset.univ.filter (PrefixFew s e true P)).card * 2 ^ s :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub_pf)
        _ ≤ (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ r :=
            card_prefixFew_le r s e true P hP_causal

  have hex_c : ∃ c : Fin r → Bool, ∀ x j, vote c x j = gain x j := by
    let BadAll : Finset (Fin r → Bool) :=
      (Finset.univ : Finset (Finset (Fin n) × Fin n)).biUnion
        (fun p => Finset.univ.filter (fun c : Fin r → Bool => vote c p.1 p.2 ≠ gain p.1 p.2))
    have hcard_lt : BadAll.card < (Finset.univ : Finset (Fin r → Bool)).card := by
      have h1 : BadAll.card * 2 ^ s < (2 ^ r) * 2 ^ s := by
        calc BadAll.card * 2 ^ s
            ≤ (∑ p : Finset (Fin n) × Fin n,
                (Finset.univ.filter (fun c : Fin r → Bool => vote c p.1 p.2 ≠ gain p.1 p.2)).card) * 2 ^ s :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ p : Finset (Fin n) × Fin n,
                (Finset.univ.filter (fun c : Fin r → Bool => vote c p.1 p.2 ≠ gain p.1 p.2)).card * 2 ^ s :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ _p : Finset (Fin n) × Fin n, (∑ i ∈ Finset.range e, Nat.choose s i) * 2 ^ r :=
              Finset.sum_le_sum (fun p _ => hbad_card p.1 p.2)
          _ = (n * 2 ^ n * (∑ i ∈ Finset.range e, Nat.choose s i)) * 2 ^ r := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
                Fintype.card_finset, smul_eq_mul]
              ring
          _ < 2 ^ s * 2 ^ r := Nat.mul_lt_mul_of_pos_right hcount (by positivity)
          _ = 2 ^ r * 2 ^ s := by ring
      have h2 : BadAll.card < 2 ^ r := Nat.lt_of_mul_lt_mul_right h1
      simpa using h2
    have hne : (Finset.univ \ BadAll).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : (Finset.univ : Finset (Fin r → Bool)) ⊆ BadAll := Finset.sdiff_eq_empty_iff_subset.mp hemp
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨c, hc⟩ := hne
    rw [Finset.mem_sdiff] at hc
    refine ⟨c, fun x j => ?_⟩
    by_contra hne_v
    apply hc.2
    rw [Finset.mem_biUnion]
    exact ⟨(x, j), Finset.mem_univ _, by simp [hne_v]⟩
  obtain ⟨c, hc_good⟩ := hex_c
  refine ⟨c, hc_good, ?_⟩

  intro j
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h0 => Fin.elim0 (h0 ▸ j))

  let inMap : Fin r → ℕ → ℕ := fun a w =>
    if w < r * n then
      let p1 := w / n
      let p2 := w % n
      if hp1 : p1 < a.val then
        if c ⟨p1, by omega⟩ = true ∧ p2 = j.val then n + 1 else p2
      else if p1 = a.val then p2
      else n
    else if w = r * n then n
    else n + 1
  have hinMap_lt : ∀ (a : Fin r) (w : ℕ), w < r * n + 2 → inMap a w < n + 2 := by
    intro a w _
    simp only [inMap]
    split_ifs with h1 h2 h3 h4 h5
    · omega
    · have := Nat.mod_lt w hn_pos; omega
    · have := Nat.mod_lt w hn_pos; omega
    · omega
    · omega
    · omega

  have hinMap_val : ∀ (a : Fin r) (x : Finset (Fin n)) (w : ℕ), w < r * n + 2 →
      (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]).getD (inMap a w) false =
      ((List.ofFn (fun b : Fin r => List.ofFn (fun i : Fin n => decide ((b, i) ∈ query c x j a)))).flatten ++ [false, true]).getD w false := by
    intro a x w hw
    have hflat_len : ((List.ofFn (fun b : Fin r => List.ofFn (fun i : Fin n => decide ((b, i) ∈ query c x j a)))).flatten).length = r * n := by
      simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
        List.length_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hflat_get : ∀ (b : Fin r) (i : Fin n),
        ((List.ofFn (fun b : Fin r => List.ofFn (fun i : Fin n => decide ((b, i) ∈ query c x j a)))).flatten).getD (b.val * n + i.val) false =
        decide ((b, i) ∈ query c x j a) := by
      intro b i
      have hgen : ∀ (m : ℕ) (g : Fin m → Fin n → Bool) (b : Fin m) (i : Fin n),
          ((List.ofFn (fun b : Fin m => List.ofFn (fun i : Fin n => g b i))).flatten).getD (b.val * n + i.val) false = g b i := by
        intro m
        induction m with
        | zero => intro _ b; exact Fin.elim0 b
        | succ m ih =>
          intro g b i
          rw [List.ofFn_succ, List.flatten_cons]
          cases b using Fin.cases with
          | zero =>
            simp only [Fin.val_zero, zero_mul, zero_add, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left (by simp)]
            simp
          | succ b' =>
            simp only [Fin.val_succ, add_mul, one_mul, List.getD_eq_getElem?_getD]
            have hge : (List.ofFn (fun i : Fin n => g 0 i)).length ≤ b'.val * n + n + i.val := by
              simp; omega
            rw [List.getElem?_append_right hge]
            simp only [List.length_ofFn]
            have hsub : b'.val * n + n + i.val - n = b'.val * n + i.val := by omega
            rw [hsub, ← List.getD_eq_getElem?_getD]
            exact ih (fun b'' => g b''.succ) b' i
      exact hgen r (fun b i => decide ((b, i) ∈ query c x j a)) b i
    have hxin_len : (List.ofFn (fun i : Fin n => decide (i ∈ x))).length = n := by simp
    have hxin_get : ∀ (k : ℕ) (hk : k < n),
        (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]).getD k false = decide (⟨k, hk⟩ ∈ x) := by
      intro k hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hk])]
      simp [hk]
    have hxin_n : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]).getD n false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), hxin_len]; simp
    have hxin_n1 : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]).getD (n + 1) false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), hxin_len]; simp
    by_cases hw_lt : w < r * n
    · have hp1_lt : w / n < r := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      have hp2_lt : w % n < n := Nat.mod_lt w hn_pos
      let p1 : Fin r := ⟨w / n, hp1_lt⟩
      let p2 : Fin n := ⟨w % n, hp2_lt⟩
      have hw_eq : w = p1.val * n + p2.val := by
        simp only [p1, p2]; linarith [Nat.div_add_mod w n, mul_comm n (w / n)]
      have hRHS : ((List.ofFn (fun b : Fin r => List.ofFn (fun i : Fin n => decide ((b, i) ∈ query c x j a)))).flatten ++ [false, true]).getD w false =
          decide ((p1, p2) ∈ query c x j a) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, hw_eq]
        exact hflat_get p1 p2
      rw [hRHS]
      simp only [inMap, if_pos hw_lt]
      split_ifs with h1 h2 h3
      · rw [hxin_n1]
        have hmem : (p1, p2) ∈ query c x j a := by
          simp only [query, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl ⟨h1, Or.inr ⟨h2.1, Fin.ext h2.2⟩⟩
        simp [hmem]
      · rw [hxin_get (w % n) hp2_lt]
        have hiff : (p1, p2) ∈ query c x j a ↔ p2 ∈ x := by
          simp only [query, Finset.mem_filter, Finset.mem_univ, true_and]
          have hne : p1 ≠ a := Fin.ne_of_lt h1
          have hnot : ¬ (c p1 = true ∧ p2 = j) := by
            rintro ⟨hc1, hp2j⟩; exact h2 ⟨hc1, by simpa [p2] using congrArg Fin.val hp2j⟩
          simp [show p1 < a from h1, hne, hnot]
        simp [hiff, p2]
      · rw [hxin_get (w % n) hp2_lt]
        have heq : p1 = a := Fin.ext h3
        have hiff : (p1, p2) ∈ query c x j a ↔ p2 ∈ x := by
          simp [query, heq]
        simp [hiff, p2]
      · rw [hxin_n]
        have hnotmem : (p1, p2) ∉ query c x j a := by
          simp only [query, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and]
          exact ⟨fun hlt => absurd hlt h1, fun heq => absurd (congrArg Fin.val heq) h3⟩
        simp [hnotmem]
    · by_cases hwrn : w = r * n
      · subst hwrn
        simp only [inMap, if_neg hw_lt, ↓reduceIte]
        rw [hxin_n, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hflat_len]
        simp
      · have hwrn1 : w = r * n + 1 := by omega
        subst hwrn1
        simp only [inMap, if_neg hw_lt, if_neg hwrn]
        rw [hxin_n1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hflat_len]
        simp

  have hbuild : ∀ k ≤ r,
      ∃ (gs : List Gate) (T : Fin (s + 1) → ℕ),
        FanInTwo ⟨gs, 0⟩ ∧
        ReadsBack (n + 2) ⟨gs, 0⟩ ∧
        gs.length = k * (C.size + 2 * (s + 1)) ∧
        notCount ⟨gs, 0⟩ = k * notCount C ∧
        (∀ m : Fin (s + 1), T m < n + 2 + gs.length) ∧
        (∀ (x : Finset (Fin n)) (m : Fin (s + 1)),
          (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD (T m) false =
          decide (m.val + 1 ≤ (Finset.univ.filter (fun a : Fin r => a.val < k ∧ f (query c x j a) (a, j) = true)).card)) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨[], fun _ => n, ?_, ?_, by simp, by simp [notCount], ?_, ?_⟩
      · intro g hg; simp at hg
      · intro j hj; simp at hj
      · intro m; simp
      · intro x m
        simp only [Circuit.wires, List.foldl_nil, Nat.not_lt_zero, false_and, Finset.filter_false,
          Finset.card_empty, Nat.not_succ_le_zero, decide_false]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
    | succ k ih =>
      have hk' : k < r := by omega
      let a : Fin r := ⟨k, hk'⟩
      obtain ⟨gs, T, hF_gs, hRB_gs, hlen_gs, hnot_gs, hT_lt, hT_val⟩ := ih (by omega)
      let baseC := n + 2 + gs.length
      let copyG := remapGates (r * n + 2) (inMap a) baseC C.gates
      let wVote := remapWire (r * n + 2) (inMap a) baseC (tap (a, j)).val
      let baseV := n + 2 + (gs ++ copyG).length
      let voteG := voteStepGates s (n + 1) wVote baseV T
      let gs' := (gs ++ copyG) ++ voteG
      let T' := voteStepNext s baseV
      have hcopy_len : copyG.length = C.size := remapGates_length _ _ _ _
      have hvote_len : voteG.length = 2 * (s + 1) := voteStepGates_length _ _ _ _ _
      have hwVote_lt : wVote < baseV := by
        simp only [wVote, remapWire, baseV, List.length_append, hcopy_len, baseC]
        split_ifs with hlt
        · have := hinMap_lt a (tap (a, j)).val hlt; omega
        · have := (tap (a, j)).isLt; omega
      have hF_copy : FanInTwo ⟨copyG, 0⟩ := remapGates_fanInTwo hFan 0
      have hF_vote : FanInTwo ⟨voteG, 0⟩ := voteStepGates_fanInTwo _ _ _ _ _ 0
      have hF' : FanInTwo ⟨gs', 0⟩ := fanInTwo_append (o₁ := 0) (fanInTwo_append (o := 0) hF_gs hF_copy) hF_vote
      have hRB_mid : ReadsBack (n + 2) ⟨gs ++ copyG, 0⟩ :=
        readsBack_append hRB_gs (remapGates_readsBack hRB (fun w hw =>
          lt_of_lt_of_le (hinMap_lt a w hw) (Nat.le_add_right _ _)))
      have hRB' : ReadsBack (n + 2) ⟨gs', 0⟩ :=
        readsBack_append hRB_mid (voteStepGates_readsBack
          (by omega) hwVote_lt (fun m => lt_of_lt_of_le (hT_lt m) (by simp)))
      have hlen' : gs'.length = (k + 1) * (C.size + 2 * (s + 1)) := by
        simp only [gs', List.length_append, hlen_gs, hcopy_len, hvote_len]; ring
      have hnot' : notCount ⟨gs', 0⟩ = (k + 1) * notCount C := by
        rw [notCount_append (gs ++ copyG) voteG 0 0 0, notCount_append gs copyG 0 0 0,
          hnot_gs, remapGates_notCount, voteStepGates_notCount]
        have hnc : notCount ⟨C.gates, 0⟩ = notCount C := rfl
        rw [hnc]
        simp [add_mul]
      have hT'_lt : ∀ m : Fin (s + 1), T' m < n + 2 + gs'.length := by
        intro m
        simp only [T', voteStepNext, gs', List.length_append, hvote_len, baseV]
        omega
      refine ⟨gs', T', hF', hRB', hlen', hnot', hT'_lt, ?_⟩
      intro x m
      let xD := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
      have hxD_len : xD.length = n + 2 := by simp [xD]
      have hbaseC_eq : xD.length + gs.length = baseC := by rw [hxD_len]
      have hbaseV_eq : xD.length + (gs ++ copyG).length = baseV := by rw [hxD_len]
      let xC := (List.ofFn (fun b : Fin r => List.ofFn (fun i : Fin n => decide ((b, i) ∈ query c x j a)))).flatten ++ [false, true]
      have hxC_len : xC.length = r * n + 2 := by
        simp only [xC, List.length_append, List.length_flatten, List.map_ofFn, List.sum_ofFn,
          Function.comp_def, List.length_ofFn, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, List.length_cons, List.length_nil]
      have hwVote_val : (Circuit.wires ⟨gs ++ copyG, 0⟩ xD).getD wVote false = f (query c x j a) (a, j) := by
        have hrem := remapGates_eval gs C xD xC hxC_len hRB
          (fun w hw => by rw [hxD_len]; exact lt_of_lt_of_le (hinMap_lt a w hw) (Nat.le_add_right _ _))
          (fun w hw => by
            have h1 : (Circuit.wires ⟨gs, 0⟩ xD).getD (inMap a w) false = xD.getD (inMap a w) false := by
              have hlt : inMap a w < xD.length + ([] : List Gate).length := by
                rw [hxD_len]; simpa using hinMap_lt a w hw
              simpa [Circuit.wires] using wires_getD_append_left [] gs xD hlt
            rw [h1]
            exact hinMap_val a x w hw)
          (tap (a, j)).val (tap (a, j)).isLt
        have hxC_eq : xC = input (query c x j a) := by
          simp only [xC, input]
          apply congrArg (· ++ [false, true])
          apply congrArg List.flatten
          apply congrArg List.ofFn
          funext b
          apply congrArg List.ofFn
          funext i
          apply Bool.eq_iff_iff.mpr; simp
        rw [hxC_eq] at hrem
        simpa [copyG, wVote, hbaseC_eq, f] using hrem
      have hwTrue_val : (Circuit.wires ⟨gs ++ copyG, 0⟩ xD).getD (n + 1) false = true := by
        have hlt : n + 1 < xD.length + ([] : List Gate).length := by rw [hxD_len]; simp
        have h1 := wires_getD_append_left [] (gs ++ copyG) xD hlt
        simp only [List.nil_append] at h1
        rw [h1]
        change xD.getD (n + 1) false = true
        rw [List.getD_eq_getElem?_getD]
        simp only [xD]
        rw [List.getElem?_append_right (by simp)]
        simp
      have hT_mid : ∀ m' : Fin (s + 1),
          (Circuit.wires ⟨gs ++ copyG, 0⟩ xD).getD (T m') false =
          (Circuit.wires ⟨gs, 0⟩ xD).getD (T m') false := by
        intro m'
        exact wires_getD_append_left gs copyG xD (by rw [hxD_len]; exact hT_lt m')
      have heval := voteStepGates_eval (gs ++ copyG) xD T
        (by rw [hxD_len]; omega)
        (by rw [hbaseV_eq]; exact hwVote_lt)
        (fun m' => by rw [hxD_len]; simp; have := hT_lt m'; omega)
        hwTrue_val m
      rw [hbaseV_eq] at heval
      change (Circuit.wires ⟨(gs ++ copyG) ++ voteG, 0⟩ xD).getD (T' m) false = _
      rw [heval, hT_mid m, hT_val x m, hwVote_val]

      let cntK := (Finset.univ.filter (fun b : Fin r => b.val < k ∧ f (query c x j b) (b, j) = true)).card
      let cntK1 := (Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ f (query c x j b) (b, j) = true)).card
      have hcnt : cntK1 = cntK + (if f (query c x j a) (a, j) = true then 1 else 0) := by
        by_cases hfa : f (query c x j a) (a, j) = true
        · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ f (query c x j b) (b, j) = true) =
              insert a (Finset.univ.filter (fun b : Fin r => b.val < k ∧ f (query c x j b) (b, j) = true)) := by
            ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, a]
            constructor
            · rintro ⟨hlt, h2⟩
              by_cases hbk : b.val = k
              · exact Or.inl hbk
              · exact Or.inr ⟨by omega, h2⟩
            · rintro (rfl | ⟨hlt, h2⟩)
              · exact ⟨Nat.lt_succ_self _, hfa⟩
              · exact ⟨by omega, h2⟩
          have hna : a ∉ Finset.univ.filter (fun b : Fin r => b.val < k ∧ f (query c x j b) (b, j) = true) := by
            simp [a]
          simp only [cntK1, cntK, hfilt, Finset.card_insert_of_notMem hna, if_pos hfa]
        · have hfilt : Finset.univ.filter (fun b : Fin r => b.val < k + 1 ∧ f (query c x j b) (b, j) = true) =
              Finset.univ.filter (fun b : Fin r => b.val < k ∧ f (query c x j b) (b, j) = true) := by
            ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, h2⟩
              by_cases hbk : b.val = k
              · exact absurd ((Fin.ext hbk : b = a) ▸ h2) hfa
              · exact ⟨by omega, h2⟩
            · rintro ⟨hlt, h2⟩; exact ⟨by omega, h2⟩
          simp only [cntK1, cntK, hfilt, if_neg hfa, add_zero]
      change (decide (m.val + 1 ≤ cntK) ||
        ((if hk0 : m.val = 0 then true else (Circuit.wires ⟨gs ++ copyG, 0⟩ xD).getD (T ⟨m.val - 1, by omega⟩) false) &&
          f (query c x j a) (a, j))) = decide (m.val + 1 ≤ cntK1)
      split_ifs with hm0
      · cases hfa : f (query c x j a) (a, j) <;> simp [hcnt, hfa, hm0] <;> omega
      · rw [hT_mid ⟨m.val - 1, by omega⟩, hT_val x ⟨m.val - 1, by omega⟩]
        have hm_sub : m.val - 1 + 1 = m.val := by omega
        rw [hm_sub]
        change (decide (m.val + 1 ≤ cntK) || (decide (m.val ≤ cntK) && f (query c x j a) (a, j))) =
          decide (m.val + 1 ≤ cntK1)
        cases hfa : f (query c x j a) (a, j)
        · simp [hcnt, hfa]
        · simp only [hcnt, hfa, ↓reduceIte, Bool.and_true]
          by_cases hle : m.val + 1 ≤ cntK
          · simp [hle, show m.val + 1 ≤ cntK + 1 by omega]
          · by_cases hle' : m.val ≤ cntK
            · simp [hle, hle', show m.val + 1 ≤ cntK + 1 by omega]
            · simp [hle, hle', show ¬ (m.val + 1 ≤ cntK + 1) by omega]
  obtain ⟨gs, T, hF, hRB_D, hlen, hnot, hT_lt, hT_val⟩ := hbuild r (le_refl r)
  let D : Circuit := ⟨gs, T ⟨s, Nat.lt_succ_self s⟩⟩
  refine ⟨D, hF, hRB_D, hT_lt ⟨s, Nat.lt_succ_self s⟩, by simp [D, Circuit.size, hlen],
    le_of_eq hnot, ?_⟩
  intro x
  have h1 := hT_val x ⟨s, Nat.lt_succ_self s⟩
  have hfilt : Finset.univ.filter (fun a : Fin r => a.val < r ∧ f (query c x j a) (a, j) = true) =
      Finset.univ.filter (fun a : Fin r => f (query c x j a) (a, j) = true) := by
    ext a; simp
  rw [hfilt] at h1
  have hxin_eq : List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) ++ [false, true] =
      List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true] := by
    congr 2; funext i; apply Bool.eq_iff_iff.mpr; simp
  change (Circuit.wires ⟨gs, 0⟩ _).getD (T ⟨s, Nat.lt_succ_self s⟩) false = vote c x j
  rw [hxin_eq, h1]
  apply Bool.eq_iff_iff.mpr
  simp only [vote, decide_eq_true_eq]
  have hceq : (Finset.univ.filter (fun a : Fin r => f (query c x j a) (a, j) = true)).card =
      (@Finset.filter (Fin r) (fun a : Fin r => f (query c x j a) (a, j) = true)
        (fun a => Classical.propDecidable _) Finset.univ).card := by
    congr 1; ext a; simp
  rw [hceq]
  simp only [Nat.succ_le_iff]
