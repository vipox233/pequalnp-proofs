import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_883_aux

open Finset

def Wd {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin q)).filter (fun i => l < cap i)).card

def Ud {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ := ∑ i : Fin q, min (cap i) l

noncomputable def gd (k W : ℕ) : ℝ := ((W - 2 * k : ℕ) : ℝ) / (W : ℝ)

theorem Ud_succ {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : Ud cap (l + 1) = Ud cap l + Wd cap l := by
  unfold Ud Wd
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

theorem Ud_zero {q : ℕ} (cap : Fin q → ℕ) : Ud cap 0 = 0 := by
  simp [Ud]

theorem Ud_eq_sum {q : ℕ} (cap : Fin q → ℕ) (n : ℕ) :
    Ud cap n = ∑ l ∈ range n, Wd cap l := by
  induction n with
  | zero => simp [Ud_zero]
  | succ n ih => rw [Ud_succ, ih, Finset.sum_range_succ]

theorem Wd_anti {q : ℕ} (cap : Fin q → ℕ) {l l' : ℕ} (h : l ≤ l') : Wd cap l' ≤ Wd cap l := by
  unfold Wd
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem Ud_mono {q : ℕ} (cap : Fin q → ℕ) {l l' : ℕ} (h : l ≤ l') : Ud cap l ≤ Ud cap l' := by
  unfold Ud
  apply Finset.sum_le_sum
  intro i _
  omega

theorem greedy_prefix {q : ℕ} (cap : Fin q → ℕ) (E n : ℕ) :
    ∑ l ∈ range n, min (Wd cap l) (E - Ud cap l) = min E (Ud cap n) := by
  induction n with
  | zero => simp [Ud_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Ud_succ]
    omega

theorem gd_nonneg (k W : ℕ) : 0 ≤ gd k W := by
  unfold gd; positivity

theorem gd_mono (k : ℕ) {a b : ℕ} (h : b ≤ a) : gd k b ≤ gd k a := by
  unfold gd
  by_cases hb : b < 2 * k
  · rw [Nat.sub_eq_zero_of_le (le_of_lt hb)]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · rw [not_lt] at hb
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; simp only [Nat.cast_zero, div_zero]; positivity
    · have ha0 : 0 < a := lt_of_lt_of_le hb0 h
      have hab : 2 * k ≤ a := le_trans hb h
      rw [div_le_div_iff₀ (by exact_mod_cast hb0) (by exact_mod_cast ha0)]
      push_cast [Nat.cast_sub hb, Nat.cast_sub hab]
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      nlinarith

theorem gd_anti {q : ℕ} (cap : Fin q → ℕ) (k : ℕ) {l l' : ℕ} (h : l ≤ l') :
    gd k (Wd cap l') ≤ gd k (Wd cap l) :=
  gd_mono k (Wd_anti cap h)

theorem abel_nonneg (g d : ℕ → ℝ) (N : ℕ) (hg0 : ∀ l, 0 ≤ g l) (hg : ∀ l, g (l + 1) ≤ g l)
    (hP : ∀ n ≤ N, 0 ≤ ∑ l ∈ range n, d l) : 0 ≤ ∑ l ∈ range N, g l * d l := by
  have key : ∀ n ≤ N, g n * ∑ l ∈ range n, d l ≤ ∑ l ∈ range n, g l * d l := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hPn1 := hP (n + 1) hn
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at hPn1
      have h1 : g (n + 1) * (∑ l ∈ range n, d l + d n) ≤ g n * (∑ l ∈ range n, d l + d n) :=
        mul_le_mul_of_nonneg_right (hg n) hPn1
      nlinarith
  have := key N le_rfl
  have h0 := hP N le_rfl
  nlinarith [hg0 N]

theorem sum_layers (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    ∑ l ∈ range N, min (max (x - l) 0) 1 = min x N := by
  induction N with
  | zero => simp [hx]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    simp only [min_def, max_def]
    split_ifs <;> linarith

theorem layer_bound {q : ℕ} (S U : Finset (Fin q)) (k : ℕ) (v : Fin q → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hvS : ∀ i, i ∉ S → v i = 0) (hU : U.card = k)
    (dom : ∀ i ∈ U, ∀ j, j ∉ U → v j ≤ v i) :
    (∑ i, v i) - 2 * ∑ i ∈ U, v i ≤ gd k S.card * ∑ i, v i := by
  set t := ∑ i ∈ U, v i with ht
  set o := ∑ i ∈ Uᶜ, v i with ho
  have hsplit : (∑ i, v i) = t + o := (Finset.sum_add_sum_compl U v).symm
  have ht0 : 0 ≤ t := Finset.sum_nonneg (fun i _ => hv0 i)
  have ho0 : 0 ≤ o := Finset.sum_nonneg (fun i _ => hv0 i)

  have ho' : o = ∑ j ∈ S \ U, v j := by
    rw [ho]
    have hsub : S \ U ⊆ Uᶜ := by
      intro j hj; simp only [Finset.mem_sdiff] at hj; simpa using hj.2
    rw [← Finset.sum_subset hsub]
    intro j hj hjn
    apply hvS
    intro hjS
    apply hjn
    simp only [Finset.mem_sdiff]
    exact ⟨hjS, by simpa using hj⟩

  have hdc : (k : ℝ) * o ≤ ((S \ U).card : ℝ) * t := by
    rw [ho']
    have h1 : ∑ j ∈ S \ U, ∑ i ∈ U, v j ≤ ∑ j ∈ S \ U, ∑ i ∈ U, v i := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact dom i hi j (Finset.mem_sdiff.1 hj).2
    simp only [Finset.sum_const, nsmul_eq_mul, hU] at h1
    rw [Finset.mul_sum]
    exact h1

  have hcase : (U ⊆ S ∧ ((S \ U).card : ℝ) = (S.card : ℝ) - k) ∨ o = 0 := by
    by_cases hUS : U ⊆ S
    · left
      refine ⟨hUS, ?_⟩
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hUS, hU]
      have : k ≤ S.card := hU ▸ Finset.card_le_card hUS
      push_cast [this]
      ring
    · right
      rw [Finset.not_subset] at hUS
      obtain ⟨u, huU, huS⟩ := hUS
      have hu0 : v u = 0 := hvS u huS
      rw [ho]
      apply le_antisymm _ ho0
      calc ∑ i ∈ Uᶜ, v i ≤ ∑ i ∈ Uᶜ, (0 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have := dom u huU j (by simpa using hj)
            linarith
        _ = 0 := by simp
  have hkS : U ⊆ S → k ≤ S.card := fun h => hU ▸ Finset.card_le_card h
  rw [hsplit]
  unfold gd
  by_cases hW : 2 * k ≤ S.card
  · rcases Nat.eq_zero_or_pos S.card with hW0 | hW0
    ·
      have hk0 : k = 0 := by omega
      have hU0 : U = ∅ := Finset.card_eq_zero.1 (hU.trans hk0)
      have hS0 : S = ∅ := Finset.card_eq_zero.1 hW0
      have hall : ∀ i, v i = 0 := fun i => hvS i (by simp [hS0])
      have : t = 0 := by rw [ht]; simp [hall]
      have : o = 0 := by rw [ho]; simp [hall]
      simp [*]
    · have hWr : (0 : ℝ) < S.card := by exact_mod_cast hW0
      push_cast [Nat.cast_sub hW]
      rw [div_mul_eq_mul_div, le_div_iff₀ hWr]
      rcases hcase with ⟨hUS, hc⟩ | ho0'
      · rw [hc] at hdc
        nlinarith
      · rw [ho0']
        have : (k : ℝ) ≤ S.card := by exact_mod_cast (by omega : k ≤ S.card)
        nlinarith
  · rw [not_le] at hW
    rw [Nat.sub_eq_zero_of_le (le_of_lt hW)]
    simp only [Nat.cast_zero, zero_div, zero_mul]
    rcases hcase with ⟨hUS, hc⟩ | ho0'
    · rw [hc] at hdc
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hlt : (S.card : ℝ) - k ≤ k := by
        have : (S.card : ℝ) < 2 * k := by exact_mod_cast hW
        linarith
      nlinarith
    · rw [ho0']; linarith

noncomputable def gainD {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) : ℝ :=
  ∑ l ∈ Finset.range E,
    ((min (Wd cap l) (E - Ud cap l) * (Wd cap l - 2 * k) : ℕ) : ℝ) / (Wd cap l : ℝ)

theorem gainD_eq {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) :
    gainD k E cap = ∑ l ∈ range E,
      gd k (Wd cap l) * ((min (Wd cap l) (E - Ud cap l) : ℕ) : ℝ) := by
  unfold gainD gd
  apply Finset.sum_congr rfl
  intro l _
  push_cast
  ring

theorem part1 {q : ℕ} (k E : ℕ) (hk : k ≤ q) (cap : Fin q → ℕ) (w : Fin q → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (cap i : ℝ)) (hE : (∑ i, w i) ≤ (E : ℝ)) :
    ∃ U : Finset (Fin q), U.card = k ∧ (∑ i, w i) - 2 * ∑ i ∈ U, w i ≤ gainD k E cap := by

  obtain ⟨U, hUmem, hUmax⟩ := Finset.exists_max_image (Finset.powersetCard k Finset.univ)
    (fun U => ∑ i ∈ U, w i) (Finset.powersetCard_nonempty.2 (by simpa using hk))
  have hU : U.card = k := (Finset.mem_powersetCard.1 hUmem).2
  have dom : ∀ i ∈ U, ∀ j, j ∉ U → w j ≤ w i := by
    intro i hi j hj
    by_contra hlt
    rw [not_le] at hlt
    have hjE : j ∉ U.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hmem : insert j (U.erase i) ∈ Finset.powersetCard k Finset.univ := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hi, hU]
      have : 1 ≤ k := by rw [← hU]; exact Finset.card_pos.2 ⟨i, hi⟩
      omega
    have h1 := hUmax _ hmem
    rw [Finset.sum_insert hjE, Finset.sum_erase_eq_sub hi] at h1
    linarith
  refine ⟨U, hU, ?_⟩

  set v : ℕ → Fin q → ℝ := fun l i => min (max (w i - l) 0) 1 with hv
  have hwE : ∀ i, w i ≤ E := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => (hw j).1) (Finset.mem_univ i)) hE
  have hcol : ∀ i, ∑ l ∈ range E, v l i = w i := by
    intro i
    simp only [hv]
    rw [sum_layers (w i) (hw i).1 E, min_eq_left (hwE i)]
  have hv0 : ∀ l i, 0 ≤ v l i := fun l i => by
    simp only [hv]; exact le_min (le_max_right _ _) zero_le_one
  have hv1 : ∀ l i, v l i ≤ 1 := fun l i => by simp only [hv]; exact min_le_right _ _
  have hvS : ∀ l i, i ∉ (Finset.univ.filter (fun i => l < cap i)) → v l i = 0 := by
    intro l i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    have : w i - l ≤ 0 := by
      have := (hw i).2
      have : (cap i : ℝ) ≤ l := by exact_mod_cast hi
      linarith
    simp only [hv, max_eq_right this, min_eq_left zero_le_one]
  have hvdom : ∀ l, ∀ i ∈ U, ∀ j, j ∉ U → v l j ≤ v l i := by
    intro l i hi j hj
    simp only [hv]
    exact min_le_min_right _ (max_le_max_right _ (sub_le_sub_right (dom i hi j hj) _))
  set c : ℕ → ℝ := fun l => ∑ i, v l i with hc
  set t : ℕ → ℝ := fun l => ∑ i ∈ U, v l i with ht
  have htot : (∑ i, w i) = ∑ l ∈ range E, c l := by
    simp only [hc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => (hcol i).symm)
  have htotU : (∑ i ∈ U, w i) = ∑ l ∈ range E, t l := by
    simp only [ht]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => (hcol i).symm)
  have hlayer : ∀ l, c l - 2 * t l ≤ gd k (Wd cap l) * c l := fun l =>
    layer_bound _ U k (v l) (hv0 l) (hvS l) hU (hvdom l)
  have hcW : ∀ l, c l ≤ (Wd cap l : ℝ) := by
    intro l
    simp only [hc]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun i => l < cap i)))
      (fun i _ hi => hvS l i hi)]
    calc ∑ i ∈ Finset.univ.filter (fun i => l < cap i), v l i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => l < cap i), (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => hv1 l i)
      _ = (Wd cap l : ℝ) := by simp [Wd]
  have hc0 : ∀ l, 0 ≤ c l := fun l => Finset.sum_nonneg (fun i _ => hv0 l i)
  set f : ℕ → ℝ := fun l => ((min (Wd cap l) (E - Ud cap l) : ℕ) : ℝ) with hf
  have hprefix : ∀ n ≤ E, 0 ≤ ∑ l ∈ range n, (f l - c l) := by
    intro n hn
    rw [Finset.sum_sub_distrib, sub_nonneg]
    have hfsum : ∑ l ∈ range n, f l = ((min E (Ud cap n) : ℕ) : ℝ) := by
      simp only [hf]
      rw [← greedy_prefix cap E n, Nat.cast_sum]
    rw [hfsum]
    have h1 : ∑ l ∈ range n, c l ≤ (Ud cap n : ℝ) := by
      rw [Ud_eq_sum, Nat.cast_sum]
      exact Finset.sum_le_sum (fun l _ => hcW l)
    have h2 : ∑ l ∈ range n, c l ≤ (E : ℝ) := by
      calc ∑ l ∈ range n, c l ≤ ∑ l ∈ range E, c l :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
              (fun l _ _ => hc0 l)
        _ = ∑ i, w i := htot.symm
        _ ≤ E := hE
    rw [Nat.cast_min]
    exact le_min h2 h1
  have habel := abel_nonneg (fun l => gd k (Wd cap l)) (fun l => f l - c l) E
    (fun l => gd_nonneg k _) (fun l => gd_anti cap k (Nat.le_succ l)) hprefix
  rw [gainD_eq, htot, htotU, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc ∑ l ∈ range E, (c l - 2 * t l) ≤ ∑ l ∈ range E, gd k (Wd cap l) * c l :=
        Finset.sum_le_sum (fun l _ => hlayer l)
    _ ≤ ∑ l ∈ range E, gd k (Wd cap l) * f l := by
        have : ∑ l ∈ range E, gd k (Wd cap l) * (f l - c l) =
            ∑ l ∈ range E, gd k (Wd cap l) * f l - ∑ l ∈ range E, gd k (Wd cap l) * c l := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro l _; ring
        linarith

theorem exists_stop {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) :
    ∃ h, Wd cap h < 2 * k ∨ Wd cap h = 0 ∨ E < Ud cap h + Wd cap h := by
  refine ⟨∑ i, cap i, Or.inr (Or.inl ?_)⟩
  unfold Wd
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (cap j)) (Finset.mem_univ i)
  omega

theorem gd_zero_of_lt {k W : ℕ} (h : W < 2 * k) : gd k W = 0 := by
  unfold gd
  rw [Nat.sub_eq_zero_of_le (le_of_lt h)]
  simp

theorem gd_mul_self {k W : ℕ} (h : 2 * k ≤ W) (hW : 0 < W) :
    gd k W * (W : ℝ) = (W : ℝ) - 2 * k := by
  unfold gd
  push_cast [Nat.cast_sub h]
  rw [div_mul_cancel₀ _ (by positivity)]

theorem gain_closed {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (h : ℕ)
    (hgood : ∀ l < h, 2 * k ≤ Wd cap l ∧ 0 < Wd cap l ∧ Ud cap l + Wd cap l ≤ E)
    (hQ : Wd cap h < 2 * k ∨ Wd cap h = 0 ∨ E < Ud cap h + Wd cap h)
    (hUh : Ud cap h ≤ E) (hhE : h ≤ E) :
    gainD k E cap = (Ud cap h : ℝ) - 2 * k * h +
      ((if 2 * k ≤ Wd cap h ∧ 0 < Wd cap h then E - Ud cap h else 0 : ℕ) : ℝ) *
        gd k (Wd cap h) := by
  set r : ℕ := if 2 * k ≤ Wd cap h ∧ 0 < Wd cap h then E - Ud cap h else 0 with hr
  rw [gainD_eq]
  have hterm : ∀ l ∈ range E, gd k (Wd cap l) * ((min (Wd cap l) (E - Ud cap l) : ℕ) : ℝ) =
      (if l < h then ((Wd cap l : ℝ) - 2 * k) else 0) +
        (if l = h then (r : ℝ) * gd k (Wd cap h) else 0) := by
    intro l _
    rcases lt_trichotomy l h with hl | hl | hl
    · obtain ⟨h2k, hpos, hb⟩ := hgood l hl
      rw [if_pos hl, if_neg (ne_of_lt hl), add_zero, min_eq_left (by omega)]
      exact gd_mul_self h2k hpos
    · subst hl
      rw [if_neg (lt_irrefl l), if_pos rfl, zero_add]
      by_cases hp : 2 * k ≤ Wd cap l ∧ 0 < Wd cap l
      · have hlt : E < Ud cap l + Wd cap l := by omega
        rw [hr, if_pos hp, min_eq_right (by omega)]
        ring
      · rw [hr, if_neg hp]
        simp only [Nat.cast_zero, zero_mul]
        rcases Nat.lt_or_ge (Wd cap l) (2 * k) with h1 | h1
        · rw [gd_zero_of_lt h1, zero_mul]
        · have : Wd cap l = 0 := by omega
          rw [this]; simp
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      have hW := Wd_anti cap (le_of_lt hl)
      rcases hQ with h1 | h1 | h1
      · rw [gd_zero_of_lt (lt_of_le_of_lt hW h1), zero_mul]
      · have : Wd cap l = 0 := by omega
        rw [this]; simp
      · have h2 : Ud cap (h + 1) ≤ Ud cap l := Ud_mono cap hl
        rw [Ud_succ] at h2
        have : E - Ud cap l = 0 := by omega
        rw [this]; simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_filter]
  have hfilt : (range E).filter (fun l => l < h) = range h := by
    ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Ud_eq_sum, Finset.sum_ite_eq']
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mem_range]
  split_ifs with hhE'
  · ring
  · have hh : h = E := by omega
    have hU : h ≤ Ud cap h := by
      rw [Ud_eq_sum]
      calc h = ∑ l ∈ range h, 1 := by simp
        _ ≤ ∑ l ∈ range h, Wd cap l :=
          Finset.sum_le_sum (fun l hl => (hgood l (Finset.mem_range.1 hl)).2.1)
    have hr0 : r = 0 := by rw [hr]; split_ifs <;> omega
    rw [hr0]; push_cast; ring

theorem count_shift (n r : ℕ) (hr : r ≤ n + 1) (z : Fin (n + 1)) :
    (Finset.univ.filter (fun y : Fin (n + 1) => ((y + z : Fin (n + 1)) : ℕ) < r)).card = r := by
  have h2 : (Finset.univ.filter (fun x : Fin (n + 1) => (x : ℕ) < r)).card = r := by
    rw [Fin.card_filter_val_lt]; omega
  refine Eq.trans ?_ h2
  apply Finset.card_bij' (fun y _ => y + z) (fun x _ => x - z)
  · intro y hy; simpa using hy
  · intro x hx; simpa using hx
  · intro y _; simp
  · intro x _; simp

theorem part2 {q : ℕ} (k E : ℕ) (hq : 0 < q) (hk : k ≤ q) (cap : Fin q → ℕ) :
    ∃ (p : ℕ) (H : Fin p → Fin q → ℕ), 0 < p ∧ p ≤ q ∧
      (∀ z, (∀ i, H z i ≤ cap i) ∧ (∑ i, H z i) ≤ E) ∧
      (∀ U : Finset (Fin q), U.card = k → gainD k E cap ≤
        (∑ i, ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ)) -
          2 * ∑ i ∈ U, ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ)) ∧
      ∃ U : Finset (Fin q), U.card = k ∧
        (∑ i, ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ)) -
          2 * ∑ i ∈ U, ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ) = gainD k E cap := by
  classical
  have hex := exists_stop k E cap
  set h := Nat.find hex with hh
  have hQ : Wd cap h < 2 * k ∨ Wd cap h = 0 ∨ E < Ud cap h + Wd cap h := Nat.find_spec hex
  have hgood : ∀ l < h, 2 * k ≤ Wd cap l ∧ 0 < Wd cap l ∧ Ud cap l + Wd cap l ≤ E := by
    intro l hl
    have := Nat.find_min hex hl
    omega
  have hUh : Ud cap h ≤ E := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, Ud_zero]; omega
    · have h1 := hgood (h - 1) (by omega)
      have e := Ud_succ cap (h - 1)
      rw [show h - 1 + 1 = h by omega] at e
      omega
  have hhU : h ≤ Ud cap h := by
    rw [Ud_eq_sum]
    calc h = ∑ l ∈ range h, 1 := by simp
      _ ≤ ∑ l ∈ range h, Wd cap l :=
        Finset.sum_le_sum (fun l hl => (hgood l (Finset.mem_range.1 hl)).2.1)
  have hhE : h ≤ E := le_trans hhU hUh
  have hgain := gain_closed k E cap h hgood hQ hUh hhE
  set r : ℕ := if 2 * k ≤ Wd cap h ∧ 0 < Wd cap h then E - Ud cap h else 0 with hr
  have hUd : (∑ i, ((min (cap i) h : ℕ) : ℝ)) = (Ud cap h : ℝ) := by
    unfold Ud; push_cast; rfl
  by_cases hr0 : r = 0
  ·
    rw [hr0] at hgain
    refine ⟨1, fun _ i => min (cap i) h, Nat.one_pos, hq, ?_, ?_, ?_⟩
    · intro _; exact ⟨fun i => min_le_left _ _, hUh⟩
    · intro U hU
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, div_one]
      rw [hgain, hUd]
      have h2 : (∑ i ∈ U, ((min (cap i) h : ℕ) : ℝ)) ≤ k * h := by
        calc _ ≤ ∑ i ∈ U, (h : ℝ) :=
              Finset.sum_le_sum (fun i _ => by exact_mod_cast min_le_right _ _)
          _ = k * h := by simp [hU]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      linarith
    · have hB : ∃ U : Finset (Fin q), U.card = k ∧ ∀ i ∈ U, h ≤ cap i := by
        rcases Nat.eq_zero_or_pos h with h0 | h0
        · obtain ⟨U, -, hU⟩ := Finset.exists_subset_card_eq
            (s := (Finset.univ : Finset (Fin q))) (n := k) (by simpa using hk)
          exact ⟨U, hU, fun i _ => by omega⟩
        · have hg := hgood (h - 1) (by omega)
          obtain ⟨U, hUs, hU⟩ := Finset.exists_subset_card_eq
            (s := Finset.univ.filter (fun i => h - 1 < cap i)) (n := k)
            (by unfold Wd at hg; omega)
          refine ⟨U, hU, fun i hi => ?_⟩
          have := hUs hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          omega
      obtain ⟨U, hU, hUcap⟩ := hB
      refine ⟨U, hU, ?_⟩
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, div_one]
      rw [hgain, hUd]
      have h2 : (∑ i ∈ U, ((min (cap i) h : ℕ) : ℝ)) = k * h := by
        rw [Finset.sum_congr rfl (fun i hi => by rw [min_eq_right (hUcap i hi)])]
        simp [hU]
      rw [h2]; push_cast; ring
  ·
    have hp : 2 * k ≤ Wd cap h ∧ 0 < Wd cap h := by
      by_contra hn; apply hr0; rw [hr, if_neg hn]
    have hrv : r = E - Ud cap h := by rw [hr, if_pos hp]
    have hra : r < Wd cap h := by omega
    set A := Finset.univ.filter (fun i => h < cap i) with hA
    have hAc : A.card = Wd cap h := rfl
    obtain ⟨n, hn⟩ : ∃ n, A.card = n + 1 := ⟨A.card - 1, by omega⟩
    set e : {x // x ∈ A} ≃ Fin (n + 1) := A.equivFin.trans (finCongr hn) with he
    set tr : Fin q → Fin (n + 1) := fun i => if hi : i ∈ A then e ⟨i, hi⟩ else 0 with htr
    set H : Fin (n + 1) → Fin q → ℕ := fun z i =>
      min (cap i) h + if i ∈ A ∧ ((tr i + z : Fin (n + 1)) : ℕ) < r then 1 else 0 with hH
    have hrn : r ≤ n + 1 := by omega
    have hcount_z : ∀ z : Fin (n + 1),
        (∑ i, if i ∈ A ∧ ((tr i + z : Fin (n + 1)) : ℕ) < r then 1 else 0) = r := by
      intro z
      simp_rw [ite_and]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← Finset.sum_coe_sort A]
      have htx : ∀ x : {x // x ∈ A}, tr x = e x := fun x => by simp [htr, x.2]
      simp_rw [htx]
      rw [Equiv.sum_comp e (fun y => if ((y + z : Fin (n + 1)) : ℕ) < r then 1 else 0),
        ← Finset.card_filter]
      exact count_shift n r hrn z
    have hcount_i : ∀ i,
        (∑ z : Fin (n + 1), if ((tr i + z : Fin (n + 1)) : ℕ) < r then 1 else 0) = r := by
      intro i
      rw [← Finset.card_filter]
      simp_rw [add_comm (tr i)]
      exact count_shift n r hrn (tr i)
    have hsum_z : ∀ z, (∑ i, H z i) = Ud cap h + r := by
      intro z
      simp only [hH]
      rw [Finset.sum_add_distrib, hcount_z]
      rfl
    have hsum_i : ∀ i, (∑ z : Fin (n + 1), H z i) =
        (n + 1) * min (cap i) h + (if i ∈ A then r else 0) := by
      intro i
      simp only [hH]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      by_cases hi : i ∈ A
      · simp only [hi, true_and, if_true]
        rw [hcount_i i]
      · simp [hi]
    have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hmean : ∀ i, ((∑ z : Fin (n + 1), H z i : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) =
        ((min (cap i) h : ℕ) : ℝ) + (if i ∈ A then (r : ℝ) / ((n + 1 : ℕ) : ℝ) else 0) := by
      intro i
      rw [hsum_i i]
      split_ifs <;> push_cast <;> field_simp <;> ring
    set M : ℝ := (h : ℝ) + (r : ℝ) / ((n + 1 : ℕ) : ℝ) with hM
    have hle : ∀ i, ((∑ z : Fin (n + 1), H z i : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ M := by
      intro i
      rw [hmean i, hM]
      have h1 : ((min (cap i) h : ℕ) : ℝ) ≤ h := by exact_mod_cast min_le_right _ _
      have h2 : (0 : ℝ) ≤ (r : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
      split_ifs <;> linarith
    have heq : ∀ i ∈ A, ((∑ z : Fin (n + 1), H z i : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) = M := by
      intro i hi
      rw [hmean i, hM, if_pos hi]
      have : h < cap i := (Finset.mem_filter.1 hi).2
      rw [min_eq_right (le_of_lt this)]
    have htot : (∑ i, ((∑ z : Fin (n + 1), H z i : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        (Ud cap h : ℝ) + r := by
      simp_rw [hmean]
      rw [Finset.sum_add_distrib, hUd, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, hn, nsmul_eq_mul]
      field_simp
    have hgd : gd k (Wd cap h) = (((n + 1 : ℕ) : ℝ) - 2 * k) / ((n + 1 : ℕ) : ℝ) := by
      rw [← hAc, hn]
      unfold gd
      have : 2 * k ≤ n + 1 := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hgain' : gainD k E cap = (Ud cap h : ℝ) - 2 * k * h + r - 2 * k * (r / ((n + 1 : ℕ) : ℝ)) := by
      rw [hgain, hgd]
      field_simp
      ring
    refine ⟨n + 1, H, Nat.succ_pos n, ?_, ?_, ?_, ?_⟩
    · have := Finset.card_le_univ A
      simp only [Fintype.card_fin] at this
      omega
    · intro z
      refine ⟨fun i => ?_, by rw [hsum_z]; omega⟩
      simp only [hH]
      split_ifs with hc
      · have : h < cap i := (Finset.mem_filter.1 hc.1).2
        omega
      · omega
    · intro U hU
      rw [htot, hgain']
      have hUle : (∑ i ∈ U, ((∑ z : Fin (n + 1), H z i : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ k * M := by
        calc _ ≤ ∑ i ∈ U, M := Finset.sum_le_sum (fun i _ => hle i)
          _ = k * M := by simp [hU]
      rw [hM] at hUle
      linarith
    · have hkA : k ≤ A.card := by omega
      obtain ⟨U, hUA, hU⟩ := Finset.exists_subset_card_eq hkA
      refine ⟨U, hU, ?_⟩
      rw [htot, hgain', Finset.sum_congr rfl (fun i hi => heq i (hUA hi))]
      simp only [Finset.sum_const, hU, nsmul_eq_mul, hM]
      ring

end PEqualNP.Outside.L_lib_883_aux

open PEqualNP.Outside.L_lib_883_aux in
theorem PEqualNP.Outside.L_lib_883 : (∀ (q k E : ℕ), 0 < q → k ≤ q → ∀ cap : Fin q → ℕ,
  let I := Fin q
  let width := fun l : ℕ => ((Finset.univ : Finset I).filter (fun i => l < cap i)).card
  let used := fun l : ℕ => ∑ i : I, min (cap i) l
  let gain := ∑ l ∈ Finset.range E,
    ((min (width l) (E-used l) * (width l-2*k) : ℕ) : ℝ)/(width l : ℝ)
  let score := fun (w : I → ℝ) (U : Finset I) => (∑ i, w i) - 2 * ∑ i ∈ U, w i
  (∀ w : I → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ (cap i : ℝ)) → (∑ i, w i) ≤ (E : ℝ) →
    ∃ U : Finset I, U.card = k ∧ score w U ≤ gain) ∧
  ∃ (p : ℕ) (H : Fin p → I → ℕ), 0 < p ∧ p ≤ q ∧
    (∀ z, (∀ i, H z i ≤ cap i) ∧ (∑ i, H z i) ≤ E) ∧
    let mean := fun i : I => ((∑ z : Fin p, H z i : ℕ) : ℝ)/(p : ℝ)
    (∀ U : Finset I, U.card = k → gain ≤ score mean U) ∧
    ∃ U : Finset I, U.card = k ∧ score mean U = gain) := by
  intro q k E hq hk cap
  exact ⟨fun w hw hE => part1 k E hk cap w hw hE, part2 k E hq hk cap⟩
