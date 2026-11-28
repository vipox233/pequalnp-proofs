import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_942_aux

open Finset

section LP
variable {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev Con (κ : Type) := ((κ → ℚ) →ₗ[ℚ] ℚ) × ℚ

def Sat (L : List (Con κ)) (x : κ → ℚ) : Prop := ∀ c ∈ L, c.1 x ≤ c.2

def coef (g : (κ → ℚ) →ₗ[ℚ] ℚ) (v : κ) : ℚ := g (Pi.single v 1)

lemma apply_update (g : (κ → ℚ) →ₗ[ℚ] ℚ) (x : κ → ℚ) (v : κ) (y : ℚ) :
    g (Function.update x v y) = g x + (y - x v) * coef g v := by
  have : Function.update x v y = x + (y - x v) • Pi.single v 1 := by
    funext i
    by_cases h : i = v
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_apply, h]
  rw [this, map_add, map_smul, smul_eq_mul, coef]

lemma apply_eq_sum (g : (κ → ℚ) →ₗ[ℚ] ℚ) (x : κ → ℚ) : g x = ∑ i, x i * coef g i := by
  have hx : x = ∑ i, x i • (Pi.single i (1:ℚ) : κ → ℚ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, coef]

lemma coef_comb (a b : ℚ) (g h : (κ → ℚ) →ₗ[ℚ] ℚ) (i : κ) :
    coef (a • g + b • h) i = a * coef g i + b * coef h i := by
  simp [coef]

def comb (v : κ) (p q : Con κ) : Con κ :=
  if 0 < coef p.1 v ∧ coef q.1 v < 0 then
    ((-coef q.1 v) • p.1 + coef p.1 v • q.1, (-coef q.1 v) * p.2 + coef p.1 v * q.2)
  else (0, 0)

def elim (v : κ) (L : List (Con κ)) : List (Con κ) :=
  L.filter (fun c => decide (coef c.1 v = 0)) ++ L.flatMap (fun p => L.map (comb v p))

lemma mem_elim {v : κ} {L : List (Con κ)} {c : Con κ} :
    c ∈ elim v L ↔ (c ∈ L ∧ coef c.1 v = 0) ∨ ∃ p ∈ L, ∃ q ∈ L, comb v p q = c := by
  simp [elim, List.mem_flatMap]

lemma elim_sat (v : κ) (L : List (Con κ)) (x : κ → ℚ) (h : Sat L x) : Sat (elim v L) x := by
  intro c hc
  rcases mem_elim.1 hc with ⟨hc, _⟩ | ⟨p, hp, q, hq, rfl⟩
  · exact h c hc
  · unfold comb
    split_ifs with hpq
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      have h1 := h p hp
      have h2 := h q hq
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.2 hpq.2))
      have := mul_le_mul_of_nonneg_left h2 (le_of_lt hpq.1)
      linarith
    · simp

lemma exists_between_lists (Lo Up : List ℚ) (h : ∀ l ∈ Lo, ∀ u ∈ Up, l ≤ u) :
    ∃ y, (∀ l ∈ Lo, l ≤ y) ∧ ∀ u ∈ Up, y ≤ u := by
  by_cases hL : Lo.toFinset.Nonempty
  · refine ⟨Lo.toFinset.max' hL, fun l hl => Finset.le_max' _ _ (List.mem_toFinset.2 hl),
      fun u hu => h _ (List.mem_toFinset.1 (Finset.max'_mem _ _)) u hu⟩
  · have hL' : ∀ l ∈ Lo, False := fun l hl => hL ⟨l, List.mem_toFinset.2 hl⟩
    by_cases hU : Up.toFinset.Nonempty
    · exact ⟨Up.toFinset.min' hU, fun l hl => (hL' l hl).elim,
        fun u hu => Finset.min'_le _ _ (List.mem_toFinset.2 hu)⟩
    · exact ⟨0, fun l hl => (hL' l hl).elim,
        fun u hu => (hU ⟨u, List.mem_toFinset.2 hu⟩).elim⟩

lemma elim_lift (v : κ) (L : List (Con κ)) (x : κ → ℚ) (hx : Sat (elim v L) x) :
    ∃ y, Sat L (Function.update x v y) := by
  let s : Con κ → ℚ := fun c => c.1 x - x v * coef c.1 v
  let bd : Con κ → ℚ := fun c => (c.2 - s c) / coef c.1 v
  have hupd : ∀ c : Con κ, ∀ y, c.1 (Function.update x v y) = s c + y * coef c.1 v := by
    intro c y; rw [apply_update]; simp only [s]; ring
  obtain ⟨y, hlo, hup⟩ := exists_between_lists
      ((L.filter (fun c => decide (coef c.1 v < 0))).map bd)
      ((L.filter (fun c => decide (0 < coef c.1 v))).map bd) (by
    intro l hl u hu
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hl hu
    obtain ⟨q, ⟨hq, hqn⟩, rfl⟩ := hl
    obtain ⟨p, ⟨hp, hpp⟩, rfl⟩ := hu
    have hc := hx (comb v p q) (mem_elim.2 (Or.inr ⟨p, hp, q, hq, rfl⟩))
    simp only [comb, hpp, hqn, and_self, if_true] at hc
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hc
    simp only [bd, s]
    rw [← neg_div_neg_eq (q.2 - _) _, div_le_div_iff₀ (neg_pos.2 hqn) hpp]
    nlinarith [hc])
  refine ⟨y, fun c hc => ?_⟩
  rw [hupd]
  rcases lt_trichotomy (coef c.1 v) 0 with hneg | hz | hpos
  · have := hlo (bd c) (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hneg]⟩, rfl⟩)
    simp only [bd] at this
    rw [div_le_iff_of_neg hneg] at this
    linarith
  · have := hx c (mem_elim.2 (Or.inl ⟨hc, hz⟩))
    simp only [s, hz, mul_zero, sub_zero, add_zero]
    exact this
  · have := hup (bd c) (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hpos]⟩, rfl⟩)
    simp only [bd] at this
    rw [le_div_iff₀ hpos] at this
    linarith

lemma lp_base (t : κ) (L : List (Con κ))
    (hs : ∀ c ∈ L, ∀ i, i ≠ t → coef c.1 i = 0)
    (hf : ∃ x, Sat L x) (hb : ∃ B, ∀ x, Sat L x → x t ≤ B) :
    ∃ x, Sat L x ∧ ∀ x', Sat L x' → x' t ≤ x t := by
  have hev : ∀ c ∈ L, ∀ x : κ → ℚ, c.1 x = x t * coef c.1 t := by
    intro c hc x
    rw [apply_eq_sum, Finset.sum_eq_single t]
    · intro i _ hi; rw [hs c hc i hi, mul_zero]
    · simp
  obtain ⟨x0, hx0⟩ := hf
  obtain ⟨B, hB⟩ := hb
  let Up := (L.filter (fun c => decide (0 < coef c.1 t))).map (fun c => c.2 / coef c.1 t)
  have hx0up : ∀ u ∈ Up, x0 t ≤ u := by
    intro u hu
    simp only [Up, List.mem_map, List.mem_filter, decide_eq_true_eq] at hu
    obtain ⟨c, ⟨hc, hpos⟩, rfl⟩ := hu
    rw [le_div_iff₀ hpos, ← hev c hc]
    exact hx0 c hc
  by_cases hU : Up.toFinset.Nonempty
  · let τ := Up.toFinset.min' hU
    have hτ : τ ∈ Up := List.mem_toFinset.1 (Finset.min'_mem _ _)
    have hx0τ : x0 t ≤ τ := hx0up τ hτ
    have hsat : Sat L (Function.update x0 t τ) := by
      intro c hc
      rw [hev c hc, Function.update_self]
      by_cases hpos : 0 < coef c.1 t
      · have : τ ≤ c.2 / coef c.1 t := Finset.min'_le _ _ (List.mem_toFinset.2
          (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hpos]⟩, rfl⟩))
        rwa [le_div_iff₀ hpos] at this
      · push_neg at hpos
        have h1 := hx0 c hc
        rw [hev c hc] at h1
        have := mul_le_mul_of_nonpos_right hx0τ hpos
        linarith
    refine ⟨_, hsat, fun x' hx' => ?_⟩
    rw [Function.update_self]
    apply Finset.le_min'
    intro u hu
    have hu := List.mem_toFinset.1 hu
    simp only [Up, List.mem_map, List.mem_filter, decide_eq_true_eq] at hu
    obtain ⟨c, ⟨hc, hpos⟩, rfl⟩ := hu
    rw [le_div_iff₀ hpos, ← hev c hc]
    exact hx' c hc
  · exfalso
    have hnp : ∀ c ∈ L, coef c.1 t ≤ 0 := by
      intro c hc
      by_contra hpos; push_neg at hpos
      exact hU ⟨_, List.mem_toFinset.2
        (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hpos]⟩, rfl⟩)⟩
    have hsat : Sat L (Function.update x0 t (max (x0 t) (B + 1))) := by
      intro c hc
      rw [hev c hc, Function.update_self]
      have h1 := hx0 c hc
      rw [hev c hc] at h1
      have := mul_le_mul_of_nonpos_right (le_max_left (x0 t) (B + 1)) (hnp c hc)
      linarith
    have := hB _ hsat
    rw [Function.update_self] at this
    have := le_max_right (x0 t) (B + 1)
    linarith

lemma lp_core (t : κ) (V : Finset κ) : ∀ (L : List (Con κ)), t ∉ V →
    (∀ c ∈ L, ∀ i, i ∉ V → i ≠ t → coef c.1 i = 0) →
    (∃ x, Sat L x) → (∃ B, ∀ x, Sat L x → x t ≤ B) →
    ∃ x, Sat L x ∧ ∀ x', Sat L x' → x' t ≤ x t := by
  induction V using Finset.induction_on with
  | empty =>
    intro L _ hs hf hb
    exact lp_base t L (fun c hc i hi => hs c hc i (Finset.notMem_empty i) hi) hf hb
  | insert v V hv ih =>
    intro L ht hs hf hb
    have htv : t ≠ v := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have htV : t ∉ V := fun h => ht (Finset.mem_insert_of_mem h)
    have hs' : ∀ c ∈ elim v L, ∀ i, i ∉ V → i ≠ t → coef c.1 i = 0 := by
      intro c hc i hiV hit
      rcases mem_elim.1 hc with ⟨hc, hcv⟩ | ⟨p, hp, q, hq, rfl⟩
      · by_cases hiv : i = v
        · subst hiv; exact hcv
        · exact hs c hc i (by simp [hiv, hiV]) hit
      · unfold comb
        split_ifs with hpq
        · rw [coef_comb]
          by_cases hiv : i = v
          · subst hiv; ring
          · rw [hs p hp i (by simp [hiv, hiV]) hit, hs q hq i (by simp [hiv, hiV]) hit]; ring
        · simp [coef]
    obtain ⟨x0, hx0⟩ := hf
    obtain ⟨B, hB⟩ := hb
    obtain ⟨xs, hxs, hmax⟩ := ih (elim v L) htV hs' ⟨x0, elim_sat v L x0 hx0⟩
      ⟨B, fun x hx => by
        obtain ⟨y, hy⟩ := elim_lift v L x hx
        have := hB _ hy
        rwa [Function.update_of_ne htv] at this⟩
    obtain ⟨y, hy⟩ := elim_lift v L xs hxs
    refine ⟨_, hy, fun x' hx' => ?_⟩
    rw [Function.update_of_ne htv]
    exact hmax x' (elim_sat v L x' hx')

theorem lp_attain (t : κ) (L : List (Con κ)) (hf : ∃ x, Sat L x)
    (hb : ∃ B, ∀ x, Sat L x → x t ≤ B) :
    ∃ x, Sat L x ∧ ∀ x', Sat L x' → x' t ≤ x t :=
  lp_core t (Finset.univ.erase t) L (by simp)
    (fun c _ i hi hit => by simp [hit] at hi) hf hb

end LP
end PEqualNP.Outside.L_lib_942_aux

namespace PEqualNP.Outside.L_lib_942_aux
open Finset

section Comb
variable {m n : ℕ}

def G (q : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (t : ℕ) (i j : Fin n) : ℕ :=
  if A i ∩ P = A j ∩ P ∧ (A i ∩ P).card ≤ t ∧ t - (A i ∩ P).card ≤ q - P.card then
    Nat.choose ((A i ∩ A j) \ P).card (t - (A i ∩ P).card) *
      Nat.choose ((Finset.univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)).card
        ((q - P.card) - (t - (A i ∩ P).card))
  else 0

lemma choose_K (b e : ℕ) : b * Nat.choose (b-1) e = (e+1) * Nat.choose b (e+1) := by
  cases b with
  | zero => simp
  | succ b => simp only [Nat.add_sub_cancel]; rw [Nat.add_one_mul_choose_eq]; ring

lemma arith (cond : Prop) [Decidable cond] (L t l b nn : ℕ) (hl : 1 ≤ l) :
    b * (if cond ∧ L+1 ≤ t ∧ t-(L+1) ≤ l-1 then
        Nat.choose (b-1) (t-(L+1)) * Nat.choose nn ((l-1)-(t-(L+1))) else 0)
    + nn * (if cond ∧ L ≤ t ∧ t - L ≤ l-1 then
        Nat.choose b (t-L) * Nat.choose (nn-1) ((l-1)-(t-L)) else 0)
    = l * (if cond ∧ L ≤ t ∧ t - L ≤ l then
        Nat.choose b (t-L) * Nat.choose nn (l-(t-L)) else 0) := by
  by_cases hc : cond
  swap
  · simp [hc]
  simp only [hc, true_and]
  rcases Nat.lt_or_ge t L with hlt | hge
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hge
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [show L + e - L = e by omega, show l + 1 - 1 = l by omega]
  rcases e with _ | e
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show l + 1 - 0 = l + 1 by omega, show l - 0 = l by omega]
    simp only [Nat.choose_zero_right, one_mul, mul_zero, zero_add]
    exact choose_K nn l
  · rw [show L + (e + 1) - (L + 1) = e by omega]
    rcases Nat.lt_or_ge l e with h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
    · by_cases h' : e + 1 ≤ l
      · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        obtain ⟨r, hr⟩ : ∃ r, l - e = r + 1 := ⟨l - e - 1, by omega⟩
        rw [show l - (e+1) = r by omega, show l + 1 - (e+1) = r + 1 by omega, hr]
        have k1 := choose_K b e
        have k2 := choose_K nn r
        have hl' : l + 1 = (e + 1) + (r + 1) := by omega
        calc b * (Nat.choose (b - 1) e * Nat.choose nn (r + 1)) +
              nn * (Nat.choose b (e + 1) * Nat.choose (nn - 1) r)
            = (b * Nat.choose (b - 1) e) * Nat.choose nn (r + 1) +
              (nn * Nat.choose (nn - 1) r) * Nat.choose b (e + 1) := by ring
          _ = _ := by rw [k1, k2, hl']; ring
      · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        have hle : l = e := by omega
        subst hle
        rw [show l - l = 0 by omega, show l + 1 - (l + 1) = 0 by omega]
        simp only [Nat.choose_zero_right, mul_one, mul_zero, add_zero]
        exact choose_K b l

lemma G_insert_sum (q : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (hP : P.card < q)
    (t : ℕ) (i j : Fin n) :
    ∑ c ∈ univ \ P, G q A (insert c P) t i j = (q - P.card) * G q A P t i j := by
  have hterm : ∀ c ∈ univ \ P, G q A (insert c P) t i j =
      (if c ∈ (A i ∩ A j) \ P then
        (if A i ∩ P = A j ∩ P ∧ (A i ∩ P).card + 1 ≤ t ∧
            t - ((A i ∩ P).card + 1) ≤ q - P.card - 1 then
          Nat.choose (((A i ∩ A j) \ P).card - 1) (t - ((A i ∩ P).card + 1)) *
            Nat.choose ((univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)).card
              (q - P.card - 1 - (t - ((A i ∩ P).card + 1)))
        else 0) else 0) +
      (if c ∈ (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) then
        (if A i ∩ P = A j ∩ P ∧ (A i ∩ P).card ≤ t ∧ t - (A i ∩ P).card ≤ q - P.card - 1 then
          Nat.choose ((A i ∩ A j) \ P).card (t - (A i ∩ P).card) *
            Nat.choose (((univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)).card - 1)
              (q - P.card - 1 - (t - (A i ∩ P).card))
        else 0) else 0) := by
    intro c hc
    have hcP : c ∉ P := (mem_sdiff.1 hc).2
    have hq1 : q - (insert c P).card = q - P.card - 1 := by
      rw [card_insert_of_notMem hcP]; omega
    by_cases ha : c ∈ A i <;> by_cases hb : c ∈ A j
    · have h1 : c ∈ (A i ∩ A j) \ P := by simp [ha, hb, hcP]
      have h2 : c ∉ (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) := by simp [ha]
      rw [if_pos h1, if_neg h2, add_zero]
      have hcond : (A i ∩ insert c P = A j ∩ insert c P) ↔ (A i ∩ P = A j ∩ P) := by
        rw [inter_insert_of_mem ha, inter_insert_of_mem hb]
        constructor
        · intro h; ext x
          have := Finset.ext_iff.1 h x
          by_cases hx : x = c
          · subst hx; simp [hcP]
          · simpa [hx] using this
        · intro h; rw [h]
      have hc1 : (A i ∩ insert c P).card = (A i ∩ P).card + 1 := by
        rw [inter_insert_of_mem ha, card_insert_of_notMem (by simp [hcP])]
      have hc2 : ((A i ∩ A j) \ insert c P).card = ((A i ∩ A j) \ P).card - 1 := by
        rw [sdiff_insert, card_erase_of_mem h1]
      have hc3 : ((univ : Finset (Fin m)) \ (insert c P ∪ A i ∪ A j)) =
          (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) := by
        ext x; by_cases hx : x = c
        · subst hx; simp [ha]
        · simp [hx]
      simp only [G, hcond, hc1, hc2, hc3, hq1]
    · have h1 : c ∉ (A i ∩ A j) \ P := by simp [hb]
      have h2 : c ∉ (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) := by simp [ha]
      rw [if_neg h1, if_neg h2, add_zero]
      have : ¬ (A i ∩ insert c P = A j ∩ insert c P) := by
        intro h
        have := Finset.ext_iff.1 h c
        simp [ha, hb] at this
      simp [G, this]
    · have h1 : c ∉ (A i ∩ A j) \ P := by simp [ha]
      have h2 : c ∉ (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) := by simp [hb]
      rw [if_neg h1, if_neg h2, add_zero]
      have : ¬ (A i ∩ insert c P = A j ∩ insert c P) := by
        intro h
        have := Finset.ext_iff.1 h c
        simp [ha, hb] at this
      simp [G, this]
    · have h1 : c ∉ (A i ∩ A j) \ P := by simp [ha]
      have h2 : c ∈ (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) := by simp [ha, hb, hcP]
      rw [if_neg h1, if_pos h2, zero_add]
      have e1 : A i ∩ insert c P = A i ∩ P := inter_insert_of_notMem ha
      have e2 : A j ∩ insert c P = A j ∩ P := inter_insert_of_notMem hb
      have e3 : (A i ∩ A j) \ insert c P = (A i ∩ A j) \ P :=
        sdiff_insert_of_notMem (by simp [ha]) _
      have hc3 : ((univ : Finset (Fin m)) \ (insert c P ∪ A i ∪ A j)).card =
          ((univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)).card - 1 := by
        rw [← card_erase_of_mem h2]
        congr 1
        ext x; by_cases hx : x = c
        · subst hx; simp
        · simp [hx]
      simp only [G, e1, e2, e3, hc3, hq1]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_mem, sum_ite_mem]
  have e1 : (univ \ P) ∩ ((A i ∩ A j) \ P) = (A i ∩ A j) \ P :=
    inter_eq_right.2 (by intro x hx; rw [mem_sdiff] at hx ⊢; exact ⟨mem_univ _, hx.2⟩)
  have e2 : (univ \ P) ∩ ((univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)) =
      (univ : Finset (Fin m)) \ (P ∪ A i ∪ A j) :=
    inter_eq_right.2 (by
      intro x hx; rw [mem_sdiff] at hx ⊢; exact ⟨mem_univ _, fun h => hx.2 (by simp [h])⟩)
  rw [e1, e2]
  rw [sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  exact arith _ _ _ _ _ _ (show 1 ≤ q - P.card by omega)

end Comb
end PEqualNP.Outside.L_lib_942_aux

namespace PEqualNP.Outside.L_lib_942_aux
open Finset

section Score
variable {m n : ℕ}

def gramF (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (level : Fin d)
    (i j : Fin n) : ℚ :=
    let t := level.val+1
    let locked := A i ∩ P
    let extra := t-locked.card
    let left := q-P.card
    let both := (A i ∩ A j) \ P
    let neither := (Finset.univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)
    if locked = A j ∩ P ∧ locked.card ≤ t ∧ extra ≤ left then
      ((Nat.choose both.card extra * Nat.choose neither.card (left-extra) : ℕ) : ℚ)
    else 0

lemma gramF_eq (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (level : Fin d)
    (i j : Fin n) : gramF q d A P level i j = (G q A P (level.val+1) i j : ℚ) := by
  unfold gramF G
  dsimp only
  by_cases h : (A i ∩ P = A j ∩ P ∧ (A i ∩ P).card ≤ level.val+1 ∧
      level.val + 1 - (A i ∩ P).card ≤ q - P.card)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Nat.cast_zero]

def hitF (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (i j : Fin n) : ℚ :=
  ∑ t : Fin d, gramF q d A P t i j

def scoreF (q d budget : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (price : ℚ)
    (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) : ℚ :=
  (∑ i : Fin n, (hitF q d A P i i * w i -
      (∑ j : Fin n, if i < j then hitF q d A P i j * z i j else 0))) /
      ((Nat.choose (m-P.card) (q-P.card) : ℕ) : ℚ) - price * (budget : ℚ)

lemma hit_insert_sum (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m))
    (hP : P.card < q) (i j : Fin n) :
    ∑ c ∈ univ \ P, hitF q d A (insert c P) i j = ((q - P.card : ℕ) : ℚ) * hitF q d A P i j := by
  simp only [hitF, gramF_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Nat.cast_sum, G_insert_sum q A P hP, Nat.cast_mul]

lemma H_eq (h : Fin n → Fin n → ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) :
    (∑ i : Fin n, (h i i * w i - ∑ j : Fin n, if i < j then h i j * z i j else 0)) =
    ∑ i, ∑ j, h i j * ((if i = j then w i else 0) - (if i < j then z i j else 0)) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma score_avg (q d budget : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m))
    (hP : P.card < q) (hq : q ≤ m) (price : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) :
    ∑ c ∈ univ \ P, scoreF q d budget A (insert c P) price w z =
      ((m - P.card : ℕ) : ℚ) * scoreF q d budget A P price w z := by
  have hcard : (univ \ P).card = m - P.card := by
    rw [card_univ_diff, Fintype.card_fin]
  have hins : ∀ c ∈ univ \ P, (insert c P).card = P.card + 1 :=
    fun c hc => card_insert_of_notMem (mem_sdiff.1 hc).2
  obtain ⟨M, hM⟩ : ∃ M, m - P.card = M + 1 := ⟨m - P.card - 1, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, q - P.card = K + 1 := ⟨q - P.card - 1, by omega⟩
  have hKM : K ≤ M := by omega
  let Hf : Finset (Fin m) → ℚ := fun Q => ∑ i, ∑ j, hitF q d A Q i j *
    ((if i = j then w i else 0) - (if i < j then z i j else 0))
  have step : ∀ c ∈ univ \ P, scoreF q d budget A (insert c P) price w z =
      Hf (insert c P) / (Nat.choose M K : ℚ) - price * budget := by
    intro c hc
    simp only [scoreF, Hf, H_eq]
    rw [hins c hc, show m - (P.card + 1) = M by omega, show q - (P.card + 1) = K by omega]
  have hP' : scoreF q d budget A P price w z =
      Hf P / (Nat.choose (M+1) (K+1) : ℚ) - price * budget := by
    simp only [scoreF, Hf, H_eq]
    rw [hM, hK]
  have hsumH : ∑ c ∈ univ \ P, Hf (insert c P) = ((K+1 : ℕ) : ℚ) * Hf P := by
    simp only [Hf]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, hit_insert_sum q d A P hP, hK]
    ring
  rw [sum_congr rfl step, sum_sub_distrib, ← sum_div, hsumH, sum_const, hcard, hM, hP',
    nsmul_eq_mul]
  have hc1 : (Nat.choose M K : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hKM).ne'
  have hc2 : (Nat.choose (M+1) (K+1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
  have hid : ((M+1 : ℕ) : ℚ) * Nat.choose M K = Nat.choose (M+1) (K+1) * (K+1 : ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq M K
  have key : ((K+1 : ℕ) : ℚ) * Hf P / (Nat.choose M K : ℚ) =
      ((M+1 : ℕ) : ℚ) * (Hf P / (Nat.choose (M+1) (K+1) : ℚ)) := by
    rw [mul_div_assoc', div_eq_div_iff hc1 hc2]
    linear_combination (-(Hf P)) * hid
  rw [key]
  push_cast
  ring

end Score
end PEqualNP.Outside.L_lib_942_aux

namespace PEqualNP.Outside.L_lib_942_aux
open Finset

section Panel
variable {n : ℕ} {β : Type} [DecidableEq β]

def fitsF (cost : Fin n → ℕ) (price : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) : Prop :=
    0 ≤ price ∧ price ≤ 1 ∧ (∀ i, 0 ≤ w i ∧ w i ≤ price * (cost i : ℚ)) ∧
    (∀ i j, 0 ≤ z i j ∧ z i j ≤ w j) ∧
    ∀ i, w i + (∑ j : Fin n, if i < j then w j - z i j else 0) ≤ 1

variable (Tr : Fin n → β) (qual : β → Prop) [DecidablePred qual]

def hh (i j : Fin n) : ℚ := if Tr i = Tr j ∧ qual (Tr i) then 1 else 0

def objA (B : ℕ) (price : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) : ℚ :=
  (∑ i : Fin n, (hh Tr qual i i * w i -
    ∑ j : Fin n, if i < j then hh Tr qual i j * z i j else 0)) - price * (B : ℚ)

def remA (R : Finset (Fin n)) : ℕ := (((univ \ R).image Tr).filter qual).card

lemma hh_nonneg (i j : Fin n) : 0 ≤ hh Tr qual i j := by
  unfold hh; split_ifs <;> norm_num

lemma weak (cost : Fin n → ℕ) (B : ℕ) (price : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ)
    (hf : fitsF cost price w z) (R : Finset (Fin n)) (hR : ∑ i ∈ R, cost i ≤ B) :
    objA Tr qual B price w z ≤ remA Tr qual R := by
  obtain ⟨hp0, _, hw, hz, hrow⟩ := hf
  let F : Fin n → Finset (Fin n) := fun j => univ.filter (fun k => Tr k = Tr j)
  have hFne : ∀ j, (F j).Nonempty := fun j => ⟨j, by simp [F]⟩
  let ℓ : Fin n → Fin n := fun j => (F j).min' (hFne j)
  have hℓmem : ∀ j, Tr (ℓ j) = Tr j := fun j => by
    have := (F j).min'_mem (hFne j); simpa [F] using this
  have hℓle : ∀ j k, Tr k = Tr j → ℓ j ≤ k := fun j k h => (F j).min'_le k (by simp [F, h])
  have hℓeq : ∀ j k, Tr k = Tr j → ℓ k = ℓ j := by
    intro j k h
    have hF : F k = F j := by ext x; simp [F, h]
    simp only [ℓ]; congr 1
  let f : Fin n → ℚ := fun j =>
    if qual (Tr j) then w j - (if ℓ j < j then z (ℓ j) j else 0) else 0
  have hnn : ∀ i j, 0 ≤ (if i < j then hh Tr qual i j * z i j else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hh_nonneg Tr qual i j) (hz i j).1
    · exact le_refl _
  have s1 : objA Tr qual B price w z + price * B ≤ ∑ j, f j := by
    have hswap : ∑ i : Fin n, ∑ j : Fin n, (if i < j then hh Tr qual i j * z i j else 0) =
        ∑ j : Fin n, ∑ i : Fin n, (if i < j then hh Tr qual i j * z i j else 0) :=
      Finset.sum_comm
    simp only [objA, sub_add_cancel]
    rw [Finset.sum_sub_distrib, hswap, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hq : qual (Tr j)
    · have h1 : hh Tr qual j j = 1 := by simp [hh, hq]
      simp only [f, if_pos hq, h1, one_mul]
      by_cases hlt : ℓ j < j
      · rw [if_pos hlt]
        have := Finset.single_le_sum (f := fun i => if i < j then hh Tr qual i j * z i j else 0)
          (fun i _ => hnn i j) (mem_univ (ℓ j))
        have h2 : hh Tr qual (ℓ j) j = 1 := by simp [hh, hℓmem j, hq]
        simp only [if_pos hlt, h2, one_mul] at this
        linarith
      · rw [if_neg hlt]
        have := Finset.sum_nonneg (fun i (_ : i ∈ univ) => hnn i j)
        linarith
    · have h0 : ∀ i, hh Tr qual i j = 0 := by
        intro i; unfold hh; split_ifs with h
        · exact absurd (h.1 ▸ h.2) hq
        · rfl
      simp [f, hq, h0]
  let RS := ((univ \ R).image Tr).filter qual
  have partA : ∑ j ∈ univ.filter (fun j => Tr j ∈ RS), f j ≤ (RS.card : ℚ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Tr) (t := RS)
      (fun j hj => (mem_filter.1 hj).2)]
    calc _ ≤ ∑ T ∈ RS, (1:ℚ) := by
          refine Finset.sum_le_sum (fun T hT => ?_)
          have hT' := hT
          simp only [RS, mem_filter, mem_image] at hT'
          obtain ⟨⟨j0, _, rfl⟩, hqT⟩ := hT'
          have hΦ : (univ.filter (fun j => Tr j ∈ RS)).filter (fun j => Tr j = Tr j0) = F j0 := by
            ext x; simp only [F, mem_filter, mem_univ, true_and]
            constructor
            · exact fun h => h.2
            · intro h; exact ⟨h ▸ hT, h⟩
          rw [hΦ]
          have hl : ℓ j0 ∈ F j0 := (F j0).min'_mem (hFne j0)
          rw [← Finset.add_sum_erase (F j0) f hl]
          have hfl : f (ℓ j0) = w (ℓ j0) := by
            have : ℓ (ℓ j0) = ℓ j0 := hℓeq j0 (ℓ j0) (hℓmem j0)
            simp [f, hℓmem j0, hqT, this]
          have hrest : ∀ x ∈ (F j0).erase (ℓ j0), f x =
              if ℓ j0 < x then w x - z (ℓ j0) x else 0 := by
            intro x hx
            have hxF := mem_of_mem_erase hx
            have hxne := ne_of_mem_erase hx
            have hTx : Tr x = Tr j0 := by simpa [F] using hxF
            have hlx : ℓ j0 < x := lt_of_le_of_ne (hℓle j0 x hTx) (Ne.symm hxne)
            have : ℓ x = ℓ j0 := hℓeq j0 x hTx
            simp [f, hTx, hqT, this, hlx]
          rw [hfl, Finset.sum_congr rfl hrest]
          have hsub : ∑ x ∈ (F j0).erase (ℓ j0), (if ℓ j0 < x then w x - z (ℓ j0) x else 0) ≤
              ∑ x : Fin n, (if ℓ j0 < x then w x - z (ℓ j0) x else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
            intro x _ _; split_ifs
            · linarith [(hz (ℓ j0) x).2]
            · exact le_refl _
          linarith [hrow (ℓ j0)]
      _ = RS.card := by simp
  have partB : ∑ j ∈ univ.filter (fun j => ¬ Tr j ∈ RS), f j ≤ price * ((∑ i ∈ R, cost i : ℕ) : ℚ) := by
    calc _ ≤ ∑ j ∈ univ.filter (fun j => ¬ Tr j ∈ RS), (if j ∈ R then w j else 0) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hj' := (mem_filter.1 hj).2
          by_cases hq : qual (Tr j)
          · have hjR : j ∈ R := by
              by_contra hjR
              exact hj' (mem_filter.2 ⟨mem_image.2 ⟨j, by simp [hjR], rfl⟩, hq⟩)
            simp only [f, if_pos hq, if_pos hjR]
            split_ifs
            · linarith [(hz (ℓ j) j).1]
            · linarith
          · simp only [f, if_neg hq]
            split_ifs
            · exact (hw j).1
            · exact le_refl _
      _ ≤ ∑ j : Fin n, (if j ∈ R then w j else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          intro x _ _; split_ifs
          · exact (hw x).1
          · exact le_refl _
      _ = ∑ j ∈ R, w j := by rw [Finset.sum_ite_mem, univ_inter]
      _ ≤ ∑ j ∈ R, price * (cost j : ℚ) := Finset.sum_le_sum (fun j _ => (hw j).2)
      _ = price * ((∑ i ∈ R, cost i : ℕ) : ℚ) := by rw [← Finset.mul_sum, Nat.cast_sum]
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun j => Tr j ∈ RS) f
  have hRB : ((∑ i ∈ R, cost i : ℕ) : ℚ) ≤ B := by exact_mod_cast hR
  have : price * ((∑ i ∈ R, cost i : ℕ) : ℚ) ≤ price * B := mul_le_mul_of_nonneg_left hRB hp0
  have hrem : (remA Tr qual R : ℚ) = RS.card := rfl
  rw [hrem]
  linarith

lemma strong (cost : Fin n → ℕ) (B : ℕ) : ∃ R : Finset (Fin n), ∑ i ∈ R, cost i ≤ B ∧
    ∃ price w z, fitsF cost price w z ∧ (remA Tr qual R : ℚ) < objA Tr qual B price w z + 1 := by
  let Q := (univ.image Tr).filter qual
  let CT : β → ℕ := fun T => ∑ j ∈ univ.filter (fun j => Tr j = T), cost j
  let cD : Finset β → ℕ := fun D => ∑ T ∈ D, CT T
  let N := cD Q
  let Aff := Q.powerset.filter (fun D => cD D ≤ B)
  have hAff : Aff.Nonempty := ⟨∅, by simp [Aff, cD]⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image Aff
    (fun D => D.card * (N+1) + (N - cD D)) hAff
  have hDQ : D ⊆ Q := mem_powerset.1 (mem_filter.1 hD).1
  have hDB : cD D ≤ B := (mem_filter.1 hD).2
  have hcDle : ∀ D' ⊆ Q, cD D' ≤ N := fun D' h => Finset.sum_le_sum_of_subset h
  let R := univ.filter (fun j => Tr j ∈ D)
  have hcharge : ∑ i ∈ R, cost i = cD D := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Tr) (t := D) (fun j hj => (mem_filter.1 hj).2)]
    refine sum_congr rfl (fun T hT => ?_)
    congr 1; ext j; simp only [R, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hT, h⟩
  refine ⟨R, hcharge ▸ hDB, ?_⟩
  have hrem : remA Tr qual R ≤ (Q \ D).card := by
    apply card_le_card
    intro T hT
    simp only [mem_filter, mem_image, mem_sdiff, mem_univ, true_and, R] at hT
    obtain ⟨⟨i, hi, rfl⟩, hq⟩ := hT
    simp only [Q, mem_sdiff, mem_filter, mem_image, mem_univ, true_and]
    exact ⟨⟨⟨i, rfl⟩, hq⟩, hi⟩
  by_cases hQD : (Q \ D).Nonempty
  swap
  · refine ⟨0, 0, 0, ?_, ?_⟩
    · simp [fitsF]
    · have : (Q \ D).card = 0 := by
        rw [Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.1 hQD
      have h0 : remA Tr qual R = 0 := by omega
      simp [objA, h0]
  obtain ⟨Ts, hTs, hmin⟩ := Finset.exists_min_image (Q \ D) CT hQD
  have hTsQ : Ts ∈ Q := (mem_sdiff.1 hTs).1
  have hTsD : Ts ∉ D := (mem_sdiff.1 hTs).2
  have fact1 : B < cD D + CT Ts := by
    by_contra h; push_neg at h
    have hsub : insert Ts D ⊆ Q := insert_subset hTsQ hDQ
    have hc : cD (insert Ts D) = CT Ts + cD D := by simp only [cD]; rw [sum_insert hTsD]
    have hmem : insert Ts D ∈ Aff := mem_filter.2 ⟨mem_powerset.2 hsub, by rw [hc]; omega⟩
    have h1 := hmax _ hmem
    have h2 := hcDle _ hsub
    rw [card_insert_of_notMem hTsD, add_mul, one_mul] at h1
    generalize D.card * (N + 1) = K at h1
    omega
  have fact2 : ∀ T ∈ D, CT T ≤ CT Ts := by
    intro T hT
    by_contra h; push_neg at h
    have hTsD' : Ts ∉ D.erase T := fun h' => hTsD (mem_of_mem_erase h')
    have hsub : insert Ts (D.erase T) ⊆ Q := insert_subset hTsQ ((erase_subset _ _).trans hDQ)
    have hc : cD (insert Ts (D.erase T)) + CT T = cD D + CT Ts := by
      simp only [cD]; rw [sum_insert hTsD', add_assoc, sum_erase_add _ _ hT, add_comm]
    have hcard' : (insert Ts (D.erase T)).card = D.card := by
      rw [card_insert_of_notMem hTsD', card_erase_of_mem hT]
      have := card_pos.2 ⟨T, hT⟩; omega
    have hmem : insert Ts (D.erase T) ∈ Aff := mem_filter.2 ⟨mem_powerset.2 hsub, by omega⟩
    have h1 := hmax _ hmem
    have h2 := hcDle _ hDQ
    rw [hcard'] at h1
    generalize D.card * (N + 1) = K at h1
    omega
  set c := CT Ts with hcdef
  have hc1 : 1 ≤ c := by omega
  have hcpos : (0:ℚ) < c := by exact_mod_cast hc1
  let p : ℚ := 1 / c
  have hp0 : 0 ≤ p := by positivity
  have hpc : p * c = 1 := by simp only [p]; field_simp
  let w : Fin n → ℚ := fun j => if qual (Tr j) then
    (if CT (Tr j) ≤ c then p * cost j else (cost j : ℚ) / CT (Tr j)) else 0
  let z : Fin n → Fin n → ℚ := fun i j => if Tr i = Tr j then 0 else w j
  have hw : ∀ j, 0 ≤ w j ∧ w j ≤ p * cost j := by
    intro j
    simp only [w]
    split_ifs with hq hc
    · exact ⟨by positivity, le_refl _⟩
    · push_neg at hc
      have hCpos : (0:ℚ) < CT (Tr j) := by exact_mod_cast (show 0 < CT (Tr j) by omega)
      refine ⟨by positivity, ?_⟩
      rw [show p * (cost j : ℚ) = (cost j : ℚ) / c by simp only [p]; ring]
      exact div_le_div_of_nonneg_left (by positivity) hcpos (by exact_mod_cast hc.le)
    · exact ⟨le_refl _, by positivity⟩
  have hclass : ∀ T, ∑ j ∈ univ.filter (fun j => Tr j = T), w j =
      if qual T then (if CT T ≤ c then p * CT T else 1) else 0 := by
    intro T
    have hwT : ∀ j ∈ univ.filter (fun j => Tr j = T), w j = if qual T then
        (if CT T ≤ c then p * cost j else (cost j : ℚ) / CT T) else 0 := by
      intro j hj
      have := (mem_filter.1 hj).2
      simp only [w, this]
    rw [sum_congr rfl hwT]
    split_ifs with hq hc
    · rw [← Finset.mul_sum]; simp only [CT]; push_cast; rfl
    · push_neg at hc
      have hCpos : (0:ℚ) < CT T := by exact_mod_cast (show 0 < CT T by omega)
      rw [← Finset.sum_div]
      have : ∑ j ∈ univ.filter (fun j => Tr j = T), (cost j : ℚ) = CT T := by
        simp only [CT]; push_cast; rfl
      rw [this, div_self hCpos.ne']
    · simp
  have hclass_le : ∀ T, (if qual T then (if CT T ≤ c then p * CT T else 1) else 0 : ℚ) ≤ 1 := by
    intro T
    split_ifs with hq hc
    · have : (CT T : ℚ) ≤ c := by exact_mod_cast hc
      nlinarith
    · exact le_refl _
    · norm_num
  have hfits : fitsF cost p w z := by
    refine ⟨hp0, ?_, hw, ?_, ?_⟩
    · simp only [p]; rw [div_le_one hcpos]; exact_mod_cast hc1
    · intro i j; simp only [z]; split_ifs
      · exact ⟨le_refl _, (hw j).1⟩
      · exact ⟨(hw j).1, le_refl _⟩
    · intro i
      have h1 : ∑ j : Fin n, (if i < j then w j - z i j else 0) =
          ∑ j ∈ univ.filter (fun j => i < j ∧ Tr j = Tr i), w j := by
        rw [Finset.sum_filter]
        refine sum_congr rfl (fun j _ => ?_)
        simp only [z]
        by_cases h1 : i < j <;> by_cases h2 : Tr j = Tr i
        · simp [h1, h2]
        · simp [h1, h2, Ne.symm h2]
        · simp [h1]
        · simp [h1]
      rw [h1]
      have hi : i ∉ univ.filter (fun j => i < j ∧ Tr j = Tr i) := by simp
      rw [← Finset.sum_insert hi]
      calc _ ≤ ∑ j ∈ univ.filter (fun j => Tr j = Tr i), w j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [mem_insert] at hx
              rcases hx with rfl | hx
              · simp
              · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩
            · intro x _ _; exact (hw x).1
        _ ≤ 1 := by rw [hclass]; exact hclass_le _
  refine ⟨p, w, z, hfits, ?_⟩
  have hobj : objA Tr qual B p w z = ∑ j, w j - p * B := by
    simp only [objA]
    congr 1
    refine sum_congr rfl (fun i _ => ?_)
    have h0 : ∑ j : Fin n, (if i < j then hh Tr qual i j * z i j else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      simp only [hh, z]
      split_ifs <;> simp_all
    rw [h0, sub_zero]
    simp only [hh, w]
    split_ifs <;> simp_all
  have hsumw : ∑ j, w j = ((Q \ D).card : ℚ) + p * (cD D : ℚ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (g := Tr) (t := univ.image Tr)
      (fun j _ => mem_image_of_mem Tr (mem_univ j))]
    rw [sum_congr rfl (fun T _ => hclass T), ← Finset.sum_filter]
    rw [← Finset.sum_sdiff hDQ]
    have hA : ∑ T ∈ Q \ D, (if CT T ≤ c then p * CT T else 1 : ℚ) = ∑ T ∈ Q \ D, (1:ℚ) := by
      refine sum_congr rfl (fun T hT => ?_)
      have := hmin T hT
      split_ifs with h
      · have : CT T = c := le_antisymm h this
        rw [this, hpc]
      · rfl
    have hB : ∑ T ∈ D, (if CT T ≤ c then p * CT T else 1 : ℚ) = ∑ T ∈ D, p * (CT T : ℚ) := by
      refine sum_congr rfl (fun T hT => ?_)
      rw [if_pos (fact2 T hT)]
    rw [hA, hB, ← Finset.mul_sum]
    simp only [cD]; push_cast
    simp
  rw [hobj, hsumw]
  have hrem' : (remA Tr qual R : ℚ) ≤ (Q \ D).card := by exact_mod_cast hrem
  have hfact : (B : ℚ) < cD D + c := by exact_mod_cast fact1
  have : p * B < p * (cD D + c) := mul_lt_mul_of_pos_left hfact (by positivity)
  rw [mul_add, hpc] at this
  linarith

end Panel
end PEqualNP.Outside.L_lib_942_aux

namespace PEqualNP.Outside.L_lib_942_aux
open Finset

section Encode
variable {n : ℕ}

abbrev Kv (n : ℕ) := Option (Option (Fin n ⊕ Fin n × Fin n))

def vt : Kv n := none
def vp : Kv n := some none
def vw (i : Fin n) : Kv n := some (some (Sum.inl i))
def vz (i j : Fin n) : Kv n := some (some (Sum.inr (i, j)))

def pj (k : Kv n) : (Kv n → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj k

lemma pj_apply (k : Kv n) (x : Kv n → ℚ) : pj k x = x k := rfl

def objL (h : Fin n → Fin n → ℚ) (C B : ℚ) : (Kv n → ℚ) →ₗ[ℚ] ℚ :=
  (1 / C) • (∑ i, (h i i • pj (vw i) - ∑ j, if i < j then h i j • pj (vz i j) else 0)) -
    B • pj vp

lemma objL_apply (h : Fin n → Fin n → ℚ) (C B : ℚ) (x : Kv n → ℚ) :
    objL h C B x = (∑ i, (h i i * x (vw i) - ∑ j, if i < j then h i j * x (vz i j) else 0)) / C
      - x vp * B := by
  simp only [objL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, pj_apply, smul_eq_mul, apply_ite (fun f : (Kv n → ℚ) →ₗ[ℚ] ℚ => f x),
    LinearMap.zero_apply]
  ring

def fitsL (cost : Fin n → ℕ) : List (Con (Kv n)) :=
  [(-pj vp, 0), (pj vp, 1)] ++
  (List.finRange n).flatMap (fun i => [(-pj (vw i), 0), (pj (vw i) - (cost i : ℚ) • pj vp, 0),
     (pj (vw i) + ∑ j, (if i < j then pj (vw j) - pj (vz i j) else 0), 1)]) ++
  (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j =>
     [(-pj (vz i j), 0), (pj (vz i j) - pj (vw j), 0)]))

lemma sum_lin_apply (x : Kv n → ℚ) (i : Fin n) :
    (∑ j, (if i < j then pj (vw j) - pj (vz i j) else 0 : (Kv n → ℚ) →ₗ[ℚ] ℚ)) x =
      ∑ j, (if i < j then x (vw j) - x (vz i j) else 0) := by
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  refine sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [pj_apply]

lemma sat_fitsL (cost : Fin n → ℕ) (x : Kv n → ℚ) :
    Sat (fitsL cost) x ↔ fitsF cost (x vp) (fun i => x (vw i)) (fun i j => x (vz i j)) := by
  simp only [Sat, fitsL, List.forall_mem_append, List.forall_mem_cons, List.mem_flatMap,
    List.mem_finRange, true_and, forall_exists_index, List.not_mem_nil,
    IsEmpty.forall_iff, forall_const, and_true, LinearMap.neg_apply, pj_apply]
  simp only [fitsF]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨by linarith, h2, fun i => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩, fun i => ?_⟩
    · have := h3 (-pj (vw i), 0) i (by simp)
      simp only [LinearMap.neg_apply, pj_apply] at this; linarith
    · have := h3 (pj (vw i) - (cost i : ℚ) • pj vp, 0) i (by simp)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pj_apply, smul_eq_mul] at this
      linarith
    · have := h4 (-pj (vz i j), 0) i j (by simp)
      simp only [LinearMap.neg_apply, pj_apply] at this; linarith
    · have := h4 (pj (vz i j) - pj (vw j), 0) i j (by simp)
      simp only [LinearMap.sub_apply, pj_apply] at this; linarith
    · have := h3 (pj (vw i) + ∑ j, (if i < j then pj (vw j) - pj (vz i j) else 0), 1) i (by simp)
      simp only [LinearMap.add_apply, pj_apply, sum_lin_apply] at this
      exact this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨⟨by linarith, h2⟩, ?_⟩, ?_⟩
    · intro c i hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · simp only [LinearMap.neg_apply, pj_apply]; linarith [(h3 i).1]
      · simp only [LinearMap.sub_apply, LinearMap.smul_apply, pj_apply, smul_eq_mul]
        linarith [(h3 i).2]
      · simp only [LinearMap.add_apply, pj_apply, sum_lin_apply]; exact h5 i
    · intro c i j hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [LinearMap.neg_apply, pj_apply]; linarith [(h4 i j).1]
      · simp only [LinearMap.sub_apply, pj_apply]; linarith [(h4 i j).2]

lemma attain_gen (cost : Fin n → ℕ) (h : Fin n → Fin n → ℚ) (C B : ℚ)
    (hbd : ∃ M, ∀ pr w z, fitsF cost pr w z →
      (∑ i, (h i i * w i - ∑ j, if i < j then h i j * z i j else 0)) / C - pr * B ≤ M) :
    ∃ pr w z, fitsF cost pr w z ∧ ∀ pr' w' z', fitsF cost pr' w' z' →
      (∑ i, (h i i * w' i - ∑ j, if i < j then h i j * z' i j else 0)) / C - pr' * B ≤
      (∑ i, (h i i * w i - ∑ j, if i < j then h i j * z i j else 0)) / C - pr * B := by
  let L : List (Con (Kv n)) := fitsL cost ++ [(pj vt - objL h C B, 0)]
  have hSat : ∀ x, Sat L x ↔ fitsF cost (x vp) (fun i => x (vw i)) (fun i j => x (vz i j)) ∧
      x vt ≤ objL h C B x := by
    intro x
    have : Sat L x ↔ Sat (fitsL cost) x ∧ ((pj (vt : Kv n) - objL h C B : (Kv n → ℚ) →ₗ[ℚ] ℚ) x ≤ 0) := by
      simp only [Sat, L, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, forall_const, and_true]
    rw [this, sat_fitsL, LinearMap.sub_apply, pj_apply, sub_nonpos]
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨xs, hxs, hmax⟩ := lp_attain (vt : Kv n) L
    ⟨0, (hSat 0).2 ⟨by simp [fitsF], by simp⟩⟩
    ⟨M, fun x hx => by
      obtain ⟨hf, hle⟩ := (hSat x).1 hx
      have := hM _ _ _ hf
      rw [objL_apply] at hle
      linarith⟩
  obtain ⟨hf, hle⟩ := (hSat xs).1 hxs
  refine ⟨xs vp, fun i => xs (vw i), fun i j => xs (vz i j), hf, fun pr' w' z' hf' => ?_⟩
  let val := (∑ i, (h i i * w' i - ∑ j, if i < j then h i j * z' i j else 0)) / C - pr' * B
  let x' : Kv n → ℚ := fun k => match k with
    | none => val
    | some none => pr'
    | some (some (Sum.inl i)) => w' i
    | some (some (Sum.inr (i, j))) => z' i j
  have hx' : Sat L x' := (hSat x').2 ⟨hf', by rw [objL_apply]; exact le_refl _⟩
  have := hmax x' hx'
  rw [objL_apply] at hle
  exact this.trans hle

end Encode

section Final
variable {m n : ℕ}

lemma gramF_nonneg (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (t : Fin d)
    (i j : Fin n) : 0 ≤ gramF q d A P t i j := by
  rw [gramF_eq]; positivity

lemma hitF_nonneg (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (i j : Fin n) :
    0 ≤ hitF q d A P i j :=
  Finset.sum_nonneg (fun t _ => gramF_nonneg q d A P t i j)

lemma attain_score (q d budget : ℕ) (A : Fin n → Finset (Fin m)) (cost : Fin n → ℕ)
    (P : Finset (Fin m)) :
    ∃ pr w z, fitsF cost pr w z ∧ ∀ pr' w' z', fitsF cost pr' w' z' →
      scoreF q d budget A P pr' w' z' ≤ scoreF q d budget A P pr w z := by
  have := attain_gen cost (hitF q d A P) ((Nat.choose (m-P.card) (q-P.card) : ℕ) : ℚ)
    (budget : ℚ) ⟨(∑ i, hitF q d A P i i * cost i) / ((Nat.choose (m-P.card) (q-P.card) : ℕ) : ℚ),
      fun pr w z hf => by
        obtain ⟨hp0, hp1, hw, hz, _⟩ := hf
        have h1 : (∑ i, (hitF q d A P i i * w i -
            ∑ j, if i < j then hitF q d A P i j * z i j else 0)) ≤
            ∑ i, hitF q d A P i i * cost i := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hs : 0 ≤ ∑ j, (if i < j then hitF q d A P i j * z i j else 0) := by
            refine Finset.sum_nonneg (fun j _ => ?_)
            split_ifs
            · exact mul_nonneg (hitF_nonneg q d A P i j) (hz i j).1
            · exact le_refl _
          have hwi : w i ≤ cost i := by
            have := (hw i).2
            have : pr * (cost i : ℚ) ≤ cost i := by
              have hc : (0:ℚ) ≤ cost i := by positivity
              nlinarith
            linarith
          have := mul_le_mul_of_nonneg_left hwi (hitF_nonneg q d A P i i)
          linarith
        have h2 := div_le_div_of_nonneg_right h1
          (show (0:ℚ) ≤ ((Nat.choose (m-P.card) (q-P.card) : ℕ) : ℚ) by positivity)
        have h3 : 0 ≤ pr * (budget : ℚ) := by positivity
        linarith⟩
  simpa only [scoreF] using this

lemma hit_full (q d : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m)) (hP : P.card = q)
    (i j : Fin n) : hitF q d A P i j =
      hh (fun i => A i ∩ P) (fun T => T.Nonempty ∧ T.card ≤ d) i j := by
  have hG : ∀ t : Fin d, (G q A P (t.val + 1) i j : ℚ) =
      if A i ∩ P = A j ∩ P ∧ (A i ∩ P).card = t.val + 1 then 1 else 0 := by
    intro t
    unfold G
    by_cases h : A i ∩ P = A j ∩ P ∧ (A i ∩ P).card = t.val + 1
    · rw [if_pos ⟨h.1, by omega, by omega⟩, if_pos h]
      rw [show t.val + 1 - (A i ∩ P).card = 0 by omega, hP]
      simp
    · rw [if_neg (fun h' => h ⟨h'.1, by omega⟩), if_neg h]; simp
  simp only [hitF, gramF_eq, hG, hh]
  by_cases hc : A i ∩ P = A j ∩ P ∧ 1 ≤ (A i ∩ P).card ∧ (A i ∩ P).card ≤ d
  · have hd : (A i ∩ P).card - 1 < d := by omega
    rw [Finset.sum_eq_single ⟨(A i ∩ P).card - 1, hd⟩]
    · rw [if_pos ⟨hc.1, by simp; omega⟩, if_pos ⟨hc.1, Finset.card_pos.1 (by omega), hc.2.2⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply hb; ext; simp; omega
    · simp
  · rw [if_neg]
    · refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hc ⟨h1, by omega, by have := t.isLt; omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact hc ⟨h1, Finset.card_pos.2 h2, h3⟩

lemma score_full (q d budget : ℕ) (A : Fin n → Finset (Fin m)) (P : Finset (Fin m))
    (hP : P.card = q) (pr : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) :
    scoreF q d budget A P pr w z =
      objA (fun i => A i ∩ P) (fun T => T.Nonempty ∧ T.card ≤ d) budget pr w z := by
  simp only [scoreF, objA, hit_full q d A P hP, hP, Nat.sub_self, Nat.choose_zero_right,
    Nat.cast_one, div_one]

end Final
end PEqualNP.Outside.L_lib_942_aux

open PEqualNP.Outside.L_lib_942_aux in
theorem PEqualNP.Outside.L_lib_942 : (∀ (m n q d budget : ℕ) (A : Fin n → Finset (Fin m)) (cost : Fin n → ℕ), q ≤ m →
  let W := Fin n → ℚ
  let D := Fin n → Fin n → ℚ
  let fits := fun (price : ℚ) (w : W) (z : D) =>
    0 ≤ price ∧ price ≤ 1 ∧ (∀ i, 0 ≤ w i ∧ w i ≤ price * (cost i : ℚ)) ∧
    (∀ i j, 0 ≤ z i j ∧ z i j ≤ w j) ∧
    ∀ i, w i + (∑ j : Fin n, if i < j then w j - z i j else 0) ≤ 1
  let panels := fun P : Finset (Fin m) => Nat.choose (m-P.card) (q-P.card)
  let gram := fun (P : Finset (Fin m)) (level : Fin d) (i j : Fin n) =>
    let t := level.val+1
    let locked := A i ∩ P
    let extra := t-locked.card
    let left := q-P.card
    let both := (A i ∩ A j) \ P
    let neither := (Finset.univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)
    if locked = A j ∩ P ∧ locked.card ≤ t ∧ extra ≤ left then
      ((Nat.choose both.card extra * Nat.choose neither.card (left-extra) : ℕ) : ℚ)
    else 0
  let hit := fun (P : Finset (Fin m)) (i j : Fin n) => ∑ t : Fin d, gram P t i j
  let score := fun (P : Finset (Fin m)) (price : ℚ) (w : W) (z : D) =>
    (∑ i : Fin n, (hit P i i * w i - (∑ j : Fin n, if i < j then hit P i j * z i j else 0))) /
      (panels P : ℚ) - price * (budget : ℚ)
  let charge := fun R : Finset (Fin n) => ∑ i ∈ R, cost i
  let remain := fun (P : Finset (Fin m)) (R : Finset (Fin n)) =>
    ((((Finset.univ \ R).image (fun i : Fin n => A i ∩ P))).filter
      (fun T => T.Nonempty ∧ T.card ≤ d)).card
  ∃ value : Finset (Fin m) → ℚ, ∀ P : Finset (Fin m), P.card ≤ q →
    (∃ (price : ℚ) (w : W) (z : D), fits price w z ∧ score P price w z = value P) ∧
    (∀ (price : ℚ) (w : W) (z : D), fits price w z → score P price w z ≤ value P) ∧
    (P.card < q → ((m-P.card : ℕ) : ℚ) * value P ≤
      ∑ j ∈ (Finset.univ \ P), value (insert j P)) ∧
    (P.card = q → ∃ R : Finset (Fin n), charge R ≤ budget ∧ (remain P R : ℚ) < value P + 1) ∧
    ∃ S : Finset (Fin m), P ⊆ S ∧ S.card = q ∧
      ∀ R : Finset (Fin n), charge R ≤ budget → value P ≤ (remain S R : ℚ)) := by
  intro m n q d budget A cost hq W D fits panels gram hit score charge remain
  choose pr w z hf hmax using fun P => attain_score q d budget A cost P
  let value : Finset (Fin m) → ℚ := fun P => scoreF q d budget A P (pr P) (w P) (z P)
  have havg : ∀ P : Finset (Fin m), P.card < q →
      ((m - P.card : ℕ) : ℚ) * value P ≤ ∑ j ∈ Finset.univ \ P, value (insert j P) := by
    intro P hP
    rw [← score_avg q d budget A P hP hq]
    exact Finset.sum_le_sum (fun c _ => hmax (insert c P) _ _ _ (hf P))
  have hfull_le : ∀ S : Finset (Fin m), S.card = q → ∀ R : Finset (Fin n),
      ∑ i ∈ R, cost i ≤ budget →
      value S ≤ (remA (fun i => A i ∩ S) (fun T => T.Nonempty ∧ T.card ≤ d) R : ℚ) := by
    intro S hS R hR
    simp only [value]
    rw [score_full q d budget A S hS]
    exact weak _ _ cost budget _ _ _ (hf S) R hR
  have hclimb : ∀ k, ∀ P : Finset (Fin m), q - P.card = k → P.card ≤ q →
      ∃ S, P ⊆ S ∧ S.card = q ∧ value P ≤ value S := by
    intro k
    induction k with
    | zero => intro P hk hP; exact ⟨P, subset_refl _, by omega, le_refl _⟩
    | succ k ih =>
      intro P hk hP
      have hlt : P.card < q := by omega
      have hne : (Finset.univ \ P).Nonempty := by
        rw [← Finset.card_pos, Finset.card_univ_diff, Fintype.card_fin]; omega
      obtain ⟨c, hc, hcv⟩ : ∃ c ∈ Finset.univ \ P, value P ≤ value (insert c P) := by
        by_contra hno
        push_neg at hno
        have := Finset.sum_lt_sum_of_nonempty hne hno
        rw [Finset.sum_const, Finset.card_univ_diff, Fintype.card_fin, nsmul_eq_mul] at this
        have h2 := havg P hlt
        push_cast [Nat.cast_sub (show P.card ≤ m by omega)] at h2 this
        linarith
      have hcard : (insert c P).card = P.card + 1 :=
        Finset.card_insert_of_notMem (Finset.mem_sdiff.1 hc).2
      obtain ⟨S, hS1, hS2, hS3⟩ := ih (insert c P) (by omega) (by omega)
      exact ⟨S, (Finset.subset_insert c P).trans hS1, hS2, hcv.trans hS3⟩
  refine ⟨value, fun P hP => ⟨⟨pr P, w P, z P, hf P, rfl⟩,
    fun pr' w' z' h' => hmax P pr' w' z' h', fun hlt => havg P hlt, fun heq => ?_, ?_⟩⟩
  · obtain ⟨R, hR, pr', w', z', hf', hlt⟩ :=
      strong (fun i => A i ∩ P) (fun T => T.Nonempty ∧ T.card ≤ d) cost budget
    refine ⟨R, hR, ?_⟩
    have := hmax P pr' w' z' hf'
    rw [score_full q d budget A P heq] at this
    show (remA (fun i => A i ∩ P) (fun T => T.Nonempty ∧ T.card ≤ d) R : ℚ) < value P + 1
    linarith
  · obtain ⟨S, hS1, hS2, hS3⟩ := hclimb _ P rfl hP
    exact ⟨S, hS1, hS2, fun R hR => hS3.trans (hfull_le S hS2 R hR)⟩
