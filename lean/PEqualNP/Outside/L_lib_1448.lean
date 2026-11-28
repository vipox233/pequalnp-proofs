import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1448

open PEqualNP.CircuitLowerBounds

def hh (L s : ℕ) : ℕ :=
  if s = 0 then 0 else if s = 2*L+1 then L else if s % 2 = 1 then (s+1)/2 else (s-2)/2

def bb (L t d s : ℕ) : ℕ :=
  hh L s * d + (if s ≠ 0 ∧ (s % 2 = 0 ∨ s = 2*L+1) then t+d else 0)

def wd (L q t d s v : ℕ) : Prop := v < hh L s * q ∨ (L*q ≤ v ∧ v < L*q + bb L t d s)

lemma stage (L t d s : ℕ) (hs : s < 2*L+2) :
    (s = 0 ∧ hh L s = 0 ∧ bb L t d s = 0) ∨
    (s % 2 = 1 ∧ s < 2*L+1 ∧ 2 * hh L s = s + 1 ∧ bb L t d s = hh L s * d) ∨
    (s % 2 = 0 ∧ s ≠ 0 ∧ 2 * hh L s + 2 = s ∧ bb L t d s = hh L s * d + t + d) ∨
    (s = 2*L+1 ∧ hh L s = L ∧ bb L t d s = hh L s * d + t + d) := by
  unfold bb hh
  split_ifs <;> omega

lemma gap (L t d q s u : ℕ) (hq : q + d = t) (h2 : 2*d ≤ t) (hu : u < s) (hs : s < 2*L+2) :
    t ≤ (hh L s * q - hh L u * q) + (bb L t d s - bb L t d u) := by
  have hS := stage L t d s hs
  have hU := stage L t d u (by omega)
  generalize bb L t d s = bs at *
  generalize bb L t d u = bu at *
  generalize hh L s = H at *
  generalize hh L u = G at *
  rcases le_or_gt G H with hGH | hGH
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hGH
    have e1 : (G+e)*q = G*q + e*q := by ring
    have e2 : (G+e)*d = G*d + e*d := by ring
    have e3 : 1 ≤ e → q ≤ e*q := fun h => Nat.le_mul_of_pos_left q h
    have e4 : 1 ≤ e → d ≤ e*d := fun h => Nat.le_mul_of_pos_left d h
    have e5 : 2 ≤ e → 2*q ≤ e*q := fun h => Nat.mul_le_mul_right q h
    omega
  · have e1 : G = H+1 → G*d = H*d + d := by rintro rfl; ring
    have e2 : H*q ≤ G*q := Nat.mul_le_mul_right q hGH.le
    omega

def ob (L a q t d s v : ℕ) : Prop :=
  s ≠ 0 ∧ (s = 2*L+1 ∨ v < ((s+1)/2 - 1)*q ∨ (v < (s+1)/2*q ∧ a ≤ v % q) ∨
    (L*q ≤ v ∧ v < L*q + (s/2+1)*d) ∨ (L*q ≤ v ∧ v < L*q + s/2*d + t ∧ a ≤ v % q))

lemma ob_mono (L a q t d s u v : ℕ) (hsu : s ≤ u) (hu : u < 2*L+2) (h : ob L a q t d s v) :
    ob L a q t d u v := by
  unfold ob at *
  have h1 : ((s+1)/2 - 1)*q ≤ ((u+1)/2 - 1)*q := Nat.mul_le_mul_right q (by omega)
  have h2 : (s+1)/2*q ≤ (u+1)/2*q := Nat.mul_le_mul_right q (by omega)
  have h3 : (s/2+1)*d ≤ (u/2+1)*d := Nat.mul_le_mul_right d (by omega)
  have h4 : s/2*d ≤ u/2*d := Nat.mul_le_mul_right d (by omega)
  omega

def xlo (L q d s : ℕ) : ℕ := if s % 2 = 1 then (hh L s - 1)*q else L*q + (s/2+1)*d
def xhi (L q d s : ℕ) : ℕ := if s % 2 = 1 then L*q + hh L s * d else hh L s * q

lemma near_lo (L a q t d s v : ℕ) (hq : q + d = t) (hs : s < 2*L+2) (hw : wd L q t d s v)
    (ho : ¬ ob L a q t d s v) : xlo L q d s ≤ v ∧ v < xlo L q d s + q ∧ v % q < a := by
  have hS := stage L t d s hs
  unfold wd at hw; unfold ob at ho; unfold xlo
  generalize bb L t d s = bs at *
  generalize hh L s = H at *
  rcases hS with ⟨h0, hH, hb⟩ | ⟨h1, h1', hH, hb⟩ | ⟨h1, h1', hH, hb⟩ | ⟨h0, hH, hb⟩
  · subst hH hb; omega
  · obtain ⟨k, rfl⟩ : ∃ k, H = k+1 := ⟨H-1, by omega⟩
    have e3 : (s+1)/2 - 1 = k := by omega
    have e1 : (s+1)/2 = k+1 := by omega
    have e2 : s/2 = k := by omega
    rw [e3, e1, e2] at ho
    rw [if_pos h1, Nat.add_sub_cancel]
    have p1 : (k+1)*q = k*q + q := by ring
    have p2 : (k+1)*d = k*d + d := by ring
    omega
  · have e3 : (s+1)/2 - 1 = H := by omega
    have e1 : (s+1)/2 = H+1 := by omega
    have e2 : s/2 = H+1 := by omega
    rw [e3, e1, e2] at ho
    rw [if_neg (by omega), e2]
    have p1 : (H+1)*q = H*q + q := by ring
    have p2 : (H+1)*d = H*d + d := by ring
    have p3 : (H+1+1)*d = H*d + d + d := by ring
    omega
  · omega

lemma near_hi (L a q t d s v : ℕ) (hq : q + d = t) (hs : s < 2*L+2)
    (hv : v < L*q + L*d + t + d) (ho : ob L a q t d s v) (hw : ¬ wd L q t d s v) :
    xhi L q d s ≤ v ∧ v < xhi L q d s + q ∧ a ≤ v % q := by
  have hS := stage L t d s hs
  unfold wd at hw; unfold ob at ho; unfold xhi
  generalize bb L t d s = bs at *
  generalize hh L s = H at *
  rcases hS with ⟨h0, hH, hb⟩ | ⟨h1, h1', hH, hb⟩ | ⟨h1, h1', hH, hb⟩ | ⟨h0, hH, hb⟩
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, H = k+1 := ⟨H-1, by omega⟩
    have e3 : (s+1)/2 - 1 = k := by omega
    have e1 : (s+1)/2 = k+1 := by omega
    have e2 : s/2 = k := by omega
    rw [e3, e1, e2] at ho
    rw [if_pos h1]
    have p1 : (k+1)*q = k*q + q := by ring
    have p2 : (k+1)*d = k*d + d := by ring
    omega
  · have e3 : (s+1)/2 - 1 = H := by omega
    have e1 : (s+1)/2 = H+1 := by omega
    have e2 : s/2 = H+1 := by omega
    rw [e3, e1, e2] at ho
    rw [if_neg (by omega)]
    have p1 : (H+1)*q = H*q + q := by ring
    have p2 : (H+1)*d = H*d + d := by ring
    have p3 : (H+1+1)*d = H*d + d + d := by ring
    omega
  · subst hH hb; omega

lemma common (L t d q v : ℕ) (hL : 0 < L) (hq : q + d = t) :
    (∀ s, s < 2*L+2 → (wd L q t d s v ↔ (s ≠ 0 ∧ (s % 2 = 0 ∨ s = 2*L+1)))) ↔
      (L*q + L*d ≤ v ∧ v < L*q + t + d) := by
  constructor
  · intro h
    have h2 := h 2 (by omega)
    have h1 := h (2*L-1) (by omega)
    have a1 : hh L 2 = 0 := by unfold hh; split_ifs <;> omega
    have a2 : bb L t d 2 = t + d := by unfold bb; rw [a1, if_pos (by omega)]; omega
    have a3 : hh L (2*L-1) = L := by unfold hh; split_ifs <;> omega
    have a4 : bb L t d (2*L-1) = L*d := by unfold bb; rw [a3, if_neg (by omega)]; omega
    unfold wd at h1 h2
    rw [a1, a2] at h2
    rw [a3, a4] at h1
    omega
  · rintro ⟨h1, h2⟩ s hs
    have hS := stage L t d s hs
    unfold wd
    generalize bb L t d s = bs at *
    generalize hh L s = H at *
    have hHL : H ≤ L := by omega
    have := Nat.mul_le_mul_right q hHL
    have := Nat.mul_le_mul_right d hHL
    omega

lemma card_Ico_fin (r lo hi : ℕ) (h : hi ≤ r) (S : Finset (Fin r))
    (hS : ∀ v, v ∈ S ↔ lo ≤ v.val ∧ v.val < hi) : S.card = hi - lo := by
  have : S.map Fin.valEmbedding = Finset.Ico lo hi := by
    ext x
    simp only [Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hS v).1 hv
    · intro hx
      exact ⟨⟨x, by omega⟩, (hS _).2 hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

lemma card_two (r x1 y1 x2 y2 : ℕ) (h1 : y1 ≤ x2) (h3 : y1 ≤ r) (h2 : y2 ≤ r) (S : Finset (Fin r))
    (hS : ∀ v, v ∈ S ↔ (x1 ≤ v.val ∧ v.val < y1) ∨ (x2 ≤ v.val ∧ v.val < y2)) :
    S.card = (y1 - x1) + (y2 - x2) := by
  have : S.map Fin.valEmbedding = Finset.Ico x1 y1 ∪ Finset.Ico x2 y2 := by
    ext x
    simp only [Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_Ico, Finset.mem_union]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hS v).1 hv
    · intro hx
      exact ⟨⟨x, by omega⟩, (hS _).2 hx, rfl⟩
  have hd : Disjoint (Finset.Ico x1 y1) (Finset.Ico x2 y2) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_Ico] at hx hx2
    omega
  rw [← Finset.card_map Fin.valEmbedding, this, Finset.card_union_of_disjoint hd, Nat.card_Ico,
    Nat.card_Ico]

lemma card_chain {α : Type} [DecidableEq α] (W1 W2 X Y T : Finset α) (a f : ℕ)
    (h1 : (W1 \ X).card ≤ a) (h2 : (Y \ W2).card ≤ f) (hXY : X ⊆ Y)
    (hT : ∀ x ∈ T, x ∈ W1 ∧ x ∉ W2) : T.card ≤ a + f := by
  have hsub : T ⊆ (W1 \ X) ∪ (Y \ W2) := by
    intro x hx
    obtain ⟨p, p'⟩ := hT x hx
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hxX : x ∈ X
    · right; exact ⟨hXY hxX, p'⟩
    · left; exact ⟨p, hxX⟩
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_union_le (W1 \ X) (Y \ W2)
  omega

lemma mod_inj (q x v w : ℕ) (hv : x ≤ v) (hv' : v < x+q) (hw : x ≤ w) (hw' : w < x+q)
    (h : v % q = w % q) : v = w := by
  rcases le_total v w with hvw | hvw
  · have h1 : q ∣ w - v := (Nat.modEq_iff_dvd' hvw).1 h
    have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega
  · have h1 : q ∣ v - w := (Nat.modEq_iff_dvd' hvw).1 h.symm
    have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega

lemma card_lo (r q a x : ℕ) (S : Finset (Fin r))
    (hS : ∀ v ∈ S, x ≤ v.val ∧ v.val < x + q ∧ v.val % q < a) : S.card ≤ a := by
  have := Finset.card_le_card_of_injOn (s := S) (t := Finset.range a) (fun v => v.val % q)
    (fun v hv => Finset.mem_range.2 (hS v hv).2.2)
    (fun v hv w hw h => Fin.ext (mod_inj q x _ _ (hS v hv).1 (hS v hv).2.1 (hS w hw).1
      (hS w hw).2.1 h))
  simpa using this

lemma card_hi (r q a f x : ℕ) (hqaf : q ≤ a + f) (S : Finset (Fin r))
    (hS : ∀ v ∈ S, x ≤ v.val ∧ v.val < x + q ∧ a ≤ v.val % q) : S.card ≤ f := by
  have := Finset.card_le_card_of_injOn (s := S) (t := Finset.Ico a q) (fun v => v.val % q)
    (fun v hv => Finset.mem_Ico.2 ⟨(hS v hv).2.2, Nat.mod_lt _ (by have := hS v hv; omega)⟩)
    (fun v hv w hw h => Fin.ext (mod_inj q x _ _ (hS v hv).1 (hS v hv).2.1 (hS w hw).1
      (hS w hw).2.1 h))
  rw [Nat.card_Ico] at this
  omega

def gA (L q d j : ℕ) : ℕ :=
  if j < L*q then j/q else if (j - L*q)/d < L then (j-L*q)/d else L+1

def gB (L q t d j : ℕ) : ℕ :=
  if j < L*q then L+1 else if j - L*q < t+d then L+2
    else if (j-L*q-(t+d))/d < L then (j-L*q-(t+d))/d else L+1

lemma gA_lt (L q d j : ℕ) : gA L q d j < L+3 := by
  unfold gA
  split_ifs with h1 h2
  · have : j / q < L := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h1)
    omega
  · omega
  · omega

lemma gB_lt (L q t d j : ℕ) : gB L q t d j < L+3 := by
  unfold gB
  split_ifs <;> omega

lemma sel_spec (L q t d H j : ℕ) (U : Prop) (xv : ℕ → Bool) (hq0 : 0 < q) (hd0 : 0 < d)
    (hHL : H ≤ L) (hj : j < L*q + L*d + t + d)
    (h1 : ∀ i, i < L → (xv i = true ↔ i < H)) (h2 : xv L = true ↔ U) (h3 : xv (L+1) = false)
    (h4 : xv (L+2) = true) (bbv : ℕ) (hb1 : U → bbv = H*d + t + d) (hb0 : ¬U → bbv = H*d) :
    ((xv (gA L q d j) || (xv L && xv (gB L q t d j))) = true ↔
      (j < H*q ∨ (L*q ≤ j ∧ j < L*q + bbv))) := by
  unfold gA gB
  have hHq : H*q ≤ L*q := Nat.mul_le_mul_right q hHL
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  by_cases hjm : j < L*q
  · rw [if_pos hjm, if_pos hjm, h3]
    have : j/q < L := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hjm)
    rw [h1 _ this, Nat.div_lt_iff_lt_mul hq0]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · simp at h
    · rintro (h | h)
      · exact Or.inl h
      · omega
  · rw [if_neg hjm, if_neg hjm]
    obtain ⟨j', rfl⟩ : ∃ j', j = L*q + j' := ⟨j - L*q, by omega⟩
    simp only [Nat.add_sub_cancel_left]
    have hA : (xv (if j'/d < L then j'/d else L+1) = true) ↔ j' < H*d := by
      by_cases h : j'/d < L
      · rw [if_pos h, h1 _ h, Nat.div_lt_iff_lt_mul hd0]
      · rw [if_neg h, h3]
        have : ¬ j' < H*d := fun h' => h (lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul hd0).2 h') hHL)
        simp [this]
    have hB : (xv (if j' < t+d then L+2 else if (j'-(t+d))/d < L then (j'-(t+d))/d else L+1) = true) ↔
        (j' < t + d ∨ j' - (t+d) < H*d) := by
      by_cases h : j' < t+d
      · rw [if_pos h, h4]; simp [h]
      · rw [if_neg h]
        have hlt : (j'-(t+d))/d < L := (Nat.div_lt_iff_lt_mul hd0).2 (by omega)
        rw [if_pos hlt, h1 _ hlt, Nat.div_lt_iff_lt_mul hd0]
        simp [h]
    rw [hA, hB, h2]
    by_cases hU : U
    · rw [hb1 hU]; simp only [hU, true_and]; omega
    · rw [hb0 hU]; simp only [hU, false_and, or_false]; omega

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := List.getD_append _ _ _ _ h

lemma getD_snoc_eq (w : List Bool) (b : Bool) (i : ℕ) (h : i = w.length) :
    (w ++ [b]).getD i false = b := by
  subst h
  simp

def mkGates (L : ℕ) (A B : ℕ → ℕ) (n : ℕ) : List Gate :=
  (List.range n).flatMap fun j => [⟨GateOp.and, [L, B j]⟩, ⟨GateOp.or, [A j, L+3+2*j]⟩]

lemma mkGates_succ (L : ℕ) (A B : ℕ → ℕ) (n : ℕ) : mkGates L A B (n+1) =
    mkGates L A B n ++ [⟨GateOp.and, [L, B n]⟩, ⟨GateOp.or, [A n, L+3+2*n]⟩] := by
  simp [mkGates, List.range_succ, List.flatMap_append]

lemma mkGates_length (L : ℕ) (A B : ℕ → ℕ) (n : ℕ) : (mkGates L A B n).length = 2*n := by
  induction n with
  | zero => simp [mkGates]
  | succ n ih => rw [mkGates_succ, List.length_append, ih]; simp; omega

lemma wires_spec (L : ℕ) (A B : ℕ → ℕ) (hA : ∀ j, A j < L+3) (hB : ∀ j, B j < L+3) (o : ℕ)
    (x : List Bool) (hx : x.length = L+3) (n : ℕ) :
    ((⟨mkGates L A B n, o⟩ : Circuit).wires x).length = L+3+2*n ∧
    (∀ i, i < L+3 → ((⟨mkGates L A B n, o⟩ : Circuit).wires x).getD i false = x.getD i false) ∧
    (∀ j, j < n → ((⟨mkGates L A B n, o⟩ : Circuit).wires x).getD (L+3+2*j+1) false =
      (x.getD (A j) false || (x.getD L false && x.getD (B j) false))) := by
  induction n with
  | zero => simp [mkGates, Circuit.wires, hx]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [Circuit.wires] at h1 h2 h3 ⊢
    rw [mkGates_succ, List.foldl_append]
    generalize List.foldl _ x (mkGates L A B n) = w at *
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
    refine ⟨by simp [h1]; omega, ?_, ?_⟩
    · intro i hi
      rw [getD_snoc_lt _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
      exact h2 i hi
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [getD_snoc_lt _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
        exact h3 j hj
      · rw [getD_snoc_eq _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by have := hA j; omega),
          getD_snoc_eq _ _ _ (by omega), h2 _ (hA j), h2 L (by omega), h2 _ (hB j)]

lemma fanin (L : ℕ) (A B : ℕ → ℕ) (n o : ℕ) :
    PEqualNP.MetaComplexity.FanInTwo ⟨mkGates L A B n, o⟩ := by
  intro g hg
  simp only [mkGates, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨j, _, hg⟩ := hg
  simp at hg
  rcases hg with rfl | rfl <;> simp

lemma nonot (L : ℕ) (A B : ℕ → ℕ) (n o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨mkGates L A B n, o⟩ = 0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp only [mkGates, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨j, _, hg⟩ := hg
  simp at hg
  rcases hg with rfl | rfl <;> simp

lemma rb (L : ℕ) (A B : ℕ → ℕ) (hA : ∀ j, A j < L+3) (hB : ∀ j, B j < L+3) (n : ℕ) :
    ∀ k, k < 2*n → ∀ i ∈ ((mkGates L A B n).getD k ⟨GateOp.or, []⟩).inputs, i < L+3+k := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk i hi
    rw [mkGates_succ] at hi
    rcases Nat.lt_or_ge k (2*n) with hk' | hk'
    · rw [List.getD_append _ _ _ _ (by rw [mkGates_length]; exact hk')] at hi
      exact ih k hk' i hi
    · rw [List.getD_append_right _ _ _ _ (by rw [mkGates_length]; exact hk'), mkGates_length] at hi
      obtain rfl | rfl : k = 2*n ∨ k = 2*n+1 := by omega
      · simp at hi
        have := hB n
        omega
      · simp at hi
        have := hA n
        omega

end PEqualNP.Outside.L_lib_1448

open PEqualNP.Outside.L_lib_1448

theorem PEqualNP.Outside.L_lib_1448 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (L a f d : Nat), 0<L → 0<d →
  let t := a+f+1
  2*d ≤ t →
  let q := t-d
  let r := (L+1)*t+d
  let height := fun (s : Fin (2*L+2)) => if s.val=0 then 0 else if s.val=2*L+1 then L else
    if s.val % 2=1 then (s.val+1)/2 else (s.val-2)/2
  let upper := fun (s : Fin (2*L+2)) => s.val≠0 ∧ (s.val % 2=0 ∨ s.val=2*L+1)
  let raw := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin (L+1) => i.val < height s ∨ (i.val=L ∧ upper s))
  let word := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin r =>
    i.val < height s*q ∨ (L*q ≤ i.val ∧ i.val < L*q+height s*d+(if upper s then t+d else 0)))
  let near := fun (s : Fin (2*L+2)) (Y : Finset (Fin r)) => (word s \ Y).card ≤ a ∧ (Y \ word s).card ≤ f
  let bits := fun {k : Nat} (X : Finset (Fin k)) => List.ofFn (fun j : Fin k => decide (j ∈ X)) ++ [false,true]
  (∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin r → Nat),
    PEqualNP.MetaComplexity.FanInTwo E ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (L+3) E ∧
    E.output < L+3+E.size ∧ E.size ≤ 4*(r+1) ∧ PEqualNP.NotBracket.notCount E=0 ∧
    (∀ j, out j < L+3+E.size) ∧ ∀ s j, ((E.wires (bits (raw s))).getD (out j) false = true ↔ j ∈ word s)) ∧
  ((Finset.univ.filter (fun v : Fin r => ∀ s, v ∈ word s ↔ upper s)).card = t+d-L*d) ∧
  (∀ s u X Y, near s X → near u Y → X ⊆ Y → s ≤ u) ∧
  ∃ obs : Fin (2*L+2) → Finset (Fin r), Monotone obs ∧ ∀ s, near s (obs s)) := by
  intro L a f d hL hd t ht q r height upper raw word near bits
  have htdef : t = a+f+1 := rfl
  have hqdef : q = t-d := rfl
  have hq : q + d = t := by omega
  have hq0 : 0 < q := by omega
  have hLt : L*t = L*q + L*d := by rw [← hq]; ring
  have hr : r = L*q + L*d + t + d := by
    have h1 : r = (L+1)*t+d := rfl
    have h2 : (L+1)*t = L*t+t := by ring
    omega
  have hheight : ∀ s : Fin (2*L+2), height s = hh L s.val := by
    intro s
    simp only [height, hh]
    split_ifs <;> rfl
  have hword : ∀ (s : Fin (2*L+2)) (i : Fin r), i ∈ word s ↔ wd L q t d s.val i.val := by
    intro s i
    simp only [word, Finset.mem_filter, Finset.mem_univ, true_and, wd, bb, hheight, upper]
    split_ifs <;> first | rfl | rw [Nat.add_assoc]
  have hstage := fun (s : Fin (2*L+2)) => stage L t d s.val s.isLt
  have hbits : ∀ s : Fin (2*L+2), (bits (raw s)).length = L+3 ∧
      (∀ i, i < L → ((bits (raw s)).getD i false = true ↔ i < hh L s.val)) ∧
      ((bits (raw s)).getD L false = true ↔ upper s) ∧
      (bits (raw s)).getD (L+1) false = false ∧ (bits (raw s)).getD (L+2) false = true := by
    intro s
    have hraw : ∀ i : Fin (L+1), i ∈ raw s ↔ (i.val < hh L s.val ∨ (i.val = L ∧ upper s)) := by
      intro i
      simp only [raw, hheight]
      rw [@Finset.mem_filter _ _ (_) _ _]
      simp only [Finset.mem_univ, true_and]
    have hSs := hstage s
    have hHL : hh L s.val ≤ L := by omega
    refine ⟨by simp [bits], ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [bits]
      rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; omega), List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dif_pos (by omega : i < L+1)]
      simp only [Option.getD_some, decide_eq_true_eq]
      rw [hraw]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact h
        · exact absurd h (Nat.ne_of_lt hi)
      · intro h
        exact Or.inl h
    · simp only [bits]
      rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; omega), List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dif_pos (Nat.lt_succ_self L)]
      simp only [Option.getD_some, decide_eq_true_eq]
      rw [hraw]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact absurd h (Nat.not_lt.2 hHL)
        · exact h
      · intro h
        exact Or.inr ⟨rfl, h⟩
    · simp only [bits]
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn]
      simp
    · simp only [bits]
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨mkGates L (gA L q d) (gB L q t d) r, L+3⟩, fun j => L+3+2*j.val+1, fanin _ _ _ _ _, ?_, ?_,
      ?_, nonot _ _ _ _ _, ?_, ?_⟩
    · intro j hj
      exact rb L _ _ (gA_lt L q d) (gB_lt L q t d) r j
        (by rw [← mkGates_length L (gA L q d) (gB L q t d) r]; exact hj)
    · show L+3 < L+3+(mkGates L (gA L q d) (gB L q t d) r).length
      rw [mkGates_length]; omega
    · show (mkGates L (gA L q d) (gB L q t d) r).length ≤ 4*(r+1)
      rw [mkGates_length]; omega
    · intro j
      show L+3+2*j.val+1 < L+3+(mkGates L (gA L q d) (gB L q t d) r).length
      rw [mkGates_length]; omega
    · intro s j
      obtain ⟨hx, x1, x2, x3, x4⟩ := hbits s
      rw [(wires_spec L _ _ (gA_lt L q d) (gB_lt L q t d) (L+3) _ hx r).2.2 j.val j.isLt, hword]
      have hSs := hstage s
      exact sel_spec L q t d (hh L s.val) j.val (upper s) (fun i => (bits (raw s)).getD i false)
        hq0 hd (by omega) (by have := j.isLt; omega) x1 x2 x3 x4 (bb L t d s.val)
        (by
          intro hU
          unfold bb
          rw [if_pos (show (s.val ≠ 0 ∧ (s.val % 2 = 0 ∨ s.val = 2*L+1)) from hU)]
          omega)
        (by
          intro hU
          unfold bb
          rw [if_neg (show ¬ (s.val ≠ 0 ∧ (s.val % 2 = 0 ∨ s.val = 2*L+1)) from hU)]
          omega)
  · refine (card_Ico_fin r (L*q+L*d) (L*q+t+d) (by omega) _ ?_).trans (by omega)
    intro v
    rw [@Finset.mem_filter _ _ (_) _ _]
    simp only [Finset.mem_univ, true_and]
    rw [← common L t d q v.val hL hq]
    constructor
    · intro h s hs
      have := h ⟨s, hs⟩
      rw [hword] at this
      exact this
    · intro h s
      rw [hword]
      exact h s.val s.isLt
  · intro s u X Y hX hY hXY
    by_contra hsu
    have hus : u.val < s.val := not_le.1 hsu
    have hg := gap L t d q s.val u.val hq ht hus s.isLt
    have hSs := hstage s
    have hSu := hstage u
    have b0 : hh L s.val ≤ L := by omega
    have b0' : hh L u.val ≤ L := by omega
    have b1 : hh L s.val * q ≤ L*q := Nat.mul_le_mul_right q b0
    have b2 : hh L s.val * d ≤ L*d := Nat.mul_le_mul_right d b0
    have b4 : hh L u.val * q ≤ L*q := Nat.mul_le_mul_right q b0'
    have b3 : bb L t d s.val ≤ L*d + t + d := by omega
    let T : Finset (Fin r) := Finset.univ.filter (fun v : Fin r =>
      (hh L u.val * q ≤ v.val ∧ v.val < hh L s.val * q) ∨
        (L*q + bb L t d u.val ≤ v.val ∧ v.val < L*q + bb L t d s.val))
    have hTm : ∀ v, v ∈ T ↔ ((hh L u.val * q ≤ v.val ∧ v.val < hh L s.val * q) ∨
        (L*q + bb L t d u.val ≤ v.val ∧ v.val < L*q + bb L t d s.val)) := by
      intro v
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc := card_two r (hh L u.val * q) (hh L s.val * q) (L*q + bb L t d u.val)
      (L*q + bb L t d s.val) (by omega) (by omega) (by omega) T hTm
    have hT := @card_chain _ (_) (word s) (word u) X Y T a f hX.1 hY.2 hXY (by
      intro v hv
      rw [hTm] at hv
      rw [hword, hword]
      unfold wd
      omega)
    omega
  · refine ⟨fun s => @Finset.filter _ (fun v : Fin r => ob L a q t d s.val v.val)
      (fun _ => Classical.propDecidable _) Finset.univ, ?_, ?_⟩
    · intro s u hsu v hv
      rw [@Finset.mem_filter _ _ (_) _ _] at hv ⊢
      exact ⟨hv.1, ob_mono L a q t d s.val u.val v.val hsu u.isLt hv.2⟩
    · intro s
      refine ⟨?_, ?_⟩
      · apply card_lo r q a (xlo L q d s.val)
        intro v hv
        rw [@Finset.mem_sdiff _ (_) _ _ _, hword, @Finset.mem_filter _ _ (_) _ _] at hv
        exact near_lo L a q t d s.val v.val hq s.isLt hv.1 (fun h => hv.2 ⟨Finset.mem_univ _, h⟩)
      · apply card_hi r q a f (xhi L q d s.val) (by omega)
        intro v hv
        rw [@Finset.mem_sdiff _ (_) _ _ _, @Finset.mem_filter _ _ (_) _ _, hword] at hv
        exact near_hi L a q t d s.val v.val hq s.isLt (by have := v.isLt; omega) hv.1.2 hv.2
