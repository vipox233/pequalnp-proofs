import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49523

def admits (V : Type) (g : V → V → Prop) (D B : ℕ) : Prop :=
  ∃ f : Finset V → V → ℕ,
    (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, g i j) → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
    ∀ (l : ℕ) (p : Fin (l + 1) → Finset V) (a : Fin l → V),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B

def cyc (m : ℕ) (i j : Fin m) : Prop :=
  j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m

lemma admits_pullback {V1 V2 : Type} [DecidableEq V2] {g1 : V1 → V1 → Prop} {g2 : V2 → V2 → Prop}
    {D B : ℕ} (φ : V1 → V2) (hφ : ∀ i j, g1 i j → g2 (φ i) (φ j))
    (h : admits V2 g2 D B) : admits V1 g1 D B := by
  obtain ⟨f, hle, hP, hZ, hanti, hbud⟩ := h
  refine ⟨fun x j => f (x.image φ) (φ j), ?_, ?_, ?_, ?_, ?_⟩
  · intro x j; exact hle _ _
  · intro x j hx
    apply hP
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hφ i j (hx i hi)
  · intro x j hj
    exact hZ _ _ (Finset.mem_image_of_mem φ hj)
  · intro x y hxy j
    exact hanti _ _ (Finset.image_subset_image hxy) _
  · intro l p a hsub
    exact hbud l (fun k => (p k).image φ) (fun i => φ (a i)) (fun i => Finset.image_subset_image (hsub i))

lemma admits_of_coloring {V C : Type} [Fintype C] [DecidableEq C]
    {g : V → V → Prop} {D B : ℕ} (hcardC : Fintype.card C ≤ B)
    (col : V → Finset C) (hcol_card : ∀ j, (col j).card = D)
    (hcol_disj : ∀ i j, g i j → Disjoint (col i) (col j)) :
    admits V g D B := by
  refine ⟨fun x j => (col j \ x.biUnion col).card, ?_, ?_, ?_, ?_, ?_⟩
  · intro x j
    calc (col j \ x.biUnion col).card ≤ (col j).card := Finset.card_le_card Finset.sdiff_subset
      _ = D := hcol_card j
  · intro x j hx
    dsimp only
    have hdisj : Disjoint (col j) (x.biUnion col) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact (hcol_disj i j (hx i hi)).symm
    rw [Finset.sdiff_eq_self_of_disjoint hdisj, hcol_card j]
  · intro x j hj
    dsimp only
    have hsub : col j ⊆ x.biUnion col := Finset.subset_biUnion_of_mem col hj
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
  · intro x y hxy j
    exact Finset.card_le_card (Finset.sdiff_subset_sdiff (le_refl _) (Finset.biUnion_subset_biUnion_of_subset_left col hxy))
  · intro l p a hsub
    have hstep : ∀ i : Fin l,
        (col (a i) \ (p i.castSucc).biUnion col).card - (col (a i) \ (p i.succ).biUnion col).card ≤
        ((p i.succ).biUnion col).card - ((p i.castSucc).biUnion col).card := by
      intro i
      let U := (p i.castSucc).biUnion col
      let W := (p i.succ).biUnion col
      have hUW : U ⊆ W := Finset.biUnion_subset_biUnion_of_subset_left col (hsub i)
      have hsub1 : (col (a i) \ U) \ (col (a i) \ W) ⊆ W \ U := by
        intro c hc
        simp only [Finset.mem_sdiff] at hc ⊢
        tauto
      have hsub2 : col (a i) \ W ⊆ col (a i) \ U := Finset.sdiff_subset_sdiff (le_refl _) hUW
      have h1 : (col (a i) \ U).card - (col (a i) \ W).card = ((col (a i) \ U) \ (col (a i) \ W)).card :=
        (Finset.card_sdiff_of_subset hsub2).symm
      have h2 : (W \ U).card = W.card - U.card := Finset.card_sdiff_of_subset hUW
      rw [h1, ← h2]
      exact Finset.card_le_card hsub1
    have htel : ∀ (k : ℕ) (q : Fin (k + 1) → Finset C),
        (∀ i : Fin k, q i.castSucc ⊆ q i.succ) →
        Finset.univ.sum (fun i : Fin k => (q i.succ).card - (q i.castSucc).card) =
          (q (Fin.last k)).card - (q 0).card := by
      intro k
      induction k with
      | zero => intro q _; simp
      | succ k ih =>
        intro q hq
        rw [Fin.sum_univ_castSucc]
        have hq' : ∀ i : Fin k, q i.castSucc.castSucc ⊆ q i.succ.castSucc := fun i => by
          rw [← Fin.succ_castSucc]; exact hq i.castSucc
        have hih := ih (fun t => q t.castSucc) hq'
        simp only [Fin.castSucc_zero] at hih
        have h1 : (∑ i : Fin k, ((q i.castSucc.succ).card - (q i.castSucc.castSucc).card)) =
            (q (Fin.last k).castSucc).card - (q 0).card := by
          convert hih using 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fin.succ_castSucc]
        rw [h1]
        have h0_le : (q 0).card ≤ (q (Fin.last k).castSucc).card := by
          have hgen : ∀ t : Fin (k + 1), q 0 ⊆ q t.castSucc := by
            intro t
            induction t using Fin.induction with
            | zero => exact le_refl _
            | succ t iht => exact iht.trans (hq t.castSucc)
          exact Finset.card_le_card (hgen (Fin.last k))
        have hlast_le : (q (Fin.last k).castSucc).card ≤ (q (Fin.last k.succ)).card := by
          have := hq (Fin.last k)
          rw [Fin.succ_last] at this
          exact Finset.card_le_card this
        rw [Fin.succ_last]
        change (q (Fin.last k).castSucc).card - (q 0).card +
          ((q (Fin.last k.succ)).card - (q (Fin.last k).castSucc).card) =
          (q (Fin.last k.succ)).card - (q 0).card
        omega
    calc Finset.univ.sum (fun i : Fin l => (col (a i) \ (p i.castSucc).biUnion col).card -
            (col (a i) \ (p i.succ).biUnion col).card)
        ≤ Finset.univ.sum (fun i : Fin l => ((p i.succ).biUnion col).card - ((p i.castSucc).biUnion col).card) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = ((p (Fin.last l)).biUnion col).card - ((p 0).biUnion col).card :=
          htel l (fun k => (p k).biUnion col) (fun i => Finset.biUnion_subset_biUnion_of_subset_left col (hsub i))
      _ ≤ ((p (Fin.last l)).biUnion col).card := Nat.sub_le _ _
      _ ≤ Fintype.card C := Finset.card_le_univ _
      _ ≤ B := hcardC

lemma odd_cycle_lower {r D B : ℕ} (hr : 0 < r) (hD : 0 < D)
    (h : admits (Fin (2 * r + 1)) (cyc (2 * r + 1)) D B) :
    2 * D + (D + r - 1) / r ≤ B := by
  let m := 2 * r + 1
  obtain ⟨f, hle, hP, hZ, hanti, hbud⟩ := h
  have hstep : ∀ u v w j : Fin m, cyc m u w → cyc m v w → 2 * D + (f {u} j - f {v} j) ≤ B := by
    intro u v w j huw hvw
    let p : Fin 4 → Finset (Fin m) := fun k =>
      match k.val with
      | 0 => ∅
      | 1 => {u}
      | 2 => {u, v}
      | _ => {u, v, w}
    let a : Fin 3 → Fin m := fun k =>
      match k.val with
      | 0 => u
      | 1 => j
      | _ => w
    have hsub : ∀ i : Fin 3, p i.castSucc ⊆ p i.succ := by
      intro i
      fin_cases i
      · exact Finset.empty_subset _
      · change ({u} : Finset (Fin m)) ⊆ {u, v}
        intro x hx; simp only [Finset.mem_singleton, Finset.mem_insert] at hx ⊢; exact Or.inl hx
      · change ({u, v} : Finset (Fin m)) ⊆ {u, v, w}
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    have hsum := hbud 3 p a hsub
    rw [Fin.sum_univ_three] at hsum
    have h0 : f (p 0) u = D := hP ∅ u (by simp)
    have h1 : f (p 1) u = 0 := hZ {u} u (by simp)
    have h2 : f (p 2) w = D := by
      apply hP
      intro x hx
      change x ∈ ({u, v} : Finset (Fin m)) at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact huw
      · exact hvw
    have h3 : f (p 3) w = 0 := hZ {u, v, w} w (by simp)
    have hanti_uv : f {u, v} j ≤ f {v} j := hanti {v} {u, v} (by intro x hx; simp at hx ⊢; exact Or.inr hx) j
    have h0' : f (p 0) (a 0) = D := h0
    have h1' : f (p 1) (a 0) = 0 := h1
    have h2' : f (p 2) (a 2) = D := h2
    have h3' : f (p 3) (a 2) = 0 := h3
    change (f (p 0) (a 0) - f (p 1) (a 0)) + (f (p 1) (a 1) - f (p 2) (a 1)) + (f (p 2) (a 2) - f (p 3) (a 2)) ≤ B at hsum
    rw [h0', h1', h2', h3'] at hsum
    change D - 0 + (f {u} j - f {u, v} j) + (D - 0) ≤ B at hsum
    omega
  have h2D : 2 * D ≤ B := by
    have hc1 : cyc m ⟨0, by omega⟩ ⟨1, by omega⟩ := Or.inl (by simp [m, Nat.mod_eq_of_lt (show 1 < 2 * r + 1 by omega)])
    have := hstep ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ hc1 hc1
    omega
  have hwalk : ∀ (k : ℕ) (hk : k ≤ r), f {⟨2 * k, by omega⟩} ⟨0, by omega⟩ ≤ k * (B - 2 * D) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hz : f {⟨0, by omega⟩} ⟨0, by omega⟩ = 0 := hZ {⟨0, by omega⟩} ⟨0, by omega⟩ (by simp)
      simpa using hz.le
    | succ k ih =>
      intro hk
      have hih := ih (by omega)
      let u : Fin m := ⟨2 * k + 2, by omega⟩
      let v : Fin m := ⟨2 * k, by omega⟩
      let w : Fin m := ⟨2 * k + 1, by omega⟩
      have hvw : cyc m v w := Or.inl (by
        simp only [v, w, m]
        rw [Nat.mod_eq_of_lt (by omega)])
      have huw : cyc m u w := Or.inr (by
        simp only [u, w, m]
        rw [Nat.mod_eq_of_lt (by omega)])
      have hst := hstep u v w ⟨0, by omega⟩ huw hvw
      have hu_eq : u = ⟨2 * (k + 1), by omega⟩ := Fin.ext (by dsimp only [u]; omega)
      rw [hu_eq] at hst
      dsimp only [v] at hst
      have hmul : (k + 1) * (B - 2 * D) = k * (B - 2 * D) + (B - 2 * D) := by ring
      omega
  have htop : f {⟨2 * r, by omega⟩} ⟨0, by omega⟩ = D := by
    apply hP
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    left
    simp [m]
  have hDr : D ≤ r * (B - 2 * D) := by
    have := hwalk r (le_refl r)
    rw [htop] at this
    exact this
  have hceil : (D + r - 1) / r ≤ B - 2 * D := by
    have h1 : D + r - 1 < (B - 2 * D + 1) * r := by
      have : D + r - 1 + 1 = D + r := by omega
      nlinarith
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hr).mpr h1)
  omega

def pal (r : ℕ) (u : Fin (2 * r + 1)) : Finset (Fin (2 * r + 1)) :=
  (Finset.univ : Finset (Fin r)).image (fun k => ⟨(u.val + 2 * k.val) % (2 * r + 1), Nat.mod_lt _ (by omega)⟩)

lemma pal_card (r : ℕ) (u : Fin (2 * r + 1)) : (pal r u).card = r := by
  have hinj : Function.Injective (fun k : Fin r =>
      (⟨(u.val + 2 * k.val) % (2 * r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * r + 1))) := by
    intro k1 k2 h
    have hv := congrArg Fin.val h
    dsimp only at hv
    have hk1 := k1.isLt
    have hk2 := k2.isLt
    have hu := u.isLt
    apply Fin.ext
    have hmod : (2 * k1.val) % (2 * r + 1) = (2 * k2.val) % (2 * r + 1) := by
      have h1 : (u.val + 2 * k1.val + (2 * r + 1 - u.val)) % (2 * r + 1) =
          (u.val + 2 * k2.val + (2 * r + 1 - u.val)) % (2 * r + 1) := by
        rw [Nat.add_mod, hv, ← Nat.add_mod]
      have ha : u.val + 2 * k1.val + (2 * r + 1 - u.val) = 2 * k1.val + (2 * r + 1) := by omega
      have hb : u.val + 2 * k2.val + (2 * r + 1 - u.val) = 2 * k2.val + (2 * r + 1) := by omega
      rw [ha, hb, Nat.add_mod_right, Nat.add_mod_right] at h1
      exact h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  rw [pal, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma pal_disjoint (r : ℕ) {u v : Fin (2 * r + 1)} (h : cyc (2 * r + 1) u v) :
    Disjoint (pal r u) (pal r v) := by
  have haux : ∀ a b : Fin (2 * r + 1), b.val = (a.val + 1) % (2 * r + 1) → Disjoint (pal r a) (pal r b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [pal, Finset.mem_image, Finset.mem_univ, true_and] at hc1 hc2
    obtain ⟨k1, hk1⟩ := hc1
    obtain ⟨k2, hk2⟩ := hc2
    have h1 := congrArg Fin.val hk1
    have h2 := congrArg Fin.val hk2
    dsimp only at h1 h2
    have heq : (a.val + 2 * k1.val) % (2 * r + 1) = (a.val + (2 * k2.val + 1)) % (2 * r + 1) := by
      calc (a.val + 2 * k1.val) % (2 * r + 1) = c.val := h1
        _ = (b.val + 2 * k2.val) % (2 * r + 1) := h2.symm
        _ = ((a.val + 1) % (2 * r + 1) + 2 * k2.val) % (2 * r + 1) := by rw [hab]
        _ = (a.val + 1 + 2 * k2.val) % (2 * r + 1) := Nat.mod_add_mod _ _ _
        _ = (a.val + (2 * k2.val + 1)) % (2 * r + 1) := by ring_nf
    have ha := a.isLt
    have h1' : (a.val + 2 * k1.val + (2 * r + 1 - a.val)) % (2 * r + 1) =
        (a.val + (2 * k2.val + 1) + (2 * r + 1 - a.val)) % (2 * r + 1) := by
      rw [Nat.add_mod, heq, ← Nat.add_mod]
    have ha1 : a.val + 2 * k1.val + (2 * r + 1 - a.val) = 2 * k1.val + (2 * r + 1) := by omega
    have ha2 : a.val + (2 * k2.val + 1) + (2 * r + 1 - a.val) = (2 * k2.val + 1) + (2 * r + 1) := by omega
    rw [ha1, ha2, Nat.add_mod_right, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := k1.isLt; omega),
      Nat.mod_eq_of_lt (by have := k2.isLt; omega)] at h1'
    omega
  rcases h with h1 | h2
  · exact haux u v h1
  · exact (haux v u h2).symm

def foldCycle {r s : ℕ} (hs : 0 < s) (hsr : s < r) (u : Fin (2 * r + 1)) : Fin (2 * s + 1) :=
  if h : u.val < 2 * s + 1 then ⟨u.val, h⟩
  else if u.val % 2 = 0 then ⟨2 * s, by omega⟩
  else ⟨2 * s - 1, by omega⟩

lemma foldCycle_hom {r s : ℕ} (hs : 0 < s) (hsr : s < r) (u v : Fin (2 * r + 1))
    (h : cyc (2 * r + 1) u v) : cyc (2 * s + 1) (foldCycle hs hsr u) (foldCycle hs hsr v) := by
  have haux : ∀ a b : Fin (2 * r + 1), b.val = (a.val + 1) % (2 * r + 1) →
      cyc (2 * s + 1) (foldCycle hs hsr a) (foldCycle hs hsr b) := by
    intro a b hab
    have ha := a.isLt
    by_cases hlast : a.val = 2 * r
    · have hb0 : b.val = 0 := by rw [hab, hlast]; simp
      have ha_ge : ¬ (a.val < 2 * s + 1) := by omega
      have ha_ev : a.val % 2 = 0 := by omega
      left
      simp only [foldCycle, ha_ge, dite_false, ha_ev, ite_true, show b.val < 2 * s + 1 by omega, dite_true, hb0]
      simp
    · have hb_eq : b.val = a.val + 1 := by rw [hab, Nat.mod_eq_of_lt (by omega)]
      by_cases ha1 : a.val < 2 * s
      · left
        simp only [foldCycle, hb_eq, show a.val < 2 * s + 1 by omega, show a.val + 1 < 2 * s + 1 by omega, dite_true]
        rw [Nat.mod_eq_of_lt (by omega)]
      · by_cases ha2 : a.val = 2 * s
        · right
          simp only [foldCycle, show a.val < 2 * s + 1 by omega, dite_true,
            show ¬ (b.val < 2 * s + 1) by omega, dite_false, show ¬ (b.val % 2 = 0) by omega, ite_false]
          rw [ha2, Nat.mod_eq_of_lt (by omega)]
          omega
        · by_cases ha_ev : a.val % 2 = 0
          · right
            simp only [foldCycle, show ¬ (a.val < 2 * s + 1) by omega, show ¬ (b.val < 2 * s + 1) by omega,
              dite_false, ha_ev, ite_true, show ¬ (b.val % 2 = 0) by omega, ite_false]
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
          · left
            simp only [foldCycle, show ¬ (a.val < 2 * s + 1) by omega, show ¬ (b.val < 2 * s + 1) by omega,
              dite_false, ha_ev, ite_false, show b.val % 2 = 0 by omega, ite_true]
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
  rcases h with h1 | h2
  · exact haux u v h1
  · exact (haux v u h2).symm

lemma disjoint_prod_right {α β : Type*} [DecidableEq α] [DecidableEq β] (A : Finset α)
    {B1 B2 : Finset β} (h : Disjoint B1 B2) : Disjoint (A ×ˢ B1) (A ×ˢ B2) :=
  Finset.disjoint_left.mpr fun p h1 h2 =>
    Finset.disjoint_left.mp h (Finset.mem_product.mp h1).2 (Finset.mem_product.mp h2).2

lemma odd_cycle_upper {r D : ℕ} (hr : 0 < r) (hD : 0 < D) :
    admits (Fin (2 * r + 1)) (cyc (2 * r + 1)) D (2 * D + (D + r - 1) / r) := by
  let q := D / r
  let s := D % r
  have hD_eq : D = q * r + s := by have := Nat.div_add_mod D r; dsimp only [q, s]; linarith
  have hs_lt : s < r := Nat.mod_lt D hr
  by_cases hs0 : s = 0
  · have hD_q : D = q * r := by omega
    have hh : 2 * D + (D + r - 1) / r = q * (2 * r + 1) := by
      have hdiv : (D + r - 1) / r = q := by
        have h1 : q * r ≤ D + r - 1 := by omega
        have h2 : D + r - 1 < (q + 1) * r := by
          have : D + r - 1 + 1 = D + r := by omega
          nlinarith
        exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hr).mpr h2))
          ((Nat.le_div_iff_mul_le hr).mpr h1)
      rw [hdiv, hD_q]
      ring
    rw [hh]
    refine admits_of_coloring (C := Fin q × Fin (2 * r + 1)) (by simp [Fintype.card_prod])
      (fun u => (Finset.univ : Finset (Fin q)) ×ˢ pal r u) ?_ ?_
    · intro u
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, pal_card, hD_q]
    · intro u v huv
      exact disjoint_prod_right _ (pal_disjoint r huv)
  · have hs_pos : 0 < s := by omega
    have hh : 2 * D + (D + r - 1) / r = q * (2 * r + 1) + (2 * s + 1) := by
      have hdiv : (D + r - 1) / r = q + 1 := by
        have hsub : D + r - 1 + 1 = D + r := by omega
        have h1 : (q + 1) * r ≤ D + r - 1 := by nlinarith
        have h2 : D + r - 1 < (q + 2) * r := by nlinarith
        exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hr).mpr h2))
          ((Nat.le_div_iff_mul_le hr).mpr h1)
      rw [hdiv, hD_eq]
      ring
    rw [hh]
    let col (u : Fin (2 * r + 1)) : Finset ((Fin q × Fin (2 * r + 1)) ⊕ Fin (2 * s + 1)) :=
      ((Finset.univ : Finset (Fin q)) ×ˢ pal r u).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (pal s (foldCycle hs_pos hs_lt u)).map ⟨Sum.inr, Sum.inr_injective⟩
    refine admits_of_coloring (C := (Fin q × Fin (2 * r + 1)) ⊕ Fin (2 * s + 1))
      (by simp [Fintype.card_sum, Fintype.card_prod]) col ?_ ?_
    · intro u
      have hdisj : Disjoint
          (((Finset.univ : Finset (Fin q)) ×ˢ pal r u).map ⟨Sum.inl, Sum.inl_injective⟩)
          ((pal s (foldCycle hs_pos hs_lt u)).map ⟨Sum.inr, Sum.inr_injective⟩) := by
        rw [Finset.disjoint_left]
        intro c hc1 hc2
        simp only [Finset.mem_map] at hc1 hc2
        obtain ⟨_, _, rfl⟩ := hc1
        obtain ⟨_, _, hEq⟩ := hc2
        exact Sum.inl_ne_inr hEq.symm
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_product, Finset.card_univ, Fintype.card_fin, pal_card, pal_card, hD_eq]
    · intro u v huv
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      simp only [col, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hc1 hc2
      rcases hc1 with ⟨p1, hp1, rfl⟩ | ⟨q1, hq1, rfl⟩
      · rcases hc2 with ⟨p2, hp2, hEq⟩ | ⟨q2, _, hEq⟩
        · have := Sum.inl_injective hEq
          subst this
          exact (Finset.disjoint_left.mp (disjoint_prod_right _ (pal_disjoint r huv))) hp1 hp2
        · exact Sum.inr_ne_inl hEq
      · rcases hc2 with ⟨p2, _, hEq⟩ | ⟨q2, hq2, hEq⟩
        · exact Sum.inl_ne_inr hEq
        · have := Sum.inr_injective hEq
          subst this
          exact (Finset.disjoint_left.mp (pal_disjoint s (foldCycle_hom hs_pos hs_lt u v huv))) hq1 hq2

lemma uniform_keys_iff (r s q : ℕ) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q) (B : ℕ) :
    admits {a : Finset (Fin ((2 * r + 1) * s)) // a.card = r * s}
      (fun i j => Disjoint i.val j.val) (q * (r * s)) B ↔ q * ((2 * r + 1) * s) ≤ B := by
  let m := (2 * r + 1) * s
  let k := r * s
  constructor
  · intro hadm
    let blk (b : Fin (2 * r + 1)) : Finset (Fin m) :=
      (Finset.univ : Finset (Fin s)).image (fun t => ⟨b.val * s + t.val, by
        have hb := b.isLt; have ht := t.isLt; dsimp only [m]; nlinarith⟩)
    have hblk_card : ∀ b : Fin (2 * r + 1), (blk b).card = s := by
      intro b
      have hinj : Function.Injective (fun t : Fin s =>
          (⟨b.val * s + t.val, by have hb := b.isLt; have ht := t.isLt; dsimp only [m]; nlinarith⟩ : Fin m)) := by
        intro t1 t2 h
        have hv := congrArg Fin.val h
        dsimp only at hv
        exact Fin.ext (by omega)
      dsimp only [blk]
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hblk_disj : ∀ b1 b2 : Fin (2 * r + 1), b1 ≠ b2 → Disjoint (blk b1) (blk b2) := by
      intro b1 b2 hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [blk, Finset.mem_image, Finset.mem_univ, true_and] at hx1 hx2
      obtain ⟨t1, ht1⟩ := hx1
      obtain ⟨t2, ht2⟩ := hx2
      have h1 := congrArg Fin.val ht1
      have h2 := congrArg Fin.val ht2
      dsimp only at h1 h2
      have ht1l := t1.isLt
      have ht2l := t2.isLt
      have hbeq : b1.val = b2.val := by nlinarith
      exact hne (Fin.ext hbeq)
    let w (u : Fin (2 * r + 1)) : {a : Finset (Fin m) // a.card = k} :=
      ⟨(pal r u).biUnion blk, by
        rw [Finset.card_biUnion (fun b1 _ b2 _ hne => hblk_disj b1 b2 hne)]
        simp [hblk_card, pal_card, k]⟩
    have hw_hom : ∀ u v : Fin (2 * r + 1), cyc (2 * r + 1) u v → Disjoint (w u).val (w v).val := by
      intro u v huv
      rw [Finset.disjoint_biUnion_left]
      intro b1 hb1
      rw [Finset.disjoint_biUnion_right]
      intro b2 hb2
      have hne : b1 ≠ b2 := fun h => by subst h; exact (Finset.disjoint_left.mp (pal_disjoint r huv)) hb1 hb2
      exact hblk_disj b1 b2 hne
    have hcyc : admits (Fin (2 * r + 1)) (cyc (2 * r + 1)) (q * k) B :=
      admits_pullback w hw_hom hadm
    have hlow := odd_cycle_lower hr (by positivity : 0 < q * k) hcyc
    have hdiv : (q * k + r - 1) / r = q * s := by
      have hsub : q * k + r - 1 + 1 = q * k + r := by omega
      have h1 : (q * s) * r ≤ q * k + r - 1 := by dsimp only [k] at hsub ⊢; nlinarith
      have h2 : q * k + r - 1 < (q * s + 1) * r := by dsimp only [k] at hsub ⊢; nlinarith
      exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hr).mpr h2))
        ((Nat.le_div_iff_mul_le hr).mpr h1)
    rw [hdiv] at hlow
    have heq : 2 * (q * k) + q * s = q * ((2 * r + 1) * s) := by dsimp only [k]; ring
    omega
  · intro hB
    refine admits_of_coloring (C := Fin q × Fin m) (by simpa [Fintype.card_prod] using hB)
      (fun a => (Finset.univ : Finset (Fin q)) ×ˢ a.val) ?_ ?_
    · intro a
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, a.property]
    · intro a b hab
      exact disjoint_prod_right _ hab

end PEqualNP.Outside.L_meta_49523

theorem PEqualNP.Outside.L_meta_49523 : (
let admits := fun (V : Type) (g : V → V → Prop) (D B : Nat) =>
  let X := Finset V
  ∃ f : X → V → Nat,
    (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, g i j) → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
    ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → V),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B
(∀ (n r D : Nat), 0 < r → 0 < D →
  let m := 2*r+1
  let cyc := fun (i j : Fin m) =>
    j.val = (i.val+1) % m ∨ i.val = (j.val+1) % m
  let h := 2*D+(D+r-1)/r
  ∀ g : Fin n → Fin n → Prop,
    (∀ i, ¬ g i i) → (∀ i j, g i j → g j i) →
    ((∃ w : Fin m → Fin n, ∀ i j, cyc i j → g (w i) (w j)) →
      ∀ B, admits (Fin n) g D B → h ≤ B) ∧
    ((∃ v : Fin n → Fin m, ∀ i j, g i j → cyc (v i) (v j)) →
      admits (Fin n) g D h)) ∧
(∀ (r s q : Nat), 0 < r → 0 < s → 0 < q →
  let m := (2*r+1)*s
  let k := r*s
  let K := {a : Finset (Fin m) // a.card = k}
  ∀ B, admits K (fun i j => Disjoint i.val j.val) (q*k) B ↔ q*m ≤ B)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro n r D hr hD g _ _
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hw⟩ B hadm
      exact PEqualNP.Outside.L_meta_49523.odd_cycle_lower hr hD
        (PEqualNP.Outside.L_meta_49523.admits_pullback w hw hadm)
    · rintro ⟨v, hv⟩
      exact PEqualNP.Outside.L_meta_49523.admits_pullback v hv
        (PEqualNP.Outside.L_meta_49523.odd_cycle_upper hr hD)
  · intro r s q hr hs hq B
    exact PEqualNP.Outside.L_meta_49523.uniform_keys_iff r s q hr hs hq B
