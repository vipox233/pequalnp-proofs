import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Dist
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_290_aux

open Finset

def ham {p : ℕ} (x y : Fin p → Bool) : ℕ := (univ.filter (fun i : Fin p => x i ≠ y i)).card

def flip {p : ℕ} (x : Fin p → Bool) (T : Finset (Fin p)) : Fin p → Bool :=
  fun k => if k ∈ T then !x k else x k

theorem ham_flip {p : ℕ} (x : Fin p → Bool) (T : Finset (Fin p)) : ham x (flip x T) = T.card := by
  unfold ham flip
  congr 1
  ext k
  by_cases hk : k ∈ T <;> simp [hk]

theorem flip_in {p : ℕ} (x : Fin p → Bool) (T : Finset (Fin p)) (k : Fin p) (h : k ∈ T) :
    flip x T k = !x k := by simp [flip, h]

theorem flip_out {p : ℕ} (x : Fin p → Bool) (T : Finset (Fin p)) (k : Fin p) (h : k ∉ T) :
    flip x T k = x k := by simp [flip, h]

theorem ham_compl {p : ℕ} (x x' y : Fin p → Bool) (hx : ∀ j, x j ≠ x' j) :
    ham x' y + ham x y = p := by
  unfold ham
  have : univ.filter (fun i : Fin p => x' i ≠ y i) = univ.filter (fun i => ¬ (x i ≠ y i)) := by
    ext k
    have := hx k
    cases hxk : x k <;> cases hx'k : x' k <;> cases hyk : y k <;> simp_all
  rw [this, add_comm, card_filter_add_card_filter_not]
  simp

theorem combB {p : ℕ} (φ : ℕ → Prop) (x x' : Fin p → Bool) (hx : ∀ j, x j ≠ x' j)
    (H : ∀ y, φ (ham x y) ↔ φ (ham x' y)) : ∀ h, h ≤ p → (φ h ↔ φ (p - h)) := by
  intro h hh
  obtain ⟨T, -, hT⟩ := exists_subset_card_eq (s := (univ : Finset (Fin p))) (n := h) (by simpa using hh)
  have h1 := H (flip x T)
  have h2 := ham_compl x x' (flip x T) hx
  rw [ham_flip, hT] at h1 h2
  have h3 : ham x' (flip x T) = p - h := by omega
  rw [h3] at h1
  exact h1

theorem combA {p : ℕ} (φ : ℕ → Prop) (x x' : Fin p → Bool) (i j : Fin p)
    (hi : x i ≠ x' i) (hj : x j = x' j)
    (H : ∀ y, φ (ham x y) ↔ φ (ham x' y)) : ∀ h, h + 2 ≤ p → (φ h ↔ φ (h + 2)) := by
  intro h hh
  have hij : i ≠ j := by
    intro e; subst e; exact hi hj
  have hc : ((univ.erase i).erase j).card = p - 2 := by
    rw [card_erase_of_mem (by simp [Ne.symm hij]), card_erase_of_mem (by simp)]
    simp only [card_univ, Fintype.card_fin]; omega
  obtain ⟨T, hTs, hT⟩ := exists_subset_card_eq (s := (univ.erase i).erase j) (n := h) (by omega)
  have hiT : i ∉ T := fun hm => by have := hTs hm; simp at this
  have hjT : j ∉ T := fun hm => by have := hTs hm; simp at this
  have h1 := H (flip x T)
  have h2 := H (flip x (insert i (insert j T)))
  rw [ham_flip] at h1 h2
  have hc2 : (insert i (insert j T)).card = h + 2 := by
    rw [card_insert_of_notMem (by simp [hij, hiT]), card_insert_of_notMem hjT, hT]
  rw [hT] at h1
  rw [hc2] at h2
  have he : ham x' (flip x T) = ham x' (flip x (insert i (insert j T))) := by
    unfold ham
    have hF : univ.filter (fun k : Fin p => x' k ≠ flip x (insert i (insert j T)) k) =
        insert j ((univ.filter (fun k : Fin p => x' k ≠ flip x T k)).erase i) := by
      ext k
      rw [mem_insert, mem_erase, mem_filter, mem_filter]
      simp only [mem_univ, true_and]
      by_cases hki : k = i
      · subst hki
        rw [flip_in x _ k (by simp), flip_out x T k hiT]
        simp only [hij, false_or, ne_eq, not_true_eq_false, false_and, iff_false]
        cases hxk : x k <;> cases hx'k : x' k <;> simp_all
      · by_cases hkj : k = j
        · subst hkj
          rw [flip_in x _ k (by simp), flip_out x T k hjT]
          simp only [true_or, iff_true]
          cases hxk : x k <;> cases hx'k : x' k <;> simp_all
        · have e1 : flip x (insert i (insert j T)) k = flip x T k := by
            unfold flip; simp [hki, hkj]
          rw [e1]
          simp [hki, hkj]
    have hjn : j ∉ (univ.filter (fun k : Fin p => x' k ≠ flip x T k)).erase i := by
      rw [mem_erase, mem_filter, flip_out x T j hjT]; simp [hj]
    have hin : i ∈ univ.filter (fun k : Fin p => x' k ≠ flip x T k) := by
      rw [mem_filter, flip_out x T i hiT]; simp [Ne.symm hi]
    rw [hF, card_insert_of_notMem hjn, card_erase_of_mem hin]
    have : 0 < (univ.filter (fun k : Fin p => x' k ≠ flip x T k)).card :=
      card_pos.mpr ⟨i, hin⟩
    omega
  rw [h1, he, ← h2]

theorem arithA (a p d : ℕ) (hn : 32 ≤ a+p+d) (hp : 2 ≤ p)
    (H : ∀ c h, c ≤ d → h + 2 ≤ p →
      (16 * Nat.dist (2*(min a (17*(a+p+d)/32) + h + c)) (a+p+d) ≤ a+p+d ↔
       16 * Nat.dist (2*(min a (17*(a+p+d)/32) + (h+2) + c)) (a+p+d) ≤ a+p+d)) : False := by
  have h1 := H 0 (17*(a+p+d)/32 - min a (17*(a+p+d)/32))
  have h2 := H d (17*(a+p+d)/32 - min a (17*(a+p+d)/32) - d)
  have h3 := H (17*(a+p+d)/32 - min a (17*(a+p+d)/32) - (p-2)) (p-2)
  have h4 := H (17*(a+p+d)/32 - min a (17*(a+p+d)/32)) 0
  simp only [Nat.dist] at h1 h2 h3 h4
  omega

theorem phi_iff (m n : ℕ) :
    16 * Nat.dist (2*m) n ≤ n ↔ (15*n ≤ 32*m ∧ 32*m ≤ 17*n) := by
  simp only [Nat.dist]
  omega

theorem coreB (a p d U : ℕ) (hn : 32 ≤ a+p+d) (hU1 : 32*U ≤ 17*(a+p+d))
    (hU2 : 17*(a+p+d) < 32*U+32) (hp : 1 ≤ p) (hpn : p < a+p+d)
    (H : ∀ c h, c ≤ d → h ≤ p →
      ((15*(a+p+d) ≤ 32*(min a U + h + c) ∧ 32*(min a U + h + c) ≤ 17*(a+p+d)) ↔
       (15*(a+p+d) ≤ 32*(min a U + (p-h) + c) ∧ 32*(min a U + (p-h) + c) ≤ 17*(a+p+d)))) :
    False := by
  rcases Nat.lt_or_ge U a with hlt | hle
  · have hm : min a U = U := by omega
    rw [hm] at H
    have h1 := H 0 0 (by omega) (by omega)
    omega
  · have hm : min a U = a := by omega
    rw [hm] at H
    by_cases h3 : U ≤ a + d
    · obtain ⟨k, hk⟩ : ∃ k, U = a + k := ⟨U - a, by omega⟩
      have h1 := H k 0 (by omega) (by omega)
      omega
    · by_cases h4 : a + d + U ≤ a + p + d
      · obtain ⟨k, hk⟩ : ∃ k, a + p + d = a + d + U + k := ⟨a + p + d - (a + d + U), by omega⟩
        have h1 := H d k (by omega) (by omega)
        omega
      · have h1 := H d 0 (by omega) (by omega)
        omega

theorem arithB(a p d : ℕ) (hn : 32 ≤ a+p+d) (hp : 1 ≤ p) (hpn : p < a+p+d)
    (H : ∀ c h, c ≤ d → h ≤ p →
      (16 * Nat.dist (2*(min a (17*(a+p+d)/32) + h + c)) (a+p+d) ≤ a+p+d ↔
       16 * Nat.dist (2*(min a (17*(a+p+d)/32) + (p-h) + c)) (a+p+d) ≤ a+p+d)) : False := by
  apply coreB a p d (17*(a+p+d)/32) hn (by omega) (by omega) hp hpn
  intro c h hc hh
  rw [← phi_iff, ← phi_iff]
  exact H c h hc hh

theorem sep (a p r r' : ℕ) (hn : 32 ≤ a+p+a) (hr : r < r') (hr' : r' ≤ a)
    (hr0 : a - (a+p+a - 17*(a+p+a)/32) ≤ r)
    (H : ∀ h c, h ≤ p → c ≤ a →
      (16 * Nat.dist (2*(r + h + c)) (a+p+a) ≤ a+p+a ↔
       16 * Nat.dist (2*(r' + h + c)) (a+p+a) ≤ a+p+a)) : False := by
  have := H (min p (17*(a+p+a)/32 - r)) (17*(a+p+a)/32 - r - min p (17*(a+p+a)/32 - r))
  simp only [Nat.dist] at this
  omega

def tst (a p d : ℕ) (v : Fin (a+1) × (Fin p → Bool)) (w : (Fin p → Bool) × Fin (d+1)) : Bool :=
  decide (16 * Nat.dist (2*(v.1.val + ham v.2 w.1 + w.2.val)) (a+p+d) ≤ a+p+d)

theorem tst_eq (a p d : ℕ) (r : Fin (a+1)) (x x' : Fin p → Bool)
    (h : tst a p d (r, x) = tst a p d (r, x')) (c : ℕ) (hc : c ≤ d) (y : Fin p → Bool) :
    (16 * Nat.dist (2*(r.val + ham x y + c)) (a+p+d) ≤ a+p+d ↔
     16 * Nat.dist (2*(r.val + ham x' y + c)) (a+p+d) ≤ a+p+d) := by
  have := congrFun h (y, ⟨c, by omega⟩)
  simp only [tst, decide_eq_decide] at this
  exact this

theorem sep2 (a p r r' : ℕ) (hn : 32 ≤ a+p+a) (hr : r < r') (hr' : r' ≤ a)
    (hr0 : a - (a+p+a - 17*(a+p+a)/32) ≤ r) (h1 : r < a+1) (h2 : r' < a+1)
    (H : tst a p a (⟨r, h1⟩, fun _ => false) = tst a p a (⟨r', h2⟩, fun _ => false)) : False := by
  apply sep a p r r' hn hr hr' hr0
  intro h c hh hc
  obtain ⟨T, -, hT⟩ := exists_subset_card_eq (s := (univ : Finset (Fin p))) (n := h) (by simpa using hh)
  have := congrFun H (flip (fun _ => false) T, ⟨c, by omega⟩)
  simp only [tst, decide_eq_decide, ham_flip, hT] at this
  exact this

theorem main (a p d : ℕ) (hn : 32 ≤ a+p+d) :
    ((univ.image (tst a p d)).card ≤ (a+1)*2^p) ∧
    (p < a+p+d → 2^p ≤ (univ.image (tst a p d)).card) ∧
    (p = a+p+d → (univ.image (tst a p d)).card = 2^(a+p+d-1)) ∧
    (a = d → min a ((a+p+d)-(17*(a+p+d))/32) + 1 ≤ (univ.image (tst a p d)).card) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact card_image_le.trans (by simp [Fintype.card_prod, Fintype.card_fun])
  · intro hpn
    let r0 : Fin (a+1) := ⟨min a (17*(a+p+d)/32), by omega⟩
    have inj : Function.Injective (fun x : Fin p → Bool => tst a p d (r0, x)) := by
      intro x x' hxx
      by_contra hne
      simp only at hxx
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      by_cases hall : ∃ j, x j = x' j
      · obtain ⟨j, hj⟩ := hall
        have hij : i ≠ j := by intro e; subst e; exact hi hj
        have hp2 : 2 ≤ p := by
          have := card_le_card (subset_univ ({i, j} : Finset (Fin p)))
          rw [card_pair hij] at this
          simpa using this
        apply arithA a p d hn hp2
        intro c h hc hh
        exact combA (fun m => 16 * Nat.dist (2*(min a (17*(a+p+d)/32) + m + c)) (a+p+d) ≤ a+p+d)
          x x' i j hi hj (fun y => tst_eq a p d r0 x x' hxx c hc y) h hh
      · push_neg at hall
        have hp1 : 1 ≤ p := by
          have := i.isLt; omega
        apply arithB a p d hn hp1 hpn
        intro c h hc hh
        exact combB (fun m => 16 * Nat.dist (2*(min a (17*(a+p+d)/32) + m + c)) (a+p+d) ≤ a+p+d)
          x x' hall (fun y => tst_eq a p d r0 x x' hxx c hc y) h hh
    calc 2^p = (univ.image (fun x : Fin p → Bool => tst a p d (r0, x))).card := by
          rw [card_image_of_injective _ inj]; simp
      _ ≤ (univ.image (tst a p d)).card := by
          apply card_le_card
          intro f hf
          simp only [mem_image, mem_univ, true_and] at hf ⊢
          obtain ⟨x, rfl⟩ := hf
          exact ⟨(r0, x), rfl⟩
  · intro hpn
    have ha : a = 0 := by omega
    have hd : d = 0 := by omega
    subst ha hd
    clear hpn
    let r0 : Fin (0+1) := ⟨min 0 (17*(0+p+0)/32), by omega⟩
    have fwd : ∀ (r : Fin (0+1)) (x : Fin p → Bool),
        tst 0 p 0 (r, fun i => !x i) = tst 0 p 0 (r, x) := by
      intro r x
      funext w
      have h2 := ham_compl x (fun i => !x i) w.1 (by intro j; cases x j <;> simp)
      have hw : w.2.val = 0 := by omega
      have hr : r.val = 0 := by omega
      simp only [tst, decide_eq_decide, hw, hr, Nat.dist]
      omega
    have conv : ∀ x x' : Fin p → Bool, tst 0 p 0 (r0, x) = tst 0 p 0 (r0, x') →
        x' = x ∨ x' = (fun i => !x i) := by
      intro x x' hxx
      by_contra hne
      push_neg at hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne.1
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne.2
      have hj' : x j = x' j := by
        cases h1 : x j <;> cases h2 : x' j <;> simp_all
      have hp2 : 2 ≤ p := by omega
      apply arithA 0 p 0 hn hp2
      intro c h hc hh
      exact combA (fun m => 16 * Nat.dist (2*(min 0 (17*(0+p+0)/32) + m + c)) (0+p+0) ≤ 0+p+0)
        x x' i j (Ne.symm hi) hj' (fun y => tst_eq 0 p 0 r0 x x' hxx c hc y) h hh
    have hS : univ.image (tst 0 p 0) = univ.image (fun x : Fin p → Bool => tst 0 p 0 (r0, x)) := by
      ext f
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨v.2, ?_⟩
        have hv : (r0, v.2) = v := Prod.ext (Fin.ext (by have := v.1.isLt; have := r0.isLt; omega)) rfl
        rw [hv]
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin p → Bool)))
      (t := univ.image (fun x : Fin p → Bool => tst 0 p 0 (r0, x)))
      (f := fun x : Fin p → Bool => tst 0 p 0 (r0, x))
      (fun x _ => mem_image_of_mem _ (mem_univ x))
    have hfib : ∀ b ∈ univ.image (fun x : Fin p → Bool => tst 0 p 0 (r0, x)),
        (univ.filter (fun x : Fin p → Bool => tst 0 p 0 (r0, x) = b)).card = 2 := by
      intro b hb
      obtain ⟨x, -, hxb⟩ := mem_image.mp hb
      have hE : univ.filter (fun x' : Fin p → Bool => tst 0 p 0 (r0, x') = b)
          = {x, (fun i => !x i)} := by
        ext x'
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro h
          exact conv x x' (hxb.trans h.symm)
        · intro h
          rcases h with h | h
          · rw [h]; exact hxb
          · rw [h, fwd r0 x]; exact hxb
      rw [hE, card_pair]
      intro e
      have h0 := congrFun e ⟨0, by omega⟩
      cases hx0 : x ⟨0, by omega⟩ <;> simp [hx0] at h0
    rw [sum_congr rfl hfib, sum_const, smul_eq_mul] at hsum
    simp only [card_univ, Fintype.card_pi, Fintype.card_bool, prod_const, Fintype.card_fin] at hsum
    rw [hS]
    have hq : 2^(0+p+0-1) * 2 = 2^p := by
      rw [← pow_succ]
      congr 1
      omega
    omega
  · intro had
    subst had
    have g_inj : Function.Injective (fun k : Fin (min a ((a+p+a)-(17*(a+p+a))/32) + 1) =>
        tst a p a (⟨a - k.val, by omega⟩, fun _ => false)) := by
      intro k k' hk
      simp only at hk
      by_contra hne
      have hv : k.val ≠ k'.val := fun e => hne (Fin.ext e)
      have hk1 := k.isLt
      have hk2 := k'.isLt
      rcases Nat.lt_or_gt_of_ne hv with hlt | hlt
      · exact sep2 a p (a - k'.val) (a - k.val) hn (by omega) (by omega) (by omega) _ _ hk.symm
      · exact sep2 a p (a - k.val) (a - k'.val) hn (by omega) (by omega) (by omega) _ _ hk
    calc min a ((a+p+a)-(17*(a+p+a))/32) + 1
        = (univ.image (fun k : Fin (min a ((a+p+a)-(17*(a+p+a))/32) + 1) =>
            tst a p a (⟨a - k.val, by omega⟩, fun _ => false))).card := by
          rw [card_image_of_injective _ g_inj]; simp
      _ ≤ (univ.image (tst a p a)).card := by
          apply card_le_card
          intro f hf
          simp only [mem_image, mem_univ, true_and] at hf ⊢
          obtain ⟨k, rfl⟩ := hf
          exact ⟨_, rfl⟩

end PEqualNP.Outside.L_pcx_290_aux

theorem PEqualNP.Outside.L_pcx_290 : ∀ (a p d : ℕ),
  let n := a+p+d
  let X := Fin p → Bool
  let Row := Fin (a+1) × X
  let Col := X × Fin (d+1)
  let test := fun (v : Row) (w : Col) =>
    let dist := v.1.val + (Finset.univ.filter (fun i : Fin p => v.2 i ≠ w.1 i)).card + w.2.val
    decide (16 * Nat.dist (2*dist) n ≤ n)
  let states := (Finset.univ.image test).card
  32 ≤ n →
    (states ≤ (a+1)*2^p) ∧
    (p < n → 2^p ≤ states) ∧
    (p = n → states = 2^(n-1)) ∧
    (a = d → min a (n-(17*n)/32) + 1 ≤ states) := by
  intro a p d
  exact PEqualNP.Outside.L_pcx_290_aux.main a p d
