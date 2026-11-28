import PEqualNP.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_lib_1012

abbrev W (m q : Nat) := Fin m → Fin q

def hDist {m q : Nat} (x y : W m q) : Nat :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)).card

def ballS {m q : Nat} (S : Finset (W m q)) (v : W m q) (rad : Nat) : Finset (W m q) :=
  S.filter (fun x => hDist v x ≤ rad)

def H (r q : Nat) : Nat := 1 + 4 * r * q

def M (m r : Nat) : Nat := (m + 1) ^ (r - 1)

def A (q r k t : Nat) : Nat := r * q ^ r * ((k + 1) * H r q) ^ t

lemma A_zero (q r k : Nat) : A q r k 0 = r * q ^ r := by
  simp [A]

lemma A_succ (q r k t : Nat) : A q r k (t + 1) = (k + 1) * H r q * A q r k t := by
  simp only [A, pow_succ]
  ring

lemma A_mono (q r k a b : Nat) (hab : a ≤ b) : A q r k a ≤ A q r k b := by
  unfold A
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right
  · have h1 : 0 < k + 1 := Nat.succ_pos k
    have h2 : 0 < H r q := by
      unfold H
      omega
    exact Nat.mul_pos h1 h2
  · exact hab

lemma hDist_self {m q : Nat} (x : W m q) : hDist x x = 0 := by
  simp [hDist]

lemma hDist_comm {m q : Nat} (x y : W m q) : hDist x y = hDist y x := by
  unfold hDist
  congr 1
  ext i
  simp [ne_comm]

lemma hDist_triangle {m q : Nat} (x y z : W m q) : hDist x z ≤ hDist x y + hDist y z := by
  unfold hDist
  have hsub : (Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ z i) ⊆
      ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)) ∪
      ((Finset.univ : Finset (Fin m)).filter (fun i => y i ≠ z i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hxy : x i = y i
    · right
      intro hyz
      exact hi (hxy.trans hyz)
    · left
      exact hxy
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

def snocEdit {d : Nat} {α : Type*} (f : Fin d → α) (a : α) : Fin (d + 1) → α :=
  fun j => if h : j.val < d then f ⟨j.val, h⟩ else a

lemma snocEdit_castSucc {d : Nat} {α : Type*} (f : Fin d → α) (a : α) (j : Fin d) :
    snocEdit f a j.castSucc = f j := by
  simp [snocEdit, j.isLt]

lemma snocEdit_last {d : Nat} {α : Type*} (f : Fin d → α) (a : α) :
    snocEdit f a (Fin.last d) = a := by
  simp [snocEdit]

def applyEdits {m q : Nat} : (d : Nat) → W m q → (Fin d → Option (Fin m) × Fin q) → W m q
  | 0, v, _ => v
  | d + 1, v, f =>
    let w := applyEdits d v (fun j => f j.castSucc)
    match (f (Fin.last d)).1 with
    | none => w
    | some i => Function.update w i (f (Fin.last d)).2

lemma exists_applyEdits {m q : Nat} (hq : 0 < q) :
    ∀ (d : Nat) (v x : W m q), hDist v x ≤ d →
      ∃ f : Fin d → Option (Fin m) × Fin q, applyEdits d v f = x
  | 0, v, x, h => by
    refine ⟨Fin.elim0, ?_⟩
    simp only [applyEdits]
    have h0 : ((Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i)).card = 0 := by
      unfold hDist at h
      omega
    rw [Finset.card_eq_zero] at h0
    funext i
    by_contra hne
    have hi : i ∈ (Finset.univ : Finset (Fin m)).filter (fun j => v j ≠ x j) := by
      simp [hne]
    rw [h0] at hi
    simp at hi
  | d + 1, v, x, h => by
    by_cases hvx : v = x
    · subst hvx
      have h0 : hDist v v ≤ d := by
        rw [hDist_self]
        exact Nat.zero_le d
      obtain ⟨f', hf'⟩ := exists_applyEdits hq d v v h0
      refine ⟨snocEdit f' (none, ⟨0, hq⟩), ?_⟩
      simp only [applyEdits, snocEdit_castSucc, snocEdit_last]
      exact hf'
    · have hex : ∃ i₀ : Fin m, v i₀ ≠ x i₀ := by
        by_contra hall
        apply hvx
        funext i
        by_contra hne
        exact hall ⟨i, hne⟩
      obtain ⟨i₀, hi₀⟩ := hex
      let x' : W m q := Function.update x i₀ (v i₀)
      have hfilt : (Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x' i) =
          ((Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i)).erase i₀ := by
        ext i
        by_cases hi : i = i₀
        · subst hi
          simp [x', Function.update]
        · simp [x', Function.update, hi]
      have hmem : i₀ ∈ (Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i) := by
        simp [hi₀]
      have hdx' : hDist v x' ≤ d := by
        unfold hDist at h ⊢
        rw [hfilt, Finset.card_erase_of_mem hmem]
        omega
      obtain ⟨f', hf'⟩ := exists_applyEdits hq d v x' hdx'
      refine ⟨snocEdit f' (some i₀, x i₀), ?_⟩
      simp only [applyEdits, snocEdit_castSucc, snocEdit_last, hf']
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp [Function.update]
      · simp [x', Function.update, hi]

lemma card_ball_r_sub_one {q r k m : Nat} (hq : 2 ≤ q) (hr : 0 < r)
    (S : Finset (W m q)) (v : W m q) :
    (ballS S v (r - 1)).card ≤ A q r k 0 * M m r := by
  have hqpos : 0 < q := by omega
  have hsub : ballS S v (r - 1) ⊆
      (Finset.univ : Finset (Fin (r - 1) → Option (Fin m) × Fin q)).image (applyEdits (r - 1) v) := by
    intro x hx
    simp only [ballS, Finset.mem_filter] at hx
    obtain ⟨f, hf⟩ := exists_applyEdits hqpos (r - 1) v x hx.2
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ f, hf⟩
  have hcard1 : (ballS S v (r - 1)).card ≤
      (Finset.univ : Finset (Fin (r - 1) → Option (Fin m) × Fin q)).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcard2 : (Finset.univ : Finset (Fin (r - 1) → Option (Fin m) × Fin q)).card =
      q ^ (r - 1) * M m r := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, M]
    rw [mul_pow, mul_comm]
  have hqpow : q ^ (r - 1) ≤ A q r k 0 := by
    rw [A_zero]
    have h1 : q ^ (r - 1) ≤ q ^ r := Nat.pow_le_pow_right (by omega) (Nat.sub_le r 1)
    have h2 : q ^ r ≤ r * q ^ r := Nat.le_mul_of_pos_left (q ^ r) hr
    exact h1.trans h2
  calc (ballS S v (r - 1)).card
      ≤ q ^ (r - 1) * M m r := by omega
    _ ≤ A q r k 0 * M m r := Nat.mul_le_mul_right (M m r) hqpow

lemma ball_inter_le {q r m j t B_bound : Nat} (hj : 1 ≤ j) (hsum : j + t < 4 * r)
    (S : Finset (W m q)) (hsmall : ∀ u : W m q, (ballS S u (j - 1)).card ≤ B_bound)
    (v y : W m q) (hgt : t < j + hDist v y) :
    ((ballS S v j).filter (fun x => hDist x y ≤ t)).card ≤ H r q * B_bound := by
  by_cases hvy : 4 * r ≤ hDist v y
  · have hemp : (ballS S v j).filter (fun x => hDist x y ≤ t) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [ballS, Finset.mem_filter] at hx
      have htri := hDist_triangle v x y
      omega
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  · let D : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ y i)
    let Centers : Finset (W m q) :=
      insert v ((D ×ˢ (Finset.univ : Finset (Fin q))).image (fun ic => Function.update v ic.1 ic.2))
    have hcardC : Centers.card ≤ H r q := by
      have h1 : Centers.card ≤ ((D ×ˢ (Finset.univ : Finset (Fin q))).image
          (fun ic => Function.update v ic.1 ic.2)).card + 1 := Finset.card_insert_le _ _
      have h2 : ((D ×ˢ (Finset.univ : Finset (Fin q))).image
          (fun ic => Function.update v ic.1 ic.2)).card ≤
          (D ×ˢ (Finset.univ : Finset (Fin q))).card := Finset.card_image_le
      have h3 : (D ×ˢ (Finset.univ : Finset (Fin q))).card = D.card * q := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have h4 : D.card ≤ 4 * r := by
        change hDist v y ≤ 4 * r
        omega
      have h5 : D.card * q ≤ 4 * r * q := Nat.mul_le_mul_right q h4
      unfold H
      omega
    have hsub : (ballS S v j).filter (fun x => hDist x y ≤ t) ⊆
        Centers.biUnion (fun u => ballS S u (j - 1)) := by
      intro x hx
      simp only [ballS, Finset.mem_filter] at hx
      rcases hx with ⟨⟨hxS, hvx⟩, hxy⟩
      by_cases hvx_lt : hDist v x ≤ j - 1
      · refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self v _, ?_⟩
        simp only [ballS, Finset.mem_filter]
        exact ⟨hxS, hvx_lt⟩
      · have hvx_eq : hDist v x = j := by omega
        have hex : ∃ i₀ ∈ D, v i₀ ≠ x i₀ := by
          by_contra hno
          have hall : ∀ i ∈ D, v i = x i := by
            intro i hi
            by_contra hne
            exact hno ⟨i, hi, hne⟩
          let E : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i)
          let F : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)
          have hdisj : Disjoint D E := by
            rw [Finset.disjoint_left]
            intro i hiD hiE
            simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hiE
            exact hiE (hall i hiD)
          have hDE : D ∪ E = F := by
            ext i
            simp only [Finset.mem_union, D, E, F, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h
              rcases h with hvyi | hvxi
              · have hiD : i ∈ D := by
                  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hvyi
                rw [← hall i hiD]
                exact hvyi
              · by_cases hvyi : v i = y i
                · rw [← hvyi]
                  exact Ne.symm hvxi
                · have hiD : i ∈ D := by
                    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact hvyi
                  exact absurd (hall i hiD) hvxi
            · intro hxyi
              by_cases hvyi : v i = y i
              · right
                rw [hvyi]
                exact Ne.symm hxyi
              · left
                exact hvyi
          have hcardF : F.card = D.card + E.card := by
            rw [← hDE, Finset.card_union_of_disjoint hdisj]
          change hDist x y = hDist v y + hDist v x at hcardF
          omega
        obtain ⟨i₀, hi₀D, hvxi₀⟩ := hex
        let u : W m q := Function.update v i₀ (x i₀)
        have huC : u ∈ Centers := by
          apply Finset.mem_insert_of_mem
          refine Finset.mem_image.mpr ⟨(i₀, x i₀), ?_, rfl⟩
          exact Finset.mem_product.mpr ⟨hi₀D, Finset.mem_univ (x i₀)⟩
        have hfilt : (Finset.univ : Finset (Fin m)).filter (fun i => u i ≠ x i) =
            ((Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i)).erase i₀ := by
          ext i
          by_cases hi : i = i₀
          · subst hi
            simp [u, Function.update]
          · simp [u, Function.update, hi]
        have hmem : i₀ ∈ (Finset.univ : Finset (Fin m)).filter (fun i => v i ≠ x i) := by
          simp [hvxi₀]
        have hdux : hDist u x = j - 1 := by
          unfold hDist
          rw [hfilt, Finset.card_erase_of_mem hmem]
          change hDist v x - 1 = j - 1
          omega
        refine Finset.mem_biUnion.mpr ⟨u, huC, ?_⟩
        simp only [ballS, Finset.mem_filter]
        exact ⟨hxS, by omega⟩
    calc ((ballS S v j).filter (fun x => hDist x y ≤ t)).card
        ≤ (Centers.biUnion (fun u => ballS S u (j - 1))).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Centers, (ballS S u (j - 1)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ Centers, B_bound := Finset.sum_le_sum (fun u _ => hsmall u)
      _ = Centers.card * B_bound := by simp
      _ ≤ H r q * B_bound := Nat.mul_le_mul_right B_bound hcardC

def nearCount {m q : Nat} (r : Nat) (S : Finset (W m q)) : Nat :=
  ((S ×ˢ S).filter (fun p => hDist p.1 p.2 < 2 * r)).card

def farCount {m q : Nat} (r : Nat) (S : Finset (W m q)) : Nat :=
  ((S ×ˢ S).filter (fun p => 2 * r < hDist p.1 p.2)).card

lemma card_product_filter_left {α : Type*} (X Y : Finset α)
    (P : α → α → Prop) [DecidableRel P] :
    ((X ×ˢ Y).filter (fun p => P p.1 p.2)).card =
      ∑ x ∈ X, (Y.filter (fun y => P x y)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_product X Y (fun p : α × α => if P p.1 p.2 then (1 : Nat) else 0)

lemma card_product_filter_right {α : Type*} (X Y : Finset α)
    (P : α → α → Prop) [DecidableRel P] :
    ((X ×ˢ Y).filter (fun p => P p.1 p.2)).card =
      ∑ y ∈ Y, (X.filter (fun x => P x y)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_product_right X Y (fun p : α × α => if P p.1 p.2 then (1 : Nat) else 0)

lemma card_product_filter_partition {α : Type*} [DecidableEq α]
    (S S' B : Finset α) (hdisj : Disjoint S' B) (hunion : S' ∪ B = S)
    (P : α → α → Prop) [DecidableRel P] (hsymm : ∀ x y, P x y ↔ P y x) :
    ((S ×ˢ S).filter (fun p => P p.1 p.2)).card =
      ((S' ×ˢ S').filter (fun p => P p.1 p.2)).card +
      ((B ×ˢ B).filter (fun p => P p.1 p.2)).card +
      2 * ∑ y ∈ S', (B.filter (fun x => P x y)).card := by
  rw [← hunion]
  simp only [Finset.card_filter]
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
  rw [Finset.sum_union hdisj]
  have h1 : ∀ x, (∑ y ∈ S' ∪ B, if P x y then (1 : Nat) else 0) =
      (∑ y ∈ S', if P x y then 1 else 0) + (∑ y ∈ B, if P x y then 1 else 0) :=
    fun x => Finset.sum_union hdisj
  simp only [h1, Finset.sum_add_distrib]
  have hcross1 : (∑ x ∈ S', ∑ y ∈ B, if P x y then (1 : Nat) else 0) =
      ∑ y ∈ S', ∑ x ∈ B, if P x y then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    simp [hsymm y x]
  have hcross2 : (∑ x ∈ B, ∑ y ∈ S', if P x y then (1 : Nat) else 0) =
      ∑ y ∈ S', ∑ x ∈ B, if P x y then 1 else 0 := Finset.sum_comm
  rw [hcross1, hcross2]
  ring

lemma A_internal_bound {q r k : Nat} (hr : 0 < r) (hk : 0 < k) {t₀ : Nat}
    (ht1 : 1 ≤ t₀) (htr : t₀ ≤ r) :
    A q r k 0 + H r q * A q r k (t₀ - 1) ≤ A q r k r := by
  have h0 : A q r k 0 ≤ A q r k (r - 1) := A_mono q r k 0 (r - 1) (Nat.zero_le _)
  have ht : A q r k (t₀ - 1) ≤ A q r k (r - 1) := A_mono q r k (t₀ - 1) (r - 1) (by omega)
  have hHpos : 1 ≤ H r q := by
    unfold H
    omega
  have hcoeff : 1 + H r q ≤ (k + 1) * H r q := by
    have h2 : 2 ≤ k + 1 := by omega
    have hmul : 2 * H r q ≤ (k + 1) * H r q := Nat.mul_le_mul_right (H r q) h2
    omega
  have hsucc : A q r k r = (k + 1) * H r q * A q r k (r - 1) := by
    have h := A_succ q r k (r - 1)
    rwa [Nat.sub_add_cancel hr] at h
  rw [hsucc]
  calc A q r k 0 + H r q * A q r k (t₀ - 1)
      ≤ A q r k (r - 1) + H r q * A q r k (r - 1) :=
        Nat.add_le_add h0 (Nat.mul_le_mul_left (H r q) ht)
    _ = (1 + H r q) * A q r k (r - 1) := by ring
    _ ≤ (k + 1) * H r q * A q r k (r - 1) := Nat.mul_le_mul_right _ hcoeff

lemma main_ind {q r k m : Nat} (hq : 2 ≤ q) (hr : 0 < r) (hk : 0 < k) :
    ∀ nS : Nat, ∀ S : Finset (W m q), S.card = nS →
      k * nearCount r S ≤ k * A q r k r * M m r * S.card + farCount r S := by
  intro nS
  induction nS using Nat.strong_induction_on with
  | ind nS ih =>
    intro S hScard
    classical
    by_cases hall : ∀ t₀ ∈ Finset.Icc 1 r, ∀ v : W m q,
        (ballS S v (r - 1 + t₀)).card ≤ A q r k t₀ * M m r
    · have hr_mem : r ∈ Finset.Icc 1 r := by
        simp only [Finset.mem_Icc]
        omega
      have hnear_eq : nearCount r S = ∑ x ∈ S, (S.filter (fun y => hDist x y < 2 * r)).card :=
        card_product_filter_left S S (fun x y => hDist x y < 2 * r)
      have hrow : ∀ x ∈ S, (S.filter (fun y => hDist x y < 2 * r)).card ≤ A q r k r * M m r := by
        intro x _
        have hfilt_eq : S.filter (fun y => hDist x y < 2 * r) = ballS S x (r - 1 + r) := by
          ext y
          simp only [ballS, Finset.mem_filter]
          exact and_congr_right fun _ => by omega
        rw [hfilt_eq]
        exact hall r hr_mem x
      have hnear_le : nearCount r S ≤ S.card * (A q r k r * M m r) := by
        rw [hnear_eq]
        calc (∑ x ∈ S, (S.filter (fun y => hDist x y < 2 * r)).card)
            ≤ ∑ _x ∈ S, A q r k r * M m r := Finset.sum_le_sum hrow
          _ = S.card * (A q r k r * M m r) := by simp
      have hmul : k * nearCount r S ≤ k * (S.card * (A q r k r * M m r)) :=
        Nat.mul_le_mul_left k hnear_le
      have hrew : k * (S.card * (A q r k r * M m r)) = k * A q r k r * M m r * S.card := by ring
      omega
    · let BadT : Finset Nat :=
        (Finset.Icc 1 r).filter (fun t₀ => ∃ v : W m q, A q r k t₀ * M m r < (ballS S v (r - 1 + t₀)).card)
      have hBad_ne : BadT.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hall
        intro t₀ ht₀ v
        by_contra hlt
        have hmem : t₀ ∈ BadT := by
          simp only [BadT, Finset.mem_filter]
          exact ⟨ht₀, ⟨v, by omega⟩⟩
        rw [hemp] at hmem
        simp at hmem
      let t₀ : Nat := BadT.min' hBad_ne
      have ht₀_mem : t₀ ∈ BadT := Finset.min'_mem BadT hBad_ne
      have ht₀_bounds : 1 ≤ t₀ ∧ t₀ ≤ r := by
        simp only [BadT, Finset.mem_filter, Finset.mem_Icc] at ht₀_mem
        exact ht₀_mem.1
      have hex_v : ∃ v : W m q, A q r k t₀ * M m r < (ballS S v (r - 1 + t₀)).card := by
        simp only [BadT, Finset.mem_filter] at ht₀_mem
        exact ht₀_mem.2
      obtain ⟨v, hv_big⟩ := hex_v
      let j : Nat := r - 1 + t₀
      have hj_lo : r ≤ j := by omega
      have hj_hi : j ≤ 2 * r - 1 := by omega
      have hj_pos : 1 ≤ j := by omega
      have hsmall : ∀ u : W m q, (ballS S u (j - 1)).card ≤ A q r k (t₀ - 1) * M m r := by
        intro u
        by_cases ht1 : t₀ = 1
        · have hj1 : j - 1 = r - 1 := by omega
          have ht0 : t₀ - 1 = 0 := by omega
          rw [hj1, ht0]
          exact card_ball_r_sub_one hq hr S u
        · have hprev_mem : t₀ - 1 ∈ Finset.Icc 1 r := by
            simp only [Finset.mem_Icc]
            omega
          have hjprev : j - 1 = r - 1 + (t₀ - 1) := by omega
          rw [hjprev]
          by_contra hlt
          have hmem : t₀ - 1 ∈ BadT := by
            simp only [BadT, Finset.mem_filter]
            exact ⟨hprev_mem, ⟨u, by omega⟩⟩
          have hle : t₀ ≤ t₀ - 1 := Finset.min'_le BadT (t₀ - 1) hmem
          omega
      let B : Finset (W m q) := ballS S v j
      let S' : Finset (W m q) := S \ B
      have hB_sub : B ⊆ S := Finset.filter_subset _ _
      have hdisj : Disjoint S' B := Finset.sdiff_disjoint
      have hunion : S' ∪ B = S := Finset.sdiff_union_of_subset hB_sub
      have hScard_split : S.card = S'.card + B.card := by
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
      have hB_pos : 0 < B.card := by
        change 0 < (ballS S v (r - 1 + t₀)).card
        omega
      have hS'_lt : S'.card < nS := by omega
      have hIH : k * nearCount r S' ≤ k * A q r k r * M m r * S'.card + farCount r S' :=
        ih S'.card hS'_lt S' rfl
      have hnear_part : nearCount r S =
          nearCount r S' + nearCount r B + 2 * ∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card := by
        unfold nearCount
        exact card_product_filter_partition S S' B hdisj hunion
          (fun x y => hDist x y < 2 * r) (fun x y => by rw [hDist_comm])
      have hfar_part : farCount r S =
          farCount r S' + farCount r B + 2 * ∑ y ∈ S', (B.filter (fun x => 2 * r < hDist x y)).card := by
        unfold farCount
        exact card_product_filter_partition S S' B hdisj hunion
          (fun x y => 2 * r < hDist x y) (fun x y => by rw [hDist_comm])
      let Q : Nat := H r q * (A q r k (t₀ - 1) * M m r)
      have hB_gt_Q : k * Q + Q < B.card := by
        have hAt0 : A q r k t₀ = (k + 1) * H r q * A q r k (t₀ - 1) := by
          have h := A_succ q r k (t₀ - 1)
          rwa [Nat.sub_add_cancel ht₀_bounds.1] at h
        have hmul_eq : A q r k t₀ * M m r = k * Q + Q := by
          rw [hAt0]
          dsimp only [Q]
          ring
        change A q r k t₀ * M m r < B.card at hv_big
        omega
      have hcross_pt : ∀ y ∈ S',
          k * (B.filter (fun x => hDist x y < 2 * r)).card ≤
            (B.filter (fun x => 2 * r < hDist x y)).card := by
        intro y hy
        have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
        have hyNotB : y ∉ B := (Finset.mem_sdiff.mp hy).2
        have hj_lt : j < hDist v y := by
          by_contra hle
          apply hyNotB
          simp only [B, ballS, Finset.mem_filter]
          exact ⟨hyS, by omega⟩
        have hleQ : (B.filter (fun x => hDist x y ≤ 2 * r)).card ≤ Q := by
          exact ball_inter_le hj_pos (by omega) S hsmall v y (by omega)
        have hlt_le : (B.filter (fun x => hDist x y < 2 * r)).card ≤
            (B.filter (fun x => hDist x y ≤ 2 * r)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, by omega⟩
        have hcompl : (B.filter (fun x => hDist x y ≤ 2 * r)).card +
            (B.filter (fun x => 2 * r < hDist x y)).card = B.card := by
          have hdisjB : Disjoint (B.filter (fun x => hDist x y ≤ 2 * r))
              (B.filter (fun x => 2 * r < hDist x y)) := by
            rw [Finset.disjoint_left]
            intro x h1 h2
            simp only [Finset.mem_filter] at h1 h2
            omega
          have hunionB : B.filter (fun x => hDist x y ≤ 2 * r) ∪
              B.filter (fun x => 2 * r < hDist x y) = B := by
            ext x
            simp only [Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
            · intro hx
              by_cases hle : hDist x y ≤ 2 * r
              · left
                exact ⟨hx, hle⟩
              · right
                exact ⟨hx, by omega⟩
          rw [← Finset.card_union_of_disjoint hdisjB, hunionB]
        have hkn : k * (B.filter (fun x => hDist x y < 2 * r)).card ≤ k * Q :=
          Nat.mul_le_mul_left k (hlt_le.trans hleQ)
        omega
      have hcross : k * (2 * ∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card) ≤
          2 * ∑ y ∈ S', (B.filter (fun x => 2 * r < hDist x y)).card := by
        have hsum_le : k * (∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card) ≤
            ∑ y ∈ S', (B.filter (fun x => 2 * r < hDist x y)).card := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hcross_pt
        have hcomm : k * (2 * ∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card) =
            2 * (k * ∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card) := by ring
        rw [hcomm]
        exact Nat.mul_le_mul_left 2 hsum_le
      have hB_near : nearCount r B ≤ A q r k r * M m r * B.card := by
        have hB_eq : nearCount r B = ∑ y ∈ B, (B.filter (fun x => hDist x y < 2 * r)).card :=
          card_product_filter_right B B (fun x y => hDist x y < 2 * r)
        rw [hB_eq]
        rw [← Finset.sum_filter_add_sum_filter_not B (fun y => hDist v y ≤ r - 1)]
        let B₁ := B.filter (fun y => hDist v y ≤ r - 1)
        let B₂ := B.filter (fun y => ¬ hDist v y ≤ r - 1)
        have hB1_sub : B₁ ⊆ ballS S v (r - 1) := by
          intro y hy
          simp only [B₁, B, ballS, Finset.mem_filter] at hy ⊢
          exact ⟨hy.1.1, hy.2⟩
        have hB1_card : B₁.card ≤ A q r k 0 * M m r :=
          (Finset.card_le_card hB1_sub).trans (card_ball_r_sub_one hq hr S v)
        have hsum1 : (∑ y ∈ B₁, (B.filter (fun x => hDist x y < 2 * r)).card) ≤
            A q r k 0 * M m r * B.card := by
          calc (∑ y ∈ B₁, (B.filter (fun x => hDist x y < 2 * r)).card)
              ≤ ∑ _y ∈ B₁, B.card := Finset.sum_le_sum (fun y _ => Finset.card_filter_le _ _)
            _ = B₁.card * B.card := by simp
            _ ≤ A q r k 0 * M m r * B.card := Nat.mul_le_mul_right B.card hB1_card
        have hB2_row : ∀ y ∈ B₂, (B.filter (fun x => hDist x y < 2 * r)).card ≤ Q := by
          intro y hy
          simp only [B₂, Finset.mem_filter] at hy
          have hfeq : B.filter (fun x => hDist x y < 2 * r) =
              B.filter (fun x => hDist x y ≤ 2 * r - 1) := by
            ext x
            simp only [Finset.mem_filter]
            exact and_congr_right fun _ => by omega
          rw [hfeq]
          exact ball_inter_le hj_pos (by omega) S hsmall v y (by omega)
        have hB2_card : B₂.card ≤ B.card := Finset.card_filter_le _ _
        have hsum2 : (∑ y ∈ B₂, (B.filter (fun x => hDist x y < 2 * r)).card) ≤
            B.card * Q := by
          calc (∑ y ∈ B₂, (B.filter (fun x => hDist x y < 2 * r)).card)
              ≤ ∑ _y ∈ B₂, Q := Finset.sum_le_sum hB2_row
            _ = B₂.card * Q := by simp
            _ ≤ B.card * Q := Nat.mul_le_mul_right Q hB2_card
        have hcomb : A q r k 0 * M m r * B.card + B.card * Q =
            (A q r k 0 + H r q * A q r k (t₀ - 1)) * M m r * B.card := by
          dsimp only [Q]
          ring
        have hA_le : A q r k 0 + H r q * A q r k (t₀ - 1) ≤ A q r k r :=
          A_internal_bound hr hk ht₀_bounds.1 ht₀_bounds.2
        have hfinal_B : (A q r k 0 + H r q * A q r k (t₀ - 1)) * M m r * B.card ≤
            A q r k r * M m r * B.card :=
          Nat.mul_le_mul_right B.card (Nat.mul_le_mul_right (M m r) hA_le)
        calc (∑ y ∈ B₁, (B.filter (fun x => hDist x y < 2 * r)).card) +
              (∑ y ∈ B₂, (B.filter (fun x => hDist x y < 2 * r)).card)
            ≤ A q r k 0 * M m r * B.card + B.card * Q := Nat.add_le_add hsum1 hsum2
          _ = (A q r k 0 + H r q * A q r k (t₀ - 1)) * M m r * B.card := hcomb
          _ ≤ A q r k r * M m r * B.card := hfinal_B
      have hkB : k * nearCount r B ≤ k * A q r k r * M m r * B.card := by
        have h1 := Nat.mul_le_mul_left k hB_near
        have h2 : k * (A q r k r * M m r * B.card) = k * A q r k r * M m r * B.card := by ring
        omega
      have hS_mul : k * A q r k r * M m r * S.card =
          k * A q r k r * M m r * S'.card + k * A q r k r * M m r * B.card := by
        rw [hScard_split]
        ring
      have hnear_mul : k * nearCount r S =
          k * nearCount r S' + k * nearCount r B +
          k * (2 * ∑ y ∈ S', (B.filter (fun x => hDist x y < 2 * r)).card) := by
        rw [hnear_part]
        ring
      linarith

end PEqualNP.Outside.L_lib_1012

theorem PEqualNP.Outside.L_lib_1012 : (∀ (q r k : Nat), 2 ≤ q → 0 < r → 0 < k →
  let C := r * q^r * ((k+1)*(1+4*r*q))^r
  ∀ m : Nat,
    let W := Fin m → Fin q
    let dist := fun (x y : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)).card
    ∀ S : Finset W,
      let pairs := S.product S
      let near := (pairs.filter (fun p => dist p.1 p.2 < 2*r)).card
      let far := (pairs.filter (fun p => 2*r < dist p.1 p.2)).card
      k * near ≤ k * C * (m+1)^(r-1) * S.card + far) := by
  intro q r k hq hr hk C m W dist S pairs near far
  exact PEqualNP.Outside.L_lib_1012.main_ind hq hr hk S.card S rfl
