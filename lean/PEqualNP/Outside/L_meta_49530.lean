import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49530_aux
open Classical

section Chain
variable {V : Type}

theorem chain_mono {l : ℕ} (x : Fin (l + 1) → Finset V) (hx : ∀ i : Fin l, x i.castSucc ⊆ x i.succ) :
    ∀ (b a : Fin (l + 1)), a ≤ b → x a ⊆ x b := by
  intro b
  induction b using Fin.induction with
  | zero =>
    intro a ha
    have : a = 0 := le_antisymm ha (Fin.zero_le a)
    subst this
    exact Finset.Subset.refl _
  | succ b ih =>
    intro a ha
    rcases lt_or_eq_of_le ha with h | h
    · have : a ≤ b.castSucc := by
        rw [Fin.le_def]; simp only [Fin.val_castSucc]
        have := Fin.lt_def.mp h
        simp only [Fin.val_succ] at this
        omega
      exact (ih a this).trans (hx b)
    · rw [h]

theorem succ_sub {l : ℕ} (x : Fin (l + 1) → Finset V) (hx : ∀ i : Fin l, x i.castSucc ⊆ x i.succ)
    {i i' : Fin l} (h : i < i') : x i.succ ⊆ x i'.castSucc := by
  apply chain_mono x hx
  rw [Fin.le_def]
  simp only [Fin.val_succ, Fin.val_castSucc]
  have := Fin.lt_def.mp h
  omega

theorem chain_drops [inst : ∀ p : Prop, Decidable p] {l : ℕ} (g : V → V → Prop)
    (uniq : ∀ a b : V, a ≠ b → ∀ j j' : V, g a j → g b j → g a j' → g b j' → j = j')
    (x : Fin (l + 1) → Finset V) (hx : ∀ i : Fin l, x i.castSucc ⊆ x i.succ) (j : Fin l → V) :
    (Finset.univ.filter (fun i : Fin l => (∀ e ∈ x i.castSucc, g e (j i)) ∧
      ¬ ∀ e ∈ x i.succ, g e (j i))).card ≤ 3 := by
  set Dr := Finset.univ.filter (fun i : Fin l => (∀ e ∈ x i.castSucc, g e (j i)) ∧
      ¬ ∀ e ∈ x i.succ, g e (j i)) with hDr
  have hmem : ∀ i, i ∈ Dr ↔ (∀ e ∈ x i.castSucc, g e (j i)) ∧ ¬ ∀ e ∈ x i.succ, g e (j i) := by
    intro i; simp [hDr]
  have h0 : (Dr.filter (fun i => x i.castSucc = ∅)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    have key : ∀ i i', i ∈ Dr.filter (fun i => x i.castSucc = ∅) →
        i' ∈ Dr.filter (fun i => x i.castSucc = ∅) → i < i' → False := by
      intro i i' hi hi' hlt
      obtain ⟨hiD, hie⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi'D, hi'e⟩ := Finset.mem_filter.mp hi'
      have hsub := succ_sub x hx hlt
      rw [hi'e] at hsub
      have : x i.succ = ∅ := Finset.subset_empty.mp hsub
      exact ((hmem i).mp hiD).2 (by simp [this])
    intro a ha b hb
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha hb h).elim
    · exact h
    · exact (key b a hb ha h).elim
  have h1 : (Dr.filter (fun i => (x i.castSucc).card = 1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    have key : ∀ i i', i ∈ Dr.filter (fun i => (x i.castSucc).card = 1) →
        i' ∈ Dr.filter (fun i => (x i.castSucc).card = 1) → i < i' → False := by
      intro i i' hi hi' hlt
      obtain ⟨hiD, hic⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi'D, hi'c⟩ := Finset.mem_filter.mp hi'
      have hsub := succ_sub x hx hlt
      have hs1 : x i.succ ⊆ x i'.castSucc := hsub
      have hs2 : x i.castSucc ⊆ x i.succ := hx i
      have hEq : x i.castSucc = x i'.castSucc :=
        Finset.eq_of_subset_of_card_le (hs2.trans hs1) (by rw [hic, hi'c])
      have hEq2 : x i.succ = x i.castSucc :=
        Finset.Subset.antisymm (by rw [hEq]; exact hs1) hs2
      obtain ⟨hA, hB⟩ := (hmem i).mp hiD
      exact hB (by rw [hEq2]; exact hA)
    intro a ha b hb
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha hb h).elim
    · exact h
    · exact (key b a hb ha h).elim
  have h2 : (Dr.filter (fun i => 2 ≤ (x i.castSucc).card)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    have key : ∀ i i', i ∈ Dr.filter (fun i => 2 ≤ (x i.castSucc).card) →
        i' ∈ Dr.filter (fun i => 2 ≤ (x i.castSucc).card) → i < i' → False := by
      intro i i' hi hi' hlt
      obtain ⟨hiD, hic⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi'D, hi'c⟩ := Finset.mem_filter.mp hi'
      obtain ⟨hA, hB⟩ := (hmem i).mp hiD
      obtain ⟨hA', hB'⟩ := (hmem i').mp hi'D
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le Nat.one_lt_two hic)
      have hsub := succ_sub x hx hlt
      have hmono : x i.castSucc ⊆ x i'.castSucc := (hx i).trans hsub
      have e1 := uniq a b hab (j i) (j i') (hA a ha) (hA b hb) (hA' a (hmono ha)) (hA' b (hmono hb))
      apply hB
      intro e he
      have : e ∈ x i'.castSucc := hsub he
      rw [e1]; exact hA' e this
    intro a ha b hb
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha hb h).elim
    · exact h
    · exact (key b a hb ha h).elim
  have hcover : Dr ⊆ Dr.filter (fun i => x i.castSucc = ∅) ∪
      Dr.filter (fun i => (x i.castSucc).card = 1) ∪
      Dr.filter (fun i => 2 ≤ (x i.castSucc).card) := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases Nat.lt_or_ge (x i.castSucc).card 2 with h | h
    · rcases Nat.lt_or_ge (x i.castSucc).card 1 with h' | h'
      · left; left; exact ⟨hi, Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h')⟩
      · left; right; exact ⟨hi, Nat.le_antisymm (Nat.lt_succ_iff.mp h) h'⟩
    · right; exact ⟨hi, h⟩
  calc Dr.card ≤ (Dr.filter (fun i => x i.castSucc = ∅) ∪
      Dr.filter (fun i => (x i.castSucc).card = 1) ∪
      Dr.filter (fun i => 2 ≤ (x i.castSucc).card)).card := Finset.card_le_card hcover
    _ ≤ (Dr.filter (fun i => x i.castSucc = ∅) ∪
      Dr.filter (fun i => (x i.castSucc).card = 1)).card +
      (Dr.filter (fun i => 2 ≤ (x i.castSucc).card)).card := Finset.card_union_le _ _
    _ ≤ ((Dr.filter (fun i => x i.castSucc = ∅)).card +
      (Dr.filter (fun i => (x i.castSucc).card = 1)).card) +
      (Dr.filter (fun i => 2 ≤ (x i.castSucc).card)).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 3 := le_trans (Nat.add_le_add (Nat.add_le_add h0 h1) h2) (le_refl 3)

theorem chain_sum [inst : ∀ p : Prop, Decidable p] {l : ℕ} (g : V → V → Prop) (D : ℕ)
    (uniq : ∀ a b : V, a ≠ b → ∀ j j' : V, g a j → g b j → g a j' → g b j' → j = j')
    (x : Fin (l + 1) → Finset V) (hx : ∀ i : Fin l, x i.castSucc ⊆ x i.succ) (j : Fin l → V) :
    (Finset.univ.sum (fun i : Fin l =>
      (if ∀ e ∈ x i.castSucc, g e (j i) then D else 0) -
      (if ∀ e ∈ x i.succ, g e (j i) then D else 0))) ≤ 3 * D := by
  have hterm : ∀ i : Fin l,
      ((if ∀ e ∈ x i.castSucc, g e (j i) then D else 0) -
      (if ∀ e ∈ x i.succ, g e (j i) then D else 0)) =
      if ((∀ e ∈ x i.castSucc, g e (j i)) ∧ ¬ ∀ e ∈ x i.succ, g e (j i)) then D else 0 := by
    intro i
    by_cases hA : ∀ e ∈ x i.castSucc, g e (j i)
    · by_cases hB : ∀ e ∈ x i.succ, g e (j i)
      · rw [if_pos hA, if_pos hB, if_neg (fun h => h.2 hB)]; simp
      · rw [if_pos hA, if_neg hB, if_pos ⟨hA, hB⟩]; simp
    · rw [if_neg hA, if_neg (fun h => hA (fun e he => h e (hx i he))),
        if_neg (fun h => hA h.1)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul]
  have := chain_drops g uniq x hx j
  exact Nat.mul_le_mul_right D this

end Chain

end PEqualNP.Outside.L_meta_49530_aux

namespace PEqualNP.Outside.L_meta_49530_aux
open Classical

section Plane
variable {p : ℕ} [Fact p.Prime]

abbrev Pt (p : ℕ) := ZMod p × ZMod p

def rel (x y : Pt p) : Prop := x.2 + y.2 = x.1 * y.1

theorem rel_symm {x y : Pt p} (h : rel x y) : rel y x := by
  unfold rel at *
  rw [add_comm, mul_comm]; exact h

theorem card_nbrs (x : Pt p) : (Finset.univ.filter (fun w : Pt p => rel x w)).card = p := by
  have : Finset.univ.filter (fun w : Pt p => rel x w) =
      (Finset.univ : Finset (ZMod p)).image (fun a => (a, x.1 * a - x.2)) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, h⟩
      unfold rel at h
      exact ⟨w.1, Finset.mem_univ _, Prod.ext rfl (by simp only; linear_combination -h)⟩
    · rintro ⟨a, -, rfl⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold rel
      simp only; ring
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  simp [ZMod.card]

theorem card_common (x y : Pt p) (hxy : x ≠ y) :
    (Finset.univ.filter (fun w : Pt p => rel x w ∧ rel y w)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro w hw w' hw'
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hw).2
  obtain ⟨h1', h2'⟩ := (Finset.mem_filter.mp hw').2
  unfold rel at h1 h2 h1' h2'
  have hmul : (x.1 - y.1) * (w.1 - w'.1) = 0 := by
    linear_combination -h1 + h2 + h1' - h2'
  rcases mul_eq_zero.mp hmul with h | h
  · exfalso
    apply hxy
    have hx1 : x.1 = y.1 := sub_eq_zero.mp h
    have hx2 : x.2 = y.2 := by
      linear_combination h1 - h2 + w.1 * hx1
    exact Prod.ext hx1 hx2
  · have hw1 : w.1 = w'.1 := sub_eq_zero.mp h
    ext
    · exact hw1
    · linear_combination h1 - h1' + x.1 * hw1

end Plane

end PEqualNP.Outside.L_meta_49530_aux

namespace PEqualNP.Outside.L_meta_49530_aux
open Classical

section Indep
variable {p : ℕ} [Fact p.Prime]

theorem indep_bound (S : Finset (Pt p)) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ rel x y) :
    S.card ^ 2 ≤ p * S.card + p ^ 2 * (p - 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set t := S.card with ht
  set c : Pt p → ℕ := fun w => (S.filter (fun x => rel x w)).card with hcdef
  have hc_eq : ∀ w : Pt p, c w = ∑ x ∈ S, if rel x w then 1 else 0 := by
    intro w; show (S.filter (fun x => rel x w)).card = _; exact Finset.card_filter _ _
  have hc_sum : ∑ w : Pt p, c w = p * t := by
    rw [Finset.sum_congr rfl (fun w _ => hc_eq w), Finset.sum_comm]
    have : ∀ x ∈ S, ∑ w : Pt p, (if rel x w then 1 else 0) = p := by
      intro x _
      rw [← Finset.card_filter]; exact card_nbrs x
    rw [Finset.sum_congr rfl this]; simp [ht, mul_comm]
  have hc_sq : ∑ w : Pt p, c w ^ 2 ≤ t * (p - 1 + t) := by
    have e1 : ∀ w : Pt p, c w ^ 2 = ∑ x ∈ S, ∑ y ∈ S,
        (if rel x w then 1 else 0) * (if rel y w then 1 else 0) := by
      intro w
      rw [hc_eq w, sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun w _ => e1 w), Finset.sum_comm]
    have e2 : ∀ x ∈ S, ∑ w : Pt p, ∑ y ∈ S,
        (if rel x w then 1 else 0) * (if rel y w then 1 else 0) ≤ p - 1 + t := by
      intro x hx
      rw [Finset.sum_comm]
      have e3 : ∀ y ∈ S, ∑ w : Pt p, (if rel x w then 1 else 0) * (if rel y w then 1 else 0) ≤
          (if y = x then p - 1 else 0) + 1 := by
        intro y hy
        have : ∑ w : Pt p, (if rel x w then 1 else 0) * (if rel y w then 1 else 0) =
            (Finset.univ.filter (fun w : Pt p => rel x w ∧ rel y w)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro w _
          by_cases h1 : rel x w <;> by_cases h2 : rel y w <;> simp [h1, h2]
        rw [this]
        by_cases hyx : y = x
        · subst hyx
          have : (Finset.univ.filter (fun w : Pt p => rel y w ∧ rel y w)) =
              Finset.univ.filter (fun w : Pt p => rel y w) := by
            ext w; simp
          rw [this, card_nbrs]
          simp; omega
        · have := card_common x y (Ne.symm hyx)
          simp [hyx]; exact this
      calc _ ≤ ∑ y ∈ S, ((if y = x then p - 1 else 0) + 1) := Finset.sum_le_sum e3
        _ = (p - 1) + t := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S x, if_pos hx]; simp [ht]
    calc _ ≤ ∑ x ∈ S, (p - 1 + t) := Finset.sum_le_sum e2
      _ = t * (p - 1 + t) := by simp [ht]
  have hinS : ∀ w ∈ S, c w ≤ 1 := by
    intro w hw
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxw : x = w := by
      by_contra hne
      exact hS x hx'.1 w hw hne hx'.2
    have hyw : y = w := by
      by_contra hne
      exact hS y hy'.1 w hw hne hy'.2
    rw [hxw, hyw]
  set O : Finset (Pt p) := Finset.univ \ S with hO
  have hOcard : O.card = p * p - t := by
    rw [hO, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [ZMod.card, Fintype.card_prod, ht]
  have hsumO : p * t - t ≤ ∑ w ∈ O, c w := by
    have h1 : ∑ w ∈ O, c w + ∑ w ∈ S, c w = ∑ w : Pt p, c w :=
      Finset.sum_sdiff (Finset.subset_univ S)
    have h2 : ∑ w ∈ S, c w ≤ t := by
      calc ∑ w ∈ S, c w ≤ ∑ w ∈ S, 1 := Finset.sum_le_sum hinS
        _ = t := by simp [ht]
    omega
  have hsqO : ∑ w ∈ O, c w ^ 2 ≤ t * (p - 1 + t) := by
    refine le_trans ?_ hc_sq
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ O)
  have hcs : (∑ w ∈ O, c w) ^ 2 ≤ O.card * ∑ w ∈ O, c w ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq O (fun w => (1 : ℕ)) (fun w => c w)
    simpa [mul_comm] using this

  by_cases ht0 : t = 0
  · rw [ht0]; simp
  have htpos : 0 < t := Nat.pos_of_ne_zero ht0
  have htp : t ≤ p * p := by
    have : S.card ≤ Fintype.card (Pt p) := Finset.card_le_univ S
    simpa [ZMod.card, Fintype.card_prod] using this
  have hpt : t ≤ p * t := by nlinarith
  have hA : (p - 1) * t ≤ ∑ w ∈ O, c w := by
    have : (p - 1) * t = p * t - t := by
      rw [Nat.sub_mul, one_mul]
    omega
  have hA2 : ((p - 1) * t) ^ 2 ≤ (O.card * (t * (p - 1 + t)) : ℕ) :=
    (Nat.pow_le_pow_left hA 2).trans (hcs.trans (Nat.mul_le_mul_left _ hsqO))
  rw [hOcard] at hA2
  have hp1 : 1 ≤ p := by omega
  zify [hp1, htp] at hA2 ⊢
  have hT : (0 : ℤ) < t := by exact_mod_cast htpos
  have key : (t : ℤ) * ((t : ℤ) ^ 2 - p * t - p ^ 2 * (p - 1)) ≤ 0 := by nlinarith [hA2]
  by_contra hcon
  push_neg at hcon
  have hD : 0 < (t : ℤ) ^ 2 - p * t - p ^ 2 * (p - 1) := by linarith
  nlinarith [mul_pos hT hD, key]

end Indep

end PEqualNP.Outside.L_meta_49530_aux

open PEqualNP.Outside.L_meta_49530_aux in
theorem PEqualNP.Outside.L_meta_49530 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (p : Nat), p.Prime →
  ∀ (n : Nat) (v : Fin n → Fin p × Fin p), Function.Injective v →
    let g := fun (i j : Fin n) => i ≠ j ∧
      ((v i).2.val + (v j).2.val) % p = ((v i).1.val * (v j).1.val) % p
    ∀ D : Nat,
      let f := fun (x : Finset (Fin n)) (j : Fin n) => if ∀ i ∈ x, g i j then D else 0
      (∀ (l : Nat) (x : Fin (l+1) → Finset (Fin n)) (j : Fin l → Fin n),
        (∀ i : Fin l, x i.castSucc ⊆ x i.succ) →
        Finset.univ.sum (fun i : Fin l => f (x i.castSucc) (j i) - f (x i.succ) (j i))
          ≤ 3*D) ∧
      ∀ (K : Nat) (color : Fin n → Finset (Fin K)),
        (∀ i, (color i).card = D) →
        (∀ i j, g i j → Disjoint (color i) (color j)) →
        (n*D)^2 ≤ K*p*(n*D) + K^2*p^2*(p-1)) := by
  intro p hp n v hv g D f
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let pt : Fin n → Pt p := fun i => (((v i).1.val : ZMod p), ((v i).2.val : ZMod p))
  have hg : ∀ i j, g i j ↔ (i ≠ j ∧ rel (pt i) (pt j)) := by
    intro i j
    show (i ≠ j ∧ ((v i).2.val + (v j).2.val) % p = ((v i).1.val * (v j).1.val) % p) ↔ _
    apply and_congr_right
    intro _
    unfold rel
    simp only [pt]
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    exact Iff.rfl
  have hptinj : Function.Injective pt := by
    intro i j h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [pt] at h1 h2
    have a1 : (v i).1.val = (v j).1.val := by
      have := congrArg ZMod.val h1
      rwa [ZMod.val_natCast_of_lt (v i).1.isLt, ZMod.val_natCast_of_lt (v j).1.isLt] at this
    have b1 : (v i).2.val = (v j).2.val := by
      have := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt (v i).2.isLt, ZMod.val_natCast_of_lt (v j).2.isLt] at this
    exact hv (Prod.ext (Fin.ext a1) (Fin.ext b1))
  have uniq : ∀ a b : Fin n, a ≠ b → ∀ j j' : Fin n, g a j → g b j → g a j' → g b j' → j = j' := by
    intro a b hab j j' h1 h2 h3 h4
    have hne : pt a ≠ pt b := fun h => hab (hptinj h)
    have hc := card_common (pt a) (pt b) hne
    have e1 := ((hg a j).mp h1).2
    have e2 := ((hg b j).mp h2).2
    have e3 := ((hg a j').mp h3).2
    have e4 := ((hg b j').mp h4).2
    have := Finset.card_le_one.mp hc (pt j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e1, e2⟩)
      (pt j') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e3, e4⟩)
    exact hptinj this
  refine ⟨fun l x j hx => chain_sum g D uniq x hx j, ?_⟩
  intro K color hcard hdisj
  set tk : Fin K → ℕ := fun k => (Finset.univ.filter (fun i : Fin n => k ∈ color i)).card with htk
  have hsumt : ∑ k : Fin K, tk k = n * D := by
    have e1 : ∀ k : Fin K, tk k = ∑ i : Fin n, if k ∈ color i then 1 else 0 := by
      intro k; show (Finset.univ.filter (fun i : Fin n => k ∈ color i)).card = _
      exact Finset.card_filter _ _
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_comm]
    have e2 : ∀ i : Fin n, ∑ k : Fin K, (if k ∈ color i then 1 else 0) = D := by
      intro i
      rw [← Finset.card_filter]
      have : Finset.univ.filter (fun k : Fin K => k ∈ color i) = color i := by
        ext k; simp
      rw [this]; exact hcard i
    rw [Finset.sum_congr rfl (fun i _ => e2 i)]
    simp
  have hbound : ∀ k : Fin K, tk k ^ 2 ≤ p * tk k + p ^ 2 * (p - 1) := by
    intro k
    set S := (Finset.univ.filter (fun i : Fin n => k ∈ color i)).image pt with hS
    have hcardS : S.card = tk k := Finset.card_image_of_injective _ hptinj
    rw [← hcardS]
    apply indep_bound
    intro x hx y hy hxy hrel
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (by rw [h])
    have hd := hdisj i j ((hg i j).mpr ⟨hij, hrel⟩)
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hcs : (∑ k : Fin K, tk k) ^ 2 ≤ K * ∑ k : Fin K, tk k ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin K)) (fun _ => (1 : ℕ)) tk
    simpa [mul_comm] using this
  have hsq : ∑ k : Fin K, tk k ^ 2 ≤ p * (n * D) + K * (p ^ 2 * (p - 1)) := by
    calc ∑ k : Fin K, tk k ^ 2 ≤ ∑ k : Fin K, (p * tk k + p ^ 2 * (p - 1)) :=
          Finset.sum_le_sum (fun k _ => hbound k)
      _ = p * (n * D) + K * (p ^ 2 * (p - 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumt]; simp
  calc (n * D) ^ 2 = (∑ k : Fin K, tk k) ^ 2 := by rw [hsumt]
    _ ≤ K * ∑ k : Fin K, tk k ^ 2 := hcs
    _ ≤ K * (p * (n * D) + K * (p ^ 2 * (p - 1))) := Nat.mul_le_mul_left _ hsq
    _ = K * p * (n * D) + K ^ 2 * p ^ 2 * (p - 1) := by ring
