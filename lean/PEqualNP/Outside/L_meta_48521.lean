import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48521

/- Part 1: parity of alternating labellings. -/

def altL : Bool → List Bool → Bool
  | _, [] => true
  | s, x :: xs => (x == s) && altL (!s) xs

def par (t : ℕ) : Bool := decide (t % 2 = 1)

def ind (b : Bool) : ZMod 2 := if b then 1 else 0

def flp (t : ℕ) : ℕ := if t % 2 = 1 then t - 1 else t + 1

lemma two_zero (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

lemma list_count (l : List ℕ) : ∀ s : Bool, l.Nodup → l ≠ [] →
    (l.map fun t => ind (altL s ((l.erase t).map par))).sum
      = ind (altL s (l.map par)) + ind (altL (!s) (l.map par)) := by
  induction l with
  | nil => intro s _ h; exact absurd rfl h
  | cons x xs ih =>
    intro s hnd _
    rw [List.nodup_cons] at hnd
    by_cases hxs : xs = []
    · subst hxs
      cases s <;> cases hx : par x <;> simp [altL, ind, hx]
    have htail : (xs.map fun t => ind (altL s (((x :: xs).erase t).map par)))
        = xs.map fun t => ind ((par x == s) && altL (!s) ((xs.erase t).map par)) := by
      apply List.map_congr_left
      intro t ht
      have hne : ¬ (x == t) = true := by
        intro h
        rw [beq_iff_eq] at h
        exact hnd.1 (h ▸ ht)
      rw [List.erase_cons_tail hne]
      simp [altL]
    rw [List.map_cons, List.sum_cons, List.erase_cons_head, htail]
    by_cases hx : par x = s
    · have h1 : (par x == s) = true := by simp [hx]
      have h2 : (par x == !s) = false := by rw [hx]; cases s <;> rfl
      simp only [h1, Bool.true_and, List.map_cons, altL, h2, Bool.false_and]
      rw [ih (!s) hnd.2 hxs, Bool.not_not]
      have h0 : ind false = 0 := rfl
      rw [h0, add_zero, add_comm (ind (altL (!s) (xs.map par))), ← add_assoc, two_zero, zero_add]
    · have h1 : (par x == s) = false := by simpa using hx
      have h2 : (par x == !s) = true := by
        revert hx; cases s <;> cases par x <;> simp
      simp only [h1, Bool.false_and, List.map_cons, altL, h2, Bool.true_and, Bool.not_not]
      have h0 : ind false = 0 := rfl
      simp [h0]

lemma sort_erase' (T : Finset ℕ) (a : ℕ) :
    (T.erase a).sort (· ≤ ·) = (T.sort (· ≤ ·)).erase a := by
  have hnd : (T.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; exact le_antisymm h1 h2
  · exact Finset.pairwise_sort _ _
  · exact (Finset.pairwise_sort T (· ≤ ·)).sublist List.erase_sublist
  · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (hnd.erase a)]
    intro b
    rw [hnd.mem_erase_iff]
    simp

def good {ι : Type} (s : Bool) (g : ι → ℕ) (J : Finset ι) : Bool :=
  decide ((J.image g).card = J.card) && altL s (((J.image g).sort (· ≤ ·)).map par)

lemma facet_count {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : ι → ℕ) (s : Bool) :
    ∑ j, ind (good s g (Finset.univ.erase j))
      = ind (good s g Finset.univ) + ind (good (!s) g Finset.univ) := by
  by_cases hg : Function.Injective g
  · set T := Finset.univ.image g with hT
    have hcard : ∀ J : Finset ι, (J.image g).card = J.card :=
      fun J => Finset.card_image_of_injective J hg
    have h1 : ∀ s' j, good s' g (Finset.univ.erase j)
        = altL s' (((T.sort (· ≤ ·)).erase (g j)).map par) := by
      intro s' j
      unfold good
      rw [decide_eq_true (hcard _), Bool.true_and, Finset.image_erase hg, ← hT, sort_erase']
    have h2 : ∀ s', good s' g Finset.univ = altL s' ((T.sort (· ≤ ·)).map par) := by
      intro s'
      unfold good
      rw [decide_eq_true (hcard _), Bool.true_and, ← hT]
    simp only [h1, h2]
    have h3 : ∑ j, ind (altL s (((T.sort (· ≤ ·)).erase (g j)).map par))
        = ∑ t ∈ T, ind (altL s (((T.sort (· ≤ ·)).erase t).map par)) := by
      rw [hT, Finset.sum_image (fun a _ b _ h => hg h)]
    have h4 : ∑ t ∈ T, ind (altL s (((T.sort (· ≤ ·)).erase t).map par))
        = ((T.sort (· ≤ ·)).map fun t => ind (altL s (((T.sort (· ≤ ·)).erase t).map par))).sum := by
      rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
    rw [h3, h4]
    apply list_count _ s (Finset.sort_nodup _ _)
    intro h
    have hne : T.Nonempty := Finset.univ_nonempty.image g
    obtain ⟨t, ht⟩ := hne
    have : t ∈ T.sort (· ≤ ·) := (Finset.mem_sort _).2 ht
    rw [h] at this
    exact absurd this List.not_mem_nil
  · have hu : ∀ s', good s' g Finset.univ = false := by
      intro s'
      unfold good
      have : ¬ (Finset.univ.image g).card = (Finset.univ : Finset ι).card := by
        intro h
        rw [Finset.card_image_iff] at h
        exact hg (fun a b hab => h (by simp) (by simp) hab)
      rw [decide_eq_false this, Bool.false_and]
    rw [hu, hu]
    unfold Function.Injective at hg
    push Not at hg
    obtain ⟨a, b, hab, hne⟩ := hg
    have hz : ∀ j, j ≠ a → j ≠ b → ind (good s g (Finset.univ.erase j)) = 0 := by
      intro j hja hjb
      have : ¬ ((Finset.univ.erase j).image g).card = (Finset.univ.erase j).card := by
        intro h
        rw [Finset.card_image_iff] at h
        exact hne (h (by simp [Ne.symm hja]) (by simp [Ne.symm hjb]) hab)
      unfold good
      rw [decide_eq_false this, Bool.false_and]
      rfl
    rw [Fintype.sum_eq_add a b hne (fun j hj => hz j hj.1 hj.2)]
    have himg : ∀ a b : ι, a ≠ b → g a = g b →
        (Finset.univ.erase a).image g = Finset.univ.image g := by
      intro a b hne hab
      apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
      intro t ht
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 ht
      by_cases hc : c = a
      · exact Finset.mem_image.2 ⟨b, by simp [Ne.symm hne], by rw [hc, hab]⟩
      · exact Finset.mem_image.2 ⟨c, by simp [hc], rfl⟩
    have he : good s g (Finset.univ.erase a) = good s g (Finset.univ.erase b) := by
      unfold good
      rw [himg a b hne hab, himg b a (Ne.symm hne) hab.symm,
        Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_erase_of_mem (Finset.mem_univ b)]
    rw [he, two_zero]
    simp [ind]

lemma altL_not (l : List Bool) : ∀ s, altL (!s) (l.map (!·)) = altL s l := by
  induction l with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    simp only [List.map_cons, altL, ih (!s)]
    cases x <;> cases s <;> rfl

lemma sort_flp (T : Finset ℕ) (h : ∀ a ∈ T, ∀ b ∈ T, a / 2 = b / 2 → a = b) :
    (T.image flp).sort (· ≤ ·) = (T.sort (· ≤ ·)).map flp := by
  have hinj : Function.Injective flp := by
    intro a b hab
    unfold flp at hab
    split_ifs at hab <;> omega
  have hnd : ((T.sort (· ≤ ·)).map flp).Nodup := (Finset.sort_nodup _ _).map hinj
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; exact le_antisymm h1 h2
  · exact Finset.pairwise_sort _ _
  · rw [List.pairwise_map]
    have hp : (T.sort (· ≤ ·)).Pairwise (fun a b => a ≤ b ∧ a ≠ b) :=
      (Finset.pairwise_sort T (· ≤ ·)).and (Finset.sort_nodup T (· ≤ ·))
    refine hp.imp_of_mem ?_
    intro a b ha hb hab
    rw [Finset.mem_sort] at ha hb
    have : a / 2 ≠ b / 2 := fun e => hab.2 (h a ha b hb e)
    have := hab.1
    unfold flp
    split_ifs <;> omega
  · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnd]
    intro b
    simp

lemma good_flp {ι : Type} (s : Bool) (g : ι → ℕ) (J : Finset ι)
    (h : ∀ i j, g i / 2 = g j / 2 → g i = g j) :
    good (!s) (fun i => flp (g i)) J = good s g J := by
  have hinj : Function.Injective flp := by
    intro a b hab
    unfold flp at hab
    split_ifs at hab <;> omega
  have himg : J.image (fun i => flp (g i)) = (J.image g).image flp := by
    rw [Finset.image_image]; rfl
  unfold good
  rw [himg, Finset.card_image_of_injective _ hinj, sort_flp, List.map_map]
  · have : (par ∘ flp) = ((!·) ∘ par) := by
      funext t
      unfold par flp
      simp only [Function.comp]
      by_cases ht : t % 2 = 1
      · have : ¬ (t - 1) % 2 = 1 := by omega
        simp [ht, this]
      · have : (t + 1) % 2 = 1 := by omega
        simp [ht, this]
    rw [this, ← List.map_map, altL_not]
  · intro a ha b hb e
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hb
    exact h i j e

/- Part 2: the octahedral Ky Fan lemma. -/

abbrev Facet (m : ℕ) := Equiv.Perm (Fin m) × (Fin m → Bool)

def V {m : ℕ} (σ : Facet m) (j : Fin m) : Finset (ℕ × Bool) :=
  (Finset.Iic j).image (fun t => ((σ.1 t).val, σ.2 (σ.1 t)))

def neg (X : Finset (ℕ × Bool)) : Finset (ℕ × Bool) := X.image (fun p => (p.1, !p.2))

def Valid (n : ℕ) (X : Finset (ℕ × Bool)) : Prop :=
  (∀ p ∈ X, p.1 < n) ∧ (∀ a ∈ X, ∀ b ∈ X, a.1 = b.1 → a = b)

lemma V_valid {m n : ℕ} (hmn : m ≤ n) (σ : Facet m) (j : Fin m) : Valid n (V σ j) := by
  constructor
  · intro p hp
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hp
    exact lt_of_lt_of_le (σ.1 t).isLt hmn
  · intro a ha b hb hab
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hb
    have : σ.1 t = σ.1 u := Fin.ext hab
    simp only [this]

lemma V_mono {m : ℕ} (σ : Facet m) {i j : Fin m} (h : i ≤ j) : V σ i ⊆ V σ j :=
  Finset.image_subset_image (Finset.Iic_subset_Iic.2 h)

lemma V_nonempty {m : ℕ} (σ : Facet m) (j : Fin m) : (V σ j).Nonempty :=
  Finset.Nonempty.image ⟨j, Finset.mem_Iic.2 le_rfl⟩ _

def extP {m : ℕ} (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr π (Equiv.refl (Fin 1)))).trans finSumFinEquiv

lemma extP_cast {m : ℕ} (π : Equiv.Perm (Fin m)) (i : Fin m) :
    extP π i.castSucc = (π i).castSucc := by
  have h : i.castSucc = Fin.castAdd 1 i := rfl
  rw [h]
  unfold extP
  simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_apply_left]
  rfl

lemma extP_last {m : ℕ} (π : Equiv.Perm (Fin m)) : extP π (Fin.last m) = Fin.last m := by
  have h : Fin.last m = Fin.natAdd m (0 : Fin 1) := by ext; simp
  rw [h]
  unfold extP
  simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
    Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]

def ext' {m : ℕ} (τ : Facet m) : Facet (m+1) := (extP τ.1, Fin.snoc τ.2 true)

lemma V_ext {m : ℕ} (τ : Facet m) (j : Fin m) : V (ext' τ) j.castSucc = V τ j := by
  unfold V
  rw [← Fin.map_castSuccEmb_Iic, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro t _
  simp [ext', extP_cast]

lemma good_ext {m : ℕ} (lab : Finset (ℕ × Bool) → ℕ) (τ : Facet m) :
    good true (fun j => lab (V (ext' τ) j)) (Finset.univ.erase (Fin.last m))
      = good true (fun j => lab (V τ j)) Finset.univ := by
  have h1 : (Finset.univ.erase (Fin.last m)) = Finset.univ.image Fin.castSucc := by
    ext i
    simp [Fin.exists_castSucc_eq]
  have h2 : (Finset.univ.erase (Fin.last m)).image (fun j => lab (V (ext' τ) j))
      = Finset.univ.image (fun j => lab (V τ j)) := by
    rw [h1, Finset.image_image]
    apply Finset.image_congr
    intro t _
    simp [V_ext]
  have h3 : (Finset.univ.erase (Fin.last m)).card = (Finset.univ : Finset (Fin m)).card := by
    simp
  unfold good
  rw [h2, h3]

def nb {m : ℕ} (p : Facet (m+1) × Fin (m+1)) : Facet (m+1) × Fin (m+1) :=
  if h : p.2.val < m then ((p.1.1 * Equiv.swap p.2 ⟨p.2.val+1, by omega⟩, p.1.2), p.2)
  else ((p.1.1, Function.update p.1.2 (p.1.1 p.2) (!p.1.2 (p.1.1 p.2))), p.2)

lemma nb_snd {m : ℕ} (p : Facet (m+1) × Fin (m+1)) : (nb p).2 = p.2 := by
  unfold nb; split_ifs <;> rfl

lemma nb_nb {m : ℕ} (p : Facet (m+1) × Fin (m+1)) : nb (nb p) = p := by
  obtain ⟨⟨π, ε⟩, j⟩ := p
  by_cases h : j.val < m
  · simp [nb, h, mul_assoc]
  · simp [nb, h]

lemma nb_ne {m : ℕ} (p : Facet (m+1) × Fin (m+1)) : nb p ≠ p := by
  obtain ⟨⟨π, ε⟩, j⟩ := p
  intro e
  by_cases h : j.val < m
  · simp only [nb, h, dif_pos, Prod.mk.injEq, and_true] at e
    have e2 := congrArg (fun q : Equiv.Perm (Fin (m+1)) => q j) e
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at e2
    have := congrArg Fin.val (π.injective e2)
    simp at this
  · simp only [nb, h, dif_neg, not_false_eq_true, Prod.mk.injEq, and_true, true_and] at e
    have := congrFun e (π j)
    simp at this

lemma nb_face {m : ℕ} (p : Facet (m+1) × Fin (m+1)) (k : Fin (m+1)) (hk : k ≠ p.2) :
    V (nb p).1 k = V p.1 k := by
  obtain ⟨⟨π, ε⟩, j⟩ := p
  simp only at hk
  have hk' : k.val ≠ j.val := fun e => hk (Fin.ext e)
  by_cases h : j.val < m
  · simp only [nb, h, dif_pos, V]
    set j' : Fin (m+1) := ⟨j.val+1, by omega⟩ with hj'
    have hmem : ∀ t, t ≤ k → Equiv.swap j j' t ≤ k := by
      intro t ht
      rw [Equiv.swap_apply_def]
      have ht' : t.val ≤ k.val := ht
      split_ifs with h1 h2
      · subst h1
        show t.val + 1 ≤ k.val
        omega
      · subst h2
        show j.val ≤ k.val
        have : j.val + 1 ≤ k.val := ht'
        omega
      · exact ht
    have himg : (Finset.Iic k).image (Equiv.swap j j') = Finset.Iic k := by
      ext y
      simp only [Finset.mem_image, Finset.mem_Iic]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hmem t ht
      · intro hy
        exact ⟨Equiv.swap j j' y, hmem y hy, Equiv.swap_apply_self _ _ _⟩
    conv_rhs => rw [← himg, Finset.image_image]
    apply Finset.image_congr
    intro t _
    simp [Equiv.Perm.mul_apply]
  · simp only [nb, h, dif_neg, not_false_eq_true, V]
    apply Finset.image_congr
    intro t ht
    have ht' : t.val ≤ k.val := by simpa using ht
    have htj : t ≠ j := by
      intro e
      subst e
      have := k.isLt
      omega
    have : π t ≠ π j := fun e => htj (π.injective e)
    simp [Function.update_of_ne this]

theorem kyfan (n : ℕ) (lab : Finset (ℕ × Bool) → ℕ)
    (hanti : ∀ X, Valid n X → X.Nonempty → lab (neg X) = flp (lab X))
    (hcomp : ∀ X Y, Valid n Y → X ⊆ Y → X.Nonempty → lab X / 2 = lab Y / 2 → lab X = lab Y) :
    ∀ m, m ≤ n → ∑ σ : Facet m, ind (good true (fun j => lab (V σ j)) Finset.univ) = 1 := by
  intro m
  induction m with
  | zero =>
    intro _
    have : ∀ σ : Facet 0, ind (good true (fun j => lab (V σ j)) Finset.univ) = 1 := by
      intro σ
      rw [Finset.univ_eq_empty]
      simp [good, altL, ind]
    rw [Finset.sum_congr rfl (fun σ _ => this σ)]
    simp [Fintype.card_perm]
  | succ m ih =>
    intro hmn
    have IH := ih (by omega)
    let g : Facet (m+1) → Fin (m+1) → ℕ := fun σ j => lab (V σ j)
    have hcompat : ∀ σ : Facet (m+1), ∀ i j, g σ i / 2 = g σ j / 2 → g σ i = g σ j := by
      intro σ i j e
      rcases le_total i j with h | h
      · exact hcomp _ _ (V_valid hmn σ j) (V_mono σ h) (V_nonempty σ i) e
      · exact (hcomp _ _ (V_valid hmn σ i) (V_mono σ h) (V_nonempty σ j) e.symm).symm
    let H : Finset (Facet (m+1)) := Finset.univ.filter (fun σ => σ.2 (Fin.last m) = true)
    let F : Facet (m+1) × Fin (m+1) → ZMod 2 :=
      fun p => ind (good true (g p.1) (Finset.univ.erase p.2))
    let P : Finset (Facet (m+1) × Fin (m+1)) := H ×ˢ Finset.univ
    let Q : Facet (m+1) × Fin (m+1) → Prop :=
      fun p => p.2 = Fin.last m ∧ p.1.1 (Fin.last m) = Fin.last m
    have htot : ∑ p ∈ P, F p
        = ∑ σ ∈ H, (ind (good true (g σ) Finset.univ) + ind (good false (g σ) Finset.univ)) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro σ _
      exact facet_count (g σ) true
    have hrest : ∑ p ∈ P.filter (fun p => ¬ Q p), F p = 0 := by
      refine Finset.sum_involution (fun p _ => nb p) ?_ (fun p _ _ => nb_ne p) ?_
        (fun p _ => nb_nb p)
      · intro p _
        have : F (nb p) = F p := by
          have himg : (Finset.univ.erase p.2).image (g (nb p).1)
              = (Finset.univ.erase p.2).image (g p.1) := by
            apply Finset.image_congr
            intro k hk
            have hk' : k ≠ p.2 := by simpa using hk
            show lab _ = lab _
            rw [nb_face p k hk']
          show ind (good true (g (nb p).1) (Finset.univ.erase (nb p).2)) = _
          rw [nb_snd]
          unfold good
          rw [himg]
          simp only [F, good]
        rw [this, two_zero]
      · intro p hp
        simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_univ, and_true, H,
          true_and] at hp ⊢
        obtain ⟨⟨π, ε⟩, j⟩ := p
        by_cases h : j.val < m
        · have hj : j ≠ Fin.last m := by
            intro e; rw [e] at h; simp at h
          simp only [nb, h, dif_pos]
          exact ⟨hp.1, fun q => hj q.1⟩
        · have hj : j = Fin.last m := by
            apply Fin.ext
            have := j.isLt
            simp only [Fin.val_last]
            omega
          have hπ : π j ≠ Fin.last m := by
            intro e
            exact hp.2 ⟨hj, by rw [← hj]; simpa [hj] using e⟩
          simp only [nb, h, dif_neg, not_false_eq_true]
          refine ⟨?_, hp.2⟩
          rw [Function.update_of_ne (Ne.symm hπ)]
          exact hp.1
    have hbd : ∑ p ∈ P.filter Q, F p = 1 := by
      rw [← IH]
      symm
      refine Finset.sum_bij (fun τ _ => (ext' τ, Fin.last m)) ?_ ?_ ?_ ?_
      · intro τ _
        simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_univ, and_true, H,
          true_and, Q]
        exact ⟨by simp [ext'], by simp [ext', extP_last]⟩
      · intro τ _ τ' _ e
        have e1 : ext' τ = ext' τ' := (Prod.mk.inj e).1
        obtain ⟨e2, e3⟩ := Prod.mk.inj e1
        apply Prod.ext
        · apply Equiv.ext
          intro i
          have := congrArg (fun q : Equiv.Perm (Fin (m+1)) => q i.castSucc) e2
          simp only [extP_cast] at this
          exact Fin.castSucc_injective _ this
        · funext i
          have := congrFun e3 i.castSucc
          simpa using this
      · intro p hp
        simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_univ, and_true, H,
          true_and, Q] at hp
        obtain ⟨⟨π, ε⟩, j⟩ := p
        obtain ⟨hε, hj, hπ⟩ := hp
        simp only at hε hj hπ
        have hne : ∀ i : Fin m, π i.castSucc ≠ Fin.last m := by
          intro i e
          exact Fin.castSucc_ne_last i (π.injective (e.trans hπ.symm))
        let f : Fin m → Fin m := fun i => (π i.castSucc).castPred (hne i)
        have hf : Function.Injective f := by
          intro a b e
          have := congrArg Fin.castSucc e
          simp only [f, Fin.castSucc_castPred] at this
          exact Fin.castSucc_injective _ (π.injective this)
        let π' : Equiv.Perm (Fin m) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
        refine ⟨(π', fun i => ε i.castSucc), Finset.mem_univ _, ?_⟩
        have h1 : extP π' = π := by
          apply Equiv.ext
          intro i
          induction i using Fin.lastCases with
          | last => rw [extP_last, hπ]
          | cast i =>
            rw [extP_cast]
            show (f i).castSucc = _
            simp [f]
        have h2 : (Fin.snoc (fun i : Fin m => ε i.castSucc) true : Fin (m+1) → Bool) = ε := by
          funext i
          induction i using Fin.lastCases with
          | last => rw [Fin.snoc_last, hε]
          | cast i => rw [Fin.snoc_castSucc]
        simp only [ext', h1, h2, hj]
      · intro τ _
        show _ = ind (good true (g (ext' τ)) (Finset.univ.erase (Fin.last m)))
        rw [good_ext lab τ]
    have hH : ∑ σ ∈ H, (ind (good true (g σ) Finset.univ) + ind (good false (g σ) Finset.univ))
        = 1 := by
      rw [← htot, ← Finset.sum_filter_add_sum_filter_not P Q, hbd, hrest, add_zero]
    have hneg : ∑ σ ∈ H, ind (good false (g σ) Finset.univ)
        = ∑ σ ∈ Finset.univ.filter (fun σ : Facet (m+1) => ¬ σ.2 (Fin.last m) = true),
            ind (good true (g σ) Finset.univ) := by
      refine Finset.sum_nbij' (fun σ => (σ.1, fun i => !σ.2 i)) (fun σ => (σ.1, fun i => !σ.2 i))
        ?_ ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [H, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          Finset.mem_filter] at hσ ⊢
        simp [hσ]
      · intro σ hσ
        simp only [H, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          Finset.mem_filter] at hσ ⊢
        simpa using hσ
      · intro σ _; simp
      · intro σ _; simp
      · intro σ _
        have hg : g (σ.1, fun i => !σ.2 i) = fun j => flp (g σ j) := by
          funext j
          have hV : V (σ.1, fun i => !σ.2 i) j = neg (V σ j) := by
            unfold V neg
            rw [Finset.image_image]
            rfl
          show lab _ = flp (lab _)
          rw [hV]
          exact hanti _ (V_valid hmn σ j) (V_nonempty σ j)
        rw [hg]
        have := good_flp false (g σ) Finset.univ (hcompat σ)
        simp only [Bool.not_false] at this
        rw [this]
    show ∑ σ : Facet (m+1), ind (good true (g σ) Finset.univ) = 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Facet (m+1) => σ.2 (Fin.last m) = true)]
    rw [← hneg, ← Finset.sum_add_distrib]
    exact hH

/- Part 3: fits and falls. -/

lemma tel : ∀ (l : ℕ) (t : Fin l → ℕ) (u : Fin (l+1) → ℕ),
    (∀ i, t i + u i.castSucc ≤ u i.succ) → ∑ i, t i + u 0 ≤ u (Fin.last l) := by
  intro l
  induction l with
  | zero => intro t u _; simp
  | succ l ih =>
    intro t u h
    have h1 := ih (fun i => t i.succ) (fun i => u i.succ) (fun i => by
      have := h i.succ
      rwa [← Fin.succ_castSucc] at this)
    have h0 := h 0
    simp only [Fin.castSucc_zero] at h0
    rw [Fin.sum_univ_succ, ← Fin.succ_last]
    omega

section
variable {K : Type} [Fintype K]

def Bd (f : Finset K → K → ℕ) (x : Finset K) (B : ℕ) : Prop :=
  ∀ (l : ℕ) (p : Fin (l+1) → Finset K) (a : Fin l → K),
    (∀ i : Fin l, p i.castSucc ⊆ p i.succ) → p (Fin.last l) ⊆ x →
    ∑ i : Fin l, (f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B

variable (f : Finset K → K → ℕ) (h1 : ∀ x j, f x j ≤ 1)
  (hm : ∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)

include h1 hm in
lemma Bd_exists (x : Finset K) : ∃ B, Bd f x B := by
  classical
  refine ⟨∑ _a : K, 1, ?_⟩
  intro l p a hp _
  have h := tel l (fun i => f (p i.castSucc) (a i) - f (p i.succ) (a i))
    (fun i => ∑ b : K, (1 - f (p i) b)) (fun i => by
      have e : f (p i.castSucc) (a i) - f (p i.succ) (a i)
          = ∑ b : K, (if b = a i then f (p i.castSucc) b - f (p i.succ) b else 0) := by
        rw [Finset.sum_ite_eq' Finset.univ (a i)]
        simp
      rw [e, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      have := h1 (p i.castSucc) b
      have := h1 (p i.succ) b
      have := hm _ _ (hp i) b
      split_ifs <;> omega)
  have h2 : ∑ b : K, (1 - f (p (Fin.last l)) b) ≤ ∑ _a : K, 1 :=
    Finset.sum_le_sum (fun b _ => Nat.sub_le _ _)
  omega

open Classical in
noncomputable def Nf (x : Finset K) : ℕ :=
  if h : ∃ B, Bd f x B then Nat.find h else 0

include h1 hm in
lemma Nf_spec (x : Finset K) : Bd f x (Nf f x) := by
  classical
  have h := Bd_exists f h1 hm x
  unfold Nf
  rw [dif_pos h]
  exact Nat.find_spec h

lemma Nf_le (x : Finset K) (B : ℕ) (hB : Bd f x B) : Nf f x ≤ B := by
  classical
  unfold Nf
  rw [dif_pos ⟨B, hB⟩]
  exact Nat.find_min' _ hB

include h1 hm in
lemma Nf_mono {x y : Finset K} (h : x ⊆ y) : Nf f x ≤ Nf f y :=
  Nf_le f x _ (fun l p a hp hl => Nf_spec f h1 hm y l p a hp (hl.trans h))

include h1 hm in
lemma Nf_step {x y : Finset K} (h : x ⊆ y) (b : K) (hx : f x b = 1) (hy : f y b = 0) :
    Nf f x + 1 ≤ Nf f y := by
  have key : ∀ (l : ℕ) (p : Fin (l+1) → Finset K) (a : Fin l → K),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) → p (Fin.last l) ⊆ x →
      ∑ i : Fin l, (f (p i.castSucc) (a i) - f (p i.succ) (a i)) + 1 ≤ Nf f y := by
    intro l p a hp hl
    let p1 : Fin (l+2) → Finset K := Fin.snoc p x
    let p2 : Fin (l+3) → Finset K := Fin.snoc p1 y
    let a1 : Fin (l+1) → K := Fin.snoc a b
    let a2 : Fin (l+2) → K := Fin.snoc a1 b
    have hstep : ∀ i : Fin (l+2), p2 i.castSucc ⊆ p2 i.succ := by
      intro i
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last]
        simp only [p2, Fin.snoc_castSucc, Fin.snoc_last]
        have : p1 (Fin.last (l+1)) = x := by simp [p1]
        rw [this]
        exact h
      | cast i =>
        rw [Fin.succ_castSucc]
        simp only [p2, Fin.snoc_castSucc]
        induction i using Fin.lastCases with
        | last =>
          rw [Fin.succ_last]
          simp only [p1, Fin.snoc_castSucc, Fin.snoc_last]
          exact hl
        | cast i =>
          rw [Fin.succ_castSucc]
          simp only [p1, Fin.snoc_castSucc]
          exact hp i
    have hlast : p2 (Fin.last (l+2)) ⊆ y := by simp [p2]
    have hb := Nf_spec f h1 hm y (l+2) p2 a2 hstep hlast
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hb
    have e1 : ∀ i : Fin l, f (p2 i.castSucc.castSucc.castSucc) (a2 i.castSucc.castSucc)
          - f (p2 i.castSucc.castSucc.succ) (a2 i.castSucc.castSucc)
        = f (p i.castSucc) (a i) - f (p i.succ) (a i) := by
      intro i
      simp only [Fin.succ_castSucc, p2, p1, a2, a1, Fin.snoc_castSucc]
    have e3 : f (p2 (Fin.last (l+1)).castSucc) (a2 (Fin.last (l+1)))
          - f (p2 (Fin.last (l+1)).succ) (a2 (Fin.last (l+1))) = 1 := by
      have u1 : p2 (Fin.last (l+1)).castSucc = x := by
        simp only [p2, Fin.snoc_castSucc]
        simp [p1]
      have u2 : p2 (Fin.last (l+1)).succ = y := by
        rw [Fin.succ_last]; simp [p2]
      have u3 : a2 (Fin.last (l+1)) = b := by simp [a2]
      rw [u1, u2, u3, hx, hy]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), e3] at hb
    omega
  have h2 : 1 ≤ Nf f y := by
    have := key 0 (fun _ => ∅) Fin.elim0 (fun i => i.elim0) (Finset.empty_subset _)
    omega
  have h3 : Nf f x ≤ Nf f y - 1 := by
    apply Nf_le
    intro l p a hp hl
    have := key l p a hp hl
    omega
  omega

lemma Nf_empty : Nf f ∅ = 0 := by
  apply Nat.le_zero.1
  apply Nf_le
  intro l p a hp hl
  have he : ∀ i, p i = ∅ := by
    intro i
    have hmono : Monotone p := Fin.monotone_iff_le_succ.2 hp
    exact Finset.subset_empty.1 ((hmono (Fin.le_last i)).trans hl)
  simp [he]

end

/- Part 4: the two shores. -/

section
variable (k d : ℕ)

abbrev Key := {s : Finset (Fin d) // s.card = k}

def pos (s : Bool) (X : Finset (ℕ × Bool)) : Finset (Fin d) :=
  Finset.univ.filter (fun i => (i.val, s) ∈ X)

def Cl (A : Finset (Fin d)) : Finset (Key k d) := Finset.univ.filter (fun a => a.val ⊆ A)

variable (f : Finset (Key k d) → Key k d → ℕ)

noncomputable def NS (s : Bool) (X : Finset (ℕ × Bool)) : ℕ := Nf f (Cl k d (pos d s X))

noncomputable def code (s : Bool) (X : Finset (ℕ × Bool)) : ℕ :=
  (Fintype.equivFin (Finset (Key k d))
    (Finset.univ.filter (fun a => f (Cl k d (pos d s X)) a = 0))).val

def sg1 (X : Finset (ℕ × Bool)) : Bool :=
  if h : (X.image Prod.fst).Nonempty then decide (((X.image Prod.fst).min' h, true) ∈ X) else false

noncomputable def sg (X : Finset (ℕ × Bool)) : Bool :=
  if X.card ≤ 2*k-2 then sg1 X
  else if NS k d f false X < NS k d f true X then true
  else if NS k d f true X < NS k d f false X then false
  else decide (code k d f false X < code k d f true X)

noncomputable def mag (X : Finset (ℕ × Bool)) : ℕ :=
  if X.card ≤ 2*k-2 then X.card else 2*k-2 + NS k d f true X + NS k d f false X

noncomputable def lab (X : Finset (ℕ × Bool)) : ℕ :=
  2 * mag k d f X + (if sg k d f X then 1 else 0)

lemma lab_half (X : Finset (ℕ × Bool)) : lab k d f X / 2 = mag k d f X := by
  unfold lab; split_ifs <;> omega

lemma lab_par (X : Finset (ℕ × Bool)) : par (lab k d f X) = sg k d f X := by
  unfold par lab
  cases sg k d f X
  · simp
  · simp [Nat.add_mod]

lemma mem_neg (X : Finset (ℕ × Bool)) (i : ℕ) (s : Bool) : (i, s) ∈ neg X ↔ (i, !s) ∈ X := by
  unfold neg
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, h, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    simpa using h
  · intro h
    exact ⟨_, h, by simp⟩

lemma pos_neg (X : Finset (ℕ × Bool)) (s : Bool) : pos d s (neg X) = pos d (!s) X := by
  ext i
  simp [pos, mem_neg]

lemma card_neg (X : Finset (ℕ × Bool)) : (neg X).card = X.card := by
  apply Finset.card_image_of_injective
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have : b = e := by simpa using congrArg (!·) h2
  simp only at h1
  rw [h1, this]

lemma pos_mono {X Y : Finset (ℕ × Bool)} (h : X ⊆ Y) (s : Bool) : pos d s X ⊆ pos d s Y := by
  intro i hi
  simp only [pos, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h hi

lemma Cl_mono {A B : Finset (Fin d)} (h : A ⊆ B) : Cl k d A ⊆ Cl k d B := by
  intro a ha
  simp only [Cl, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.trans h

lemma pos_disj {n : ℕ} (X : Finset (ℕ × Bool)) (hX : Valid n X) :
    Disjoint (pos d true X) (pos d false X) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  simp only [pos, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  have := hX.2 _ h1 _ h2 rfl
  simp at this

lemma card_le_pos (X : Finset (ℕ × Bool)) (hX : Valid d X) :
    X.card ≤ (pos d true X).card + (pos d false X).card := by
  have : X ⊆ (pos d true X).image (fun i => (i.val, true))
      ∪ (pos d false X).image (fun i => (i.val, false)) := by
    rintro ⟨a, b⟩ h
    have ha : a < d := hX.1 _ h
    rw [Finset.mem_union]
    cases b
    · right
      exact Finset.mem_image.2 ⟨⟨a, ha⟩, by simp [pos, h], rfl⟩
    · left
      exact Finset.mem_image.2 ⟨⟨a, ha⟩, by simp [pos, h], rfl⟩
  exact (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le))

variable (h1 : ∀ x j, f x j ≤ 1)
  (hdis : ∀ (x : Finset (Key k d)) j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = 1)
  (hin : ∀ (x : Finset (Key k d)) j, j ∈ x → f x j = 0)
  (hm : ∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)

include h1 hdis hin hm in
lemma Nf_pos (x : Finset (Key k d)) (hx : x.Nonempty) : 1 ≤ Nf f x := by
  obtain ⟨a, ha⟩ := hx
  have := Nf_step f h1 hm (Finset.empty_subset x) a (hdis ∅ a (by simp)) (hin x a ha)
  omega

include h1 hdis hin hm in
lemma NS_pos (hk : 0 < k) (X : Finset (ℕ × Bool)) (hX : Valid d X) (hc : ¬ X.card ≤ 2*k-2) :
    1 ≤ NS k d f true X + NS k d f false X := by
  have := card_le_pos d X hX
  have hs : ∀ s, k ≤ (pos d s X).card → 1 ≤ NS k d f s X := by
    intro s hs
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hs
    apply Nf_pos k d f h1 hdis hin hm
    exact ⟨⟨t, htc⟩, by simp [Cl, ht]⟩
  by_cases h : k ≤ (pos d true X).card
  · have := hs true h; omega
  · have := hs false (by omega); omega

include h1 hdis hin hm in
lemma code_ne (hk : 0 < k) (X : Finset (ℕ × Bool)) (hX : Valid d X) (hc : ¬ X.card ≤ 2*k-2)
    (he : NS k d f true X = NS k d f false X) : code k d f false X ≠ code k d f true X := by
  intro e
  have hs := NS_pos k d f h1 hdis hin hm hk X hX hc
  have hne : ∀ s, 1 ≤ NS k d f s X → (Cl k d (pos d s X)).Nonempty := by
    intro s h
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    unfold NS at h
    rw [h0, Nf_empty] at h
    omega
  obtain ⟨a, ha⟩ := hne true (by omega)
  have e' := (Fintype.equivFin (Finset (Key k d))).injective (Fin.ext e)
  have ha1 : a ∈ Finset.univ.filter (fun a => f (Cl k d (pos d true X)) a = 0) := by
    simp [hin _ a ha]
  rw [← e'] at ha1
  have ha2 : f (Cl k d (pos d false X)) a = 0 := (Finset.mem_filter.1 ha1).2
  have ha3 : f (Cl k d (pos d false X)) a = 1 := by
    apply hdis
    intro i hi
    simp only [Cl, Finset.mem_filter, Finset.mem_univ, true_and] at hi ha
    exact ((pos_disj d X hX).symm.mono hi ha)
  omega

include h1 hdis hin hm in
lemma lab_anti (hk : 0 < k) (X : Finset (ℕ × Bool)) (hX : Valid d X) (hne : X.Nonempty) :
    lab k d f (neg X) = flp (lab k d f X) := by
  have hN : ∀ s, NS k d f s (neg X) = NS k d f (!s) X := by
    intro s; unfold NS; rw [pos_neg]
  have hC : ∀ s, code k d f s (neg X) = code k d f (!s) X := by
    intro s; unfold code; rw [pos_neg]
  have hmag : mag k d f (neg X) = mag k d f X := by
    unfold mag
    rw [card_neg, hN, hN]
    simp only [Bool.not_true, Bool.not_false]
    split_ifs <;> omega
  have hsg : sg k d f (neg X) = !sg k d f X := by
    unfold sg
    rw [card_neg, hN, hN, hC, hC]
    simp only [Bool.not_true, Bool.not_false]
    by_cases hc : X.card ≤ 2*k-2
    · rw [if_pos hc, if_pos hc]
      unfold sg1
      have hfst : (neg X).image Prod.fst = X.image Prod.fst := by
        unfold neg; rw [Finset.image_image]; rfl
      have hfne : (X.image Prod.fst).Nonempty := hne.image _
      simp only [hfst, dif_pos hfne, mem_neg, Bool.not_true]
      obtain ⟨⟨a, b⟩, hab, e⟩ := Finset.mem_image.1 (Finset.min'_mem _ hfne)
      simp only at e
      rw [e] at hab
      cases b
      · have : ((X.image Prod.fst).min' hfne, true) ∉ X := by
          intro h
          have := hX.2 _ h _ hab rfl
          simp at this
        simp [this, hab]
      · have : ((X.image Prod.fst).min' hfne, false) ∉ X := by
          intro h
          have := hX.2 _ h _ hab rfl
          simp at this
        simp [this, hab]
    · rw [if_neg hc, if_neg hc]
      rcases lt_trichotomy (NS k d f true X) (NS k d f false X) with h | h | h
      · have h' : ¬ NS k d f false X < NS k d f true X := by omega
        simp [h, h']
      · have hcn := code_ne k d f h1 hdis hin hm hk X hX hc h
        simp only [h, lt_irrefl, if_false]
        rcases lt_or_gt_of_ne hcn with q | q
        · have q' : ¬ code k d f true X < code k d f false X := by omega
          simp [q, q']
        · have q' : ¬ code k d f false X < code k d f true X := by omega
          simp [q, q']
      · have h' : ¬ NS k d f true X < NS k d f false X := by omega
        simp [h, h']
  unfold lab flp
  rw [hmag, hsg]
  cases sg k d f X
  · have e : (2 * mag k d f X) % 2 = 0 := by omega
    simp [e]
  · have e : (2 * mag k d f X + 1) % 2 = 1 := by omega
    simp [e]

include h1 hm in
lemma NS_mono {X Y : Finset (ℕ × Bool)} (h : X ⊆ Y) (s : Bool) :
    NS k d f s X ≤ NS k d f s Y :=
  Nf_mono f h1 hm (Cl_mono k d (pos_mono d h s))

include h1 hm in
lemma code_eq {X Y : Finset (ℕ × Bool)} (h : X ⊆ Y) (s : Bool)
    (e : NS k d f s X = NS k d f s Y) : code k d f s X = code k d f s Y := by
  have hsub := Cl_mono k d (pos_mono d h s)
  have : (Finset.univ.filter (fun a => f (Cl k d (pos d s X)) a = 0))
      = (Finset.univ.filter (fun a => f (Cl k d (pos d s Y)) a = 0)) := by
    apply Finset.filter_congr
    intro a _
    have hle := hm _ _ hsub a
    constructor
    · intro h0; omega
    · intro h0
      by_contra hne
      have := h1 (Cl k d (pos d s X)) a
      have := Nf_step f h1 hm hsub a (by omega) h0
      unfold NS at e
      omega
  unfold code
  rw [this]

include h1 hdis hin hm in
lemma lab_comp (hk : 0 < k) (X Y : Finset (ℕ × Bool)) (hY : Valid d Y) (h : X ⊆ Y)
    (e : lab k d f X / 2 = lab k d f Y / 2) : lab k d f X = lab k d f Y := by
  rw [lab_half, lab_half] at e
  have hcard := Finset.card_le_card h
  by_cases hc : Y.card ≤ 2*k-2
  · have hcX : X.card ≤ 2*k-2 := hcard.trans hc
    unfold mag at e
    rw [if_pos hc, if_pos hcX] at e
    have : X = Y := Finset.eq_of_subset_of_card_le h e.ge
    rw [this]
  · have hpos := NS_pos k d f h1 hdis hin hm hk Y hY hc
    have hcX : ¬ X.card ≤ 2*k-2 := by
      intro hcX
      unfold mag at e
      rw [if_neg hc, if_pos hcX] at e
      omega
    have e' := e
    unfold mag at e'
    rw [if_neg hc, if_neg hcX] at e'
    have m1 := NS_mono k d f h1 hm h true
    have m2 := NS_mono k d f h1 hm h false
    have q1 : NS k d f true X = NS k d f true Y := by omega
    have q2 : NS k d f false X = NS k d f false Y := by omega
    have c1 := code_eq k d f h1 hm h true q1
    have c2 := code_eq k d f h1 hm h false q2
    have s : sg k d f X = sg k d f Y := by
      unfold sg
      rw [if_neg hc, if_neg hcX, q1, q2, c1, c2]
    unfold lab
    rw [e, s]

lemma altL_adj (l : List Bool) : ∀ s, altL s l = true → ∀ i (h : i + 1 < l.length),
    l[i]'(by omega) ≠ l[i+1] := by
  induction l with
  | nil => intro s _ i h; simp at h
  | cons x xs ih =>
    intro s ha i h
    simp only [altL, Bool.and_eq_true, beq_iff_eq] at ha
    cases i with
    | zero =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp only [altL, Bool.and_eq_true, beq_iff_eq] at ha
        simp only [List.getElem_cons_zero, zero_add, List.getElem_cons_succ]
        rw [ha.1, ha.2.1]
        cases s <;> simp
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact ih (!s) ha.2 i (by simpa using h)

include h1 hdis hin hm in
theorem two_shores (h : ℕ) (hk : 0 < k) (hd : d = 2*k+2*h) :
    ∃ A B : Finset (Fin d), Disjoint A B ∧ h+1 ≤ Nf f (Cl k d A) ∧ h+1 ≤ Nf f (Cl k d B) := by
  have hky := kyfan d (lab k d f)
    (fun X hX hne => lab_anti k d f h1 hdis hin hm hk X hX hne)
    (fun X Y hY hXY _ e => lab_comp k d f h1 hdis hin hm hk X Y hY hXY e) d le_rfl
  have hex : ∃ σ : Facet d, good true (fun j => lab k d f (V σ j)) Finset.univ = true := by
    by_contra hno
    push Not at hno
    have : ∑ σ : Facet d, ind (good true (fun j => lab k d f (V σ j)) Finset.univ) = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      simp [ind, hno σ]
    rw [this] at hky
    exact zero_ne_one hky
  obtain ⟨σ, hσ⟩ := hex
  set g : Fin d → ℕ := fun j => lab k d f (V σ j) with hg
  unfold good at hσ
  rw [Bool.and_eq_true, decide_eq_true_eq] at hσ
  obtain ⟨hcard, halt⟩ := hσ
  set T := Finset.univ.image g with hT
  set l := T.sort (· ≤ ·) with hl
  have hlen : l.length = d := by
    rw [hl, Finset.length_sort, hcard]
    simp
  have hmem : ∀ i (hi : i < l.length), ∃ j, g j = l[i] := by
    intro i hi
    have : l[i] ∈ T := (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
    obtain ⟨j, _, e⟩ := Finset.mem_image.1 this
    exact ⟨j, e⟩
  have hcompat : ∀ i j, g i / 2 = g j / 2 → g i = g j := by
    intro i j e
    rcases le_total i j with q | q
    · exact lab_comp k d f h1 hdis hin hm hk _ _ (V_valid le_rfl σ j) (V_mono σ q) e
    · exact (lab_comp k d f h1 hdis hin hm hk _ _ (V_valid le_rfl σ i) (V_mono σ q) e.symm).symm
  have hstrict : ∀ i (hi : i + 1 < l.length), l[i]'(by omega) / 2 < l[i+1] / 2 := by
    intro i hi
    have hle : l[i]'(by omega) ≤ l[i+1] :=
      List.pairwise_iff_getElem.1 (Finset.pairwise_sort T (· ≤ ·)) i (i+1)
        (Nat.lt_of_succ_lt hi) hi (Nat.lt_succ_self i)
    have hne : l[i]'(by omega) ≠ l[i+1] := by
      intro e
      have := ((Finset.sort_nodup T (· ≤ ·)).getElem_inj_iff
        (i := i) (j := i+1) (hi := by rw [← hl]; omega) (hj := by rw [← hl]; omega)).1 e
      omega
    obtain ⟨a, ha⟩ := hmem i (by omega)
    obtain ⟨b, hb⟩ := hmem (i+1) hi
    have : l[i]'(by omega) / 2 ≠ l[i+1] / 2 := by
      intro e
      rw [← ha, ← hb] at e
      exact hne (by rw [← ha, ← hb]; exact hcompat a b e)
    omega
  have hmag1 : ∀ j, 1 ≤ g j / 2 := by
    intro j
    show 1 ≤ lab k d f (V σ j) / 2
    rw [lab_half]
    unfold mag
    split_ifs with hc
    · exact (V_nonempty σ j).card_pos
    · have := NS_pos k d f h1 hdis hin hm hk _ (V_valid le_rfl σ j) hc
      omega
  have hlow : ∀ i (hi : i < l.length), i + 1 ≤ l[i] / 2 := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨a, ha⟩ := hmem 0 hi
      rw [← ha]; exact hmag1 a
    | succ i ih =>
      intro hi
      have := ih (by omega)
      have := hstrict i hi
      omega
  have hd2 : 2 ≤ d := by omega
  have hi1 : d - 2 + 1 < l.length := by omega
  obtain ⟨j1, e1⟩ := hmem (d-2) (by omega)
  obtain ⟨j2, e2⟩ := hmem (d-2+1) hi1
  have hlt : g j1 / 2 < g j2 / 2 := by
    rw [e1, e2]; exact hstrict (d-2) hi1
  have hsign : par (g j1) ≠ par (g j2) := by
    have := altL_adj (l.map par) true halt (d-2) (by simpa using hi1)
    rw [List.getElem_map, List.getElem_map] at this
    rw [e1, e2]
    exact this
  have hbig : d - 1 ≤ g j1 / 2 := by
    have := hlow (d-2) (by omega)
    rw [e1]; omega
  set Y1 := V σ j1 with hY1
  set Y2 := V σ j2 with hY2
  have g1 : g j1 = lab k d f Y1 := rfl
  have g2 : g j2 = lab k d f Y2 := rfl
  rw [g1, g2, lab_half, lab_half] at hlt
  rw [g1, g2, lab_par, lab_par] at hsign
  rw [g1, lab_half] at hbig
  have hsub : Y1 ⊆ Y2 := by
    rcases le_total j1 j2 with q | q
    · exact V_mono σ q
    · exfalso
      have hsub' : Y2 ⊆ Y1 := V_mono σ q
      have hv : Valid d Y1 := V_valid le_rfl σ j1
      have : mag k d f Y2 ≤ mag k d f Y1 := by
        unfold mag
        have hc := Finset.card_le_card hsub'
        have m1 := NS_mono k d f h1 hm hsub' true
        have m2 := NS_mono k d f h1 hm hsub' false
        split_ifs with a b b
        · exact hc
        · have := NS_pos k d f h1 hdis hin hm hk Y1 hv b
          omega
        · omega
        · omega
      omega
  have hc1 : ¬ Y1.card ≤ 2*k-2 := by
    intro hc
    unfold mag at hbig
    rw [if_pos hc] at hbig
    omega
  have hc2 : ¬ Y2.card ≤ 2*k-2 := fun hc => hc1 ((Finset.card_le_card hsub).trans hc)
  have hsum : 2*h+1 ≤ NS k d f true Y1 + NS k d f false Y1 := by
    unfold mag at hbig
    rw [if_neg hc1] at hbig
    omega
  have hsgT : ∀ Y : Finset (ℕ × Bool), ¬ Y.card ≤ 2*k-2 → sg k d f Y = true →
      NS k d f false Y ≤ NS k d f true Y := by
    intro Y hc hs
    by_contra hcon
    unfold sg at hs
    have a : ¬ NS k d f false Y < NS k d f true Y := by omega
    have b : NS k d f true Y < NS k d f false Y := by omega
    rw [if_neg hc, if_neg a, if_pos b] at hs
    exact Bool.false_ne_true hs
  have hsgF : ∀ Y : Finset (ℕ × Bool), ¬ Y.card ≤ 2*k-2 → sg k d f Y = false →
      NS k d f true Y ≤ NS k d f false Y := by
    intro Y hc hs
    by_contra hcon
    unfold sg at hs
    have a : NS k d f false Y < NS k d f true Y := by omega
    rw [if_neg hc, if_pos a] at hs
    exact Bool.false_ne_true hs.symm
  have m1 := NS_mono k d f h1 hm hsub true
  have m2 := NS_mono k d f h1 hm hsub false
  have hfin : h+1 ≤ NS k d f true Y2 ∧ h+1 ≤ NS k d f false Y2 := by
    cases s1 : sg k d f Y1
    · have s2 : sg k d f Y2 = true := by
        cases s2 : sg k d f Y2
        · exact absurd (s1.trans s2.symm) hsign
        · rfl
      have a := hsgF Y1 hc1 s1
      have b := hsgT Y2 hc2 s2
      omega
    · have s2 : sg k d f Y2 = false := by
        cases s2 : sg k d f Y2
        · rfl
        · exact absurd (s1.trans s2.symm) hsign
      have a := hsgT Y1 hc1 s1
      have b := hsgF Y2 hc2 s2
      omega
  exact ⟨pos d true Y2, pos d false Y2, pos_disj d Y2 (V_valid le_rfl σ j2), hfin.1, hfin.2⟩

end

/- Part 5: the fractional fit. -/

lemma frac_bound {k d : ℕ} (G : Finset (Key k d) → Finset (Fin d))
    (hG : ∀ x i, i ∈ G x ↔ ∃ a ∈ x, i ∈ a.val)
    (F : Finset (Key k d) → Key k d → ℕ)
    (hF : ∀ x j, F x j = (j.val \ G x).card)
    (x : Finset (Key k d)) : Bd F x (G x).card := by
  intro l p a hp hl
  have hmono : ∀ y z : Finset (Key k d), y ⊆ z → G y ⊆ G z := by
    intro y z h i hi
    rw [hG] at hi ⊢
    obtain ⟨b, hb, hib⟩ := hi
    exact ⟨b, h hb, hib⟩
  have h := tel l (fun i => F (p i.castSucc) (a i) - F (p i.succ) (a i))
    (fun i => (G (p i)).card) (fun i => by
      have hs := hmono _ _ (hp i)
      have h1 : (a i).val \ G (p i.castSucc)
          ⊆ ((a i).val \ G (p i.succ)) ∪ (G (p i.succ) \ G (p i.castSucc)) := by
        intro t ht
        rw [Finset.mem_sdiff] at ht
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
        by_cases q : t ∈ G (p i.succ)
        · exact Or.inr ⟨q, ht.2⟩
        · exact Or.inl ⟨ht.1, q⟩
      have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      have h3 := Finset.card_sdiff_add_card_eq_card hs
      rw [hF, hF]
      omega)
  have h4 := Finset.card_le_card (hmono _ _ hl)
  omega

theorem main (h : ℕ) (hh : 0 < h) (k d : ℕ) (hk : k = (2*h+1)^2) (hd : d = 2*k+2*h)
    (G : Finset (Key k d) → Finset (Fin d))
    (hG : ∀ x i, i ∈ G x ↔ ∃ a ∈ x, i ∈ a.val)
    (rank : Finset (Key k d) → ℕ)
    (hr1 : ∀ x z, z ⊆ x → (∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint i.val j.val) → z.card ≤ rank x)
    (hr2 : ∀ x n, (∀ z, z ⊆ x → (∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint i.val j.val) → z.card ≤ n)
      → rank x ≤ n)
    (F : Finset (Key k d) → Key k d → ℕ)
    (hF : ∀ x j, F x j = (j.val \ G x).card) :
    ((∀ x j, F x j ≤ k) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → F x j = k) ∧
      (∀ x j, j ∈ x → F x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, F y j ≤ F x j)) ∧
    (∀ x, Bd F x (G x).card ∧ Bd F x (k * rank x + k + 2*h)) ∧
    ∀ f : Finset (Key k d) → Key k d → ℕ,
      ((∀ x j, f x j ≤ 1) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = 1) ∧
        (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)) →
      ∃ x y : Finset (Key k d), Disjoint (G x) (G y) ∧ rank x = 1 ∧ rank y = 1 ∧
        ¬ Bd f x h ∧ ¬ Bd f y h ∧ Bd F x (k+2*h) ∧ Bd F y (k+2*h) := by
  have hk2 : 2*h < k := by
    rw [hk]
    have : 2*h+1 ≤ (2*h+1)^2 := Nat.le_self_pow (by omega) _
    omega
  have hkpos : 0 < k := by omega
  have hGcard : ∀ x, (G x).card ≤ d := fun x =>
    (Finset.card_le_univ _).trans (by simp)
  have hkey : ∀ (x : Finset (Key k d)) a, a ∈ x → a.val ⊆ G x := by
    intro x a ha i hi
    rw [hG]
    exact ⟨a, ha, hi⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x j
    rw [hF]
    exact (Finset.card_le_card Finset.sdiff_subset).trans j.2.le
  · intro x j hj
    have : Disjoint j.val (G x) := by
      rw [Finset.disjoint_left]
      intro t ht htG
      obtain ⟨a, ha, hta⟩ := (hG x t).1 htG
      exact Finset.disjoint_left.1 (hj a ha) hta ht
    rw [hF, Finset.sdiff_eq_self_of_disjoint this]
    exact j.2
  · intro x j hj
    rw [hF, Finset.sdiff_eq_empty_iff_subset.2 (hkey x j hj)]
    rfl
  · intro x y hxy j
    rw [hF, hF]
    apply Finset.card_le_card
    apply Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
    intro i hi
    rw [hG] at hi ⊢
    obtain ⟨b, hb, hib⟩ := hi
    exact ⟨b, hxy hb, hib⟩
  · intro x
    have hb := frac_bound G hG F hF x
    refine ⟨hb, ?_⟩
    have hle : (G x).card ≤ k * rank x + k + 2*h := by
      rcases x.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · have : G ∅ = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro i hi
          obtain ⟨b, hb, _⟩ := (hG _ i).1 hi
          simp at hb
        simp [this]
      · have h1 : 1 ≤ rank x := by
          have := hr1 x {a} (by simpa using ha) (by
            intro i hi j hj hij
            rw [Finset.mem_singleton] at hi hj
            exact absurd (hi.trans hj.symm) hij)
          simpa using this
        have h2 : k ≤ k * rank x := Nat.le_mul_of_pos_right k h1
        have := hGcard x
        omega
    intro l p a hp hl
    exact (hb l p a hp hl).trans hle
  · rintro f ⟨h1, hdis, hin, hm⟩
    obtain ⟨A, B, hAB, hA, hB⟩ := two_shores k d f h1 hdis hin hm h hkpos hd
    have hsub : ∀ A : Finset (Fin d), G (Cl k d A) ⊆ A := by
      intro A i hi
      obtain ⟨a, ha, hia⟩ := (hG _ i).1 hi
      simp only [Cl, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha hia
    have hne : ∀ A : Finset (Fin d), h+1 ≤ Nf f (Cl k d A) → (Cl k d A).Nonempty := by
      intro A hA
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Nf_empty] at hA
      omega
    have hdisj : Disjoint (G (Cl k d A)) (G (Cl k d B)) := hAB.mono (hsub A) (hsub B)
    obtain ⟨a, ha⟩ := hne A hA
    obtain ⟨b, hb⟩ := hne B hB
    have hlow : ∀ (x : Finset (Key k d)) c, c ∈ x → k ≤ (G x).card := by
      intro x c hc
      have := Finset.card_le_card (hkey x c hc)
      rw [c.2] at this
      exact this
    have hsum : (G (Cl k d A)).card + (G (Cl k d B)).card ≤ d := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact (Finset.card_le_univ _).trans (by simp)
    have hxA : (G (Cl k d A)).card ≤ k + 2*h := by
      have := hlow _ b hb; omega
    have hyB : (G (Cl k d B)).card ≤ k + 2*h := by
      have := hlow _ a ha; omega
    have hrank : ∀ x : Finset (Key k d), x.Nonempty → (G x).card ≤ k + 2*h → rank x = 1 := by
      intro x hx hxc
      apply le_antisymm
      · apply hr2
        intro z hz hzd
        by_contra hcon
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < z.card)
        have hd' := hzd u hu v hv huv
        have : u.val ∪ v.val ⊆ G x :=
          Finset.union_subset (hkey x u (hz hu)) (hkey x v (hz hv))
        have := Finset.card_le_card this
        rw [Finset.card_union_of_disjoint hd', u.2, v.2] at this
        omega
      · obtain ⟨c, hc⟩ := hx
        have := hr1 x {c} (by simpa using hc) (by
          intro i hi j hj hij
          rw [Finset.mem_singleton] at hi hj
          exact absurd (hi.trans hj.symm) hij)
        simpa using this
    have hnb : ∀ x : Finset (Key k d), h+1 ≤ Nf f x → ¬ Bd f x h := by
      intro x hx hb
      have := Nf_le f x h hb
      omega
    have hfr : ∀ x : Finset (Key k d), (G x).card ≤ k + 2*h → Bd F x (k+2*h) := by
      intro x hx l p c hp hl
      exact (frac_bound G hG F hF x l p c hp hl).trans hx
    exact ⟨Cl k d A, Cl k d B, hdisj, hrank _ ⟨a, ha⟩ hxA, hrank _ ⟨b, hb⟩ hyB,
      hnb _ hA, hnb _ hB, hfr _ hxA, hfr _ hyB⟩

end PEqualNP.Outside.L_meta_48521

theorem PEqualNP.Outside.L_meta_48521 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ h : Nat, 0 < h →
  let k := (2*h+1)^2
  let d := 2*k+2*h
  let K := {s : Finset (Fin d) // s.card = k}
  let X := Finset K
  let ground := fun (x : X) => x.biUnion (fun i => i.val)
  let rank := fun (x : X) => (x.powerset.filter
    (fun z => ∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint i.val j.val)).sup Finset.card
  let fit := fun (D : Nat) (f : X → K → Nat) =>
    (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
  let bounds := fun (f : X → K → Nat) (x : X) (B : Nat) =>
    ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → K),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) → p (Fin.last l) ⊆ x →
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B
  ∃ F : X → K → Nat, fit k F ∧
    (∀ x, bounds F x (ground x).card ∧ bounds F x (k * rank x + k + 2*h)) ∧
    ∀ f : X → K → Nat, fit 1 f →
      ∃ x y : X, Disjoint (ground x) (ground y) ∧
        rank x = 1 ∧ rank y = 1 ∧
        ¬ bounds f x h ∧ ¬ bounds f y h ∧
        bounds F x (k+2*h) ∧ bounds F y (k+2*h) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro h hh k d K X ground rank fit bounds
  have hG : ∀ (x : X) (i : Fin d), i ∈ ground x ↔ ∃ a ∈ x, i ∈ a.val := by
    intro x i
    exact Finset.mem_biUnion
  have hr1 : ∀ (x z : X), z ⊆ x → (∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint i.val j.val) →
      z.card ≤ rank x := by
    intro x z hz hd
    apply Finset.le_sup (f := Finset.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hz, hd⟩
  have hr2 : ∀ (x : X) (n : ℕ), (∀ z : X, z ⊆ x →
      (∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint i.val j.val) → z.card ≤ n) → rank x ≤ n := by
    intro x n hn
    apply Finset.sup_le
    intro z hz
    rw [Finset.mem_filter, Finset.mem_powerset] at hz
    exact hn z hz.1 hz.2
  have key := PEqualNP.Outside.L_meta_48521.main h hh k d rfl rfl ground hG rank hr1 hr2
    (fun x j => (j.val \ ground x).card) (fun x j => by
      refine congrArg Finset.card (Finset.ext (fun t => ?_))
      simp only [Finset.mem_sdiff])
  exact ⟨fun x j => (j.val \ ground x).card, key.1, key.2.1, key.2.2⟩
