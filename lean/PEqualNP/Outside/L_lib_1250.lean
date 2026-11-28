import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1250

open Finset

noncomputable def nm {n m : Nat} (A B C D : Fin m → Finset (Fin n)) (js : List (Fin m)) :
    Finset (Fin n) → Prop :=
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      A j ⊆ u ∧ u ⊆ B j ∧ C j ⊆ v ∧ v ⊆ D j) js

theorem closed {n m : Nat} (A B C D : Fin m → Finset (Fin n)) :
    ∀ (js : List (Fin m)) (y : Finset (Fin n)), nm A B C D js y ↔
      (∀ j ∈ js, A j ⊆ B j ∧ A j ⊆ D j ∧ C j ⊆ D j) ∧
      js.Pairwise (fun l e => (A e ⊆ B l ∧ A e ⊆ D l) ∧ (C e ⊆ B l ∧ C e ⊆ D l)) ∧
      ∀ j ∈ js, A j ⊆ y ∧ C j ⊆ y
  | [], y => by
    show True ↔ _
    simp
  | j :: js, y => by
    have ih := closed A B C D js
    show (∃ u v, nm A B C D js u ∧ u ⊆ v ∧ v ⊆ y ∧
      A j ⊆ u ∧ u ⊆ B j ∧ C j ⊆ v ∧ v ⊆ D j) ↔ _
    simp only [ih, List.forall_mem_cons, List.pairwise_cons]
    constructor
    · rintro ⟨u, v, ⟨hv, hp, hr⟩, uv, vy, Au, uB, Cv, vD⟩
      refine ⟨⟨⟨Au.trans uB, Au.trans (uv.trans vD), Cv.trans vD⟩, hv⟩, ⟨fun e he => ?_, hp⟩,
        ⟨Au.trans (uv.trans vy), Cv.trans vy⟩, fun e he =>
          ⟨(hr e he).1.trans (uv.trans vy), (hr e he).2.trans (uv.trans vy)⟩⟩
      exact ⟨⟨(hr e he).1.trans uB, (hr e he).1.trans (uv.trans vD)⟩,
        (hr e he).2.trans uB, (hr e he).2.trans (uv.trans vD)⟩
    · rintro ⟨⟨vj, hv⟩, ⟨hh, hp⟩, rj, hr⟩
      let u := A j ∪ js.toFinset.biUnion (fun e => A e ∪ C e)
      have sub : ∀ T : Finset (Fin n), A j ⊆ T → (∀ e ∈ js, A e ⊆ T ∧ C e ⊆ T) → u ⊆ T := by
        intro T h1 h2
        refine union_subset h1 (biUnion_subset.2 fun e he => ?_)
        rw [List.mem_toFinset] at he
        exact union_subset (h2 e he).1 (h2 e he).2
      have mem : ∀ e ∈ js, A e ⊆ u ∧ C e ⊆ u := fun e he =>
        ⟨fun x hx => mem_union_right _ (mem_biUnion.2
            ⟨e, List.mem_toFinset.2 he, mem_union_left _ hx⟩),
          fun x hx => mem_union_right _ (mem_biUnion.2
            ⟨e, List.mem_toFinset.2 he, mem_union_right _ hx⟩)⟩
      exact ⟨u, u ∪ C j, ⟨hv, hp, mem⟩, subset_union_left,
        union_subset (sub y rj.1 hr) rj.2, subset_union_left,
        sub (B j) vj.1 (fun e he => ⟨(hh e he).1.1, (hh e he).2.1⟩), subset_union_right,
        union_subset (sub (D j) vj.2.1 (fun e he => ⟨(hh e he).1.2, (hh e he).2.2⟩)) vj.2.2⟩

theorem sortk {α : Type} [DecidableEq α] (tau : α → ℕ) (S : Finset α) :
    ∃ js : List α, js.Nodup ∧ js.toFinset = S ∧ js.Pairwise (fun l e => tau e ≤ tau l) := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with h | hne
    · exact ⟨[], by simp, by simp [h], by simp⟩
    obtain ⟨x, hx, hmax⟩ := exists_max_image S tau hne
    obtain ⟨js, nd, tf, pw⟩ := ih (S.erase x) (erase_ssubset hx)
    refine ⟨x :: js, List.nodup_cons.2 ⟨fun h => ?_, nd⟩, ?_,
      List.pairwise_cons.2 ⟨fun e he => hmax e ?_, pw⟩⟩
    · rw [← List.mem_toFinset, tf] at h
      exact notMem_erase _ _ h
    · rw [List.toFinset_cons, tf, insert_erase hx]
    · have : e ∈ S.erase x := tf ▸ List.mem_toFinset.2 he
      exact mem_of_mem_erase this

theorem key :
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  ∀ w : Nat,
  let m := w+2*(w*w)
  let cut := w+w*w
  ∃ b : Fin m → Finset (Fin m),
  (∀ i, i ∉ b i) ∧
  let conf := fun (i j : Fin m) => i ∉ b j
  let live := fun (k : Nat) => (Finset.univ : Finset (Fin m)).filter
    (fun i => i.val < k ∧ ∃ j : Fin m, k ≤ j.val ∧ (conf i j ∨ conf j i))
  (∀ k, (live k).card ≤ w) ∧
  let a := fun (_ : Fin m) => (∅ : Finset (Fin m))
  let c := fun (i : Fin m) => ({i} : Finset (Fin m))
  let d := fun (_ : Fin m) => (Finset.univ : Finset (Fin m))
  let named := fun (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin m) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
  let feasible := fun (S : Finset (Fin m)) =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ named js
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin m), feasible S ↔
      ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ)
  (∃ P Q : Equiv.Perm (Fin w) → Finset (Fin m),
    (∀ s, (P s).card ≤ w+(w-1) ∧ (Q s).card ≤ w-1 ∧
      (∀ i ∈ P s, i.val < cut) ∧ ∀ i ∈ Q s, cut ≤ i.val) ∧
    ∀ s t, feasible (P s ∪ Q t) ↔ s=t) ∧
  ∀ (W : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin m → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge → w.factorial ≤ W := by
  intro w m cut
  classical
  letI : DecidableEq (Fin (w+2*(w*w))) := fun a b => Classical.propDecidable (a = b)
  letI : ∀ (i : Fin (w+2*(w*w))) (S : Finset (Fin (w+2*(w*w)))), Decidable (i ∈ S) :=
    fun i S => Classical.propDecidable _
  have fl : ∀ x y : Fin w, (finProdFinEquiv (x,y)).val < w*w := fun x y =>
    (finProdFinEquiv (x,y)).2
  let it : Fin w → Fin m := fun x => ⟨x.val, by
    have := x.2; show x.val < w+2*(w*w); omega⟩
  let pp : Fin w → Fin w → Fin m := fun x y => ⟨w + (finProdFinEquiv (x,y)).val, by
    have := fl x y; show _ < w+2*(w*w); omega⟩
  let qq : Fin w → Fin w → Fin m := fun x y => ⟨w + w*w + (finProdFinEquiv (x,y)).val, by
    have := fl x y; show _ < w+2*(w*w); omega⟩
  have vit : ∀ x, (it x).val = x.val := fun _ => rfl
  have vpp : ∀ x y, (pp x y).val = w + (finProdFinEquiv (x,y)).val := fun _ _ => rfl
  have vqq : ∀ x y, (qq x y).val = w + w*w + (finProdFinEquiv (x,y)).val := fun _ _ => rfl
  have itinj : ∀ x y, it x = it y → x = y := fun x y h =>
    Fin.ext (by have := congrArg Fin.val h; rwa [vit, vit] at this)
  have itpp : ∀ z x y, it z ≠ pp x y := by
    intro z x y h
    have := congrArg Fin.val h
    rw [vit, vpp] at this
    have := z.2; omega
  have itqq : ∀ z x y, it z ≠ qq x y := by
    intro z x y h
    have := congrArg Fin.val h
    rw [vit, vqq] at this
    have := z.2; omega
  have ppqq : ∀ x y a b, pp x y ≠ qq a b := by
    intro x y a b h
    have := congrArg Fin.val h
    rw [vpp, vqq] at this
    have := fl x y; omega
  have ppinj : ∀ x y a b, pp x y = pp a b → x = a ∧ y = b := by
    intro x y a b h
    have h1 := congrArg Fin.val h
    rw [vpp, vpp] at h1
    have h2 : finProdFinEquiv (x,y) = finProdFinEquiv (a,b) := Fin.ext (by omega)
    exact Prod.mk.inj (finProdFinEquiv.injective h2)
  have qqinj : ∀ x y a b, qq x y = qq a b → x = a ∧ y = b := by
    intro x y a b h
    have h1 := congrArg Fin.val h
    rw [vqq, vqq] at h1
    have h2 : finProdFinEquiv (x,y) = finProdFinEquiv (a,b) := Fin.ext (by omega)
    exact Prod.mk.inj (finProdFinEquiv.injective h2)
  let gad : Fin m → Fin w → Fin w → Prop := fun g x y => g = pp x y ∨ g = qq x y
  let bad : Fin m → Fin m → Prop := fun i j => i = j ∨ (∃ x y, gad i x y ∧ j = it x) ∨
    (∃ x y, i = it y ∧ gad j x y)
  let b : Fin m → Finset (Fin m) := fun j => univ.filter (fun i => ¬ bad i j)
  have gadge : ∀ g x y, gad g x y → w ≤ g.val := by
    intro g x y h
    rcases h with h | h
    · rw [h, vpp]; omega
    · rw [h, vqq]; omega
  refine ⟨b, fun i h => (mem_filter.1 h).2 (Or.inl rfl), ?_⟩
  intro conf live
  have cf : ∀ i j, conf i j → bad i j := by
    intro i j h
    by_contra hn
    exact h (mem_filter.2 ⟨mem_univ _, hn⟩)
  refine ⟨fun k => ?_, ?_⟩
  · have sub : live k ⊆ univ.image it := by
      intro i hi
      have hi' : i.val < k ∧ ∃ j : Fin m, k ≤ j.val ∧ (conf i j ∨ conf j i) := by
        simp only [live, Finset.mem_filter] at hi
        exact hi.2
      obtain ⟨hik, j, hkj, h⟩ := hi'
      have hij : i.val < j.val := by omega
      have : i.val < w := by
        by_contra hw
        rcases h with h | h
        · rcases cf _ _ h with h0 | ⟨x, y, h1, h2⟩ | ⟨x, y, h1, h2⟩
          · rw [h0] at hij; omega
          · have := congrArg Fin.val h2
            rw [vit] at this
            have := x.2; omega
          · have := congrArg Fin.val h1
            rw [vit] at this
            have := y.2; omega
        · rcases cf _ _ h with h0 | ⟨x, y, h1, h2⟩ | ⟨x, y, h1, h2⟩
          · rw [h0] at hij; omega
          · have := congrArg Fin.val h2
            rw [vit] at this
            have := x.2; omega
          · have h3 := congrArg Fin.val h1
            rw [vit] at h3
            have := gadge _ _ _ h2
            have := y.2; omega
      exact mem_image.2 ⟨⟨i.val, this⟩, mem_univ _, Fin.ext rfl⟩
    exact (card_le_card sub).trans (card_image_le.trans (by simp))
  intro a c d named feasible recognizes
  have eqv : ∀ js : List (Fin m), named js ↔ js.Pairwise (fun l e => ¬ bad e l) := by
    intro js
    refine (closed a b c d js univ).trans ⟨fun h => h.2.1.imp (fun {l e} p => ?_),
      fun h => ⟨fun j _ => ⟨empty_subset _, empty_subset _, subset_univ _⟩,
        h.imp (fun {l e} p => ⟨⟨empty_subset _, empty_subset _⟩, ?_, subset_univ _⟩),
        fun j _ => ⟨empty_subset _, subset_univ _⟩⟩⟩
    · have : e ∈ b l := p.2.1 (mem_singleton_self e)
      exact (mem_filter.1 this).2
    · show ({e} : Finset (Fin m)) ⊆ b l
      exact singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _, p⟩)
  have feas : ∀ S, feasible S ↔ ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧
      js.Pairwise (fun l e => ¬ bad e l) := fun S =>
    exists_congr fun js => and_congr Iff.rfl (and_congr
      (by constructor <;> intro h <;> convert h) (eqv js))
  let P : Equiv.Perm (Fin w) → Finset (Fin m) := fun s => univ.image it ∪
    univ.image (fun k : Fin (w-1) => pp (s ⟨k.val, by omega⟩) (s ⟨k.val+1, by omega⟩))
  let Q : Equiv.Perm (Fin w) → Finset (Fin m) := fun s =>
    univ.image (fun k : Fin (w-1) => qq (s ⟨k.val, by omega⟩) (s ⟨k.val+1, by omega⟩))
  have Pc : ∀ s, ∀ i ∈ P s, i.val < w + w*w := by
    intro s i hi
    rcases mem_union.1 hi with h | h
    · obtain ⟨x, _, rfl⟩ := mem_image.1 h
      rw [vit]; have := x.2; omega
    · obtain ⟨k, _, rfl⟩ := mem_image.1 h
      rw [vpp]
      have := fl (s ⟨k.val, by omega⟩) (s ⟨k.val+1, by omega⟩)
      omega
  have Qc : ∀ s, ∀ i ∈ Q s, w + w*w ≤ i.val := by
    intro s i hi
    obtain ⟨k, _, rfl⟩ := mem_image.1 hi
    rw [vqq]; omega
  have main : ∀ s t, feasible (P s ∪ Q t) ↔ s = t := by
    intro s t
    constructor
    · intro h
      obtain ⟨js, nd, tf, pw⟩ := (feas _).1 h
      have memjs : ∀ i, i ∈ P s ∪ Q t → i ∈ js := fun i hi => by
        rw [← tf] at hi; exact List.mem_toFinset.1 hi
      have ord : ∀ e l, e ∈ js → l ∈ js → e ≠ l → bad e l → js.idxOf e < js.idxOf l := by
        intro e l he hl ne hb
        rcases lt_trichotomy (js.idxOf e) (js.idxOf l) with h | h | h
        · exact h
        · exact absurd ((List.idxOf_inj he).1 h) ne
        · have := List.pairwise_iff_getElem.1 pw _ _ (List.idxOf_lt_length_iff.2 hl)
            (List.idxOf_lt_length_iff.2 he) h
          simp only [List.getElem_idxOf] at this
          exact absurd hb this
      have hit : ∀ x, it x ∈ js := fun x => memjs _ (mem_union_left _ (mem_union_left _
        (mem_image_of_mem _ (mem_univ _))))
      have chain : ∀ (u : Equiv.Perm (Fin w)) (G : Fin w → Fin w → Fin m),
          (∀ x y, gad (G x y) x y) → (∀ z x y, it z ≠ G x y) →
          (∀ k : Fin (w-1), G (u ⟨k.val, by omega⟩) (u ⟨k.val+1, by omega⟩) ∈ js) →
          ∀ i j : Fin w, i < j → js.idxOf (it (u j)) < js.idxOf (it (u i)) := by
        intro u G hg hne hG i j hij
        have step : ∀ k (hk : k+1 < w), js.idxOf (it (u ⟨k+1, hk⟩))
            < js.idxOf (it (u ⟨k, by omega⟩)) := by
          intro k hk
          have gm := hG ⟨k, by omega⟩
          have h1 := ord _ _ gm (hit (u ⟨k, by omega⟩)) (hne _ _ _).symm
            (Or.inr (Or.inl ⟨_, _, hg (u ⟨k, by omega⟩) (u ⟨k+1, hk⟩), rfl⟩))
          have h2 := ord _ _ (hit (u ⟨k+1, hk⟩)) gm (hne _ _ _)
            (Or.inr (Or.inr ⟨_, _, rfl, hg (u ⟨k, by omega⟩) (u ⟨k+1, hk⟩)⟩))
          exact h2.trans h1
        have all : ∀ n k (h : k+n+1 < w), js.idxOf (it (u ⟨k+n+1, h⟩))
            < js.idxOf (it (u ⟨k, by omega⟩)) := by
          intro n
          induction n with
          | zero => intro k h; exact step k h
          | succ n ih => intro k h; exact (step (k+n+1) h).trans (ih k (by omega))
        have hij' : i.val < j.val := hij
        have hj := j.2
        have := all (j.val - i.val - 1) i.val (by omega)
        have e : (⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ : Fin w) = j :=
          Fin.ext (by show i.val + (j.val - i.val - 1) + 1 = j.val; omega)
        rw [e] at this
        exact this
      have cs := chain s pp (fun _ _ => Or.inl rfl) itpp (fun k => memjs _ (mem_union_left _
        (mem_union_right _ (mem_image.2 ⟨k, mem_univ _, rfl⟩))))
      have ct := chain t qq (fun _ _ => Or.inr rfl) itqq (fun k => memjs _ (mem_union_right _
        (mem_image.2 ⟨k, mem_univ _, rfl⟩)))
      let val : Fin w → ℕ := fun x => js.idxOf (it x)
      have valinj : Function.Injective val := fun x y h =>
        itinj _ _ ((List.idxOf_inj (hit x)).1 h)
      have hT : (univ.image val).card = w := by
        rw [card_image_of_injective _ valinj, card_univ, Fintype.card_fin]
      have u1 : (fun k : Fin w => val (s k.rev)) = (univ.image val).orderEmbOfFin hT :=
        orderEmbOfFin_unique hT (fun _ => mem_image_of_mem _ (mem_univ _))
          (fun i j h => cs _ _ (Fin.rev_lt_rev.2 h))
      have u2 : (fun k : Fin w => val (t k.rev)) = (univ.image val).orderEmbOfFin hT :=
        orderEmbOfFin_unique hT (fun _ => mem_image_of_mem _ (mem_univ _))
          (fun i j h => ct _ _ (Fin.rev_lt_rev.2 h))
      refine Equiv.ext fun k => valinj ?_
      have := congrFun (u1.trans u2.symm) k.rev
      simpa only [Fin.rev_rev] using this
    · intro hst
      subst hst
      refine (feas _).2 ?_
      have bnd : ∀ i : Fin m, i.val < w+2*(w*w) := fun i => i.2
      let tau : Fin m → ℕ := fun i =>
        if h : i.val < w then 3*(s.symm ⟨i.val, h⟩).val
        else if h' : i.val < w + w*w then
          3*(s.symm (finProdFinEquiv.symm (⟨i.val - w, by omega⟩ : Fin (w*w))).1).val + 1
        else 3*(s.symm (finProdFinEquiv.symm
          (⟨i.val - (w+w*w), by have := bnd i; omega⟩ : Fin (w*w))).1).val + 2
      have tit : ∀ x, tau (it x) = 3*(s.symm x).val := by
        intro x
        have : (it x).val < w := x.2
        simp only [tau, dif_pos this]
        rfl
      have tpp : ∀ x y, tau (pp x y) = 3*(s.symm x).val + 1 := by
        intro x y
        have h1 : ¬ (pp x y).val < w := by rw [vpp]; omega
        have h2 : (pp x y).val < w + w*w := by rw [vpp]; have := fl x y; omega
        have e : ∀ h, (⟨(pp x y).val - w, h⟩ : Fin (w*w)) = finProdFinEquiv (x,y) := fun h =>
          Fin.ext (by show (pp x y).val - w = _; rw [vpp]; omega)
        simp only [tau, dif_neg h1, dif_pos h2]
        rw [e, Equiv.symm_apply_apply]
      have tqq : ∀ x y, tau (qq x y) = 3*(s.symm x).val + 2 := by
        intro x y
        have h1 : ¬ (qq x y).val < w := by rw [vqq]; omega
        have h2 : ¬ (qq x y).val < w + w*w := by rw [vqq]; omega
        have e : ∀ h, (⟨(qq x y).val - (w+w*w), h⟩ : Fin (w*w)) = finProdFinEquiv (x,y) :=
          fun h => Fin.ext (by show (qq x y).val - (w+w*w) = _; rw [vqq]; omega)
        simp only [tau, dif_neg h1, dif_neg h2]
        rw [e, Equiv.symm_apply_apply]
      obtain ⟨js, nd, tf, pw⟩ := sortk tau (P s ∪ Q s)
      refine ⟨js, nd, tf, ?_⟩
      refine (pw.and nd).imp_of_mem (fun {l e} hl _ h hb => ?_)
      have lS : l ∈ P s ∪ Q s := by
        rw [← tf]; exact List.mem_toFinset.2 hl
      rcases hb with h0 | ⟨x, y, hg, hj⟩ | ⟨x, y, hi, hg⟩
      · exact h.2 h0.symm
      · have h1 := h.1
        rw [hj, tit] at h1
        rcases hg with hg | hg
        · rw [hg, tpp] at h1; omega
        · rw [hg, tqq] at h1; omega
      · have cons : ∃ k : Fin (w-1), x = s ⟨k.val, by omega⟩ ∧ y = s ⟨k.val+1, by omega⟩ := by
          rcases mem_union.1 lS with h2 | h2
          · rcases mem_union.1 h2 with h3 | h3
            · obtain ⟨z, _, hz⟩ := mem_image.1 h3
              rcases hg with hg | hg
              · exact absurd (hz.trans hg) (itpp _ _ _)
              · exact absurd (hz.trans hg) (itqq _ _ _)
            · obtain ⟨k, _, hk⟩ := mem_image.1 h3
              rcases hg with hg | hg
              · obtain ⟨a1, a2⟩ := ppinj _ _ _ _ (hk.trans hg)
                exact ⟨k, a1.symm, a2.symm⟩
              · exact absurd (hk.trans hg) (ppqq _ _ _ _)
          · obtain ⟨k, _, hk⟩ := mem_image.1 h2
            rcases hg with hg | hg
            · exact absurd (hk.trans hg).symm (ppqq _ _ _ _)
            · obtain ⟨a1, a2⟩ := qqinj _ _ _ _ (hk.trans hg)
              exact ⟨k, a1.symm, a2.symm⟩
        obtain ⟨k, hx, hy⟩ := cons
        have h1 := h.1
        have sx : (s.symm x).val = k.val := by rw [hx, Equiv.symm_apply_apply]
        have sy : (s.symm y).val = k.val+1 := by rw [hy, Equiv.symm_apply_apply]
        rw [hi, tit, sy] at h1
        rcases hg with hg | hg
        · rw [hg, tpp, sx] at h1; omega
        · rw [hg, tqq, sx] at h1; omega
  refine ⟨⟨P, Q, fun s => ⟨?_, ?_, Pc s, Qc s⟩, main⟩, ?_⟩
  · refine (card_union_le _ _).trans (Nat.add_le_add (card_image_le.trans (by simp))
      (card_image_le.trans (by simp)))
  · exact card_image_le.trans (by simp)
  intro W start finals edge hrec
  have run : ∀ s, ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
      ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ P s ∪ Q s)) (st i.succ) := fun s =>
    (hrec (P s ∪ Q s)).1 ((main s s).2 rfl)
  choose st h0 hf he using run
  have cm : w + w*w < m+1 := by show _ < w+2*(w*w)+1; omega
  have inj : Function.Injective (fun s => st s ⟨w+w*w, cm⟩) := by
    intro s t h
    simp only at h
    refine (main s t).1 ((hrec _).2 ⟨fun i => if i.val ≤ w+w*w then st s i else st t i,
      ?_, ?_, fun i => ?_⟩)
    · have : (0 : Fin (m+1)).val ≤ w+w*w := Nat.zero_le _
      simp only [if_pos this, h0]
    · by_cases c : (Fin.last m).val ≤ w+w*w
      · have e : Fin.last m = ⟨w+w*w, cm⟩ := Fin.ext (by
          have : w+w*w ≤ m := by omega
          simp only [Fin.val_last] at c ⊢; omega)
        simp only [if_pos c]
        rw [e, h, ← e]; exact hf t
      · simp only [if_neg c]; exact hf t
    · by_cases c : i.val < w+w*w
      · have c1 : i.castSucc.val ≤ w+w*w := by simp only [Fin.val_castSucc]; omega
        have c2 : i.succ.val ≤ w+w*w := by simp only [Fin.val_succ]; omega
        have bit : decide (i ∈ P s ∪ Q t) = decide (i ∈ P s ∪ Q s) := by
          refine decide_eq_decide.2 ?_
          have n1 : i ∉ Q t := fun h => by have := Qc t i h; omega
          have n2 : i ∉ Q s := fun h => by have := Qc s i h; omega
          simp only [mem_union, n1, n2]
        simp only [if_pos c1, if_pos c2]
        rw [bit]; exact he s i
      · have c2 : ¬ i.succ.val ≤ w+w*w := by simp only [Fin.val_succ]; omega
        have e1 : (if i.castSucc.val ≤ w+w*w then st s i.castSucc else st t i.castSucc)
            = st t i.castSucc := by
          split
          · next hh =>
            have : i.castSucc = ⟨w+w*w, cm⟩ := Fin.ext (by
              simp only [Fin.val_castSucc] at hh ⊢; omega)
            rw [this]; exact h
          · rfl
        have bit : decide (i ∈ P s ∪ Q t) = decide (i ∈ P t ∪ Q t) := by
          refine decide_eq_decide.2 ?_
          have n1 : i ∉ P t := fun h => by have := Pc t i h; omega
          have n2 : i ∉ P s := fun h => by have := Pc s i h; omega
          simp only [mem_union, n1, n2]
        simp only [e1, if_neg c2]
        rw [bit]; exact he t i
  have := Fintype.card_le_of_injective _ inj
  simpa [Fintype.card_perm] using this

end PEqualNP.Outside.L_lib_1250

theorem PEqualNP.Outside.L_lib_1250 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  ∀ w : Nat,
  let m := w+2*(w*w)
  let cut := w+w*w
  ∃ b : Fin m → Finset (Fin m),
  (∀ i, i ∉ b i) ∧
  let conf := fun (i j : Fin m) => i ∉ b j
  let live := fun (k : Nat) => (Finset.univ : Finset (Fin m)).filter
    (fun i => i.val < k ∧ ∃ j : Fin m, k ≤ j.val ∧ (conf i j ∨ conf j i))
  (∀ k, (live k).card ≤ w) ∧
  let a := fun (_ : Fin m) => (∅ : Finset (Fin m))
  let c := fun (i : Fin m) => ({i} : Finset (Fin m))
  let d := fun (_ : Fin m) => (Finset.univ : Finset (Fin m))
  let named := fun (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin m) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
  let feasible := fun (S : Finset (Fin m)) =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ named js
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin m), feasible S ↔
      ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ)
  (∃ P Q : Equiv.Perm (Fin w) → Finset (Fin m),
    (∀ s, (P s).card ≤ w+(w-1) ∧ (Q s).card ≤ w-1 ∧
      (∀ i ∈ P s, i.val < cut) ∧ ∀ i ∈ Q s, cut ≤ i.val) ∧
    ∀ s t, feasible (P s ∪ Q t) ↔ s=t) ∧
  ∀ (W : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin m → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge → w.factorial ≤ W) := by
  exact PEqualNP.Outside.L_lib_1250.key
