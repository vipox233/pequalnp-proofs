import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1252

open Finset

theorem key :
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  ∀ n : Nat,
  let t := 8*n*n
  ∀ order : Fin t ≃ (Fin (4*n) × (Fin n × Bool)),
  let row := fun i => (order i).1
  let var := fun i => (order i).2.1
  let sign := fun i => (order i).2.2
  let feasible := fun (S : Finset (Fin t)) =>
    (∀ i ∈ S, ∀ j ∈ S, row i = row j → i=j) ∧
    ∃ val : Fin n → Bool, ∀ i ∈ S, val (var i) = sign i
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin t → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin t), feasible S ↔
      ∃ st : Fin (t+1) → Fin W, st 0=start ∧ st (Fin.last t) ∈ finals ∧
        ∀ i : Fin t, edge i (st i.castSucc) (decide (i∈S)) (st i.succ)
  (∃ (cut : Nat) (L R : Fin n → Fin t),
    cut ≤ t ∧ Function.Injective L ∧ Function.Injective R ∧
    (∀ i, (L i).val < cut ∧ cut ≤ (R i).val) ∧
    ∀ I J : Finset (Fin n), feasible (I.image L ∪ J.image R) ↔ Disjoint I J) ∧
  ∀ (W : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin t → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge → 2^n ≤ W := by
  intro n t order row var sign feasible recognizes
  classical
  letI : DecidableEq (Fin t) := fun a b => Classical.propDecidable (a = b)
  letI : ∀ (i : Fin t) (S : Finset (Fin t)), Decidable (i ∈ S) :=
    fun i S => Classical.propDecidable _
  have er : ∀ x, row (order.symm x) = x.1 := fun x =>
    congrArg Prod.fst (order.apply_symm_apply x)
  have ev : ∀ x, var (order.symm x) = x.2.1 := fun x =>
    congrArg (fun y => y.2.1) (order.apply_symm_apply x)
  have es : ∀ x, sign (order.symm x) = x.2.2 := fun x =>
    congrArg (fun y => y.2.2) (order.apply_symm_apply x)
  suffices H : ∃ (cut : Nat) (L R : Fin n → Fin t), cut ≤ t ∧
      (∀ i, (L i).val < cut ∧ cut ≤ (R i).val) ∧
      (∀ i j, row (L i) = row (L j) → i = j) ∧
      (∀ i j, row (R i) = row (R j) → i = j) ∧
      (∀ i j, var (L i) = var (L j) → sign (L i) = sign (L j)) ∧
      (∀ i j, var (R i) = var (R j) → sign (R i) = sign (R j)) ∧
      (∀ i j, i ≠ j → row (L i) ≠ row (R j) ∧
        (var (L i) = var (R j) → sign (L i) = sign (R j))) ∧
      (∀ i, row (L i) = row (R i) ∨ (var (L i) = var (R i) ∧ sign (L i) ≠ sign (R i))) by
    obtain ⟨cut, L, R, hc, hpos, h1, h2, h5, h6, h3, h4⟩ := H
    have main : ∀ I J : Finset (Fin n),
        feasible (I.image L ∪ J.image R) ↔ Disjoint I J := by
      intro I J
      have mem : ∀ x, x ∈ I.image L ∪ J.image R ↔ (∃ i ∈ I, L i = x) ∨ ∃ j ∈ J, R j = x := by
        intro x
        rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro ⟨hr, val, hv⟩
        refine Finset.disjoint_left.2 (fun i hi hj => ?_)
        have mL := (mem _).2 (Or.inl ⟨i, hi, rfl⟩)
        have mR := (mem _).2 (Or.inr ⟨i, hj, rfl⟩)
        rcases h4 i with h | ⟨hv1, hs⟩
        · have e := congrArg Fin.val (hr _ mL _ mR h)
          have := hpos i
          omega
        · exact hs (((hv _ mL).symm.trans (congrArg val hv1)).trans (hv _ mR))
      · intro hd
        have ne : ∀ i ∈ I, ∀ j ∈ J, i ≠ j := fun i hi j hj h =>
          Finset.disjoint_left.1 hd hi (h ▸ hj)
        have cons : ∀ x ∈ I.image L ∪ J.image R, ∀ y ∈ I.image L ∪ J.image R,
            var x = var y → sign x = sign y := by
          intro x hx y hy h
          rcases (mem x).1 hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
            rcases (mem y).1 hy with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · exact h5 i j h
          · exact (h3 i j (ne i hi j hj)).2 h
          · exact ((h3 j i (ne j hj i hi)).2 h.symm).symm
          · exact h6 i j h
        refine ⟨fun x hx y hy h => ?_, fun v => decide
          (∃ x ∈ I.image L ∪ J.image R, var x = v ∧ sign x = true), fun x hx => ?_⟩
        · rcases (mem x).1 hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
            rcases (mem y).1 hy with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · rw [h1 i j h]
          · exact absurd h (h3 i j (ne i hi j hj)).1
          · exact absurd h.symm (h3 j i (ne j hj i hi)).1
          · rw [h2 i j h]
        · cases hs : sign x with
          | true => exact decide_eq_true ⟨x, hx, rfl, hs⟩
          | false =>
            refine decide_eq_false ?_
            rintro ⟨y, hy, h, ht⟩
            have := cons y hy x hx h
            rw [ht, hs] at this
            exact Bool.noConfusion this
    refine ⟨⟨cut, L, R, hc, fun i j h => h1 i j (congrArg row h),
      fun i j h => h2 i j (congrArg row h), hpos, main⟩, ?_⟩
    intro W start finals edge hrec
    have run : ∀ I : Finset (Fin n), ∃ st : Fin (t+1) → Fin W, st 0 = start ∧
        st (Fin.last t) ∈ finals ∧ ∀ i : Fin t,
          edge i (st i.castSucc) (decide (i ∈ I.image L ∪ Iᶜ.image R)) (st i.succ) := fun I =>
      (hrec _).1 ((main I Iᶜ).2 disjoint_compl_right)
    choose st h0 hf he using run
    have cm : cut < t+1 := Nat.lt_succ_of_le hc
    have sub : ∀ I J : Finset (Fin n), st I ⟨cut, cm⟩ = st J ⟨cut, cm⟩ → I ⊆ J := by
      intro I J h
      have f : feasible (I.image L ∪ Jᶜ.image R) := by
        refine (hrec _).2 ⟨fun i => if i.val ≤ cut then st I i else st J i,
          ?_, ?_, fun i => ?_⟩
        · have : (0 : Fin (t+1)).val ≤ cut := Nat.zero_le _
          simp only [if_pos this, h0]
        · by_cases c : (Fin.last t).val ≤ cut
          · have e : Fin.last t = ⟨cut, cm⟩ := Fin.ext (by
              simp only [Fin.val_last] at c ⊢; omega)
            simp only [if_pos c]
            rw [e, h, ← e]; exact hf J
          · simp only [if_neg c]; exact hf J
        · have nR : ∀ K : Finset (Fin n), i.val < cut → i ∉ K.image R := by
            intro K c hi
            obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
            have := (hpos k).2
            rw [hk] at this; omega
          have nL : ∀ K : Finset (Fin n), ¬ i.val < cut → i ∉ K.image L := by
            intro K c hi
            obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
            have := (hpos k).1
            rw [hk] at this; omega
          by_cases c : i.val < cut
          · have c1 : i.castSucc.val ≤ cut := by simp only [Fin.val_castSucc]; omega
            have c2 : i.succ.val ≤ cut := by simp only [Fin.val_succ]; omega
            have bit : decide (i ∈ I.image L ∪ Jᶜ.image R)
                = decide (i ∈ I.image L ∪ Iᶜ.image R) := by
              refine decide_eq_decide.2 ?_
              simp only [Finset.mem_union, nR Jᶜ c, nR Iᶜ c]
            simp only [if_pos c1, if_pos c2]
            rw [bit]; exact he I i
          · have c2 : ¬ i.succ.val ≤ cut := by simp only [Fin.val_succ]; omega
            have e1 : (if i.castSucc.val ≤ cut then st I i.castSucc else st J i.castSucc)
                = st J i.castSucc := by
              split
              · next hh =>
                have : i.castSucc = ⟨cut, cm⟩ := Fin.ext (by
                  simp only [Fin.val_castSucc] at hh ⊢; omega)
                rw [this]; exact h
              · rfl
            have bit : decide (i ∈ I.image L ∪ Jᶜ.image R)
                = decide (i ∈ J.image L ∪ Jᶜ.image R) := by
              refine decide_eq_decide.2 ?_
              simp only [Finset.mem_union, nL I c, nL J c]
            simp only [e1, if_neg c2]
            rw [bit]; exact he J i
      intro x hx
      by_contra hn
      exact Finset.disjoint_left.1 ((main _ _).1 f) hx (Finset.mem_compl.2 hn)
    have inj : Function.Injective (fun I => st I ⟨cut, cm⟩) := fun I J h =>
      Finset.Subset.antisymm (sub I J h) (sub J I h.symm)
    have := Fintype.card_le_of_injective _ inj
    simpa [Fintype.card_finset] using this
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have no : ∀ i : Fin n, False := fun i => by have := i.2; omega
    exact ⟨0, fun i => (no i).elim, fun i => (no i).elim, Nat.zero_le _,
      fun i => (no i).elim, fun i => (no i).elim, fun i => (no i).elim,
      fun i => (no i).elim, fun i => (no i).elim, fun i => (no i).elim,
      fun i => (no i).elim⟩
  let P : Fin (4*n) → Fin n → ℕ := fun r v => (order.symm (r,(v,true))).val
  let N : Fin (4*n) → Fin n → ℕ := fun r v => (order.symm (r,(v,false))).val
  let cnt : ℕ → ℕ := fun c =>
    (univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < c)).card
  have all : univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < t) = univ :=
    filter_true_of_mem (fun x _ => (order.symm (x.1,(x.2,true))).2)
  have total : Fintype.card (Fin (4*n) × Fin n) = 4*(n*n) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_assoc]
  have tt : 2*(n*n) ≤ cnt t := by
    show 2*(n*n) ≤ (univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < t)).card
    rw [all, card_univ, total]; omega
  have ex : ∃ c, 2*(n*n) ≤ cnt c := ⟨t, tt⟩
  obtain ⟨c, c1, c2, ct⟩ : ∃ c, 2*(n*n) ≤ cnt c ∧ cnt c ≤ 2*(n*n) ∧ c ≤ t := by
    refine ⟨Nat.find ex, Nat.find_spec ex, ?_, Nat.find_min' ex tt⟩
    rcases Nat.eq_zero_or_pos (Nat.find ex) with h | h
    · have c0 : cnt 0 = 0 := by
        show (univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < 0)).card = 0
        simp
      rw [h, c0]; exact Nat.zero_le _
    · have lt : cnt (Nat.find ex - 1) < 2*(n*n) :=
        Nat.lt_of_not_le (Nat.find_min ex (by omega))
      have step : cnt (Nat.find ex) ≤ cnt (Nat.find ex - 1) + 1 := by
        have sb : univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < Nat.find ex)
            ⊆ univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < Nat.find ex - 1)
              ∪ univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 = Nat.find ex - 1) := by
          intro x hx
          simp only [Finset.mem_union, mem_filter, mem_univ, true_and] at hx ⊢
          omega
        have one : (univ.filter (fun x : Fin (4*n) × Fin n =>
            P x.1 x.2 = Nat.find ex - 1)).card ≤ 1 := by
          refine card_le_one.2 (fun a ha b hb => ?_)
          have e : order.symm (a.1,(a.2,true)) = order.symm (b.1,(b.2,true)) :=
            Fin.val_injective (((mem_filter.1 ha).2).trans ((mem_filter.1 hb).2).symm)
          have := order.symm.injective e
          simp only [Prod.mk.injEq, and_true] at this
          exact Prod.ext this.1 this.2
        exact (card_le_card sb).trans ((card_union_le _ _).trans (Nat.add_le_add_left one _))
      omega
  let A := univ.filter (fun r : Fin (4*n) => ∀ v, P r v < c)
  let B := univ.filter (fun r : Fin (4*n) => ∀ v, c ≤ P r v)
  let Sp := univ.filter (fun r : Fin (4*n) => (∃ v, P r v < c) ∧ ∃ v, c ≤ P r v)
  have Ac : A.card ≤ 2*n := by
    have : (A ×ˢ (univ : Finset (Fin n))).card ≤ cnt c := by
      refine card_le_card (fun x hx => ?_)
      exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 (mem_product.1 hx).1).2 x.2⟩
    rw [card_product, card_univ, Fintype.card_fin] at this
    refine Nat.le_of_mul_le_mul_right (c := n) ?_ hn
    rw [Nat.mul_assoc]; exact this.trans c2
  have Bc : B.card ≤ 2*n := by
    have d : Disjoint (B ×ˢ (univ : Finset (Fin n)))
        (univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < c)) := by
      refine Finset.disjoint_left.2 (fun x hx hy => ?_)
      have h1 := (mem_filter.1 (mem_product.1 hx).1).2 x.2
      have h2 := (mem_filter.1 hy).2
      omega
    have := card_le_univ ((B ×ˢ (univ : Finset (Fin n)))
      ∪ univ.filter (fun x : Fin (4*n) × Fin n => P x.1 x.2 < c))
    rw [card_union_of_disjoint d, card_product, card_univ, Fintype.card_fin, total] at this
    change B.card * n + cnt c ≤ 4*(n*n) at this
    refine Nat.le_of_mul_le_mul_right (c := n) ?_ hn
    rw [Nat.mul_assoc]; omega
  have cover : 4*n ≤ A.card + B.card + Sp.card := by
    have : (univ : Finset (Fin (4*n))) ⊆ A ∪ B ∪ Sp := by
      intro r _
      simp only [Finset.mem_union]
      by_cases h1 : ∀ v, P r v < c
      · exact Or.inl (Or.inl (mem_filter.2 ⟨mem_univ _, h1⟩))
      by_cases h2 : ∀ v, c ≤ P r v
      · exact Or.inl (Or.inr (mem_filter.2 ⟨mem_univ _, h2⟩))
      push Not at h1 h2
      exact Or.inr (mem_filter.2 ⟨mem_univ _, h2, h1⟩)
    have h := (card_le_card this).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le A B) _))
    rwa [card_univ, Fintype.card_fin] at h
  by_cases hs : n ≤ Sp.card
  · have : Fintype.card (Fin n) ≤ Fintype.card ↥Sp := by
      rw [Fintype.card_fin, Fintype.card_coe]; exact hs
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le this
    have hr : ∀ i, ∃ a b, P (f i).1 a < c ∧ c ≤ P (f i).1 b := by
      intro i
      obtain ⟨⟨a, ha⟩, b, hb⟩ := (mem_filter.1 (f i).2).2
      exact ⟨a, b, ha, hb⟩
    choose a b ha hb using hr
    have rinj : ∀ i j, (f i).1 = (f j).1 → i = j := fun i j h => f.injective (Subtype.ext h)
    refine ⟨c, fun i => order.symm ((f i).1, (a i, true)),
      fun i => order.symm ((f i).1, (b i, true)), ct, fun i => ⟨ha i, hb i⟩,
      fun i j h => ?_, fun i j h => ?_, fun i j _ => ?_, fun i j _ => ?_,
      fun i j hij => ⟨fun h => ?_, fun _ => ?_⟩, fun i => Or.inl ?_⟩
    · rw [er, er] at h; exact rinj i j h
    · rw [er, er] at h; exact rinj i j h
    · rw [es, es]
    · rw [es, es]
    · rw [er, er] at h; exact hij (rinj i j h)
    · rw [es, es]
    · rw [er, er]
  · have Ag : n ≤ A.card := by omega
    have Bg : n ≤ B.card := by omega
    have cA : Fintype.card (Fin n) ≤ Fintype.card ↥A := by
      rw [Fintype.card_fin, Fintype.card_coe]; exact Ag
    have cB : Fintype.card (Fin n) ≤ Fintype.card ↥B := by
      rw [Fintype.card_fin, Fintype.card_coe]; exact Bg
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le cA
    obtain ⟨h⟩ := Function.Embedding.nonempty_of_card_le cB
    let q : Fin n → Prop := fun v => 2*n ≤ (univ.filter (fun r => c ≤ N r v)).card
    let rT : Fin n → Fin (4*n) := fun v => if q v then (g v).1 else (h v).1
    have AB : ∀ r, r ∈ A → r ∈ B → False := by
      intro r h1 h2
      have a := (mem_filter.1 h1).2 ⟨0, hn⟩
      have b := (mem_filter.1 h2).2 ⟨0, hn⟩
      omega
    have Tinj : ∀ i j, rT i = rT j → i = j := by
      intro i j e
      by_cases qi : q i <;> by_cases qj : q j <;>
        simp only [rT, if_pos, if_neg, qi, qj, not_false_eq_true] at e
      · exact g.injective (Subtype.ext e)
      · exact (AB _ (g i).2 (e ▸ (h j).2)).elim
      · exact (AB _ (g j).2 (e ▸ (h i).2)).elim
      · exact h.injective (Subtype.ext e)
    let Q : Fin n → Finset (Fin (4*n)) := fun v =>
      if q v then univ.filter (fun r => c ≤ N r v) else univ.filter (fun r => N r v < c)
    have Qc : ∀ v, 2*n ≤ (Q v).card := by
      intro v
      by_cases qv : q v
      · simp only [Q, if_pos qv]; exact qv
      · simp only [Q, if_neg qv]
        have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (4*n))))
          (fun r => c ≤ N r v)
        simp only [not_le, card_univ, Fintype.card_fin] at this
        have h2 : ¬ 2*n ≤ (univ.filter (fun r => c ≤ N r v)).card := qv
        omega
    have Sc : ∀ v, n ≤ (Q v \ univ.image rT).card := by
      intro v
      have h1 := le_card_sdiff (univ.image rT) (Q v)
      have h2 : (univ.image rT).card ≤ n := card_image_le.trans (by simp)
      have := Qc v
      omega
    obtain ⟨rS, Sinj, Sm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun v => Q v \ univ.image rT)).1 (fun s => by
        rcases s.eq_empty_or_nonempty with e | ⟨v, hv⟩
        · simp [e]
        refine le_trans ?_ (card_le_card (subset_biUnion_of_mem
          (fun v => Q v \ univ.image rT) hv))
        exact (card_le_univ s).trans (by rw [Fintype.card_fin]; exact Sc v))
    have TS : ∀ i j, rT i ≠ rS j := fun i j e =>
      (mem_sdiff.1 (Sm j)).2 (e ▸ mem_image_of_mem _ (mem_univ _))
    let xT : Fin n → Fin t := fun i => order.symm (rT i, (i, true))
    let xS : Fin n → Fin t := fun i => order.symm (rS i, (i, false))
    let L : Fin n → Fin t := fun i => if q i then xT i else xS i
    let R : Fin n → Fin t := fun i => if q i then xS i else xT i
    have Lr : ∀ i, row (L i) = rT i ∨ row (L i) = rS i := by
      intro i
      by_cases qi : q i
      · simp only [L, if_pos qi, xT, er]; exact Or.inl trivial
      · simp only [L, if_neg qi, xS, er]; exact Or.inr trivial
    have rows : ∀ i j (x y : Fin (4*n)), (x = rT i ∨ x = rS i) → (y = rT j ∨ y = rS j) →
        x = y → i = j := by
      intro i j x y hx hy e
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at e
      · exact Tinj i j e
      · exact absurd e (TS i j)
      · exact absurd e.symm (TS j i)
      · exact Sinj e
    have Rr : ∀ i, row (R i) = rT i ∨ row (R i) = rS i := by
      intro i
      by_cases qi : q i
      · simp only [R, if_pos qi, xS, er]; exact Or.inr trivial
      · simp only [R, if_neg qi, xT, er]; exact Or.inl trivial
    have Lv : ∀ i, var (L i) = i := by
      intro i
      by_cases qi : q i
      · simp only [L, if_pos qi, xT, ev]
      · simp only [L, if_neg qi, xS, ev]
    have Rv : ∀ i, var (R i) = i := by
      intro i
      by_cases qi : q i
      · simp only [R, if_pos qi, xS, ev]
      · simp only [R, if_neg qi, xT, ev]
    refine ⟨c, L, R, ct, fun i => ?_,
      fun i j e => rows i j _ _ (Lr i) (Lr j) e,
      fun i j e => rows i j _ _ (Rr i) (Rr j) e,
      fun i j e => ?_, fun i j e => ?_,
      fun i j hij => ⟨fun e => hij (rows i j _ _ (Lr i) (Rr j) e), fun e => ?_⟩,
      fun i => Or.inr ⟨(Lv i).trans (Rv i).symm, ?_⟩⟩
    · have m := (mem_sdiff.1 (Sm i)).1
      by_cases qi : q i
      · simp only [Q, if_pos qi] at m
        have e : rT i = (g i).1 := if_pos qi
        simp only [L, R, if_pos qi]
        refine ⟨?_, (mem_filter.1 m).2⟩
        have := (mem_filter.1 (g i).2).2 i
        rw [← e] at this; exact this
      · simp only [Q, if_neg qi] at m
        have e : rT i = (h i).1 := if_neg qi
        simp only [L, R, if_neg qi]
        refine ⟨(mem_filter.1 m).2, ?_⟩
        have := (mem_filter.1 (h i).2).2 i
        rw [← e] at this; exact this
    · rw [Lv, Lv] at e; rw [e]
    · rw [Rv, Rv] at e; rw [e]
    · rw [Lv, Rv] at e; exact absurd e hij
    · by_cases qi : q i
      · simp [L, R, if_pos qi, xT, xS, es]
      · simp [L, R, if_neg qi, xT, xS, es]

end PEqualNP.Outside.L_lib_1252

theorem PEqualNP.Outside.L_lib_1252 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  ∀ n : Nat,
  let t := 8*n*n
  ∀ order : Fin t ≃ (Fin (4*n) × (Fin n × Bool)),
  let row := fun i => (order i).1
  let var := fun i => (order i).2.1
  let sign := fun i => (order i).2.2
  let feasible := fun (S : Finset (Fin t)) =>
    (∀ i ∈ S, ∀ j ∈ S, row i = row j → i=j) ∧
    ∃ val : Fin n → Bool, ∀ i ∈ S, val (var i) = sign i
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin t → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin t), feasible S ↔
      ∃ st : Fin (t+1) → Fin W, st 0=start ∧ st (Fin.last t) ∈ finals ∧
        ∀ i : Fin t, edge i (st i.castSucc) (decide (i∈S)) (st i.succ)
  (∃ (cut : Nat) (L R : Fin n → Fin t),
    cut ≤ t ∧ Function.Injective L ∧ Function.Injective R ∧
    (∀ i, (L i).val < cut ∧ cut ≤ (R i).val) ∧
    ∀ I J : Finset (Fin n), feasible (I.image L ∪ J.image R) ↔ Disjoint I J) ∧
  ∀ (W : Nat) (start : Fin W) (finals : Finset (Fin W))
    (edge : Fin t → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge → 2^n ≤ W) := by
  exact PEqualNP.Outside.L_lib_1252.key
