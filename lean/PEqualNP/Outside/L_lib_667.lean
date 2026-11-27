import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_667_aux

abbrev V (r : ℕ) := Fin r → ZMod 2

def dot (r : ℕ) (u v : V r) : ZMod 2 := ∑ j : Fin r, u j * v j

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma v_add_self (r : ℕ) (x : V r) : x + x = 0 := by
  funext j
  exact zmod2_add_self (x j)

lemma dot_zero_left (r : ℕ) (v : V r) : dot r 0 v = 0 := by
  simp [dot]

lemma dot_zero_right (r : ℕ) (u : V r) : dot r u 0 = 0 := by
  simp [dot]

lemma dot_comm (r : ℕ) (u v : V r) : dot r u v = dot r v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma dot_add_left (r : ℕ) (u v w : V r) : dot r (u + v) w = dot r u w + dot r v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right (r : ℕ) (u v w : V r) : dot r u (v + w) = dot r u v + dot r u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma card_subspace_eq_pow2 :
    ∀ (r : ℕ) (H : Finset (V r)),
      (0 : V r) ∈ H → (∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) →
      ∃ c : ℕ, H.card = 2 ^ c := by
  intro r
  induction r with
  | zero =>
    intro H h0 _
    refine ⟨0, ?_⟩
    have huniv : H = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      have hx : x = 0 := by funext i; exact Fin.elim0 i
      rwa [hx]
    rw [huniv]
    simp [V]
  | succ r ih =>
    intro H h0 hadd
    let H0 := H.filter (fun v : V (r + 1) => v (Fin.last r) = 0)
    let H1 := H.filter (fun v : V (r + 1) => v (Fin.last r) = 1)
    have hdisj : Disjoint H0 H1 := by
      rw [Finset.disjoint_left]
      intro v hv0 hv1
      have h1 := (Finset.mem_filter.mp hv0).2
      have h2 := (Finset.mem_filter.mp hv1).2
      rw [h1] at h2
      exact absurd h2 (by decide)
    have hunion : H = H0 ∪ H1 := by
      ext v
      simp only [Finset.mem_union, H0, H1, Finset.mem_filter]
      constructor
      · intro hv
        rcases zmod2_eq_zero_or_one (v (Fin.last r)) with h | h
        · left; exact ⟨hv, h⟩
        · right; exact ⟨hv, h⟩
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    let proj : V (r + 1) → V r := fun v i => v (Fin.castSucc i)
    let P := H0.image proj
    have hP0 : (0 : V r) ∈ P := by
      rw [Finset.mem_image]
      refine ⟨0, Finset.mem_filter.mpr ⟨h0, rfl⟩, rfl⟩
    have hPadd : ∀ u ∈ P, ∀ v ∈ P, u + v ∈ P := by
      intro u hu v hv
      rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      rw [Finset.mem_image]
      refine ⟨u' + v', ?_, rfl⟩
      rw [Finset.mem_filter] at hu' hv' ⊢
      refine ⟨hadd u' hu'.1 v' hv'.1, ?_⟩
      simp [hu'.2, hv'.2]
    have hcard0 : H0.card = P.card := by
      symm
      apply Finset.card_image_of_injOn
      intro u hu v hv heq
      have hu0 := (Finset.mem_filter.mp hu).2
      have hv0 := (Finset.mem_filter.mp hv).2
      funext j
      refine Fin.lastCases ?_ ?_ j
      · rw [hu0, hv0]
      · intro i
        exact congrFun heq i
    rcases ih P hP0 hPadd with ⟨c, hc⟩
    by_cases hH1 : H1 = ∅
    · refine ⟨c, ?_⟩
      rw [hunion, hH1, Finset.union_empty, hcard0, hc]
    · have hne : H1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH1
      rcases hne with ⟨v0, hv0⟩
      have hv0H : v0 ∈ H := (Finset.mem_filter.mp hv0).1
      have hv01 : v0 (Fin.last r) = 1 := (Finset.mem_filter.mp hv0).2
      have hcard1 : H1.card = H0.card := by
        apply Finset.card_bij (fun v _ => v + v0)
        · intro v hv
          rw [Finset.mem_filter] at hv ⊢
          refine ⟨hadd v hv.1 v0 hv0H, ?_⟩
          simp only [Pi.add_apply, hv.2, hv01]
          exact zmod2_add_self 1
        · intro u _ v _ heq
          have h := congrArg (fun z => z + v0) heq
          simpa only [add_assoc, v_add_self, add_zero] using h
        · intro u hu
          rw [Finset.mem_filter] at hu
          refine ⟨u + v0, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨hadd u hu.1 v0 hv0H, ?_⟩
            simp [hu.2, hv01]
          · simp only [add_assoc, v_add_self, add_zero]
      refine ⟨c + 1, ?_⟩
      rw [hunion, Finset.card_union_of_disjoint hdisj, hcard1, hcard0, hc]
      ring

lemma card_dot_eq (r : ℕ) (hr : 1 ≤ r) (u : V r) (hu : u ≠ 0) (a : ZMod 2) :
    (Finset.univ.filter (fun x : V r => dot r u x = a)).card = 2 ^ (r - 1) := by
  have hex : ∃ i : Fin r, u i = 1 := by
    by_contra h
    push_neg at h
    apply hu
    funext i
    rcases zmod2_eq_zero_or_one (u i) with h0 | h1
    · exact h0
    · exact absurd h1 (h i)
  rcases hex with ⟨i, hi⟩
  let e1 : V r := Pi.single i 1
  have he1 : dot r u e1 = 1 := by
    simp [dot, e1, Pi.single_apply, hi]
  let S0 := Finset.univ.filter (fun x : V r => dot r u x = 0)
  let S1 := Finset.univ.filter (fun x : V r => dot r u x = 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    have hx0 := (Finset.mem_filter.mp h0).2
    have hx1 := (Finset.mem_filter.mp h1).2
    rw [hx0] at hx1
    exact absurd hx1 (by decide)
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod2_eq_zero_or_one (dot r u x)
  have hbij : S0.card = S1.card := by
    apply Finset.card_bij (fun x _ => x + e1)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [dot_add_right, hx.2, he1, zero_add]
    · intro x _ y _ heq
      have h := congrArg (fun z => z + e1) heq
      simpa only [add_assoc, v_add_self, add_zero] using h
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨y + e1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [dot_add_right, hy.2, he1, zmod2_add_self]
      · simp only [add_assoc, v_add_self, add_zero]
  have htot : S0.card + S1.card = 2 ^ r := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    simp [V]
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have : r = (r - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · change S0.card = 2 ^ (r - 1); omega
  · change S1.card = 2 ^ (r - 1); omega

lemma exists_dual_pair (r : ℕ) (u v : V r) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∃ e1 e2 : V r, dot r u e1 = 1 ∧ dot r v e1 = 0 ∧ dot r u e2 = 0 ∧ dot r v e2 = 1 := by
  have hexu : ∃ i : Fin r, u i = 1 := by
    by_contra h; push_neg at h; apply hu; funext i
    rcases zmod2_eq_zero_or_one (u i) with h0 | h1
    · exact h0
    · exact absurd h1 (h i)
  rcases hexu with ⟨i, hui⟩
  rcases zmod2_eq_zero_or_one (v i) with hvi | hvi
  · have hexv : ∃ j : Fin r, v j = 1 := by
      by_contra h; push_neg at h; apply hv; funext j
      rcases zmod2_eq_zero_or_one (v j) with h0 | h1
      · exact h0
      · exact absurd h1 (h j)
    rcases hexv with ⟨j, hvj⟩
    rcases zmod2_eq_zero_or_one (u j) with huj | huj
    · refine ⟨Pi.single i 1, Pi.single j 1, ?_, ?_, ?_, ?_⟩ <;>
        simp [dot, Pi.single_apply, hui, hvi, huj, hvj]
    · refine ⟨Pi.single i 1, Pi.single j 1 + Pi.single i 1, ?_, ?_, ?_, ?_⟩
      · simp [dot, Pi.single_apply, hui]
      · simp [dot, Pi.single_apply, hvi]
      · rw [dot_add_right]
        simp [dot, Pi.single_apply, huj, hui, zmod2_add_self]
      · rw [dot_add_right]
        simp [dot, Pi.single_apply, hvj, hvi]
  · have hexd : ∃ j : Fin r, u j ≠ v j := by
      by_contra h; push_neg at h; exact huv (funext h)
    rcases hexd with ⟨j, hdj⟩
    rcases zmod2_eq_zero_or_one (u j) with huj | huj
    · have hvj : v j = 1 := by
        rcases zmod2_eq_zero_or_one (v j) with h0 | h1
        · exact absurd (huj.trans h0.symm) hdj
        · exact h1
      refine ⟨Pi.single i 1 + Pi.single j 1, Pi.single j 1, ?_, ?_, ?_, ?_⟩
      · rw [dot_add_right]; simp [dot, Pi.single_apply, hui, huj]
      · rw [dot_add_right]; simp [dot, Pi.single_apply, hvi, hvj, zmod2_add_self]
      · simp [dot, Pi.single_apply, huj]
      · simp [dot, Pi.single_apply, hvj]
    · have hvj : v j = 0 := by
        rcases zmod2_eq_zero_or_one (v j) with h0 | h1
        · exact h0
        · exact absurd (huj.trans h1.symm) hdj
      refine ⟨Pi.single j 1, Pi.single i 1 + Pi.single j 1, ?_, ?_, ?_, ?_⟩
      · simp [dot, Pi.single_apply, huj]
      · simp [dot, Pi.single_apply, hvj]
      · rw [dot_add_right]; simp [dot, Pi.single_apply, hui, huj, zmod2_add_self]
      · rw [dot_add_right]; simp [dot, Pi.single_apply, hvi, hvj]

lemma card_dot_pair_eq (r : ℕ) (hr : 2 ≤ r) (u v : V r) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (ab : ZMod 2 × ZMod 2) :
    (Finset.univ.filter (fun x : V r => (dot r u x, dot r v x) = ab)).card = 2 ^ (r - 2) := by
  rcases exists_dual_pair r u v hu hv huv with ⟨e1, e2, hu1, hv1, hu2, hv2⟩
  let F := fun p : ZMod 2 × ZMod 2 => Finset.univ.filter (fun x : V r => (dot r u x, dot r v x) = p)
  have hshift : ∀ p : ZMod 2 × ZMod 2, (F p).card = (F (0, 0)).card := by
    intro p
    let s : V r := (if p.1 = 1 then e1 else 0) + (if p.2 = 1 then e2 else 0)
    have hsu : dot r u s = p.1 := by
      dsimp only [s]
      rw [dot_add_right]
      rcases zmod2_eq_zero_or_one p.1 with h1 | h1 <;> rcases zmod2_eq_zero_or_one p.2 with h2 | h2
      · simp [h1, h2, dot_zero_right]
      · simp [h1, h2, dot_zero_right, hu2]
      · simp [h1, h2, dot_zero_right, hu1]
      · simp [h1, h2, hu1, hu2]
    have hsv : dot r v s = p.2 := by
      dsimp only [s]
      rw [dot_add_right]
      rcases zmod2_eq_zero_or_one p.1 with h1 | h1 <;> rcases zmod2_eq_zero_or_one p.2 with h2 | h2
      · simp [h1, h2, dot_zero_right]
      · simp [h1, h2, dot_zero_right, hv2]
      · simp [h1, h2, dot_zero_right, hv1]
      · simp [h1, h2, hv1, hv2]
    apply Finset.card_bij (fun x _ => x + s)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : dot r u x = p.1 := congrArg Prod.fst hx.2
      have h2 : dot r v x = p.2 := congrArg Prod.snd hx.2
      apply Prod.ext
      · dsimp only; rw [dot_add_right, h1, hsu, zmod2_add_self]
      · dsimp only; rw [dot_add_right, h2, hsv, zmod2_add_self]
    · intro x _ y _ heq
      have h := congrArg (fun z => z + s) heq
      simpa only [add_assoc, v_add_self, add_zero] using h
    · intro y hy
      rw [Finset.mem_filter] at hy
      have h1 : dot r u y = 0 := congrArg Prod.fst hy.2
      have h2 : dot r v y = 0 := congrArg Prod.snd hy.2
      refine ⟨y + s, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Prod.ext
        · dsimp only; rw [dot_add_right, h1, hsu, zero_add]
        · dsimp only; rw [dot_add_right, h2, hsv, zero_add]
      · simp only [add_assoc, v_add_self, add_zero]
  have hsum : (∑ p : ZMod 2 × ZMod 2, (F p).card) = 2 ^ r := by
    have hbi : (Finset.univ : Finset (V r)) =
        (Finset.univ : Finset (ZMod 2 × ZMod 2)).biUnion F := by
      ext x
      simp [F]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (ZMod 2 × ZMod 2))) F := by
      intro p _ q _ hpq
      change Disjoint (F p) (F q)
      rw [Finset.disjoint_left]
      intro x hxp hxq
      have h1 := (Finset.mem_filter.mp hxp).2
      have h2 := (Finset.mem_filter.mp hxq).2
      exact hpq (h1.symm.trans h2)
    rw [← Finset.card_biUnion hdisj, ← hbi, Finset.card_univ]
    simp [V]
  have hsum2 : (∑ p : ZMod 2 × ZMod 2, (F p).card) = 4 * (F (0, 0)).card := by
    have : ∀ p ∈ (Finset.univ : Finset (ZMod 2 × ZMod 2)), (F p).card = (F (0, 0)).card :=
      fun p _ => hshift p
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    have hcard4 : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by decide
    rw [hcard4]
  have hpow : 2 ^ r = 4 * 2 ^ (r - 2) := by
    have : r = (r - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  change (F ab).card = 2 ^ (r - 2)
  rw [hshift ab]
  omega

lemma card_perm_fiber_map {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f g : α → β) :
    (Finset.univ.filter (fun p : Equiv.Perm α => ∀ x : α, g (p x) = f x)).card =
      if ∀ b : β, (Finset.univ.filter (fun x => f x = b)).card =
                  (Finset.univ.filter (fun x => g x = b)).card
      then ∏ b : β, ((Finset.univ.filter (fun x => f x = b)).card).factorial
      else 0 := by
  by_cases heq : ∀ b : β, (Finset.univ.filter (fun x => f x = b)).card =
      (Finset.univ.filter (fun x => g x = b)).card
  · simp only [heq, implies_true, ↓reduceIte]
    let Dom := { p : Equiv.Perm α // ∀ x : α, g (p x) = f x }
    let Cod := ∀ b : β, { x : α // f x = b } ≃ { y : α // g y = b }
    let toCod : Dom → Cod := fun p b =>
      { toFun := fun x => ⟨p.1 x.1, (p.2 x.1).trans x.2⟩
        invFun := fun y => ⟨p.1.symm y.1, by
          have h := p.2 (p.1.symm y.1)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm.trans y.2⟩
        left_inv := fun x => Subtype.ext (p.1.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (p.1.apply_symm_apply y.1) }
    let fromCod : Cod → Dom := fun φ =>
      ⟨{ toFun := fun x => (φ (f x) ⟨x, rfl⟩).1
         invFun := fun y => ((φ (g y)).symm ⟨y, rfl⟩).1
         left_inv := fun x => by
           dsimp only
           have hg : g (φ (f x) ⟨x, rfl⟩).1 = f x := (φ (f x) ⟨x, rfl⟩).2
           have hcast : ∀ (b1 b2 : β) (hb : b1 = b2) (z : { y : α // g y = b1 }),
               ((φ b1).symm z).1 = ((φ b2).symm ⟨z.1, z.2.trans hb⟩).1 := by
             intro b1 b2 hb z; subst hb; rfl
           rw [hcast (g (φ (f x) ⟨x, rfl⟩).1) (f x) hg ⟨(φ (f x) ⟨x, rfl⟩).1, rfl⟩]
           change ((φ (f x)).symm (φ (f x) ⟨x, rfl⟩)).1 = x
           rw [Equiv.symm_apply_apply]
         right_inv := fun y => by
           dsimp only
           have hf : f ((φ (g y)).symm ⟨y, rfl⟩).1 = g y := ((φ (g y)).symm ⟨y, rfl⟩).2
           have hcast : ∀ (b1 b2 : β) (hb : b1 = b2) (z : { x : α // f x = b1 }),
               (φ b1 z).1 = (φ b2 ⟨z.1, z.2.trans hb⟩).1 := by
             intro b1 b2 hb z; subst hb; rfl
           rw [hcast (f ((φ (g y)).symm ⟨y, rfl⟩).1) (g y) hf ⟨((φ (g y)).symm ⟨y, rfl⟩).1, rfl⟩]
           change (φ (g y) ((φ (g y)).symm ⟨y, rfl⟩)).1 = y
           rw [Equiv.apply_symm_apply] },
       fun x => (φ (f x) ⟨x, rfl⟩).2⟩
    let eqv : Dom ≃ Cod :=
      { toFun := toCod
        invFun := fromCod
        left_inv := fun p => by
          apply Subtype.ext
          ext x
          rfl
        right_inv := fun φ => by
          funext b
          ext x
          rcases x with ⟨x, hx⟩
          subst hx
          rfl }
    have hcard_dom : (Finset.univ.filter (fun p : Equiv.Perm α => ∀ x : α, g (p x) = f x)).card =
        Fintype.card Dom := (Fintype.card_subtype _).symm
    rw [hcard_dom, Fintype.card_congr eqv, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    have hc1 : Fintype.card { x : α // f x = b } = (Finset.univ.filter (fun x => f x = b)).card :=
      Fintype.card_subtype _
    have hc2 : Fintype.card { y : α // g y = b } = (Finset.univ.filter (fun x => g x = b)).card :=
      Fintype.card_subtype _
    have hce : Fintype.card { x : α // f x = b } = Fintype.card { y : α // g y = b } := by
      rw [hc1, hc2, heq b]
    let efg : { x : α // f x = b } ≃ { y : α // g y = b } := Fintype.equivOfCardEq hce
    have hperm : Fintype.card ({ x : α // f x = b } ≃ { y : α // g y = b }) =
        Fintype.card (Equiv.Perm { x : α // f x = b }) :=
      Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) efg.symm)
    rw [hperm, Fintype.card_perm, hc1, heq b]
  · simp only [heq, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply heq
    intro b
    apply Finset.card_bij (fun x _ => p x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, (hp x).trans hx.2⟩
    · intro x _ y _ hxy
      exact p.injective hxy
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨p.symm y, ?_, p.apply_symm_apply y⟩
      rw [Finset.mem_filter]
      have h := hp (p.symm y)
      simp only [Equiv.apply_symm_apply] at h
      exact ⟨Finset.mem_univ _, h.symm.trans hy.2⟩

def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sum_chi_dot (r : ℕ) (hr : 1 ≤ r) (z : V r) :
    (∑ u : V r, chi (dot r u z)) = if z = 0 then (2 ^ r : ℤ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [dot_zero_right, chi, ↓reduceIte, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
    simp [V]
  · simp only [hz, ↓reduceIte]
    have hcomm : (∑ u : V r, chi (dot r u z)) = ∑ u : V r, chi (dot r z u) := by
      apply Finset.sum_congr rfl; intro u _; rw [dot_comm]
    rw [hcomm]
    let S0 := Finset.univ.filter (fun u : V r => dot r z u = 0)
    let S1 := Finset.univ.filter (fun u : V r => dot r z u = 1)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro u h0 h1
      have hu0 := (Finset.mem_filter.mp h0).2
      have hu1 := (Finset.mem_filter.mp h1).2
      rw [hu0] at hu1
      exact absurd hu1 (by decide)
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext u
      simp only [Finset.mem_union, S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_eq_zero_or_one (dot r z u)
    rw [← hunion, Finset.sum_union hdisj]
    have h0 : (∑ u ∈ S0, chi (dot r z u)) = (S0.card : ℤ) := by
      have : ∀ u ∈ S0, chi (dot r z u) = 1 := fun u hu => by
        simp [chi, (Finset.mem_filter.mp hu).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : (∑ u ∈ S1, chi (dot r z u)) = -(S1.card : ℤ) := by
      have : ∀ u ∈ S1, chi (dot r z u) = -1 := fun u hu => by
        have hv := (Finset.mem_filter.mp hu).2
        simp only [chi, hv]
        decide
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h0, h1, card_dot_eq r hr z hz 0, card_dot_eq r hr z hz 1]
    ring

lemma exists_unbalanced_of_not_bijective (r : ℕ) (hr : 1 ≤ r) (tags : V r → V r)
    (hnb : ¬ Function.Bijective tags) :
    ∃ u : V r, u ≠ 0 ∧ (Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)).card ≠ 2 ^ (r - 1) := by
  by_contra hall
  push_neg at hall
  apply hnb
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨?_, rfl⟩
  intro y
  have hfib : (Finset.univ.filter (fun x : V r => tags x = y)).card = 1 := by
    have h1 : ((Finset.univ.filter (fun x : V r => tags x = y)).card : ℤ) * (2 ^ r : ℤ) =
        ∑ x : V r, if tags x + y = 0 then (2 ^ r : ℤ) else 0 := by
      have hiff : ∀ x : V r, tags x + y = 0 ↔ tags x = y := by
        intro x
        constructor
        · intro h
          have := congrArg (fun z => z + y) h
          simpa only [add_assoc, v_add_self, add_zero, zero_add] using this
        · intro h; rw [h, v_add_self]
      simp only [hiff, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
        nsmul_eq_mul]
      ring
    have h2 : (∑ x : V r, if tags x + y = 0 then (2 ^ r : ℤ) else 0) =
        ∑ x : V r, ∑ u : V r, chi (dot r u (tags x + y)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_chi_dot r hr (tags x + y)).symm
    have h3 : (∑ x : V r, ∑ u : V r, chi (dot r u (tags x + y))) =
        ∑ u : V r, chi (dot r u y) * ∑ x : V r, chi (dot r u (tags x)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [dot_add_right, chi_add, mul_comm]
    have hzero : ∀ u : V r, u ≠ 0 → (∑ x : V r, chi (dot r u (tags x))) = 0 := by
      intro u hu
      let A0 := Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)
      let A1 := Finset.univ.filter (fun x : V r => dot r u (tags x) = 1)
      have hdisj : Disjoint A0 A1 := by
        rw [Finset.disjoint_left]
        intro x hx0 hx1
        have h0 := (Finset.mem_filter.mp hx0).2
        have h1 := (Finset.mem_filter.mp hx1).2
        rw [h0] at h1
        exact absurd h1 (by decide)
      have hunion : A0 ∪ A1 = Finset.univ := by
        ext x
        simp only [Finset.mem_union, A0, A1, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact zmod2_eq_zero_or_one (dot r u (tags x))
      have hc0 : A0.card = 2 ^ (r - 1) := hall u hu
      have htot : A0.card + A1.card = 2 ^ r := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
        simp [V]
      have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
        have : r = (r - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      have hc1 : A1.card = 2 ^ (r - 1) := by omega
      rw [← hunion, Finset.sum_union hdisj]
      have hs0 : (∑ x ∈ A0, chi (dot r u (tags x))) = (A0.card : ℤ) := by
        have : ∀ x ∈ A0, chi (dot r u (tags x)) = 1 := fun x hx => by
          simp [chi, (Finset.mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hs1 : (∑ x ∈ A1, chi (dot r u (tags x))) = -(A1.card : ℤ) := by
        have : ∀ x ∈ A1, chi (dot r u (tags x)) = -1 := fun x hx => by
          have hv := (Finset.mem_filter.mp hx).2
          simp only [chi, hv]
          decide
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hs0, hs1, hc0, hc1]
      ring
    have h4 : (∑ u : V r, chi (dot r u y) * ∑ x : V r, chi (dot r u (tags x))) = (2 ^ r : ℤ) := by
      rw [Finset.sum_eq_single (0 : V r)]
      · simp only [dot_zero_left, chi, ↓reduceIte, one_mul, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_one]
        simp [V]
      · intro u _ hu
        rw [hzero u hu, mul_zero]
      · intro h0; exact absurd (Finset.mem_univ 0) h0
    have heq : ((Finset.univ.filter (fun x : V r => tags x = y)).card : ℤ) * (2 ^ r : ℤ) =
        1 * (2 ^ r : ℤ) := by
      rw [h1, h2, h3, h4, one_mul]
    have hpos : (2 ^ r : ℤ) ≠ 0 := by positivity
    have hnat : ((Finset.univ.filter (fun x : V r => tags x = y)).card : ℤ) = 1 :=
      mul_right_cancel₀ hpos heq
    exact_mod_cast hnat
  have hne : (Finset.univ.filter (fun x : V r => tags x = y)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.card_empty] at hfib
    omega
  rcases hne with ⟨x, hx⟩
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

def annSet (r : ℕ) (tags : V r → V r) (p : Equiv.Perm (V r)) : Finset (V r) :=
  Finset.univ.filter (fun u : V r => ∀ x y : V r, dot r u (p x + tags x) = dot r u (p y + tags y))

lemma zero_mem_annSet (r : ℕ) (tags : V r → V r) (p : Equiv.Perm (V r)) :
    (0 : V r) ∈ annSet r tags p := by
  simp [annSet, dot_zero_left]

lemma annSet_add_closed (r : ℕ) (tags : V r → V r) (p : Equiv.Perm (V r))
    (u v : V r) (hu : u ∈ annSet r tags p) (hv : v ∈ annSet r tags p) :
    u + v ∈ annSet r tags p := by
  rw [annSet, Finset.mem_filter] at hu hv ⊢
  refine ⟨Finset.mem_univ _, fun x y => ?_⟩
  rw [dot_add_left, dot_add_left, hu.2 x y, hv.2 x y]

lemma annSet_card_eq_pow (r : ℕ) (tags : V r → V r) (p : Equiv.Perm (V r)) :
    (annSet r tags p).card = 2 ^ Nat.log 2 (annSet r tags p).card := by
  rcases card_subspace_eq_pow2 r (annSet r tags p) (zero_mem_annSet r tags p)
      (fun u hu v hv => annSet_add_closed r tags p u v hu hv) with ⟨c, hc⟩
  rw [hc, Nat.log_pow (by omega : 1 < 2)]

lemma mem_annSet_iff_exists_shift (r : ℕ) (tags : V r → V r) (p : Equiv.Perm (V r)) (u : V r) :
    u ∈ annSet r tags p ↔ ∃ a : ZMod 2, ∀ x : V r, dot r u (p x) = dot r u (tags x) + a := by
  simp only [annSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨dot r u (p 0 + tags 0), fun x => ?_⟩
    have hx := h x 0
    rw [dot_add_right] at hx
    have hadd := congrArg (fun z => z + dot r u (tags x)) hx
    rw [add_assoc, zmod2_add_self, add_zero, add_comm] at hadd
    exact hadd
  · rintro ⟨a, ha⟩ x y
    rw [dot_add_right, dot_add_right, ha x, ha y]
    have h1 : ∀ z : ZMod 2, (z + a) + z = a := fun z => by
      rw [add_comm z a, add_assoc, zmod2_add_self, add_zero]
    rw [h1, h1]

lemma count_perm_mem_annSet (r : ℕ) (hr : 1 ≤ r) (tags : V r → V r) (u : V r) (hu : u ≠ 0) :
    (Finset.univ.filter (fun p : Equiv.Perm (V r) => u ∈ annSet r tags p)).card =
      if (Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)).card = 2 ^ (r - 1)
      then 2 * ((2 ^ (r - 1)).factorial) ^ 2
      else 0 := by
  let S := fun a : ZMod 2 =>
    Finset.univ.filter (fun p : Equiv.Perm (V r) => ∀ x : V r, dot r u (p x) = dot r u (tags x) + a)
  have hdisj : Disjoint (S 0) (S 1) := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    have h0 := (Finset.mem_filter.mp hp0).2 0
    have h1 := (Finset.mem_filter.mp hp1).2 0
    rw [h0] at h1
    have hsub := congrArg (fun z => dot r u (tags 0) + z) h1
    rw [← add_assoc, ← add_assoc, zmod2_add_self, zero_add, zero_add] at hsub
    exact absurd hsub (by decide)
  have hunion : Finset.univ.filter (fun p : Equiv.Perm (V r) => u ∈ annSet r tags p) = S 0 ∪ S 1 := by
    ext p
    simp only [Finset.mem_union, S, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_annSet_iff_exists_shift]
    constructor
    · rintro ⟨a, ha⟩
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · left; exact ha
      · right; exact ha
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hSa : ∀ a : ZMod 2, (S a).card =
      if (Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)).card = 2 ^ (r - 1)
      then ((2 ^ (r - 1)).factorial) ^ 2
      else 0 := by
    intro a
    dsimp only [S]
    rw [card_perm_fiber_map (fun x => dot r u (tags x) + a) (fun y => dot r u y)]
    have hfib_y : ∀ b : ZMod 2, (Finset.univ.filter (fun y : V r => dot r u y = b)).card = 2 ^ (r - 1) :=
      fun b => card_dot_eq r hr u hu b
    have htot : (Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)).card +
        (Finset.univ.filter (fun x : V r => dot r u (tags x) = 1)).card = 2 ^ r := by
      let A0 := Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)
      let A1 := Finset.univ.filter (fun x : V r => dot r u (tags x) = 1)
      have hd : Disjoint A0 A1 := by
        rw [Finset.disjoint_left]
        intro x h0 h1
        have hx0 := (Finset.mem_filter.mp h0).2
        have hx1 := (Finset.mem_filter.mp h1).2
        rw [hx0] at hx1; exact absurd hx1 (by decide)
      have hu' : A0 ∪ A1 = Finset.univ := by
        ext x; simp only [Finset.mem_union, A0, A1, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        exact zmod2_eq_zero_or_one _
      rw [← Finset.card_union_of_disjoint hd, hu', Finset.card_univ]; simp [V]
    have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
      have : r = (r - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have hshift_fib : ∀ b : ZMod 2,
        (Finset.univ.filter (fun x : V r => dot r u (tags x) + a = b)).card =
        (Finset.univ.filter (fun x : V r => dot r u (tags x) = b + a)).card := by
      intro b
      congr 1; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have := congrArg (fun z => z + a) h
        simpa only [add_assoc, zmod2_add_self, add_zero] using this
      · intro h; rw [h, add_assoc, zmod2_add_self, add_zero]
    by_cases hbal : (Finset.univ.filter (fun x : V r => dot r u (tags x) = 0)).card = 2 ^ (r - 1)
    · have hbal1 : (Finset.univ.filter (fun x : V r => dot r u (tags x) = 1)).card = 2 ^ (r - 1) := by
        omega
      have hallb : ∀ b : ZMod 2,
          (Finset.univ.filter (fun x : V r => dot r u (tags x) + a = b)).card =
          (Finset.univ.filter (fun y : V r => dot r u y = b)).card := by
        intro b
        rw [hshift_fib b, hfib_y b]
        rcases zmod2_eq_zero_or_one (b + a) with h | h <;> rw [h]
        · exact hbal
        · exact hbal1
      simp only [hbal, hallb, implies_true, ↓reduceIte]
      have hprod : (∏ b : ZMod 2, ((Finset.univ.filter (fun y : V r => dot r u y = b)).card).factorial) =
          ∏ _ : ZMod 2, (2 ^ (r - 1)).factorial := by
        apply Finset.prod_congr rfl
        intro b _
        rw [hfib_y b]
      rw [hprod, Finset.prod_const, Finset.card_univ, ZMod.card]
    · have hnot : ¬ ∀ b : ZMod 2,
          (Finset.univ.filter (fun x : V r => dot r u (tags x) + a = b)).card =
          (Finset.univ.filter (fun y : V r => dot r u y = b)).card := by
        intro hallb
        apply hbal
        have h := hallb a
        rw [hshift_fib a, zmod2_add_self, hfib_y a] at h
        exact h
      simp only [hbal, hnot, ↓reduceIte]
  rw [hSa 0, hSa 1]
  split_ifs <;> ring

lemma count_perm_mem_annSet_pair (r : ℕ) (hr : 2 ≤ r) (u v : V r)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (Finset.univ.filter (fun p : Equiv.Perm (V r) => u ∈ annSet r id p ∧ v ∈ annSet r id p)).card =
      4 * ((2 ^ (r - 2)).factorial) ^ 4 := by
  let S := fun ab : ZMod 2 × ZMod 2 =>
    Finset.univ.filter (fun p : Equiv.Perm (V r) =>
      ∀ x : V r, (dot r u (p x), dot r v (p x)) = (dot r u x + ab.1, dot r v x + ab.2))
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (ZMod 2 × ZMod 2))) S := by
    intro a _ b _ hab
    change Disjoint (S a) (S b)
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have ha := (Finset.mem_filter.mp hpa).2 0
    have hb := (Finset.mem_filter.mp hpb).2 0
    rw [ha] at hb
    simp only [dot_zero_right, zero_add] at hb
    exact hab hb
  have hunion : Finset.univ.filter (fun p : Equiv.Perm (V r) => u ∈ annSet r id p ∧ v ∈ annSet r id p) =
      (Finset.univ : Finset (ZMod 2 × ZMod 2)).biUnion S := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, S, Finset.mem_filter,
      mem_annSet_iff_exists_shift, id_eq]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), fun x => Prod.ext (ha x) (hb x)⟩
    · rintro ⟨⟨a, b⟩, hab⟩
      exact ⟨⟨a, fun x => congrArg Prod.fst (hab x)⟩, ⟨b, fun x => congrArg Prod.snd (hab x)⟩⟩
  rw [hunion, Finset.card_biUnion hdisj]
  have hSab : ∀ ab : ZMod 2 × ZMod 2, (S ab).card = ((2 ^ (r - 2)).factorial) ^ 4 := by
    intro ab
    dsimp only [S]
    rw [card_perm_fiber_map (fun x => (dot r u x + ab.1, dot r v x + ab.2))
        (fun y => (dot r u y, dot r v y))]
    have hfib_g : ∀ q : ZMod 2 × ZMod 2,
        (Finset.univ.filter (fun y : V r => (dot r u y, dot r v y) = q)).card = 2 ^ (r - 2) :=
      fun q => card_dot_pair_eq r hr u v hu hv huv q
    have hfib_f : ∀ q : ZMod 2 × ZMod 2,
        (Finset.univ.filter (fun x : V r => (dot r u x + ab.1, dot r v x + ab.2) = q)).card = 2 ^ (r - 2) := by
      rintro ⟨q1, q2⟩
      have heq : Finset.univ.filter (fun x : V r => (dot r u x + ab.1, dot r v x + ab.2) = (q1, q2)) =
          Finset.univ.filter (fun x : V r => (dot r u x, dot r v x) = (q1 + ab.1, q2 + ab.2)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2⟩
          constructor
          · have := congrArg (fun z => z + ab.1) h1
            simpa only [add_assoc, zmod2_add_self, add_zero] using this
          · have := congrArg (fun z => z + ab.2) h2
            simpa only [add_assoc, zmod2_add_self, add_zero] using this
        · rintro ⟨h1, h2⟩
          rw [h1, h2, add_assoc, zmod2_add_self, add_zero, add_assoc, zmod2_add_self, add_zero]
          exact ⟨rfl, rfl⟩
      rw [heq, hfib_g]
    have hallq : ∀ q : ZMod 2 × ZMod 2,
        (Finset.univ.filter (fun x : V r => (dot r u x + ab.1, dot r v x + ab.2) = q)).card =
        (Finset.univ.filter (fun y : V r => (dot r u y, dot r v y) = q)).card := fun q => by
      rw [hfib_f q, hfib_g q]
    simp only [hallq, implies_true, ↓reduceIte]
    have hprod : (∏ q : ZMod 2 × ZMod 2,
        ((Finset.univ.filter (fun y : V r => (dot r u y, dot r v y) = q)).card).factorial) =
        ∏ _ : ZMod 2 × ZMod 2, (2 ^ (r - 2)).factorial := by
      apply Finset.prod_congr rfl
      intro q _
      rw [hfib_g q]
    rw [hprod, Finset.prod_const]
    have hc4 : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by decide
    rw [hc4]
  have hsum : (∑ ab : ZMod 2 × ZMod 2, (S ab).card) =
      ∑ _ : ZMod 2 × ZMod 2, ((2 ^ (r - 2)).factorial) ^ 4 :=
    Finset.sum_congr rfl (fun ab _ => hSab ab)
  rw [hsum, Finset.sum_const, smul_eq_mul]
  have hc4 : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by decide
  rw [hc4]

lemma ineq_pow2_log (c : ℕ) : c ≤ 2 ^ c - 1 := by
  induction c with
  | zero => simp
  | succ k ih =>
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    rw [pow_succ]
    omega

lemma ineq_six_excess (c : ℕ) : 6 * ((2 ^ c - 1) - c) ≤ (2 ^ c - 1) * (2 ^ c - 2) := by
  induction c with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have hm : 2 ≤ 2 ^ (m + 1) := by
        have := Nat.one_le_pow m 2 (by omega)
        rw [pow_succ]; omega
      have h1 : m + 1 ≤ 2 ^ (m + 1) - 1 := ineq_pow2_log (m + 1)
      have h2 : m + 2 ≤ 2 ^ (m + 2) - 1 := ineq_pow2_log (m + 2)
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      zify [h1, h2, hm, (by omega : 1 ≤ 2 ^ (m + 1)), (by omega : 1 ≤ 2 ^ (m + 2)),
        (by omega : 2 ≤ 2 ^ (m + 2))] at ih ⊢
      have hpowZ : (2 ^ (m + 2) : ℤ) = 2 * (2 ^ (m + 1) : ℤ) := by exact_mod_cast hpow
      nlinarith

lemma factorial_gap_ineq (m : ℕ) (hm : 1 ≤ m) :
    (4 * m - 1) * (4 * m - 2) * (m.factorial) ^ 4 < 3 * ((2 * m).factorial) ^ 2 := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ t =>
      let m := t + 1
      have hm1 : 1 ≤ m := by omega
      have hih : (4 * m - 1) * (4 * m - 2) * (m.factorial) ^ 4 < 3 * ((2 * m).factorial) ^ 2 :=
        ih hm1
      have hfac1 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
      have hfac2 : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
        have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [h1, Nat.factorial_succ, Nat.factorial_succ]
        ring
      have hmul_pos : 0 < 4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 := by positivity
      have hstep : 4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 * ((4 * m - 1) * (4 * m - 2) * (m.factorial) ^ 4) <
          4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 * (3 * ((2 * m).factorial) ^ 2) :=
        Nat.mul_lt_mul_of_pos_left hih hmul_pos
      have hrhs : 4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 * (3 * ((2 * m).factorial) ^ 2) =
          3 * ((2 * (m + 1)).factorial) ^ 2 := by
        rw [hfac2]
        ring
      have hpoly : (4 * (m + 1) - 1) * (4 * (m + 1) - 2) * (m + 1) ^ 2 ≤
          4 * (2 * m + 1) ^ 2 * (4 * m - 1) * (4 * m - 2) := by
        have ha : 4 * (m + 1) - 1 = 4 * t + 7 := by omega
        have hb : 4 * (m + 1) - 2 = 4 * t + 6 := by omega
        have hc : 4 * m - 1 = 4 * t + 3 := by omega
        have hd : 4 * m - 2 = 4 * t + 2 := by omega
        rw [ha, hb, hc, hd]
        dsimp only [m]
        nlinarith [sq_nonneg t, sq_nonneg (t * t)]
      have hlhs : (4 * (m + 1) - 1) * (4 * (m + 1) - 2) * ((m + 1).factorial) ^ 4 ≤
          4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 * ((4 * m - 1) * (4 * m - 2) * (m.factorial) ^ 4) := by
        rw [hfac1]
        have h1 : (4 * (m + 1) - 1) * (4 * (m + 1) - 2) * ((m + 1) * m.factorial) ^ 4 =
            ((4 * (m + 1) - 1) * (4 * (m + 1) - 2) * (m + 1) ^ 2) * ((m + 1) ^ 2 * (m.factorial) ^ 4) := by
          ring
        have h2 : 4 * (m + 1) ^ 2 * (2 * m + 1) ^ 2 * ((4 * m - 1) * (4 * m - 2) * (m.factorial) ^ 4) =
            (4 * (2 * m + 1) ^ 2 * (4 * m - 1) * (4 * m - 2)) * ((m + 1) ^ 2 * (m.factorial) ^ 4) := by
          ring
        rw [h1, h2]
        exact Nat.mul_le_mul_right _ hpoly
      exact lt_of_le_of_lt hlhs (hrhs ▸ hstep)

lemma annSet_reidx (r : ℕ) (b : V r → V r) (hb : Function.Bijective b) (p : Equiv.Perm (V r)) :
    annSet r b ((Equiv.ofBijective b hb).trans p) = annSet r id p := by
  let e := Equiv.ofBijective b hb
  ext u
  rw [annSet, annSet, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.trans_apply, id_eq]
  constructor
  · intro h x y
    have hxy := h (e.symm x) (e.symm y)
    have he : ∀ z : V r, b (e.symm z) = z := fun z => e.apply_symm_apply z
    simpa only [e, Equiv.apply_symm_apply, he] using hxy
  · intro h x y
    have he : ∀ z : V r, b z = e z := fun _ => rfl
    simpa only [he] using h (e x) (e y)

end PEqualNP.Outside.L_lib_667_aux

theorem PEqualNP.Outside.L_lib_667 : (∀ r : Nat, 2 ≤ r →
  let K := ZMod 2
  let V := Fin r → K
  let dot := fun (u v : V) => ∑ j, u j * v j
  let deficiency := fun (tags : V → V) (p : Equiv.Perm V) =>
    Nat.log 2 ((Finset.univ : Finset V).filter (fun normal =>
      ∀ x y : V, dot normal (p x + tags x) = dot normal (p y + tags y))).card
  let score := fun (b : V → V) => ∑ p : Equiv.Perm V, deficiency b p
  ∀ tags : V → V,
    score tags ≤ score id ∧ (score tags = score id ↔ Function.Bijective tags)) := by
  intro r hr K V dot deficiency score tags
  open PEqualNP.Outside.L_lib_667_aux in
  have hr1 : 1 ≤ r := by omega
  have hbij_eq : ∀ b : V → V, Function.Bijective b → score b = score id := by
    intro b hb
    let e : Equiv.Perm V := Equiv.ofBijective b hb
    let reidx : Equiv.Perm V ≃ Equiv.Perm V :=
      { toFun := fun p => e.trans p
        invFun := fun p => e.symm.trans p
        left_inv := fun p => by ext x; simp
        right_inv := fun p => by ext x; simp }
    dsimp only [score]
    have hsum := Equiv.sum_comp reidx (fun p => deficiency b p)
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (fun s : Finset (PEqualNP.Outside.L_lib_667_aux.V r) => Nat.log 2 s.card)
      (annSet_reidx r b hb p)
  by_cases hbij : Function.Bijective tags
  · have heq := hbij_eq tags hbij
    exact ⟨le_of_eq heq, ⟨fun _ => hbij, fun _ => heq⟩⟩
  · have hstrict : score tags < score id := by
      let N1 := fun b : V → V => ∑ p : Equiv.Perm V, ((annSet r b p).card - 1)
      have hscore_le_N1 : score tags ≤ N1 tags := by
        apply Finset.sum_le_sum
        intro p _
        have hpow := annSet_card_eq_pow r tags p
        have hdef : deficiency tags p = Nat.log 2 (annSet r tags p).card := rfl
        rw [hdef]
        conv_rhs => rw [hpow]
        exact ineq_pow2_log (Nat.log 2 (annSet r tags p).card)
      have hN1_double : ∀ b : V → V,
          N1 b = ∑ u ∈ (Finset.univ : Finset V).erase 0,
            (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r b p)).card := by
        intro b
        dsimp only [N1]
        have hterm : ∀ p : Equiv.Perm V,
            (annSet r b p).card - 1 =
              ∑ u ∈ (Finset.univ : Finset V).erase 0, if u ∈ annSet r b p then 1 else 0 := by
          intro p
          rw [Finset.sum_boole, Nat.cast_id]
          have hfilt : ((Finset.univ : Finset V).erase 0).filter (fun u => u ∈ annSet r b p) =
              (annSet r b p).erase 0 := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          rw [hfilt, Finset.card_erase_of_mem (zero_mem_annSet r b p)]
        simp_rw [hterm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_boole, Nat.cast_id]
      have hN1_id : N1 id = (2 ^ r - 1) * (2 * ((2 ^ (r - 1)).factorial) ^ 2) := by
        rw [hN1_double id]
        have hterm : ∀ u ∈ (Finset.univ : Finset V).erase 0,
            (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r id p)).card =
              2 * ((2 ^ (r - 1)).factorial) ^ 2 := by
          intro u hu
          have hne : u ≠ 0 := (Finset.mem_erase.mp hu).1
          rw [count_perm_mem_annSet r hr1 id u hne]
          have hbal := card_dot_eq r hr1 u hne 0
          simp only [id_eq, hbal, ↓reduceIte]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
        simp [V, K]
      have hN1_tags : N1 tags + 2 * ((2 ^ (r - 1)).factorial) ^ 2 ≤ N1 id := by
        rcases exists_unbalanced_of_not_bijective r hr1 tags hbij with ⟨u0, hu0, hunbal⟩
        rw [hN1_double tags, hN1_id]
        have hu0_mem : u0 ∈ (Finset.univ : Finset V).erase 0 :=
          Finset.mem_erase.mpr ⟨hu0, Finset.mem_univ u0⟩
        have hzero : (Finset.univ.filter (fun p : Equiv.Perm V => u0 ∈ annSet r tags p)).card = 0 := by
          rw [count_perm_mem_annSet r hr1 tags u0 hu0]
          simp only [hunbal, ↓reduceIte]
        have hle : ∀ u ∈ ((Finset.univ : Finset V).erase 0).erase u0,
            (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r tags p)).card ≤
              2 * ((2 ^ (r - 1)).factorial) ^ 2 := by
          intro u hu
          have hne : u ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
          rw [count_perm_mem_annSet r hr1 tags u hne]
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
        have hsplit : (∑ u ∈ (Finset.univ : Finset V).erase 0,
            (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r tags p)).card) =
            (Finset.univ.filter (fun p : Equiv.Perm V => u0 ∈ annSet r tags p)).card +
            ∑ u ∈ ((Finset.univ : Finset V).erase 0).erase u0,
              (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r tags p)).card :=
          (Finset.add_sum_erase _ _ hu0_mem).symm
        rw [hsplit, hzero, zero_add]
        have hsum_le : (∑ u ∈ ((Finset.univ : Finset V).erase 0).erase u0,
              (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r tags p)).card) ≤
            (((Finset.univ : Finset V).erase 0).erase u0).card * (2 * ((2 ^ (r - 1)).factorial) ^ 2) := by
          calc _ ≤ ∑ _ ∈ ((Finset.univ : Finset V).erase 0).erase u0,
                (2 * ((2 ^ (r - 1)).factorial) ^ 2) := Finset.sum_le_sum hle
            _ = _ := by rw [Finset.sum_const, smul_eq_mul]
        have hcard_er : (((Finset.univ : Finset V).erase 0).erase u0).card + 1 = 2 ^ r - 1 := by
          rw [Finset.card_erase_of_mem hu0_mem, Finset.card_erase_of_mem (Finset.mem_univ 0),
            Finset.card_univ]
          have hcardV : Fintype.card V = 2 ^ r := by simp [V, K]
          have h2 : 2 ≤ 2 ^ r := by
            have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
            omega
          rw [hcardV]
          omega
        calc (∑ u ∈ ((Finset.univ : Finset V).erase 0).erase u0,
                (Finset.univ.filter (fun p : Equiv.Perm V => u ∈ annSet r tags p)).card) +
              2 * ((2 ^ (r - 1)).factorial) ^ 2
            ≤ (((Finset.univ : Finset V).erase 0).erase u0).card * (2 * ((2 ^ (r - 1)).factorial) ^ 2) +
              2 * ((2 ^ (r - 1)).factorial) ^ 2 := Nat.add_le_add_right hsum_le _
          _ = ((((Finset.univ : Finset V).erase 0).erase u0).card + 1) * (2 * ((2 ^ (r - 1)).factorial) ^ 2) := by
              ring
          _ = (2 ^ r - 1) * (2 * ((2 ^ (r - 1)).factorial) ^ 2) := by rw [hcard_er]
      let N2 := ∑ p : Equiv.Perm V, ((annSet r id p).card - 1) * ((annSet r id p).card - 2)
      have hN2_val : N2 = (2 ^ r - 1) * (2 ^ r - 2) * (4 * ((2 ^ (r - 2)).factorial) ^ 4) := by
        dsimp only [N2]
        have hterm : ∀ p : Equiv.Perm V,
            ((annSet r id p).card - 1) * ((annSet r id p).card - 2) =
              ∑ uv ∈ ((Finset.univ : Finset V).erase 0).offDiag,
                if uv.1 ∈ annSet r id p ∧ uv.2 ∈ annSet r id p then 1 else 0 := by
          intro p
          rw [Finset.sum_boole, Nat.cast_id]
          have hfilt : (((Finset.univ : Finset V).erase 0).offDiag).filter
              (fun uv => uv.1 ∈ annSet r id p ∧ uv.2 ∈ annSet r id p) =
              ((annSet r id p).erase 0).offDiag := by
            ext ⟨u, v⟩
            simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_univ,
              and_true]
            tauto
          rw [hfilt, Finset.offDiag_card, Finset.card_erase_of_mem (zero_mem_annSet r id p)]
          have hge1 : 1 ≤ (annSet r id p).card :=
            Finset.card_pos.mpr ⟨0, zero_mem_annSet r id p⟩
          cases hc : (annSet r id p).card with
          | zero => omega
          | succ k =>
            cases k with
            | zero => simp
            | succ m =>
              have h1 : m + 1 + 1 - 1 = m + 1 := by omega
              have h2 : m + 1 + 1 - 2 = m := by omega
              rw [h1, h2]
              have : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
                have h3 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
                omega
              exact this.symm
        simp_rw [hterm]
        rw [Finset.sum_comm]
        have hinner : ∀ uv ∈ ((Finset.univ : Finset V).erase 0).offDiag,
            (∑ p : Equiv.Perm V, if uv.1 ∈ annSet r id p ∧ uv.2 ∈ annSet r id p then 1 else 0) =
              4 * ((2 ^ (r - 2)).factorial) ^ 4 := by
          intro uv huv
          rw [Finset.sum_boole, Nat.cast_id]
          rw [Finset.mem_offDiag] at huv
          have hu : uv.1 ≠ 0 := (Finset.mem_erase.mp huv.1).1
          have hv : uv.2 ≠ 0 := (Finset.mem_erase.mp huv.2.1).1
          exact count_perm_mem_annSet_pair r hr uv.1 uv.2 hu hv huv.2.2
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, Finset.offDiag_card,
          Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
        have hcardV : Fintype.card V = 2 ^ r := by simp [V, K]
        rw [hcardV]
        have h2 : 2 ≤ 2 ^ r := by
          have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
          omega
        have hmul : (2 ^ r - 1) * (2 ^ r - 1) - (2 ^ r - 1) = (2 ^ r - 1) * (2 ^ r - 2) := by
          have : (2 ^ r - 1) * (2 ^ r - 1) = (2 ^ r - 1) * (2 ^ r - 2) + (2 ^ r - 1) := by
            zify [h2, (by omega : 1 ≤ 2 ^ r)]
            ring
          omega
        rw [hmul]
      have hexcess : 6 * (N1 id - score id) ≤ N2 := by
        have hle_pt : ∀ p : Equiv.Perm V, deficiency id p ≤ (annSet r id p).card - 1 := by
          intro p
          have hpow := annSet_card_eq_pow r id p
          have hdef : deficiency id p = Nat.log 2 (annSet r id p).card := rfl
          rw [hdef]
          conv_rhs => rw [hpow]
          exact ineq_pow2_log (Nat.log 2 (annSet r id p).card)
        have hsub : N1 id - score id = ∑ p : Equiv.Perm V, ((annSet r id p).card - 1 - deficiency id p) := by
          dsimp only [N1, score]
          have hadd : (∑ p : Equiv.Perm V, ((annSet r id p).card - 1 - deficiency id p)) +
              (∑ p : Equiv.Perm V, deficiency id p) =
              ∑ p : Equiv.Perm V, ((annSet r id p).card - 1) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p _
            exact Nat.sub_add_cancel (hle_pt p)
          omega
        rw [hsub, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p _
        let c := Nat.log 2 (annSet r id p).card
        have hc : (annSet r id p).card = 2 ^ c := annSet_card_eq_pow r id p
        have hdef : deficiency id p = c := rfl
        rw [hdef, hc]
        exact ineq_six_excess c
      have hgap : N2 < 6 * (2 * ((2 ^ (r - 1)).factorial) ^ 2) := by
        rw [hN2_val]
        let m := 2 ^ (r - 2)
        have hm1 : 1 ≤ m := Nat.one_le_pow (r - 2) 2 (by omega)
        have h2m : 2 * m = 2 ^ (r - 1) := by
          dsimp only [m]
          have : r - 1 = (r - 2) + 1 := by omega
          conv_rhs => rw [this, pow_succ]
          ring
        have h4m : 4 * m = 2 ^ r := by
          dsimp only [m]
          have : r = (r - 2) + 2 := by omega
          conv_rhs => rw [this, pow_add]
          ring
        have hineq := factorial_gap_ineq m hm1
        rw [h4m, h2m] at hineq
        linarith
      have hsc_le : score id ≤ N1 id := by
        apply Finset.sum_le_sum
        intro p _
        have hpow := annSet_card_eq_pow r id p
        have hdef : deficiency id p = Nat.log 2 (annSet r id p).card := rfl
        rw [hdef]
        conv_rhs => rw [hpow]
        exact ineq_pow2_log (Nat.log 2 (annSet r id p).card)
      omega
    exact ⟨le_of_lt hstrict, ⟨fun h => absurd h (ne_of_lt hstrict), fun h => absurd h hbij⟩⟩
