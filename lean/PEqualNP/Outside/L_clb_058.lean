import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_058_aux

private theorem two_color_involutions {X : Type} [Fintype X] [DecidableEq X]
    (α β : X → X)
    (hα_inv : ∀ x, α (α x) = x) (hβ_inv : ∀ x, β (β x) = x)
    (hα_ne : ∀ x, α x ≠ x) (hβ_ne : ∀ x, β x ≠ x) :
    ∃ col : X → Bool, ∀ x, col (α x) = !(col x) ∧ col (β x) = !(col x) := by
  classical
  let f : X → X := fun x => β (α x)
  let fi : X → X := fun x => α (β x)
  have hfi_left : ∀ x, fi (f x) = x := fun x => by dsimp [f, fi]; rw [hβ_inv, hα_inv]
  have hfi_right : ∀ x, f (fi x) = x := fun x => by dsimp [f, fi]; rw [hα_inv, hβ_inv]
  have hα_conj : ∀ k x, α (f^[k] x) = fi^[k] (α x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change fi (α (f^[k] x)) = fi (fi^[k] (α x))
      rw [ih]
  have hfi_f_cancel : ∀ k x, fi^[k] (f^[k] x) = x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, hfi_left]
  have hf_fi_cancel : ∀ k x, f^[k] (fi^[k] x) = x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, hfi_right]
  have hno_cross : ∀ k x, α x ≠ f^[k] x := by
    intro k x heq
    have hsplit : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
    rcases hsplit with hk | hk
    · let r := k / 2
      have hk2 : k = r + r := by omega
      let y := f^[r] x
      have hy : α y = y := by
        dsimp only [y]
        rw [hα_conj r x, heq, hk2, Function.iterate_add_apply, hfi_f_cancel]
      exact hα_ne y hy
    · let r := k / 2
      have hk2 : k = r + (r + 1) := by omega
      let y := α (f^[r] x)
      have hy : β y = y := by
        have h1 : β y = f^[r + 1] x := by
          dsimp only [y]; rw [Function.iterate_succ_apply']
        have h2 : y = f^[r + 1] x := by
          dsimp only [y]
          rw [hα_conj r x, heq, hk2, Function.iterate_add_apply, hfi_f_cancel]
        rw [h1, h2]
      exact hβ_ne y hy
  have hmain : ∀ (m : ℕ) (A : Finset X), A.card ≤ m →
      (∀ x ∈ A, α x ∈ A) → (∀ x ∈ A, β x ∈ A) →
      ∃ col : X → Bool, ∀ x ∈ A, col (α x) = !(col x) ∧ col (β x) = !(col x) := by
    intro m
    induction m with
    | zero =>
      intro A hA _ _
      refine ⟨fun _ => false, fun x hx => ?_⟩
      have : A = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [this] at hx; simp at hx
    | succ m ih =>
      intro A hA hAα hAβ
      by_cases hAe : A = ∅
      · refine ⟨fun _ => false, fun x hx => ?_⟩
        rw [hAe] at hx; simp at hx
      · obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
        have hfA : ∀ k, f^[k] x0 ∈ A := by
          intro k
          induction k with
          | zero => exact hx0
          | succ k ihk => rw [Function.iterate_succ_apply']; exact hAβ _ (hAα _ ihk)
        let N := Fintype.card X + 1
        let O : Finset X := (Finset.range N).image (fun k => f^[k] x0)
        have hO_sub : O ⊆ A := by
          intro y hy; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy; exact hfA k
        have hO_all : ∀ k : ℕ, f^[k] x0 ∈ O := by
          intro k
          have hfin : ∃ p < N, ∃ q < N, p < q ∧ f^[p] x0 = f^[q] x0 := by
            have hcard : ((Finset.range N).image (fun t => f^[t] x0)).card ≤ Fintype.card X :=
              Finset.card_le_univ _
            have hnot_inj : ¬ Set.InjOn (fun t => f^[t] x0) (Finset.range N : Set ℕ) := by
              intro hinj
              have := Finset.card_image_of_injOn hinj
              rw [Finset.card_range] at this; omega
            simp only [Set.InjOn, Finset.mem_coe, Finset.mem_range, not_forall] at hnot_inj
            obtain ⟨p, hp, q, hq, hpq, hne⟩ := hnot_inj
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact ⟨p, hp, q, hq, hlt, hpq⟩
            · exact ⟨q, hq, p, hp, hgt, hpq.symm⟩
          obtain ⟨p, hp, q, hq, hpq, heq⟩ := hfin
          let per := q - p
          have hper_pos : 0 < per := by omega
          have hper0 : f^[per] x0 = x0 := by
            have h1 : f^[p] (f^[per] x0) = f^[p] x0 := by
              rw [← Function.iterate_add_apply, show p + per = q by omega, heq]
            have h2 := congrArg (fi^[p]) h1
            rwa [hfi_f_cancel, hfi_f_cancel] at h2
          have hmod : ∀ t, f^[t] x0 = f^[t % per] x0 := by
            intro t
            have hdiv : t = per * (t / per) + t % per := (Nat.div_add_mod t per).symm
            conv_lhs => rw [hdiv, Nat.add_comm, Function.iterate_add_apply]
            have hmul : ∀ c, f^[per * c] x0 = x0 := by
              intro c; induction c with
              | zero => rfl
              | succ c ihc => rw [Nat.mul_succ, Function.iterate_add_apply, hper0, ihc]
            rw [hmul]
          rw [hmod k]
          exact Finset.mem_image.mpr ⟨k % per, Finset.mem_range.mpr (by have := Nat.mod_lt k hper_pos; omega), rfl⟩
        have hO_f : ∀ y ∈ O, f y ∈ O := by
          intro y hy
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
          rw [← Function.iterate_succ_apply' f k x0]; exact hO_all (k + 1)
        have hO_fi : ∀ y ∈ O, fi y ∈ O := by
          intro y hy
          have hbij : O.image f = O := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz; exact hO_f u hu
            · have hf_inj : Function.Injective f := fun u v h => by
                have := congrArg fi h; rwa [hfi_left, hfi_left] at this
              rw [Finset.card_image_of_injective O hf_inj]
          rw [← hbij] at hy
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
          rwa [hfi_left]
        let O' : Finset X := O.image α
        have hO'_sub : O' ⊆ A := by
          intro y hy; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy; exact hAα u (hO_sub hu)
        have hdisj : Disjoint O O' := by
          rw [Finset.disjoint_left]
          intro y hyO hyO'
          obtain ⟨k1, _, rfl⟩ := Finset.mem_image.mp hyO
          obtain ⟨u, huO, hαu⟩ := Finset.mem_image.mp hyO'
          obtain ⟨k2, _, rfl⟩ := Finset.mem_image.mp huO
          have h1 : α (f^[k2] x0) = f^[k1] x0 := hαu
          have h2 : α x0 = f^[k2 + k1] x0 := by
            have h3 : fi^[k2] (α x0) = f^[k1] x0 := by rw [← hα_conj, h1]
            have h4 := congrArg (f^[k2]) h3
            rw [hf_fi_cancel, ← Function.iterate_add_apply] at h4
            exact h4
          exact hno_cross (k2 + k1) x0 h2
        have hβ_O' : ∀ y ∈ O', β y ∈ O := by
          intro y hy; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy; exact hO_f u hu
        have hβ_O : ∀ y ∈ O, β y ∈ O' := by
          intro y hy
          refine Finset.mem_image.mpr ⟨fi y, hO_fi y hy, ?_⟩
          dsimp [fi]; rw [hα_inv]
        let A' := A \ (O ∪ O')
        have hx0O : x0 ∈ O := hO_all 0
        have hA'_card : A'.card ≤ m := by
          have hsub : O ∪ O' ⊆ A := Finset.union_subset hO_sub hO'_sub
          have h1 : A'.card = A.card - (O ∪ O').card := by
            dsimp only [A']; rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
          have hle : (O ∪ O').card ≤ A.card := Finset.card_le_card hsub
          have hpos : 1 ≤ (O ∪ O').card := Finset.one_le_card.mpr ⟨x0, Finset.mem_union_left _ hx0O⟩
          omega
        have hA'_α : ∀ x ∈ A', α x ∈ A' := by
          intro x hx
          obtain ⟨hxA, hxnot⟩ := Finset.mem_sdiff.mp hx
          refine Finset.mem_sdiff.mpr ⟨hAα x hxA, ?_⟩
          intro hmem
          simp only [Finset.mem_union] at hmem hxnot
          rcases hmem with hO | hO'
          · exact hxnot (Or.inr (by rw [← hα_inv x]; exact Finset.mem_image.mpr ⟨α x, hO, rfl⟩))
          · obtain ⟨u, hu, huα⟩ := Finset.mem_image.mp hO'
            have hxu : x = u := (by have := congrArg α huα; rwa [hα_inv, hα_inv] at this : u = x).symm
            exact hxnot (Or.inl (hxu ▸ hu))
        have hA'_β : ∀ x ∈ A', β x ∈ A' := by
          intro x hx
          obtain ⟨hxA, hxnot⟩ := Finset.mem_sdiff.mp hx
          refine Finset.mem_sdiff.mpr ⟨hAβ x hxA, ?_⟩
          intro hmem
          simp only [Finset.mem_union] at hmem hxnot
          rcases hmem with hO | hO'
          · exact hxnot (Or.inr (by rw [← hβ_inv x]; exact hβ_O (β x) hO))
          · exact hxnot (Or.inl (by rw [← hβ_inv x]; exact hβ_O' (β x) hO'))
        obtain ⟨col', hcol'⟩ := ih A' hA'_card hA'_α hA'_β
        let col : X → Bool := fun x =>
          if x ∈ O then false else if x ∈ O' then true else col' x
        refine ⟨col, ?_⟩
        intro x hxA
        by_cases hxO : x ∈ O
        · have hαO' : α x ∈ O' := Finset.mem_image.mpr ⟨x, hxO, rfl⟩
          have hαnO : α x ∉ O := Finset.disjoint_right.mp hdisj hαO'
          have hβO' : β x ∈ O' := hβ_O x hxO
          have hβnO : β x ∉ O := Finset.disjoint_right.mp hdisj hβO'
          simp [col, hxO, hαO', hαnO, hβO', hβnO]
        · by_cases hxO' : x ∈ O'
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxO'
            have hαO : α (α u) ∈ O := by rwa [hα_inv]
            have hβO : β (α u) ∈ O := hβ_O' (α u) hxO'
            simp [col, hxO, hxO', hαO, hβO]
          · have hxA' : x ∈ A' := Finset.mem_sdiff.mpr ⟨hxA, by simp [hxO, hxO']⟩
            have hαA' : α x ∈ A' := hA'_α x hxA'
            have hβA' : β x ∈ A' := hA'_β x hxA'
            have hαn : α x ∉ O ∧ α x ∉ O' := by
              have := (Finset.mem_sdiff.mp hαA').2; simpa using this
            have hβn : β x ∉ O ∧ β x ∉ O' := by
              have := (Finset.mem_sdiff.mp hβA').2; simpa using this
            simp only [col, hxO, hxO', hαn.1, hαn.2, hβn.1, hβn.2, ↓reduceIte]
            exact hcol' x hxA'
  obtain ⟨col, hcol⟩ := hmain (Fintype.card X) Finset.univ le_rfl
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
  exact ⟨col, fun x => hcol x (Finset.mem_univ x)⟩

private def sched : (d : ℕ) → Fin (2 * d + 1) → Fin (d + 1)
  | 0, _ => 0
  | d + 1, ℓ =>
    if h0 : ℓ.val = 0 then 0
    else if h1 : ℓ.val ≤ 2 * d + 1 then (sched d ⟨ℓ.val - 1, by omega⟩).succ
    else 0

private def applySwitch {w : ℕ} (c : Fin w) (f : (Fin w → Bool) → Bool)
    (s : Fin w → Bool) : Fin w → Bool :=
  Function.update s c (xor (s c) (f s))

private def IsIndep {w : ℕ} (c : Fin w) (f : (Fin w → Bool) → Bool) : Prop :=
  ∀ s b, f (Function.update s c b) = f s

private theorem benes_decomp : ∀ (d : ℕ) (σ : Equiv.Perm (Fin (d + 1) → Bool)),
    ∃ flip : Fin (2 * d + 1) → (Fin (d + 1) → Bool) → Bool,
      (∀ ℓ, IsIndep (sched d ℓ) (flip ℓ)) ∧
      ∀ s, (List.finRange (2 * d + 1)).foldl
        (fun cur ℓ => applySwitch (sched d ℓ) (flip ℓ) cur) s = σ s := by
  intro d
  induction d with
  | zero =>
    intro σ
    refine ⟨fun _ _ => σ (fun _ => false) 0, fun _ _ _ => rfl, ?_⟩
    intro s
    have h0 : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.ext (by omega)
    change applySwitch 0 (fun _ => σ (fun _ => false) 0) s = σ s
    funext i
    rw [h0 i]
    simp only [applySwitch, Function.update_self]
    have h01 : σ (fun _ => true) 0 = !(σ (fun _ => false) 0) := by
      have hne : σ (fun _ => true) ≠ σ (fun _ => false) := by
        intro h; have := congrFun (σ.injective h) 0; simp at this
      by_contra heq
      apply hne; funext j; rw [h0 j]
      cases h1 : σ (fun _ => true) 0 <;> cases h2 : σ (fun _ => false) 0 <;> simp_all
    cases hs0 : s 0 with
    | false =>
      have hs : s = fun _ => false := by funext j; rw [h0 j]; exact hs0
      rw [hs]; simp
    | true =>
      have hs : s = fun _ => true := by funext j; rw [h0 j]; exact hs0
      rw [hs, h01]; cases σ (fun _ => false) 0 <;> rfl
  | succ d ih =>
    intro σ
    let w := d + 1
    let flip0 : (Fin (w + 1) → Bool) → (Fin (w + 1) → Bool) :=
      fun s => Function.update s 0 (!(s 0))
    have hflip0_inv : ∀ s, flip0 (flip0 s) = s := by
      intro s; funext i; refine Fin.cases (by simp [flip0]) (fun j => by simp [flip0]) i
    have hflip0_ne : ∀ s, flip0 s ≠ s := by
      intro s heq; have := congrFun heq 0; simp [flip0] at this
    let α := flip0
    let β : (Fin (w + 1) → Bool) → (Fin (w + 1) → Bool) := fun s => σ.symm (flip0 (σ s))
    have hβ_inv : ∀ s, β (β s) = s := by
      intro s; dsimp [β]; rw [Equiv.apply_symm_apply, hflip0_inv, Equiv.symm_apply_apply]
    have hβ_ne : ∀ s, β s ≠ s := by
      intro s heq; apply hflip0_ne (σ s)
      have := congrArg σ heq; dsimp [β] at this; rwa [Equiv.apply_symm_apply] at this
    obtain ⟨col, hcol⟩ := two_color_involutions α β hflip0_inv hβ_inv hflip0_ne hβ_ne
    let fFirst : (Fin (w + 1) → Bool) → Bool := fun s => xor (s 0) (col s)
    have hfFirst_indep : IsIndep 0 fFirst := by
      intro s b; dsimp only [fFirst]
      by_cases hb : b = s 0
      · rw [hb, Function.update_eq_self]
      · have hupd : Function.update s 0 b = flip0 s := by
          funext i; refine Fin.cases ?_ (fun j => by simp [flip0]) i
          simp only [Function.update_self, flip0]; cases hb0 : b <;> cases hs0 : s 0 <;> simp_all
        rw [hupd, (hcol s).1]; simp only [flip0, Function.update_self]
        cases s 0 <;> cases col s <;> rfl
    let L1 : (Fin (w + 1) → Bool) → (Fin (w + 1) → Bool) := applySwitch 0 fFirst
    have hL1_0 : ∀ s, L1 s 0 = col s := by
      intro s; simp [L1, applySwitch, fFirst]
    have hL1_succ : ∀ s (j : Fin w), L1 s j.succ = s j.succ := fun s j => by simp [L1, applySwitch]
    have hL1_inj : Function.Injective L1 := by
      intro s1 s2 heq
      have htail : ∀ j : Fin w, s1 j.succ = s2 j.succ := fun j => by
        have := congrFun heq j.succ; simpa [hL1_succ] using this
      have hc : col s1 = col s2 := by have := congrFun heq 0; rwa [hL1_0, hL1_0] at this
      funext i; refine Fin.cases ?_ htail i
      by_contra hne
      have hs2 : s2 = flip0 s1 := by
        funext k; refine Fin.cases ?_ (fun j => by simp [flip0, htail j]) k
        simp only [flip0, Function.update_self]; cases h1 : s1 0 <;> cases h2 : s2 0 <;> simp_all
      rw [hs2, (hcol s1).1] at hc; cases col s1 <;> simp at hc
    let eL1 : Equiv.Perm (Fin (w + 1) → Bool) := Equiv.ofBijective L1 (Finite.injective_iff_bijective.mp hL1_inj)
    let mid : Equiv.Perm (Fin (w + 1) → Bool) := eL1.symm.trans σ
    let stepMid (c : Bool) (u : Fin w → Bool) : Fin w → Bool :=
      fun j => (mid (Fin.cons c u)) j.succ
    have hstepMid_inj : ∀ c, Function.Injective (stepMid c) := by
      intro c u1 u2 heq
      let s1 := eL1.symm (Fin.cons c u1)
      let s2 := eL1.symm (Fin.cons c u2)
      have hc1 : col s1 = c := by
        have := congrFun (eL1.apply_symm_apply (Fin.cons c u1)) 0
        change L1 s1 0 = c at this; rwa [hL1_0] at this
      have hc2 : col s2 = c := by
        have := congrFun (eL1.apply_symm_apply (Fin.cons c u2)) 0
        change L1 s2 0 = c at this; rwa [hL1_0] at this
      have hσ_tail : ∀ j : Fin w, σ s1 j.succ = σ s2 j.succ := fun j => congrFun heq j
      have hσ_eq : σ s1 = σ s2 := by
        funext i; refine Fin.cases ?_ hσ_tail i
        by_contra hne
        have hflip : σ s2 = flip0 (σ s1) := by
          funext k; refine Fin.cases ?_ (fun j => by simp [flip0, hσ_tail j]) k
          simp only [flip0, Function.update_self]
          cases h1 : σ s1 0 <;> cases h2 : σ s2 0 <;> simp_all
        have hs2 : s2 = β s1 := by dsimp [β]; rw [← hflip, Equiv.symm_apply_apply]
        rw [hs2, (hcol s1).2] at hc2; rw [hc1] at hc2; cases c <;> simp at hc2
      have hcons : Fin.cons c u1 = Fin.cons c u2 := eL1.symm.injective (σ.injective hσ_eq)
      funext j; exact congrFun hcons j.succ
    let permMid (c : Bool) : Equiv.Perm (Fin w → Bool) :=
      Equiv.ofBijective (stepMid c) (Finite.injective_iff_bijective.mp (hstepMid_inj c))
    obtain ⟨fF, hfF_ind, hF_eq⟩ := ih (permMid false)
    obtain ⟨fT, hfT_ind, hT_eq⟩ := ih (permMid true)
    let outBit (c : Bool) (v : Fin w → Bool) : Bool :=
      mid (Fin.cons c ((permMid c).symm v)) 0
    have houtBit_ne : ∀ v, outBit true v = !(outBit false v) := by
      intro v
      have hne_in : (Fin.cons true ((permMid true).symm v) : Fin (w + 1) → Bool) ≠
          Fin.cons false ((permMid false).symm v) := by
        intro h; have := congrFun h 0; simp at this
      have hne_out : mid (Fin.cons true ((permMid true).symm v)) ≠
          mid (Fin.cons false ((permMid false).symm v)) := fun h => hne_in (mid.injective h)
      have htail_eq : ∀ j : Fin w,
          mid (Fin.cons true ((permMid true).symm v)) j.succ =
          mid (Fin.cons false ((permMid false).symm v)) j.succ := by
        intro j
        have h1 : stepMid true ((permMid true).symm v) j = v j :=
          congrFun ((permMid true).apply_symm_apply v) j
        have h2 : stepMid false ((permMid false).symm v) j = v j :=
          congrFun ((permMid false).apply_symm_apply v) j
        exact h1.trans h2.symm
      by_contra hsame
      apply hne_out; funext i; refine Fin.cases ?_ htail_eq i
      dsimp only [outBit] at hsame
      cases h1 : mid (Fin.cons true ((permMid true).symm v)) 0 <;>
        cases h2 : mid (Fin.cons false ((permMid false).symm v)) 0 <;> simp_all
    let fLast : (Fin (w + 1) → Bool) → Bool := fun s => outBit false (fun j => s j.succ)
    have hfLast_indep : IsIndep 0 fLast := by
      intro s b; simp [fLast]
    let flip : Fin (2 * (d + 1) + 1) → (Fin (w + 1) → Bool) → Bool := fun ℓ s =>
      if h0 : ℓ.val = 0 then fFirst s
      else if h1 : ℓ.val ≤ 2 * d + 1 then
        if s 0 then fT ⟨ℓ.val - 1, by omega⟩ (fun j => s j.succ)
        else fF ⟨ℓ.val - 1, by omega⟩ (fun j => s j.succ)
      else fLast s
    refine ⟨flip, ?_, ?_⟩
    · intro ℓ s b
      dsimp only [sched, flip]
      by_cases h0 : ℓ.val = 0
      · simp only [h0, ↓reduceDIte]; exact hfFirst_indep s b
      · by_cases h1 : ℓ.val ≤ 2 * d + 1
        · simp only [h0, h1, ↓reduceDIte]
          have h0_eq : Function.update s (sched d ⟨ℓ.val - 1, by omega⟩).succ b 0 = s 0 :=
            Function.update_of_ne (Fin.succ_ne_zero (sched d ⟨ℓ.val - 1, by omega⟩)).symm b s
          rw [h0_eq]
          have htail : (fun j : Fin w => Function.update s (sched d ⟨ℓ.val - 1, by omega⟩).succ b j.succ) =
              Function.update (fun j : Fin w => s j.succ) (sched d ⟨ℓ.val - 1, by omega⟩) b := by
            funext j
            by_cases hj : j = sched d ⟨ℓ.val - 1, by omega⟩
            · subst hj; simp
            · have hj' : j.succ ≠ (sched d ⟨ℓ.val - 1, by omega⟩).succ := fun h => hj (Fin.succ_injective _ h)
              simp [hj, hj']
          rw [htail]
          cases s 0
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact hfF_ind ⟨ℓ.val - 1, by omega⟩ _ b
          · simp only [↓reduceIte]; exact hfT_ind ⟨ℓ.val - 1, by omega⟩ _ b
        · simp only [h0, h1, ↓reduceDIte]; exact hfLast_indep s b
    · intro s
      have hlist : List.finRange (2 * (d + 1) + 1) =
          (0 : Fin (2 * (d + 1) + 1)) ::
          ((List.finRange (2 * d + 1)).map (fun k : Fin (2 * d + 1) => ⟨k.val + 1, by omega⟩) ++
            [Fin.last (2 * (d + 1))]) := by
        apply List.ext_getElem
        · simp; omega
        · intro i h1 h2
          simp only [List.getElem_finRange]
          cases i with
          | zero => ext; simp
          | succ i =>
            simp only [List.getElem_cons_succ]
            by_cases hi : i < 2 * d + 1
            · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_finRange]
              ext; simp
            · rw [List.getElem_append_right (by simp; omega)]
              have heq : i = 2 * d + 1 := by simp at h1; omega
              simp [heq]; ext; simp; omega
      rw [hlist, List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_map]
      have hstep0 : applySwitch (sched (d + 1) 0) (flip 0) s = L1 s := by
        simp [sched, flip, L1]
      rw [hstep0]
      let c := (L1 s) 0
      let u : Fin w → Bool := fun j => (L1 s) j.succ
      have hL1_cons : L1 s = Fin.cons c u := by
        funext i; refine Fin.cases rfl (fun j => rfl) i
      have hmid_fold : ∀ (ls : List (Fin (2 * d + 1))) (st : Fin w → Bool),
          ls.foldl (fun cur k =>
            applySwitch (sched (d + 1) ⟨k.val + 1, by omega⟩) (flip ⟨k.val + 1, by omega⟩) cur)
            (Fin.cons c st) =
          Fin.cons c (ls.foldl (fun cur k =>
            applySwitch (sched d k) (if c then fT k else fF k) cur) st) := by
        intro ls
        induction ls with
        | nil => intro st; rfl
        | cons k ls ih_ls =>
          intro st
          simp only [List.foldl_cons]
          have h1 : applySwitch (sched (d + 1) ⟨k.val + 1, by omega⟩) (flip ⟨k.val + 1, by omega⟩)
              (Fin.cons c st) =
              Fin.cons c (applySwitch (sched d k) (if c then fT k else fF k) st) := by
            have hk0 : ¬ (k.val + 1 = 0) := by omega
            have hk1 : k.val + 1 ≤ 2 * d + 1 := by omega
            have hkeq : (⟨k.val + 1 - 1, by omega⟩ : Fin (2 * d + 1)) = k := by ext; simp
            dsimp only [sched, flip]
            simp only [hk0, hk1, ↓reduceDIte, hkeq]
            funext i
            refine Fin.cases ?_ ?_ i
            · simp only [applySwitch, Fin.cons_zero]
              rw [Function.update_of_ne (Fin.succ_ne_zero _).symm]
              rfl
            · intro j
              simp only [applySwitch, Fin.cons_succ, Fin.cons_zero]
              by_cases hj : j = sched d k
              · subst hj; cases c <;> simp
              · have hj' : j.succ ≠ (sched d k).succ := fun h => hj (Fin.succ_injective _ h)
                cases c <;> simp [hj, hj']
          rw [h1, ih_ls]
      rw [hL1_cons, hmid_fold]
      have hperm_out : (List.finRange (2 * d + 1)).foldl
          (fun cur k => applySwitch (sched d k) (if c then fT k else fF k) cur) u =
          permMid c u := by
        cases hc : c
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hF_eq u
        · simp only [↓reduceIte]; exact hT_eq u
      rw [hperm_out]
      have hlast0 : ¬ ((Fin.last (2 * (d + 1))).val = 0) := by simp
      have hlast1 : ¬ ((Fin.last (2 * (d + 1))).val ≤ 2 * d + 1) := by simp; omega
      dsimp only [sched, flip]
      simp only [hlast0, hlast1, ↓reduceDIte]
      have hmid_eq : mid (Fin.cons c u) = σ s := by
        dsimp [mid]; rw [← hL1_cons]; change σ (eL1.symm (eL1 s)) = σ s; rw [Equiv.symm_apply_apply]
      rw [← hmid_eq]
      funext i
      refine Fin.cases ?_ ?_ i
      · simp only [applySwitch, Function.update_self, Fin.cons_zero, fLast, Fin.cons_succ]
        have hout_eq : mid (Fin.cons c u) 0 = outBit c (permMid c u) := by
          dsimp only [outBit]; rw [Equiv.symm_apply_apply]
        rw [hout_eq]
        cases hc : c
        · simp
        · rw [houtBit_ne]; cases outBit false (permMid true u) <;> rfl
      · intro j
        simp only [applySwitch]
        rw [Function.update_of_ne (Fin.succ_ne_zero _)]
        rfl

private def mkLayerBlock {d : ℕ} (_σ : Equiv.Perm (Fin (d + 1) → Bool))
    (flip : Fin (2 * d + 1) → (Fin (d + 1) → Bool) → Bool)
    (pos : Fin ((d + 1) * (2 * d + 1))) (pat : Fin (d + 1 + 1) → Bool) : Bool :=
  let w := d + 1
  let ℓ : Fin (2 * d + 1) := ⟨pos.val / w, Nat.div_lt_of_lt_mul (by have := pos.isLt; dsimp [w]; linarith)⟩
  let r : Fin w := ⟨pos.val % w, Nat.mod_lt _ (by omega)⟩
  let c := sched d ℓ
  if r = c then
    let sOther : Fin w → Bool := fun j =>
      if j = c then false
      else pat ⟨(j.val + w - c.val) % w, (Nat.mod_lt _ (by omega)).trans (by omega)⟩
    pat (Fin.last w) == xor (pat 0) (flip ℓ sOther)
  else
    pat (Fin.last w) == pat 0

private theorem mkLayerBlock_eq {d : ℕ} (σ : Equiv.Perm (Fin (d + 1) → Bool))
    (flip : Fin (2 * d + 1) → (Fin (d + 1) → Bool) → Bool)
    (ℓ : Fin (2 * d + 1)) (r : Fin (d + 1))
    (pos : Fin ((d + 1) * (2 * d + 1)))
    (hpos : pos.val = ℓ.val * (d + 1) + r.val)
    (pat : Fin (d + 1 + 1) → Bool) :
    mkLayerBlock σ flip pos pat =
      if r = sched d ℓ then
        let sOther : Fin (d + 1) → Bool := fun j =>
          if j = sched d ℓ then false
          else pat ⟨(j.val + (d + 1) - (sched d ℓ).val) % (d + 1), (Nat.mod_lt _ (by omega)).trans (by omega)⟩
        pat (Fin.last (d + 1)) == xor (pat 0) (flip ℓ sOther)
      else
        pat (Fin.last (d + 1)) == pat 0 := by
  dsimp only [mkLayerBlock]
  have hd : pos.val / (d + 1) = ℓ.val := by
    rw [hpos, Nat.mul_comm ℓ.val (d + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt r.isLt, add_zero]
  have hm : pos.val % (d + 1) = r.val := by
    rw [hpos, Nat.mul_comm ℓ.val (d + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
  have hℓ : (⟨pos.val / (d + 1), Nat.div_lt_of_lt_mul (by have := pos.isLt; linarith)⟩ : Fin (2 * d + 1)) = ℓ :=
    Fin.ext hd
  have hr : (⟨pos.val % (d + 1), Nat.mod_lt _ (by omega)⟩ : Fin (d + 1)) = r :=
    Fin.ext hm
  simp only [hℓ, hr]

set_option maxHeartbeats 1600000 in
private theorem main_aux : ∀ (d m t : ℕ),
  let w := d + 1
  let State := Fin w → Bool
  let blockLen := w * (2 * d + 1)
  let n := t * blockLen + w
  let hb : 0 < blockLen := by dsimp [blockLen, w]; positivity
  let hn : 0 < n := by dsimp [n, w]; positivity
  ∀ (query : Fin t → Fin m) (step : Fin t → Bool → Equiv.Perm State)
    (start finish : State),
    let Pattern := Fin (w + 1) → Bool
    ∃ (block : Fin t → Bool → Fin blockLen → Pattern → Bool)
      (pin : Fin w → Pattern → Bool),
      ∀ x : Fin m → Bool,
        let row := fun (i : Fin n) =>
          if h : i.val / blockLen < t then
            let instr : Fin t := ⟨i.val / blockLen, h⟩
            block instr (x (query instr)) ⟨i.val % blockLen, Nat.mod_lt _ hb⟩
          else
            pin (Fin.ofNat (d + 1) (i.val - t * blockLen))
        let ok := fun (word : Fin n → Bool) => ∀ j : Fin n,
          row j (fun k => word ⟨(j.val + k.val) % n, Nat.mod_lt _ hn⟩) = true
        let lastState := (List.finRange t).foldl (fun a s => step s (x (query s)) a) start
        (Finset.univ.filter ok).card = if lastState = finish then 1 else 0 := by
  classical
  intro d m t w State blockLen n hb hn query step start finish Pattern
  choose flip hflip_ind hflip_eq using fun (s : Fin t) (b : Bool) => benes_decomp d (step s b)
  let block : Fin t → Bool → Fin blockLen → Pattern → Bool :=
    fun s b pos pat => mkLayerBlock (step s b) (flip s b) pos pat
  let pin : Fin w → Pattern → Bool := fun r pat => (pat 0 == finish r) && (pat (Fin.last w) == start r)
  refine ⟨block, pin, ?_⟩
  intro x row ok lastState
  let win (word : Fin n → Bool) (pos : ℕ) : State :=
    fun k => word ⟨(pos + k.val) % n, Nat.mod_lt _ hn⟩
  have hlayer_iff : ∀ (word : Fin n → Bool) (s : Fin t) (ℓ : Fin (2 * d + 1)),
      (∀ r : Fin w,
        let jVal := s.val * blockLen + ℓ.val * w + r.val
        have hj : jVal < n := by
          have h1 : (s.val + 1) * blockLen ≤ t * blockLen := Nat.mul_le_mul_right _ s.isLt
          have h2 : (ℓ.val + 1) * w ≤ (2 * d + 1) * w := Nat.mul_le_mul_right _ ℓ.isLt
          have h3 : r.val < w := r.isLt
          dsimp [jVal, n, blockLen] at h1 h2 ⊢; nlinarith
        row ⟨jVal, hj⟩ (fun k => word ⟨(jVal + k.val) % n, Nat.mod_lt _ hn⟩) = true) ↔
      win word (s.val * blockLen + (ℓ.val + 1) * w) =
        applySwitch (sched d ℓ) (flip s (x (query s)) ℓ) (win word (s.val * blockLen + ℓ.val * w)) := by
    intro word s ℓ
    have hdiv_mod : ∀ r : Fin w,
        let jVal := s.val * blockLen + ℓ.val * w + r.val
        jVal / blockLen = s.val ∧ jVal % blockLen = ℓ.val * w + r.val ∧
        (ℓ.val * w + r.val) / w = ℓ.val ∧ (ℓ.val * w + r.val) % w = r.val := by
      intro r jVal
      have hrem_lt : ℓ.val * w + r.val < blockLen := by
        have h2 : (ℓ.val + 1) * w ≤ (2 * d + 1) * w := Nat.mul_le_mul_right _ ℓ.isLt
        have h3 : r.val < w := r.isLt
        dsimp [blockLen]; nlinarith
      have heq1 : jVal = blockLen * s.val + (ℓ.val * w + r.val) := by dsimp [jVal]; ring
      have h1 : jVal / blockLen = s.val := by
        rw [heq1, Nat.mul_add_div hb, Nat.div_eq_of_lt hrem_lt, add_zero]
      have h2 : jVal % blockLen = ℓ.val * w + r.val := by
        rw [heq1, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
      have h3 : (ℓ.val * w + r.val) / w = ℓ.val := by
        rw [Nat.mul_comm ℓ.val w, Nat.mul_add_div (by omega), Nat.div_eq_of_lt r.isLt, add_zero]
      have h4 : (ℓ.val * w + r.val) % w = r.val := by
        rw [Nat.mul_comm ℓ.val w, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
      exact ⟨h1, h2, h3, h4⟩
    let c := sched d ℓ
    have hother_eq : ∀ (hcopy : ∀ r : Fin w, r ≠ c →
        win word (s.val * blockLen + (ℓ.val + 1) * w) r = win word (s.val * blockLen + ℓ.val * w) r),
        (fun j : Fin w => if j = c then false
          else word ⟨(s.val * blockLen + ℓ.val * w + c.val +
            (j.val + w - c.val) % w) % n, Nat.mod_lt _ hn⟩) =
        Function.update (win word (s.val * blockLen + ℓ.val * w)) c false := by
      intro hcopy
      funext j
      by_cases hj : j = c
      · subst hj; simp
      · simp only [hj, ↓reduceIte]
        rw [Function.update_of_ne hj]
        by_cases hgt : c.val < j.val
        · have hm : (j.val + w - c.val) % w = j.val - c.val := by
            rw [show j.val + w - c.val = (j.val - c.val) + w by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          rw [hm]; dsimp only [win]; congr 1; apply Fin.ext; dsimp; congr 1; omega
        · have hlt : j.val < c.val := by have : j.val ≠ c.val := fun h => hj (Fin.ext h); omega
          have hm : (j.val + w - c.val) % w = j.val + w - c.val := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          rw [← hcopy j hj]; dsimp only [win]; congr 1; apply Fin.ext; dsimp; congr 1
          rw [Nat.add_mul, one_mul]; omega
    constructor
    · intro hall
      have hcopy : ∀ r : Fin w, r ≠ c →
          win word (s.val * blockLen + (ℓ.val + 1) * w) r = win word (s.val * blockLen + ℓ.val * w) r := by
        intro r hne
        have hr := hall r
        obtain ⟨hd1, hd2, _, _⟩ := hdiv_mod r
        dsimp only [row, block] at hr
        have hlt_t : (s.val * blockLen + ℓ.val * w + r.val) / blockLen < t := by rw [hd1]; exact s.isLt
        simp only [hlt_t, ↓reduceDIte] at hr
        have hs_eq : (⟨(s.val * blockLen + ℓ.val * w + r.val) / blockLen, hlt_t⟩ : Fin t) = s := Fin.ext hd1
        rw [hs_eq, mkLayerBlock_eq _ _ ℓ r _ hd2] at hr
        change (if r = c then _ else _) = true at hr
        simp only [hne, ↓reduceIte, beq_iff_eq] at hr
        unfold win
        have e1 : s.val * blockLen + ℓ.val * w + r.val + (Fin.last w).val =
            s.val * blockLen + (ℓ.val + 1) * w + r.val := by simp [Fin.val_last]; ring
        have e2 : s.val * blockLen + ℓ.val * w + r.val + (0 : Fin (w + 1)).val =
            s.val * blockLen + ℓ.val * w + r.val := by simp
        rwa [e1, e2] at hr
      funext r
      by_cases hrc : r = c
      · subst hrc
        have hr := hall c
        obtain ⟨hd1, hd2, _, _⟩ := hdiv_mod c
        dsimp only [row, block] at hr
        have hlt_t : (s.val * blockLen + ℓ.val * w + c.val) / blockLen < t := by rw [hd1]; exact s.isLt
        simp only [hlt_t, ↓reduceDIte] at hr
        have hs_eq : (⟨(s.val * blockLen + ℓ.val * w + c.val) / blockLen, hlt_t⟩ : Fin t) = s := Fin.ext hd1
        rw [hs_eq, mkLayerBlock_eq _ _ ℓ c _ hd2] at hr
        simp only [c, ↓reduceIte, beq_iff_eq] at hr
        have e1 : s.val * blockLen + ℓ.val * w + c.val + (Fin.last w).val =
            s.val * blockLen + (ℓ.val + 1) * w + c.val := by simp [Fin.val_last]; ring
        have e2 : s.val * blockLen + ℓ.val * w + c.val + (0 : Fin (w + 1)).val =
            s.val * blockLen + ℓ.val * w + c.val := by simp
        rw [e1, e2, hother_eq hcopy, hflip_ind s (x (query s)) ℓ] at hr
        simpa [applySwitch, win, c] using hr
      · simp only [applySwitch]
        rw [Function.update_of_ne hrc]
        exact hcopy r hrc
    · intro hsw r
      obtain ⟨hd1, hd2, _, _⟩ := hdiv_mod r
      dsimp only [row, block]
      have hlt_t : (s.val * blockLen + ℓ.val * w + r.val) / blockLen < t := by rw [hd1]; exact s.isLt
      simp only [hlt_t, ↓reduceDIte]
      have hs_eq : (⟨(s.val * blockLen + ℓ.val * w + r.val) / blockLen, hlt_t⟩ : Fin t) = s := Fin.ext hd1
      rw [hs_eq, mkLayerBlock_eq _ _ ℓ r _ hd2]
      have hcopy : ∀ r' : Fin w, r' ≠ c →
          win word (s.val * blockLen + (ℓ.val + 1) * w) r' = win word (s.val * blockLen + ℓ.val * w) r' := by
        intro r' hne; have := congrFun hsw r'; simpa [applySwitch, c, hne] using this
      by_cases hrc : r = c
      · subst hrc
        simp only [c, ↓reduceIte, beq_iff_eq]
        have e1 : s.val * blockLen + ℓ.val * w + c.val + (Fin.last w).val =
            s.val * blockLen + (ℓ.val + 1) * w + c.val := by simp [Fin.val_last]; ring
        have e2 : s.val * blockLen + ℓ.val * w + c.val + (0 : Fin (w + 1)).val =
            s.val * blockLen + ℓ.val * w + c.val := by simp
        rw [e1, e2, hother_eq hcopy, hflip_ind s (x (query s)) ℓ]
        have := congrFun hsw c; simpa [applySwitch, win, c] using this
      · change (if r = c then _ else _) = true
        simp only [hrc, ↓reduceIte, beq_iff_eq]
        have e1 : s.val * blockLen + ℓ.val * w + r.val + (Fin.last w).val =
            s.val * blockLen + (ℓ.val + 1) * w + r.val := by simp [Fin.val_last]; ring
        have e2 : s.val * blockLen + ℓ.val * w + r.val + (0 : Fin (w + 1)).val =
            s.val * blockLen + ℓ.val * w + r.val := by simp
        rw [e1, e2]; exact hcopy r hrc
  have hpin_iff : ∀ word : Fin n → Bool,
      (∀ r : Fin w,
        have hj : t * blockLen + r.val < n := by dsimp [n]; omega
        row ⟨t * blockLen + r.val, hj⟩
          (fun k => word ⟨(t * blockLen + r.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) ↔
      (win word (t * blockLen) = finish ∧ win word 0 = start) := by
    intro word
    have hnot : ∀ r : Fin w, ¬ ((t * blockLen + r.val) / blockLen < t) := by
      intro r
      have h1 : t * blockLen ≤ t * blockLen + r.val := by omega
      have := Nat.div_le_div_right (c := blockLen) h1
      rw [Nat.mul_div_cancel t hb] at this; omega
    constructor
    · intro hall
      constructor <;> funext r
      · have hr := hall r
        dsimp only [row, pin] at hr
        simp only [hnot r, ↓reduceDIte, Nat.add_sub_cancel_left, Bool.and_eq_true, beq_iff_eq] at hr
        have hof : (Fin.ofNat (d + 1) r.val : Fin w) = r := by ext; simp
        rw [hof] at hr; simpa [win] using hr.1
      · have hr := hall r
        dsimp only [row, pin] at hr
        simp only [hnot r, ↓reduceDIte, Nat.add_sub_cancel_left, Bool.and_eq_true, beq_iff_eq] at hr
        have hof : (Fin.ofNat (d + 1) r.val : Fin w) = r := by ext; simp
        rw [hof] at hr
        have emod : (t * blockLen + r.val + (Fin.last w).val) % n = (0 + r.val) % n := by
          simp only [Fin.val_last, zero_add]
          rw [show t * blockLen + r.val + w = r.val + n by dsimp [n]; ring, Nat.add_mod_right]
        have hidx : (⟨(t * blockLen + r.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
            ⟨(0 + r.val) % n, Nat.mod_lt _ hn⟩ := Fin.ext emod
        dsimp only [win]; rw [← hidx]; exact hr.2
    · rintro ⟨hfin, hst⟩ r
      dsimp only [row, pin]
      simp only [hnot r, ↓reduceDIte, Nat.add_sub_cancel_left, Bool.and_eq_true, beq_iff_eq]
      have hof : (Fin.ofNat (d + 1) r.val : Fin w) = r := by ext; simp
      rw [hof]
      constructor
      · simpa [win] using congrFun hfin r
      · have emod : (t * blockLen + r.val + (Fin.last w).val) % n = (0 + r.val) % n := by
          simp only [Fin.val_last, zero_add]
          rw [show t * blockLen + r.val + w = r.val + n by dsimp [n]; ring, Nat.add_mod_right]
        have hidx : (⟨(t * blockLen + r.val + (Fin.last w).val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
            ⟨(0 + r.val) % n, Nat.mod_lt _ hn⟩ := Fin.ext emod
        rw [hidx]; exact congrFun hst r
  have hok_iff : ∀ word : Fin n → Bool, ok word ↔
      win word 0 = start ∧ win word (t * blockLen) = finish ∧
      ∀ (s : Fin t) (ℓ : Fin (2 * d + 1)),
        win word (s.val * blockLen + (ℓ.val + 1) * w) =
          applySwitch (sched d ℓ) (flip s (x (query s)) ℓ) (win word (s.val * blockLen + ℓ.val * w)) := by
    intro word
    constructor
    · intro hok
      have hp := (hpin_iff word).mp (fun r => hok ⟨t * blockLen + r.val, by dsimp [n]; omega⟩)
      refine ⟨hp.2, hp.1, fun s ℓ => (hlayer_iff word s ℓ).mp (fun r => hok _)⟩
    · rintro ⟨hst, hfin, hlay⟩ j
      by_cases hj : j.val < t * blockLen
      · let s : Fin t := ⟨j.val / blockLen, Nat.div_lt_of_lt_mul (by linarith)⟩
        let rem := j.val % blockLen
        have hrem : rem < blockLen := Nat.mod_lt _ hb
        let ℓ : Fin (2 * d + 1) := ⟨rem / w, Nat.div_lt_of_lt_mul (by dsimp [blockLen] at hrem; linarith)⟩
        let r : Fin w := ⟨rem % w, Nat.mod_lt _ (by omega)⟩
        have hjeq : j.val = s.val * blockLen + ℓ.val * w + r.val := by
          have h1 := Nat.div_add_mod j.val blockLen
          have h2 := Nat.div_add_mod rem w
          dsimp [s, ℓ, r, rem] at h1 h2 ⊢; linarith
        have h := (hlayer_iff word s ℓ).mpr (hlay s ℓ) r
        convert h using 2
        · ext; exact hjeq
        · funext k; congr 1; ext; dsimp; rw [hjeq]
      · let r : Fin w := ⟨j.val - t * blockLen, by have := j.isLt; dsimp [n] at this; omega⟩
        have hjeq : j.val = t * blockLen + r.val := by dsimp [r]; omega
        have h := (hpin_iff word).mpr ⟨hfin, hst⟩ r
        convert h using 2
        · ext; exact hjeq
        · funext k; congr 1; ext; dsimp; rw [hjeq]
  let blockState (k : ℕ) : State :=
    ((List.finRange t).take k).foldl (fun a s => step s (x (query s)) a) start
  let layerState (s : Fin t) (ℓ : ℕ) : State :=
    ((List.finRange (2 * d + 1)).take ℓ).foldl
      (fun cur j => applySwitch (sched d j) (flip s (x (query s)) j) cur) (blockState s.val)
  have hlayerState_succ : ∀ (s : Fin t) (ℓ : Fin (2 * d + 1)),
      layerState s (ℓ.val + 1) =
        applySwitch (sched d ℓ) (flip s (x (query s)) ℓ) (layerState s ℓ.val) := by
    intro s ℓ
    dsimp only [layerState]
    have hlt : ℓ.val < (List.finRange (2 * d + 1)).length := by simp [ℓ.isLt]
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp
  have hlayerState_end : ∀ (s : Fin t), layerState s (2 * d + 1) = blockState (s.val + 1) := by
    intro s
    dsimp only [layerState, blockState]
    rw [List.take_of_length_le (l := List.finRange (2 * d + 1)) (by simp), hflip_eq s (x (query s))]
    have hlt : s.val < (List.finRange t).length := by simp [s.isLt]
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp
  let canonWord : Fin n → Bool := fun p =>
    let q := p.val / w
    let r : Fin w := ⟨p.val % w, Nat.mod_lt _ (by omega)⟩
    if hq : q < t * (2 * d + 1) then
      let s : Fin t := ⟨q / (2 * d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩
      layerState s (q % (2 * d + 1)) r
    else
      blockState t r
  have hwin_canon : ∀ (q : ℕ) (hq : q ≤ t * (2 * d + 1)),
      win canonWord (q * w) =
        if h : q < t * (2 * d + 1) then
          layerState ⟨q / (2 * d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩ (q % (2 * d + 1))
        else blockState t := by
    intro q hq
    funext r
    unfold win
    have hlt_n : q * w + r.val < n := by
      have h1 : q * w ≤ (t * (2 * d + 1)) * w := Nat.mul_le_mul_right _ hq
      dsimp [n, blockLen]; nlinarith [r.isLt]
    have hidx : (⟨(q * w + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨q * w + r.val, hlt_n⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hlt_n)
    rw [hidx]
    dsimp only [canonWord]
    have hd : (q * w + r.val) / w = q := by
      rw [Nat.mul_comm q w, Nat.mul_add_div (by omega), Nat.div_eq_of_lt r.isLt, add_zero]
    have hm : (q * w + r.val) % w = r.val := by
      rw [Nat.mul_comm q w, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
    have hr_fin : (⟨(q * w + r.val) % w, Nat.mod_lt _ (by omega)⟩ : Fin w) = r := Fin.ext hm
    simp only [hd, hr_fin]
    split_ifs <;> rfl
  have hblock_unique : ∀ word, ok word →
      ∀ (s : ℕ) (hs : s ≤ t), win word (s * blockLen) = blockState s := by
    intro word hok s hs
    obtain ⟨hst, _, hlay⟩ := (hok_iff word).mp hok
    induction s with
    | zero => simpa [blockState] using hst
    | succ s ih =>
      have hprev := ih (by omega)
      let sf : Fin t := ⟨s, hs⟩
      have hinner : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ 2 * d + 1),
          win word (s * blockLen + ℓ * w) = layerState sf ℓ := by
        intro ℓ hℓ
        induction ℓ with
        | zero => simpa [layerState] using hprev
        | succ ℓ ihℓ =>
          rw [hlay sf ⟨ℓ, hℓ⟩, ihℓ (by omega), hlayerState_succ sf ⟨ℓ, hℓ⟩]
      have hend := hinner (2 * d + 1) le_rfl
      rw [hlayerState_end sf] at hend
      have heq : s * blockLen + (2 * d + 1) * w = (s + 1) * blockLen := by dsimp [blockLen]; ring
      rwa [heq] at hend
  have hlast_eq : blockState t = lastState := by
    dsimp [blockState, lastState]; rw [List.take_of_length_le (by simp)]
  by_cases hgood : lastState = finish
  · simp only [hgood, ↓reduceIte]
    have hcanon_ok : ok canonWord := by
      rw [hok_iff]
      refine ⟨?_, ?_, ?_⟩
      · have h0 := hwin_canon 0 (by omega)
        simp only [zero_mul] at h0
        rw [h0]
        by_cases ht0 : 0 < t * (2 * d + 1)
        · simp [ht0, layerState, blockState]
        · have ht_eq : t = 0 := by nlinarith
          subst ht_eq; simp [blockState]
      · have hL := hwin_canon (t * (2 * d + 1)) le_rfl
        have heq : t * (2 * d + 1) * w = t * blockLen := by dsimp [blockLen]; ring
        rw [heq] at hL; rw [hL]; simp [hlast_eq, hgood]
      · intro s ℓ
        let q1 := s.val * (2 * d + 1) + ℓ.val
        have hq1 : q1 < t * (2 * d + 1) := by
          have : (s.val + 1) * (2 * d + 1) ≤ t * (2 * d + 1) := Nat.mul_le_mul_right _ s.isLt
          dsimp [q1]; nlinarith [ℓ.isLt]
        have hw1 := hwin_canon q1 (by omega)
        have hw2 := hwin_canon (q1 + 1) (by omega)
        have e1 : q1 * w = s.val * blockLen + ℓ.val * w := by dsimp [q1, blockLen]; ring
        have e2 : (q1 + 1) * w = s.val * blockLen + (ℓ.val + 1) * w := by dsimp [q1, blockLen]; ring
        rw [e1] at hw1; rw [e2] at hw2
        have hd1 : q1 / (2 * d + 1) = s.val := by
          dsimp [q1]; rw [Nat.mul_comm s.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ℓ.isLt, add_zero]
        have hm1 : q1 % (2 * d + 1) = ℓ.val := by
          dsimp [q1]; rw [Nat.mul_comm s.val, Nat.mul_add_mod, Nat.mod_eq_of_lt ℓ.isLt]
        simp only [hq1, ↓reduceDIte] at hw1
        have hs1 : (⟨q1 / (2 * d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin t) = s := Fin.ext hd1
        rw [hs1, hm1] at hw1
        rw [hw1, hw2, ← hlayerState_succ s ℓ]
        by_cases hℓlast : ℓ.val + 1 < 2 * d + 1
        · have hq2 : q1 + 1 < t * (2 * d + 1) := by
            have : (s.val + 1) * (2 * d + 1) ≤ t * (2 * d + 1) := Nat.mul_le_mul_right _ s.isLt
            dsimp [q1]; nlinarith
          simp only [hq2, ↓reduceDIte]
          have hd2 : (q1 + 1) / (2 * d + 1) = s.val := by
            rw [show q1 + 1 = (2 * d + 1) * s.val + (ℓ.val + 1) by dsimp [q1]; ring,
              Nat.mul_add_div (by omega), Nat.div_eq_of_lt hℓlast, add_zero]
          have hm2 : (q1 + 1) % (2 * d + 1) = ℓ.val + 1 := by
            rw [show q1 + 1 = (2 * d + 1) * s.val + (ℓ.val + 1) by dsimp [q1]; ring,
              Nat.mul_add_mod, Nat.mod_eq_of_lt hℓlast]
          have hs2 : (⟨(q1 + 1) / (2 * d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩ : Fin t) = s := Fin.ext hd2
          rw [hs2, hm2]
        · have hℓeq : ℓ.val + 1 = 2 * d + 1 := by omega
          rw [hℓeq, hlayerState_end s]
          by_cases hq2 : q1 + 1 < t * (2 * d + 1)
          · simp only [hq2, ↓reduceDIte]
            have hq2eq : q1 + 1 = (s.val + 1) * (2 * d + 1) := by dsimp [q1]; nlinarith
            have hd2 : (q1 + 1) / (2 * d + 1) = s.val + 1 := by
              rw [hq2eq, Nat.mul_div_cancel _ (by omega)]
            have hm2 : (q1 + 1) % (2 * d + 1) = 0 := by
              rw [hq2eq, Nat.mul_mod_left]
            simp only [hm2, layerState, List.take_zero, List.foldl_nil]
            congr 1
          · simp only [hq2, ↓reduceDIte]
            have hq2eq : q1 + 1 = (s.val + 1) * (2 * d + 1) := by dsimp [q1]; nlinarith
            have hseq : s.val + 1 = t := by nlinarith
            rw [hseq]
    have hset : Finset.univ.filter ok = {canonWord} := by
      ext word
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hok
        obtain ⟨_, _, hlay⟩ := (hok_iff word).mp hok
        have hall_q : ∀ q ≤ t * (2 * d + 1), win word (q * w) = win canonWord (q * w) := by
          intro q hq
          rw [hwin_canon q hq]
          by_cases hlt : q < t * (2 * d + 1)
          · simp only [hlt, ↓reduceDIte]
            let s : Fin t := ⟨q / (2 * d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩
            have hbase := hblock_unique word hok s.val (by omega)
            have hinner : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ 2 * d + 1),
                win word (s.val * blockLen + ℓ * w) = layerState s ℓ := by
              intro ℓ hℓ
              induction ℓ with
              | zero => simpa [layerState] using hbase
              | succ ℓ ihℓ => rw [hlay s ⟨ℓ, hℓ⟩, ihℓ (by omega), hlayerState_succ s ⟨ℓ, hℓ⟩]
            have heq : q * w = s.val * blockLen + (q % (2 * d + 1)) * w := by
              have hdm := Nat.div_add_mod q (2 * d + 1)
              dsimp [s, blockLen]; nlinarith
            rw [heq]; exact hinner (q % (2 * d + 1)) (Nat.le_of_lt (Nat.mod_lt _ (by omega)))
          · simp only [hlt, ↓reduceDIte]
            have hqe : q = t * (2 * d + 1) := by omega
            have heq : q * w = t * blockLen := by rw [hqe]; dsimp [blockLen]; ring
            rw [heq]; exact hblock_unique word hok t le_rfl
        funext p
        let q := p.val / w
        let r : Fin w := ⟨p.val % w, Nat.mod_lt _ (by omega)⟩
        have hq : q ≤ t * (2 * d + 1) := by
          have hp : p.val < (t * (2 * d + 1) + 1) * w := by
            have := p.isLt; dsimp [n, blockLen] at this ⊢; nlinarith
          have : q < t * (2 * d + 1) + 1 := Nat.div_lt_of_lt_mul (by linarith)
          omega
        have h := congrFun (hall_q q hq) r
        unfold win at h
        have hsum : q * w + r.val = p.val := by
          dsimp [q, r]; have := Nat.div_add_mod p.val w; linarith
        have hmod : (q * w + r.val) % n = p.val := by rw [hsum, Nat.mod_eq_of_lt p.isLt]
        have hp_eq : (⟨(q * w + r.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = p := Fin.ext hmod
        rwa [hp_eq] at h
      · rintro rfl; exact hcanon_ok
    rw [hset, Finset.card_singleton]
  · simp only [hgood, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro word _ hok
    have h1 := hblock_unique word hok t le_rfl
    have h2 := ((hok_iff word).mp hok).2.1
    rw [h2, hlast_eq] at h1
    exact hgood h1.symm

end PEqualNP.Outside.L_clb_058_aux

theorem PEqualNP.Outside.L_clb_058 : (∀ (d m t : ℕ),
  let w := d + 1
  let State := Fin w → Bool
  let blockLen := w * (2 * d + 1)
  let n := t * blockLen + w
  let hb : 0 < blockLen := by dsimp [blockLen, w]; positivity
  let hn : 0 < n := by dsimp [n, w]; positivity
  ∀ (query : Fin t → Fin m) (step : Fin t → Bool → Equiv.Perm State)
    (start finish : State),
    let Pattern := Fin (w + 1) → Bool
    ∃ (block : Fin t → Bool → Fin blockLen → Pattern → Bool)
      (pin : Fin w → Pattern → Bool),
      ∀ x : Fin m → Bool,
        let row := fun (i : Fin n) =>
          if h : i.val / blockLen < t then
            let instr : Fin t := ⟨i.val / blockLen, h⟩
            block instr (x (query instr)) ⟨i.val % blockLen, Nat.mod_lt _ hb⟩
          else
            pin (Fin.ofNat (d + 1) (i.val - t * blockLen))
        let ok := fun (word : Fin n → Bool) => ∀ j : Fin n,
          row j (fun k => word ⟨(j.val + k.val) % n, Nat.mod_lt _ hn⟩) = true
        let lastState := (List.finRange t).foldl (fun a s => step s (x (query s)) a) start
        (Finset.univ.filter ok).card = if lastState = finish then 1 else 0) :=
  PEqualNP.Outside.L_clb_058_aux.main_aux
