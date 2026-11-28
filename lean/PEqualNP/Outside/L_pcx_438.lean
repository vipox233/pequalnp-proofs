import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_438_aux

noncomputable def dec {m h d : ℕ} (hm : 0 < m) (anchor : Fin m → Fin d → Bool)
    (slot : Fin m → Fin h ↪ Fin d) (z : Fin d → Bool) : Fin m := by
  classical
  exact if hh : ∃ i, ∀ p, (∀ b, slot i b ≠ p) → z p = anchor i p then hh.choose else ⟨0, hm⟩

theorem dec_eq {m h d : ℕ} (hm : 0 < m) (anchor : Fin m → Fin d → Bool)
    (slot : Fin m → Fin h ↪ Fin d)
    (hsep : ∀ i j, i ≠ j → ∃ p, (∀ b, slot i b ≠ p) ∧ (∀ b, slot j b ≠ p) ∧ anchor i p ≠ anchor j p)
    (z : Fin d → Bool) (i : Fin m) (hi : ∀ p, (∀ b, slot i b ≠ p) → z p = anchor i p) :
    dec hm anchor slot z = i := by
  classical
  unfold dec
  have hex : ∃ i, ∀ p, (∀ b, slot i b ≠ p) → z p = anchor i p := ⟨i, hi⟩
  rw [dif_pos hex]
  by_contra hne
  obtain ⟨p, h1, h2, h3⟩ := hsep _ _ hne
  exact h3 ((hex.choose_spec p h1).symm.trans (hi p h2))

end PEqualNP.Outside.L_pcx_438_aux

open PEqualNP.Outside.L_pcx_438_aux

theorem PEqualNP.Outside.L_pcx_438 : (∀ (X U : Type) (m h e d : ℕ), 0 < m →
  let I := Fin m
  let J := Fin h
  let W := J → Bool
  let T := Fin e → Bool
  let Z := Fin d → Bool
  ∀ (ok : X → I → Prop) (vis : U → I → W) (tail : U → I → T)
    (slot : I → J ↪ Fin d),
    (∀ x, ∃ i, ok x i) → (∀ i, ∃ x, ∀ j, ok x j ↔ j = i) →
    (∀ i (v : W) (t : T), ∃ u, vis u i = v ∧ tail u i = t ∧
      ∀ k, k ≠ i → ∀ b, vis u k b = false) →
    ((∃ (first : Fin d → X → (I → W) → Bool) (last : Z → X → U → T)
        (out : Z → T → I × W × T),
      ∀ x u,
        let z : Z := fun p => first p x (fun i b => decide (slot i b = p) && vis u i b)
        let ans := out z (last z x u)
        ok x ans.1 ∧ ans.2.1 = vis u ans.1 ∧ ans.2.2 = tail u ans.1) ↔
    ∃ anchor : I → Z, ∀ i j, i ≠ j → ∃ p,
      (∀ b, slot i b ≠ p) ∧ (∀ b, slot j b ≠ p) ∧ anchor i p ≠ anchor j p)) := by
  intro X U m h e d hm I J W T Z ok vis tail slot hok hx hu
  classical
  constructor
  · rintro ⟨first, last, out, H⟩
    choose xs hxs using hx
    choose uu hU1 hU2 hU3 using hu
    let t0 : T := fun _ => false
    let zz : I → W → Z := fun i v p =>
      first p (xs i) (fun k b => decide (slot k b = p) && vis (uu i v t0) k b)
    have hvis : ∀ i v t, vis (uu i v t) = vis (uu i v t0) := by
      intro i v t
      funext k b
      by_cases hk : k = i
      · subst hk; rw [hU1, hU1]
      · rw [hU3 _ _ _ k hk, hU3 _ _ _ k hk]
    have hout : ∀ i v t, out (zz i v) (last (zz i v) (xs i) (uu i v t)) = (i, v, t) := by
      intro i v t
      have H1 := H (xs i) (uu i v t)
      simp only [hvis] at H1
      obtain ⟨h1, h2, h3⟩ := H1
      have hi : (out (zz i v) (last (zz i v) (xs i) (uu i v t))).1 = i := (hxs i _).1 h1
      rw [hi] at h2 h3
      rw [hvis, hU1] at h2
      rw [hU2] at h3
      exact Prod.ext hi (Prod.ext h2 h3)
    have hinj : ∀ i j v w, zz i v = zz j w → i = j ∧ v = w := by
      intro i j v w hz
      let g : T → T := fun t => last (zz i v) (xs i) (uu i v t)
      have ginj : Function.Injective g := by
        intro t t' htt
        have a := hout i v t
        have b := hout i v t'
        have : (i, v, t) = (i, v, t') := by
          rw [← a, ← b]; exact congrArg (out (zz i v)) htt
        simpa using this
      obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 ginj)
        (last (zz j w) (xs j) (uu j w t0))
      have a := hout i v t
      have b := hout j w t0
      have : (i, v, t) = (j, w, t0) := by
        rw [← a, ← b]; simp only [g] at ht; rw [ht, hz]
      simp only [Prod.mk.injEq] at this
      exact ⟨this.1, this.2.1⟩
    let anchor : I → Z := fun i => zz i (fun _ => false)
    have L1 : ∀ i v p, (∀ b, slot i b ≠ p) → zz i v p = anchor i p := by
      intro i v p hp
      simp only [zz, anchor]
      congr 1
      funext k b
      by_cases hk : k = i
      · subst hk; simp [hp b]
      · rw [hU3 _ _ _ k hk, hU3 _ _ _ k hk]
    have L2 : ∀ i v v' b, v b = v' b → zz i v (slot i b) = zz i v' (slot i b) := by
      intro i v v' b hb
      simp only [zz]
      congr 1
      funext k b'
      by_cases hk : k = i
      · subst hk
        rw [hU1, hU1]
        by_cases hb' : b' = b
        · subst hb'; rw [hb]
        · have : slot k b' ≠ slot k b := fun e => hb' ((slot k).injective e)
          simp [this]
      · rw [hU3 _ _ _ k hk, hU3 _ _ _ k hk]
    have hit : ∀ i (z' : Z), (∀ p, (∀ b, slot i b ≠ p) → z' p = anchor i p) →
        ∃ v, zz i v = z' := by
      intro i z' hz'
      refine ⟨fun b => xor (anchor i (slot i b)) (z' (slot i b)), ?_⟩
      funext p
      by_cases hp : ∃ b, slot i b = p
      · obtain ⟨b, rfl⟩ := hp
        let δ : W := fun b' => decide (b' = b)
        have hdiff : zz i (fun _ => false) (slot i b) ≠ zz i δ (slot i b) := by
          intro heq
          have hall : zz i (fun _ => false) = zz i δ := by
            funext q
            by_cases hq : ∃ b', slot i b' = q
            · obtain ⟨b', rfl⟩ := hq
              by_cases hbb : b' = b
              · subst hbb; exact heq
              · exact L2 i _ _ b' (by simp [δ, hbb])
            · push_neg at hq
              rw [L1 i _ q hq, L1 i _ q hq]
          have := congrArg (fun f => f b) (hinj i i _ _ hall).2
          simp [δ] at this
        cases hv : xor (anchor i (slot i b)) (z' (slot i b))
        · rw [L2 i _ (fun _ => false) b hv]
          change anchor i (slot i b) = z' (slot i b)
          revert hv; cases anchor i (slot i b) <;> cases z' (slot i b) <;> simp
        · rw [L2 i _ δ b (by simp [hv, δ])]
          change anchor i (slot i b) ≠ zz i δ (slot i b) at hdiff
          revert hv hdiff
          cases anchor i (slot i b) <;> cases z' (slot i b) <;>
            cases zz i δ (slot i b) <;> simp
      · push_neg at hp
        rw [L1 i _ p hp, hz' p hp]
    refine ⟨anchor, ?_⟩
    intro i j hij
    by_contra hne
    push_neg at hne
    let zs : Z := fun p =>
      if ∃ b, slot i b = p then (if ∃ b, slot j b = p then false else anchor j p) else anchor i p
    obtain ⟨v, hv⟩ := hit i zs (by
      intro p hp
      have : ¬ ∃ b, slot i b = p := fun ⟨b, hb⟩ => hp b hb
      simp only [zs, if_neg this])
    obtain ⟨w, hw⟩ := hit j zs (by
      intro p hp
      have hj : ¬ ∃ b, slot j b = p := fun ⟨b, hb⟩ => hp b hb
      by_cases hi : ∃ b, slot i b = p
      · simp only [zs, if_pos hi, if_neg hj]
      · simp only [zs, if_neg hi]
        exact hne p (fun b hb => hi ⟨b, hb⟩) hp)
    exact hij (hinj i j v w (hv.trans hw.symm)).1
  · rintro ⟨anchor, hsep⟩
    choose c hc using hok
    refine ⟨fun p x M => xor (anchor (c x) p) (decide (∃ b, M (c x) b = true)),
      fun _ x u => tail u (c x),
      fun z t => (dec hm anchor slot z,
        fun b => xor (z (slot (dec hm anchor slot z) b)) (anchor (dec hm anchor slot z)
          (slot (dec hm anchor slot z) b)), t), ?_⟩
    intro x u
    have hd : dec hm anchor slot
        (fun p => xor (anchor (c x) p)
          (decide (∃ b, (decide (slot (c x) b = p) && vis u (c x) b) = true))) = c x := by
      apply dec_eq hm anchor slot hsep
      intro p hp
      simp [hp]
    simp only
    rw [hd]
    refine ⟨hc x, ?_, rfl⟩
    funext b
    have : (∃ b', (decide (slot (c x) b' = slot (c x) b) && vis u (c x) b') = true)
        ↔ vis u (c x) b = true := by
      constructor
      · rintro ⟨b', hb'⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
        rw [← (slot (c x)).injective hb'.1]; exact hb'.2
      · intro hv; exact ⟨b, by simp [hv]⟩
    simp only [this]
    cases anchor (c x) (slot (c x) b) <;> cases vis u (c x) b <;> simp
