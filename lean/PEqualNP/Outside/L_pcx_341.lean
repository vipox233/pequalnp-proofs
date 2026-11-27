import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_207


namespace PEqualNP.Outside.L_pcx_341_aux.GraphCounts

open PEqualNP.Expanders

abbrev Cell (m n : ℕ) := Fin m × Fin n
abbrev L (m n : ℕ) := Cell m n ⊕ (Fin (m-1) × Fin n)
abbrev R (m n : ℕ) := Cell m n ⊕ (Fin m × Fin (n-1))

abbrev baseAdj (m n : ℕ) : L m n → R m n → Bool := Sum.elim
  (fun p => Sum.elim (fun h => decide (p = h))
    (fun s => decide (p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1))))
  (fun s => Sum.elim (fun h => decide (s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1)))
    (fun _ => false))

noncomputable abbrev H (m n : ℕ) : BipGraph (Fintype.card (L m n)) (Fintype.card (R m n)) :=
  fun u => Finset.univ.filter (fun v => baseAdj m n ((Fintype.equivFin (L m n)).symm u)
    ((Fintype.equivFin (R m n)).symm v) = true)

abbrev E (m n : ℕ) := GEdge (H m n)
abbrev U (m n t : ℕ) := Fin (Fintype.card (L m n)) ⊕ (E m n × Fin t)
abbrev V (m n t : ℕ) := Fin (Fintype.card (R m n)) ⊕ (E m n × Fin t)

noncomputable abbrev adj (m n t : ℕ) : U m n t → V m n t → Bool := Sum.elim
  (fun u => Sum.elim (fun v => decide (t = 0 ∧ v ∈ H m n u))
    (fun s => decide (u = s.1.val.1 ∧ s.2.val = 0)))
  (fun s => Sum.elim (fun v => decide (v = s.1.val.2 ∧ s.2.val+1 = t))
    (fun z => decide (s.1 = z.1 ∧ (s.2 = z.2 ∨ z.2.val = s.2.val+1))))

noncomputable abbrev G (m n t : ℕ) : BipGraph (Fintype.card (U m n t)) (Fintype.card (V m n t)) :=
  fun u => Finset.univ.filter (fun v => adj m n t ((Fintype.equivFin (U m n t)).symm u)
    ((Fintype.equivFin (V m n t)).symm v) = true)

private abbrev Raw {A B : Type} (p : A → B → Prop) := {x : A × B // p x.1 x.2}

private theorem card_raw_congr {A B : Type} [Fintype A] [Fintype B]
    (p q : A → B → Prop) [DecidableRel p] [DecidableRel q] (h : ∀ a b, p a b ↔ q a b) :
    Fintype.card (Raw p) = Fintype.card (Raw q) :=
  Fintype.card_congr (Equiv.subtypeEquivRight (fun x => h x.1 x.2))

private theorem card_split {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : A ⊕ B → C ⊕ D → Prop) [DecidableRel p] :
    Fintype.card (Raw p) = Fintype.card (Raw (fun a c => p (.inl a) (.inl c))) +
      Fintype.card (Raw (fun a d => p (.inl a) (.inr d))) +
      (Fintype.card (Raw (fun b c => p (.inr b) (.inl c))) +
       Fintype.card (Raw (fun b d => p (.inr b) (.inr d)))) := by
  let f : Raw p ≃ (Raw (fun a c => p (.inl a) (.inl c)) ⊕
      Raw (fun a d => p (.inl a) (.inr d))) ⊕
      (Raw (fun b c => p (.inr b) (.inl c)) ⊕ Raw (fun b d => p (.inr b) (.inr d))) := {
    toFun := fun ⟨(x,y),h⟩ => match x,y with
      | .inl a,.inl c => .inl (.inl ⟨(a,c),h⟩)
      | .inl a,.inr d => .inl (.inr ⟨(a,d),h⟩)
      | .inr b,.inl c => .inr (.inl ⟨(b,c),h⟩)
      | .inr b,.inr d => .inr (.inr ⟨(b,d),h⟩)
    invFun := fun x => match x with
      | .inl (.inl ⟨(a,c),h⟩) => ⟨(.inl a,.inl c),h⟩
      | .inl (.inr ⟨(a,d),h⟩) => ⟨(.inl a,.inr d),h⟩
      | .inr (.inl ⟨(b,c),h⟩) => ⟨(.inr b,.inl c),h⟩
      | .inr (.inr ⟨(b,d),h⟩) => ⟨(.inr b,.inr d),h⟩
    left_inv := by rintro ⟨⟨a|b,c|d⟩,h⟩ <;> rfl
    right_inv := by rintro ((⟨⟨a,c⟩,h⟩|⟨⟨a,d⟩,h⟩)|(⟨⟨b,c⟩,h⟩|⟨⟨b,d⟩,h⟩)) <;> rfl }
  simpa only [Fintype.card_sum] using Fintype.card_congr f

private theorem card_param {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : A → B → Prop) [DecidableRel p] (f : C → A × B) (hf : Function.Injective f)
    (ok : ∀ c, p (f c).1 (f c).2) (onto : ∀ a b, p a b → ∃ c, f c = (a,b)) :
    Fintype.card (Raw p) = Fintype.card C := by
  symm
  apply Fintype.card_congr (Equiv.ofBijective (fun c => (⟨f c, ok c⟩ : Raw p)) ⟨?_,?_⟩)
  · intro a b h
    exact hf (congrArg Subtype.val h)
  · rintro ⟨⟨a,b⟩,h⟩
    obtain ⟨c,hc⟩ := onto a b h
    exact ⟨c, Subtype.ext hc⟩

private theorem card_none {A B : Type} [Fintype A] [Fintype B]
    (p : A → B → Prop) [DecidableRel p] (h : ∀ a b, ¬ p a b) : Fintype.card (Raw p) = 0 := by
  let hEmpty : IsEmpty (Raw p) := ⟨fun x => h _ _ x.property⟩
  exact @Fintype.card_of_isEmpty _ _ hEmpty

private theorem card_edges {A B : Type} [Fintype A] [Fintype B] (p : A → B → Bool) :
    Fintype.card (GEdge (fun u : Fin (Fintype.card A) =>
      Finset.univ.filter (fun v : Fin (Fintype.card B) =>
        p (Fintype.equivFin A |>.symm u) (Fintype.equivFin B |>.symm v) = true))) =
    Fintype.card (Raw (fun a b => p a b = true)) := by
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv ((Fintype.equivFin A).symm.prodCongr (Fintype.equivFin B).symm) ?_
  intro x
  simp

private def step {k : ℕ} (s : Fin (k-1)) (b : Bool) : Fin k :=
  ⟨s.val + b.toNat, by have := s.isLt; cases b <;> simp at * <;> omega⟩

private theorem step_inj {k : ℕ} (s : Fin (k-1)) : Function.Injective (step s) := by
  intro a b h
  have eq := congrArg Fin.val h
  change s.val + a.toNat = s.val + b.toNat at eq
  cases a <;> cases b <;> simp_all

private theorem step_cases {k : ℕ} {x : Fin k} {s : Fin (k-1)} :
    x.val = s.val ∨ x.val = s.val + 1 ↔ ∃ b, step s b = x := by
  constructor
  · rintro (h|h)
    · exact ⟨false, Fin.ext (by simpa [step] using h.symm)⟩
    · exact ⟨true, Fin.ext (by simpa [step] using h.symm)⟩
  · rintro ⟨b,rfl⟩
    cases b <;> simp [step]

private theorem base_edges (m n : ℕ) :
    Fintype.card (E m n) = m*n + 2*m*(n-1) + 2*n*(m-1) := by
  have h₁ : Fintype.card (Raw (fun (p h : Cell m n) => p = h)) = m*n := by
    rw [card_param _ (fun p : Cell m n => (p,p)) (fun _ _ h => congrArg Prod.fst h)
      (fun _ => rfl) (by rintro p _ rfl; exact ⟨p,rfl⟩)]
    simp [Cell]
  have h₂ : Fintype.card (Raw (fun (p : Cell m n) (s : Fin m × Fin (n-1)) =>
      p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1))) = 2*m*(n-1) := by
    rw [card_param (fun (p : Cell m n) (s : Fin m × Fin (n-1)) =>
      p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1))
      (fun x : (Fin m × Fin (n-1)) × Bool => ((x.1.1,step x.1.2 x.2),x.1))]
    · simp; ring
    · rintro ⟨s,b⟩ ⟨z,c⟩ h
      have hsz : s = z := congrArg Prod.snd h
      subst z
      exact congrArg (s, ·) (step_inj s.2 (congrArg (fun a => a.1.2) h))
    · intro x; exact ⟨rfl, step_cases.mpr ⟨x.2,rfl⟩⟩
    · rintro ⟨i,j⟩ ⟨a,b⟩ ⟨hij,h⟩
      change i = a at hij
      subst i
      obtain ⟨c,rfl⟩ := step_cases.mp h
      exact ⟨((a,b),c),rfl⟩
  have h₃ : Fintype.card (Raw (fun (s : Fin (m-1) × Fin n) (h : Cell m n) =>
      s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1))) = 2*n*(m-1) := by
    rw [card_param (fun (s : Fin (m-1) × Fin n) (h : Cell m n) =>
      s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1))
      (fun x : (Fin (m-1) × Fin n) × Bool => (x.1,(step x.1.1 x.2,x.1.2)))]
    · simp; ring
    · rintro ⟨s,b⟩ ⟨z,c⟩ h
      have hsz : s = z := congrArg Prod.fst h
      subst z
      exact congrArg (s, ·) (step_inj s.1 (congrArg (fun a => a.2.1) h))
    · intro x; exact ⟨rfl, step_cases.mpr ⟨x.2,rfl⟩⟩
    · rintro ⟨a,b⟩ ⟨i,j⟩ ⟨hij,h⟩
      change b = j at hij
      subst j
      obtain ⟨c,rfl⟩ := step_cases.mp h
      exact ⟨((a,b),c),rfl⟩
  rw [show Fintype.card (E m n) = _ from card_edges (baseAdj m n),
    card_split (fun a b => baseAdj m n a b = true),
    card_none (fun (b : Fin (m-1) × Fin n) (d : Fin m × Fin (n-1)) =>
      baseAdj m n (.inr b) (.inr d) = true) (by simp [baseAdj])]
  simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
  rw [h₁,h₂,h₃]
  omega

private theorem stretch_edges (m n t : ℕ) :
    Fintype.card (GEdge (G m n t)) = (2*t+1)*Fintype.card (E m n) := by
  rw [show Fintype.card (GEdge (G m n t)) = _ from card_edges (adj m n t),
    card_split (fun a b => adj m n t a b = true)]
  by_cases ht : t = 0
  · subst t
    rw [card_raw_congr (fun (u : Fin (Fintype.card (L m n))) (v : Fin (Fintype.card (R m n))) =>
          adj m n 0 (.inl u) (.inl v) = true) (fun u v => v ∈ H m n u)
          (by intro u v; simp only [adj, Sum.elim_inl, decide_eq_true_eq, true_and]),
        card_none (fun u (d : E m n × Fin 0) => adj m n 0 (.inl u) (.inr d) = true)
          (fun _ d => Fin.elim0 d.2),
        card_none (fun (b : E m n × Fin 0) v => adj m n 0 (.inr b) (.inl v) = true)
          (fun b _ => Fin.elim0 b.2),
        card_none (fun (b d : E m n × Fin 0) => adj m n 0 (.inr b) (.inr d) = true)
          (fun b _ => Fin.elim0 b.2)]
    change Fintype.card (E m n) + 0 + (0 + 0) = (2*0+1)*Fintype.card (E m n)
    simp
  · have ht' : 0 < t := Nat.pos_of_ne_zero ht
    simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    rw [card_none (fun u v => t = 0 ∧ v ∈ H m n u) (by simp [ht])]
    have h₁ : Fintype.card (Raw (fun u (s : E m n × Fin t) =>
        u = s.1.val.1 ∧ s.2.val = 0)) = Fintype.card (E m n) := by
      apply card_param _ (fun e : E m n => (e.val.1,(e,⟨0,ht'⟩)))
      · intro a b h; exact congrArg (fun x => x.2.1) h
      · intro e; exact ⟨rfl,rfl⟩
      · rintro u ⟨e,i⟩ ⟨hu,hi⟩
        subst u
        exact ⟨e, by simp [(Fin.ext hi.symm : (⟨0,ht'⟩ : Fin t) = i)]⟩
    have h₂ : Fintype.card (Raw (fun (s : E m n × Fin t) v =>
        v = s.1.val.2 ∧ s.2.val+1 = t)) = Fintype.card (E m n) := by
      let last : Fin t := ⟨t-1,by omega⟩
      have hl : last.val + 1 = t := by dsimp [last]; omega
      apply card_param _ (fun e : E m n => ((e,last), e.val.2))
      · intro a b h; exact congrArg (fun x => x.1.1) h
      · intro e; exact ⟨rfl,hl⟩
      · rintro ⟨e,i⟩ v ⟨hv,hi⟩
        subst v
        have hli : last.val = i.val := by
          change i.val + 1 = t at hi
          dsimp [last]
          omega
        exact ⟨e, by simp [(Fin.ext hli : last = i)]⟩
    have h₃ : Fintype.card (Raw (fun (s z : E m n × Fin t) =>
        s.1 = z.1 ∧ (s.2 = z.2 ∨ z.2.val = s.2.val+1))) =
        Fintype.card (E m n) * t + Fintype.card (E m n) * (t-1) := by
      let f : (E m n × Fin t) ⊕ (E m n × Fin (t-1)) → (E m n × Fin t) × (E m n × Fin t) :=
        Sum.elim (fun x => (x,x)) (fun x => ((x.1,step x.2 false),(x.1,step x.2 true)))
      rw [card_param (fun (s z : E m n × Fin t) =>
        s.1 = z.1 ∧ (s.2 = z.2 ∨ z.2.val = s.2.val+1)) f]
      · simp
      · intro a b h
        rcases a with a|a <;> rcases b with b|b
        · exact congrArg Sum.inl (congrArg Prod.fst h)
        · have h₀ := congrArg (fun x => x.1.2.val) h
          have h₁ := congrArg (fun x => x.2.2.val) h
          simp [f, step] at h₀ h₁
          omega
        · have h₀ := congrArg (fun x => x.1.2.val) h
          have h₁ := congrArg (fun x => x.2.2.val) h
          simp [f, step] at h₀ h₁
          omega
        · have he := congrArg (fun x => x.1.1) h
          have hi := congrArg (fun x => x.1.2.val) h
          exact congrArg Sum.inr (Prod.ext he (Fin.ext (by simpa [f,step] using hi)))
      · rintro (x|x)
        · exact ⟨rfl,Or.inl rfl⟩
        · exact ⟨rfl,Or.inr rfl⟩
      · rintro ⟨e,i⟩ ⟨d,j⟩ ⟨he,hi⟩
        change e = d at he
        subst d
        rcases hi with h|h
        · change i = j at h
          subst j
          exact ⟨.inl (e,i),rfl⟩
        · have hj := j.isLt
          have h' : i.val < t-1 := by change j.val = i.val+1 at h; omega
          refine ⟨.inr (e,⟨i.val,h'⟩), Prod.ext (Prod.ext rfl (Fin.ext rfl)) ?_⟩
          exact Prod.ext rfl (Fin.ext h.symm)
    rw [h₁,h₂,h₃]
    have et : Fintype.card (E m n) * t =
      Fintype.card (E m n) * (t-1) + Fintype.card (E m n) := by
      conv_lhs => rw [show t = (t-1)+1 by omega, Nat.mul_add, Nat.mul_one]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2*t), ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.two_mul,
      Nat.add_mul]
    omega

private abbrev degree {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] :=
  Fintype.card {a // p a}

private theorem degree_split {A B : Type} [Fintype A] [Fintype B]
    (p : A ⊕ B → Prop) [DecidablePred p] :
    degree p = degree (fun a => p (.inl a)) + degree (fun b => p (.inr b)) := by
  simpa only [degree, Fintype.card_sum] using Fintype.card_congr (Equiv.subtypeSum (p := p))

private theorem degree_le {A B : Type} [Fintype A] [Fintype B] (p : A → Prop) [DecidablePred p]
    (q : B → Prop) [DecidablePred q] (f : {a // p a} → {b // q b}) (hf : Function.Injective f) :
    degree p ≤ degree q := Fintype.card_le_of_injective f hf

private theorem degree_congr {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → Prop) [DecidablePred p] (q : B → Prop) [DecidablePred q]
    (h : ∀ a, p a ↔ q (e a)) : degree p = degree q :=
  Fintype.card_congr (Equiv.subtypeEquiv e h)

private theorem degree_one {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p]
    (h : ∀ a b, p a → p b → a = b) : degree p ≤ 1 := by
  simpa using Fintype.card_le_of_injective (fun _ : {a // p a} => ()) (by
    intro a b _
    exact Subtype.ext (h _ _ a.property b.property))

private theorem degree_two {A : Type} [Fintype A] (p q : A → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ a b, p a → p b → a = b) (hq : ∀ a b, q a → q b → a = b) :
    degree (fun a => p a ∨ q a) ≤ 2 := by
  simpa using Fintype.card_le_of_injective (fun a : {a // p a ∨ q a} => decide (p a.val)) (by
    intro a b h
    apply Subtype.ext
    by_cases ha : p a.val
    · have hb : p b.val := by simpa [ha, eq_comm] using h
      exact hp _ _ ha hb
    · have hb : ¬p b.val := by simpa [ha, eq_comm] using h
      exact hq _ _ (a.property.resolve_left ha) (b.property.resolve_left hb))

private theorem degree_zero {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p]
    (h : ∀ a, ¬p a) : degree p = 0 := by
  let hEmpty : IsEmpty {a // p a} := ⟨fun a => h _ a.property⟩
  exact @Fintype.card_of_isEmpty _ _ hEmpty

private theorem degree_grid {a b c : ℕ} (u : Fin a) (v : Fin b) :
    degree (fun s : Fin a × Fin c => u = s.1 ∧
      (v.val = s.2.val ∨ v.val = s.2.val+1)) ≤ 2 := by
  simp only [and_or_left]
  apply degree_two <;> rintro ⟨i,j⟩ ⟨k,l⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
  all_goals
    exact Prod.ext (h₁.symm.trans h₃) (Fin.ext (show j.val = l.val by dsimp at h₂ h₄; omega))

private theorem degree_grid' {a b c : ℕ} (u : Fin a) (v : Fin b) :
    degree (fun s : Fin c × Fin a => u = s.2 ∧
      (v.val = s.1.val ∨ v.val = s.1.val+1)) ≤ 2 := by
  rw [degree_congr (Equiv.prodComm (Fin c) (Fin a)) _
    (fun s => u = s.1 ∧ (v.val = s.2.val ∨ v.val = s.2.val+1)) (by intro; rfl)]
  exact degree_grid u v

private theorem base_left_raw (m n : ℕ) (u : L m n) :
    degree (fun v => baseAdj m n u v = true) ≤ 3 := by
  rw [degree_split (fun v => baseAdj m n u v = true)]
  cases u with
  | inl p =>
    simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have h := degree_one (fun h : Cell m n => p = h) (fun _ _ ha hb => ha.symm.trans hb)
    have h' := degree_grid (c := n-1) p.1 p.2
    omega
  | inr s =>
    rw [degree_zero (fun (b : Fin m × Fin (n-1)) => baseAdj m n (.inr s) (.inr b) = true)
      (by simp [baseAdj])]
    simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have hh : degree (fun v : Cell m n => s.2 = v.2 ∧
        (v.1.val = s.1.val ∨ v.1.val = s.1.val+1)) ≤ 2 := by
      simp only [and_or_left]
      apply degree_two <;> rintro ⟨i,j⟩ ⟨k,l⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
      all_goals exact Prod.ext (Fin.ext (h₂.trans h₄.symm)) (h₁.symm.trans h₃)
    omega

private theorem base_right_raw (m n : ℕ) (v : R m n) :
    degree (fun u => baseAdj m n u v = true) ≤ 3 := by
  rw [degree_split (fun u => baseAdj m n u v = true)]
  cases v with
  | inl p =>
    simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have h := degree_one (fun h : Cell m n => h = p) (fun _ _ ha hb => ha.trans hb.symm)
    have h' := degree_congr (Equiv.refl (Fin (m-1) × Fin n))
      (fun s => s.2 = p.2 ∧ (p.1.val = s.1.val ∨ p.1.val = s.1.val+1))
      (fun s => p.2 = s.2 ∧ (p.1.val = s.1.val ∨ p.1.val = s.1.val+1)) (by intro; simp [eq_comm])
    rw [h']
    have hh := degree_grid' (c := m-1) p.2 p.1
    omega
  | inr s =>
    rw [degree_zero (fun (b : Fin (m-1) × Fin n) => baseAdj m n (.inr b) (.inr s) = true)
      (by simp [baseAdj])]
    simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have hh : degree (fun v : Cell m n => v.1 = s.1 ∧
        (v.2.val = s.2.val ∨ v.2.val = s.2.val+1)) ≤ 2 := by
      simp only [and_or_left]
      apply degree_two <;> rintro ⟨i,j⟩ ⟨k,l⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
      all_goals exact Prod.ext (h₁.trans h₃.symm) (Fin.ext (h₂.trans h₄.symm))
    omega

private theorem base_left_fin (m n : ℕ) (u : Fin (Fintype.card (L m n))) :
    degree (fun v => v ∈ H m n u) ≤ 3 := by
  rw [degree_congr (Fintype.equivFin (R m n)).symm (fun v => v ∈ H m n u)
    (fun v => baseAdj m n ((Fintype.equivFin (L m n)).symm u) v = true) (by intro; simp [H])]
  exact base_left_raw m n _

private theorem base_right_fin (m n : ℕ) (v : Fin (Fintype.card (R m n))) :
    degree (fun u => v ∈ H m n u) ≤ 3 := by
  rw [degree_congr (Fintype.equivFin (L m n)).symm (fun u => v ∈ H m n u)
    (fun u => baseAdj m n u ((Fintype.equivFin (R m n)).symm v) = true) (by intro; simp [H])]
  exact base_right_raw m n _

private theorem degree_stretch_old {A B E : Type} [Fintype B] [Fintype E] [DecidableEq A]
    (p : A → B → Prop) [DecidableRel p] (a : A) (l : E → A) (r : E → B)
    (edge : ∀ e, p (l e) (r e)) (inj : ∀ e f, l e = l f → r e = r f → e = f)
    (t j : ℕ) (hd : degree (p a) ≤ 3) :
    degree (fun b => t = 0 ∧ p a b) +
      degree (fun s : E × Fin t => a = l s.1 ∧ s.2.val = j) ≤ 3 := by
  by_cases ht : t = 0
  · subst t
    rw [degree_congr (Equiv.refl B) (fun b => 0 = 0 ∧ p a b) (p a) (by simp),
      degree_zero (fun s : E × Fin 0 => a = l s.1 ∧ s.2.val = j)
        (fun s => Fin.elim0 s.2), Nat.add_zero]
    exact hd
  · rw [degree_zero (fun b => t = 0 ∧ p a b) (by simp [ht]), Nat.zero_add]
    refine (degree_le (fun s : E × Fin t => a = l s.1 ∧ s.2.val = j) (p a)
      (fun s => ⟨r s.val.1,
        Eq.mpr (congrArg (fun x => p x (r s.val.1)) s.property.1) (edge s.val.1)⟩) ?_).trans hd
    intro e f h
    apply Subtype.ext
    exact Prod.ext (inj _ _ (e.property.1.symm.trans f.property.1) (congrArg Subtype.val h))
      (Fin.ext (e.property.2.trans f.property.2.symm))

private theorem stretch_left_raw (m n t : ℕ) (u : U m n t) :
    degree (fun v => adj m n t u v = true) ≤ 3 := by
  rw [degree_split (fun v => adj m n t u v = true)]
  cases u with
  | inl u =>
    simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    exact degree_stretch_old (fun a b => b ∈ H m n a) u (fun e : E m n => e.val.1)
      (fun e => e.val.2) (fun e => e.property)
      (fun _ _ h₁ h₂ => Subtype.ext (Prod.ext h₁ h₂)) t 0 (base_left_fin m n u)
  | inr s =>
    simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have h := degree_one (fun v => v = s.1.val.2 ∧ s.2.val+1 = t)
      (fun _ _ ha hb => ha.1.trans hb.1.symm)
    have h' : degree (fun z : E m n × Fin t =>
        s.1 = z.1 ∧ (s.2 = z.2 ∨ z.2.val = s.2.val+1)) ≤ 2 := by
      simp only [and_or_left]
      apply degree_two
      · exact fun _ _ ha hb => Prod.ext (ha.1.symm.trans hb.1) (ha.2.symm.trans hb.2)
      · exact fun _ _ ha hb => Prod.ext (ha.1.symm.trans hb.1) (Fin.ext (ha.2.trans hb.2.symm))
    omega

private theorem stretch_right_raw (m n t : ℕ) (v : V m n t) :
    degree (fun u => adj m n t u v = true) ≤ 3 := by
  rw [degree_split (fun u => adj m n t u v = true)]
  cases v with
  | inl v =>
    simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    by_cases ht : t = 0
    · subst t
      rw [degree_congr (Equiv.refl _) (fun u => 0 = 0 ∧ v ∈ H m n u)
        (fun u => v ∈ H m n u) (by simp),
        degree_zero (fun s : E m n × Fin 0 => v = s.1.val.2 ∧ s.2.val+1 = 0)
          (fun s => Fin.elim0 s.2), Nat.add_zero]
      exact base_right_fin m n v
    · rw [degree_congr (Equiv.refl _) (fun s : E m n × Fin t => v = s.1.val.2 ∧ s.2.val+1 = t)
        (fun s => v = s.1.val.2 ∧ s.2.val = t-1)
        (by intro s; simp only [Equiv.refl_apply]; constructor <;> rintro ⟨h,hh⟩ <;> exact ⟨h,by omega⟩)]
      exact degree_stretch_old (fun a b => a ∈ H m n b) v (fun e : E m n => e.val.2)
        (fun e => e.val.1) (fun e => e.property)
        (fun _ _ h₁ h₂ => Subtype.ext (Prod.ext h₂ h₁)) t (t-1) (base_right_fin m n v)
  | inr s =>
    simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq]
    have h := degree_one (fun u => u = s.1.val.1 ∧ s.2.val = 0)
      (fun _ _ ha hb => ha.1.trans hb.1.symm)
    have h' : degree (fun z : E m n × Fin t =>
        z.1 = s.1 ∧ (z.2 = s.2 ∨ s.2.val = z.2.val+1)) ≤ 2 := by
      simp only [and_or_left]
      apply degree_two
      · exact fun _ _ ha hb => Prod.ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)
      · exact fun _ _ ha hb => Prod.ext (ha.1.trans hb.1.symm) (Fin.ext (by omega))
    omega

private theorem degree_finset {A : Type} [Fintype A] [DecidableEq A] (s : Finset A) :
    s.card = degree (· ∈ s) := by
  exact (@Fintype.card_of_subtype A (fun x => x ∈ s) s (fun _ => Iff.rfl)
    (Subtype.fintype (fun x => x ∈ s))).symm

set_option maxHeartbeats 800000 in
theorem counts (m n t : ℕ) (hn : 2 ≤ n) (hm : n < m) :
    LeftDegLe (G m n t) 3 ∧ RightDegLe (G m n t) 3 ∧
    Fintype.card (U m n t) + n = Fintype.card (V m n t) + m ∧
    Fintype.card (GEdge (G m n t)) =
      (2*t+1)*(m*n + 2*m*(n-1) + 2*n*(m-1)) := by
  refine ⟨?_,?_,?_,by rw [stretch_edges,base_edges]⟩
  · intro u
    rw [degree_finset]
    rw [degree_congr (Fintype.equivFin (V m n t)).symm (fun v => v ∈ G m n t u)
      (fun v => adj m n t ((Fintype.equivFin (U m n t)).symm u) v = true)
      (by intro; simp only [G,Finset.mem_filter,Finset.mem_univ,true_and])]
    exact stretch_left_raw m n t _
  · intro v
    rw [degree_finset]
    rw [degree_congr (Fintype.equivFin (U m n t)).symm (fun u => u ∈ rightNbrs (G m n t) v)
      (fun u => adj m n t u ((Fintype.equivFin (V m n t)).symm v) = true)
      (by intro; simp only [rightNbrs,G,Finset.mem_filter,Finset.mem_univ,true_and])]
    exact stretch_right_raw m n t _
  · simp only [U,V,L,R,Cell,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod]
    have hm' : m-1+1 = m := by omega
    have hn' : n-1+1 = n := by omega
    have h₁ := congrArg (· * n) hm'
    have h₂ := congrArg (m * ·) hn'
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at h₁ h₂
    omega

end PEqualNP.Outside.L_pcx_341_aux.GraphCounts


namespace PEqualNP.Outside.L_pcx_341_aux.BaseGirth

abbrev Cell (m n : ℕ) := Fin m × Fin n
abbrev L (m n : ℕ) := Cell m n ⊕ (Fin (m-1) × Fin n)
abbrev R (m n : ℕ) := Cell m n ⊕ (Fin m × Fin (n-1))

def Adj {m n : ℕ} : L m n → R m n → Prop :=
  Sum.elim
    (fun p => Sum.elim (fun h => p = h)
      (fun s => p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1)))
    (fun s => Sum.elim
      (fun h => s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1))
      (fun _ => False))

def adjBool {m n : ℕ} : L m n → R m n → Bool :=
  Sum.elim
    (fun p => Sum.elim (fun h => decide (p = h))
      (fun s => decide (p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1))))
    (fun s => Sum.elim
      (fun h => decide (s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1)))
      (fun _ => false))

theorem adjBool_eq_true {m n : ℕ} (u : L m n) (v : R m n) :
    adjBool u v = true ↔ Adj u v := by
  cases u <;> cases v <;> simp [adjBool, Adj]

-- The two families of grid lines: the first coordinate specifies the family,
-- the second the line, and the third the doubled position along the line.
private abbrev Point := Bool × ℕ × ℕ

private def encode {m n : ℕ} : L m n ⊕ R m n → Point
  | .inl (.inl (r,c)) => (false, r, 2*c.val)
  | .inl (.inr (r,c)) => (true, c, 2*r.val+1)
  | .inr (.inl (r,c)) => (true, c, 2*r.val)
  | .inr (.inr (r,c)) => (false, r, 2*c.val+1)

private theorem encode_injective {m n : ℕ} :
    Function.Injective (encode (m := m) (n := n)) := by
  rintro ((⟨a,b⟩ | ⟨a,b⟩) | (⟨a,b⟩ | ⟨a,b⟩))
    ((⟨c,d⟩ | ⟨c,d⟩) | (⟨c,d⟩ | ⟨c,d⟩)) h
  all_goals simp [encode, Fin.ext_iff, Prod.mk.injEq] at h ⊢
  all_goals omega

private def Rail (u v : Point) : Prop := u.1 = v.1 ∧ u.2.1 = v.2.1
private def Cross (u v : Point) : Prop :=
  u.1 ≠ v.1 ∧ u.2.2 = 2*v.2.1 ∧ v.2.2 = 2*u.2.1
private def Step (u v : Point) : Prop :=
  (Rail u v ∧ (u.2.2 + 1 = v.2.2 ∨ v.2.2 + 1 = u.2.2)) ∨ Cross u v

private theorem rail_symm {u v : Point} (h : Rail u v) : Rail v u :=
  ⟨h.1.symm, h.2.symm⟩

private theorem rail_trans {u v w : Point} (h : Rail u v) (h' : Rail v w) :
    Rail u w := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

private theorem point_eq {u v : Point} (h : Rail u v) (h' : u.2.2 = v.2.2) : u = v :=
  Prod.ext h.1 (Prod.ext h.2 h')

private theorem cross_symm {u v : Point} (h : Cross u v) : Cross v u :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

private theorem step_symm {u v : Point} : Step u v → Step v u
  | .inl ⟨h, h'⟩ => .inl ⟨rail_symm h, h'.symm⟩
  | .inr h => .inr (cross_symm h)

private theorem adj_step {m n : ℕ} {u : L m n} {v : R m n} (h : Adj u v) :
    Step (encode (.inl u)) (encode (.inr v)) := by
  rcases u with ⟨a,b⟩ | ⟨a,b⟩ <;> rcases v with ⟨c,d⟩ | ⟨c,d⟩
  all_goals simp [Adj, Step, Rail, Cross, encode, Fin.ext_iff] at h ⊢
  all_goals omega

private theorem bool_same {a b c : Bool} (h : a ≠ c) (h' : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem cross_at_most_one {u v w : Point} (h : Cross u v) (h' : Cross u w) :
    v = w := by
  have hh := h.2.1
  have hh' := h'.2.1
  exact point_eq ⟨bool_same h.1.symm h'.1.symm, by omega⟩ (h.2.2.trans h'.2.2.symm)

private theorem crossing_between_rails {u v u' v' : Point} (h : Cross u v)
    (h' : Cross u' v') (hu : Rail u u') (hv : Rail v v') : u = u' :=
  point_eq hu (h.2.1.trans ((congrArg (2 * ·) hv.2).trans h'.2.1.symm))

private theorem rail_along (p : ℕ → Point) (hs : ∀ i, Step (p i) (p (i+1)))
    (a b : ℕ) (hab : a ≤ b)
    (hc : ∀ i, a ≤ i → i < b → ¬ Cross (p i) (p (i+1))) : Rail (p a) (p b) := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact ⟨rfl,rfl⟩
  | succ b ih =>
      by_cases h : a ≤ b
      · exact rail_trans (ih h (fun i hi hj => hc i hi (by omega)))
          ((hs b).resolve_right (hc b h (by omega))).1
      · have : a = b+1 := by omega
        subst a
        exact ⟨rfl,rfl⟩

private theorem first_cross (p : ℕ → Point) (a b : ℕ)
    (h : ∃ i, a ≤ i ∧ i < b ∧ Cross (p i) (p (i+1))) :
    ∃ i, a ≤ i ∧ i < b ∧ Cross (p i) (p (i+1)) ∧
      ∀ j, a ≤ j → j < i → ¬ Cross (p j) (p (j+1)) := by
  classical
  obtain ⟨ha, hb, hh⟩ := Nat.find_spec h
  exact ⟨Nat.find h, ha, hb, hh, fun j hj hj' hj'' =>
    (Nat.find_min' h ⟨hj, hj'.trans hb, hj''⟩).not_gt hj'⟩

-- If the walk never changes line, a vertex at maximum position has both
-- neighbors at the same position on its line, contradicting simplicity.
private theorem no_cross_impossible (p : ℕ → Point) {N : ℕ} (hN : 4 ≤ N)
    (hclose : p N = p 0)
    (hne : ∀ i j, i < j → j < i+N → p i ≠ p j)
    (hs : ∀ i, Step (p i) (p (i+1)))
    (hc : ∀ i < N, ¬ Cross (p i) (p (i+1))) : False := by
  obtain ⟨i, hi, hmax⟩ := (Finset.range (N+1)).exists_max_image
    (fun i => (p i).2.2) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
  have hm (j : ℕ) (hj : j ≤ N) : (p j).2.2 ≤ (p i).2.2 :=
    hmax j (Finset.mem_range.mpr (by omega))
  obtain ⟨k, hk, hm⟩ : ∃ k < N, ∀ j ≤ N, (p j).2.2 ≤ (p k).2.2 := by
    by_cases H : i = N
    · refine ⟨0, by omega, ?_⟩
      simpa only [H, hclose] using hm
    · exact ⟨i, by omega, hm⟩
  let j := if k = 0 then N-1 else k-1
  have hj : j < N := by dsimp [j]; split <;> omega
  have hpj : p (j+1) = p k := by
    by_cases H : k = 0
    · have he : j+1=N := by simp [j,H]; omega
      rw [he, hclose, H]
    · have he : j+1=k := by simp [j,H]; omega
      rw [he]
  have hs₁ := (hs j).resolve_right (hc j hj)
  have hs₂ := (hs k).resolve_right (hc k hk)
  rw [hpj] at hs₁
  have he : p j = p (k+1) := by
    refine point_eq (rail_trans hs₁.1 hs₂.1) ?_
    have H₁ := hs₁.2
    have H₂ := hs₂.2
    have H₃ := hm j (by omega)
    have H₄ := hm (k+1) (by omega)
    omega
  by_cases H : k = 0
  · exact hne (k+1) j (by simp [j,H]; omega) (by simp [j,H]; omega) he.symm
  · exact hne j (k+1) (by simp [j,H]) (by simp [j,H]; omega) he

private theorem walk_length (p : ℕ → Point) {N : ℕ} (hN : 4 ≤ N)
    (hperiod : ∀ i, p (i+N) = p i)
    (hne : ∀ i j, i < j → j < i+N → p i ≠ p j)
    (hs : ∀ i, Step (p i) (p (i+1))) : 12 ≤ N := by
  obtain ⟨r, _, hr⟩ : ∃ i < N, Cross (p i) (p (i+1)) := by
    by_contra! H
    exact no_cross_impossible p hN (by simpa using hperiod 0) hne hs H
  let q (i : ℕ) := p (r+i)
  have hqs (i : ℕ) : Step (q i) (q (i+1)) := by simpa [q, Nat.add_assoc] using hs (r+i)
  have hqp (i : ℕ) : q (i+N) = q i := by simpa [q, Nat.add_assoc] using hperiod (r+i)
  have hclose : q N = q 0 := by simpa using hqp 0
  have hqn (i j : ℕ) (hij : i < j) (hj : j < i+N) : q i ≠ q j :=
    hne (r+i) (r+j) (by omega) (by omega)
  have c0 : Cross (q 0) (q 1) := by simpa [q] using hr
  have cN : Cross (q N) (q (N+1)) := by simpa [Nat.add_comm N 1, hqp 1, hclose] using c0
  have gap (i j : ℕ) (ci : Cross (q i) (q (i+1))) (cj : Cross (q j) (q (j+1)))
      (hij : i < j) : i+3 ≤ j := by
    have forbid (i : ℕ) (ci : Cross (q i) (q (i+1))) : ¬ Cross (q (i+1)) (q (i+2)) :=
      fun h => hqn i (i+2) (by omega) (by omega) (cross_at_most_one (cross_symm ci) h)
    by_contra! H
    have : j = i+1 ∨ j = i+2 := by omega
    rcases this with rfl | rfl
    · exact forbid i ci cj
    · have hline := (hqs (i+1)).resolve_right (forbid i ci)
      have h₁ := ci.2.2
      have h₂ := cj.2.1
      have h₃ : (q (i+1)).2.2 + 1 = (q (i+2)).2.2 ∨
          (q (i+2)).2.2 + 1 = (q (i+1)).2.2 := hline.2
      omega
  have return_cross (a : ℕ) (ha : a ≤ N) (h : (q a).1 ≠ (q N).1) :
      ∃ i, a ≤ i ∧ i < N ∧ Cross (q i) (q (i+1)) := by
    by_contra! H
    exact h (rail_along q hqs a N ha H).1
  obtain ⟨j, hj₁, hjN, cj, hjfirst⟩ := first_cross q 1 N
    (return_cross 1 (by omega) (by simpa [hclose] using c0.1.symm))
  have hjgap := gap 0 j c0 cj (by omega)
  have hjend := gap j N cj cN hjN
  have hjrail := rail_along q hqs 1 j hj₁ hjfirst
  have third : ∃ i, j+1 ≤ i ∧ i < N ∧ Cross (q i) (q (i+1)) := by
    by_contra! H
    have hback := rail_symm (rail_along q hqs (j+1) N (by omega) H)
    rw [hclose] at hback
    exact hqn 0 (j+1) (by omega) (by omega)
      (crossing_between_rails c0 (cross_symm cj) hback hjrail)
  obtain ⟨k, hk₁, hkN, ck, hkfirst⟩ := first_cross q (j+1) N third
  have hkgap := gap j k cj ck (by omega)
  have hkra := rail_along q hqs (j+1) k hk₁ hkfirst
  have hkorient : (q k).1 = (q 0).1 := hkra.1.symm.trans
    (bool_same (by simpa [hjrail.1] using cj.1.symm) c0.1)
  obtain ⟨l, hl₁, hlN, cl⟩ := return_cross (k+1) (by omega)
    (by simpa [hclose, hkorient] using ck.1.symm)
  have hlgap := gap k l ck cl (by omega)
  have hlend := gap l N cl cN hlN
  omega

/-- Every simple cycle of the typed base graph has at least twelve edges. -/
theorem lower {m n s : ℕ} (us : Fin (s+2) ↪ L m n) (vs : Fin (s+2) ↪ R m n)
    (hcycle : ∀ i, Adj (us i) (vs i) ∧ Adj (us (i+1)) (vs i)) : 6 ≤ s+2 := by
  let ix (j : ℕ) : Fin (s+2) := ⟨j % (s+2), Nat.mod_lt _ (by omega)⟩
  have hix (j : ℕ) : ix (j+1) = ix j + 1 := by
    apply Fin.ext
    simp [ix, Fin.val_add]
  let w (i : ℕ) : L m n ⊕ R m n :=
    if i % 2 = 0 then .inl (us (ix (i/2))) else .inr (vs (ix (i/2)))
  let p (i : ℕ) := encode (w i)
  have hp (i : ℕ) : p (i+2*(s+2)) = p i := by
    have h₁ : (i+2*(s+2)) % 2 = i%2 := by omega
    have h₂ : (i+2*(s+2)) / 2 = i/2 + (s+2) := by omega
    have h₃ : ix (i/2+(s+2)) = ix (i/2) := by apply Fin.ext; simp [ix]
    simp only [p, w, h₁, h₂, h₃]
  have hn (i j : ℕ) (hij : i < j) (hj : j < i+2*(s+2)) : p i ≠ p j := by
    intro H
    have he : w i = w j := encode_injective H
    have hpar : i % 2 = j % 2 := by
      by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0
      all_goals simp [w, hi, hj] at he
      all_goals omega
    have he' : ix (i/2) = ix (j/2) := by
      by_cases hi : i % 2 = 0
      · have hj : j % 2 = 0 := by omega
        exact us.injective (by simpa [w, hi, hj] using he)
      · have hj : j % 2 ≠ 0 := by omega
        exact vs.injective (by simpa [w, hi, hj] using he)
    have hle : i/2 ≤ j/2 := by omega
    have hdvd := (Nat.modEq_iff_dvd' (n := s+2) hle).mp (congrArg Fin.val he')
    have := Nat.le_of_dvd (by omega : 0 < j/2-i/2) hdvd
    omega
  have hs (i : ℕ) : Step (p i) (p (i+1)) := by
    by_cases hi : i % 2 = 0
    · have hj : (i+1) % 2 ≠ 0 := by omega
      have hd : (i+1) / 2 = i/2 := by omega
      simpa only [p, w, hi, hj, ite_true, ite_false, hd] using adj_step (hcycle (ix (i/2))).1
    · have hj : (i+1) % 2 = 0 := by omega
      have hd : (i+1) / 2 = i/2+1 := by omega
      simpa only [p, w, hi, hj, ite_true, ite_false, hd, hix] using
        step_symm (adj_step (hcycle (ix (i/2))).2)
  have := walk_length p (N := 2*(s+2)) (by omega) hp hn hs
  omega

/-- The unit rectangle on the first two rows and columns gives a twelve-cycle. -/
theorem exists_cycle {m n : ℕ} (hn : 2 ≤ n) (hm : n < m) :
    ∃ (us : Fin (4+2) ↪ L m n) (vs : Fin (4+2) ↪ R m n),
      ∀ i, Adj (us i) (vs i) ∧ Adj (us (i+1)) (vs i) := by
  let r0 : Fin m := ⟨0, by omega⟩
  let r1 : Fin m := ⟨1, by omega⟩
  let c0 : Fin n := ⟨0, by omega⟩
  let c1 : Fin n := ⟨1, by omega⟩
  let vr : Fin (m-1) := ⟨0, by omega⟩
  let hc : Fin (n-1) := ⟨0, by omega⟩
  let l : Fin 6 → L m n := ![.inl (r0,c0), .inl (r0,c1), .inr (vr,c1),
    .inl (r1,c1), .inl (r1,c0), .inr (vr,c0)]
  let r : Fin 6 → R m n := ![.inr (r0,hc), .inl (r0,c1), .inl (r1,c1),
    .inr (r1,hc), .inl (r1,c0), .inl (r0,c0)]
  have hl : Function.Injective l := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | simp [l, r0, r1, c0, c1, Fin.ext_iff] at h
  have hr : Function.Injective r := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | simp [r, r0, r1, c0, c1, Fin.ext_iff] at h
  refine ⟨⟨l, hl⟩, ⟨r, hr⟩, ?_⟩
  intro i
  fin_cases i <;>
    norm_num [l, r, Adj, r0, r1, c0, c1, vr, hc, Fin.ext_iff, Fin.val_add]

end PEqualNP.Outside.L_pcx_341_aux.BaseGirth


namespace PEqualNP.Outside.L_pcx_341_aux.StretchGirth

variable {A B : Type*}

abbrev Edge (rel : A → B → Prop) := {p : A × B // rel p.1 p.2}
abbrev U (rel : A → B → Prop) (t : ℕ) := A ⊕ (Edge rel × Fin t)
abbrev V (rel : A → B → Prop) (t : ℕ) := B ⊕ (Edge rel × Fin t)

def adj (rel : A → B → Prop) (t : ℕ) : U rel t → V rel t → Prop
  | .inl a, .inl b => t = 0 ∧ rel a b
  | .inl a, .inr (e,j) => a = e.val.1 ∧ j.val = 0
  | .inr (e,j), .inl b => b = e.val.2 ∧ j.val+1 = t
  | .inr (e,j), .inr (f,k) => e = f ∧ (j = k ∨ k.val = j.val+1)

def Cycle (rel : A → B → Prop) (s : ℕ) : Prop :=
  ∃ (us : Fin (s+2) ↪ A) (vs : Fin (s+2) ↪ B),
    ∀ i, rel (us i) (vs i) ∧ rel (us (i+1)) (vs i)

section Paths
variable {rel : A → B → Prop} {t : ℕ}

private def prevLeft (e : Edge rel) (j : Fin t) : U rel t :=
  if h : j.val = 0 then .inl e.val.1 else .inr (e, ⟨j.val-1, by omega⟩)

private def nextRight (e : Edge rel) (j : Fin t) : V rel t :=
  if h : j.val+1 = t then .inl e.val.2 else .inr (e, ⟨j.val+1, by omega⟩)

private theorem adj_innerR (u : U rel t) (e : Edge rel) (j : Fin t) :
    adj rel t u (.inr (e,j)) ↔ u = .inr (e,j) ∨ u = prevLeft e j := by
  rcases u with a | ⟨f,k⟩
  · by_cases h : j.val = 0 <;> simp [adj, prevLeft, h]
  · by_cases h : j.val = 0
    · simp [adj, prevLeft, h]
    · simp only [adj, prevLeft, dite_eq_right h, Sum.inr.injEq, Prod.mk.injEq]
      rw [← and_or_left]
      have hk : j.val = k.val+1 ↔ k = (⟨j.val-1, by omega⟩ : Fin t) := by
        rw [Fin.ext_iff]
        change j.val = k.val+1 ↔ k.val = j.val-1
        omega
      rw [hk]

private theorem adj_innerL (v : V rel t) (e : Edge rel) (j : Fin t) :
    adj rel t (.inr (e,j)) v ↔ v = .inr (e,j) ∨ v = nextRight e j := by
  rcases v with b | ⟨f,k⟩
  · by_cases h : j.val+1 = t <;> simp [adj, nextRight, h]
  · by_cases h : j.val+1 = t
    · have hn : k.val ≠ t := by omega
      simp [adj, nextRight, h, hn, eq_comm]
    · simp only [adj, nextRight, dite_eq_right h, Sum.inr.injEq, Prod.mk.injEq]
      rw [← and_or_left, eq_comm (a := e), eq_comm (a := j)]
      rw [Fin.ext_iff (b := (⟨j.val+1, by omega⟩ : Fin t))]

private theorem has_both {X : Type*} {x y p q : X}
    (hne : x ≠ y) (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) :
    (x = p ∨ y = p) ∧ (x = q ∨ y = q) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hne (hx.trans hy.symm)).elim
  · exact ⟨Or.inl hx, Or.inr hy⟩
  · exact ⟨Or.inr hy, Or.inl hx⟩
  · exact (hne (hx.trans hy.symm)).elim

variable (as : ℕ → U rel t) (bs : ℕ → V rel t)
variable (al : ∀ n, adj rel t (as n) (bs n))
variable (ar : ∀ n, adj rel t (as (n+1)) (bs n))
variable (ane : ∀ n, as n ≠ as (n+1))
variable (bne : ∀ n, bs n ≠ bs (n+1))
include al ar ane bne

private theorem forward (n : ℕ) (e : Edge rel) (ht : 0 < t)
    (ha : as n = .inl e.val.1) (hb : bs n = .inr (e, ⟨0, ht⟩)) :
    bs (n+t) = .inl e.val.2 ∧ ∀ j : Fin t, as (n+j.val+1) = .inr (e,j) := by
  have chain : ∀ (j : ℕ) (hj : j < t),
      bs (n+j) = .inr (e, (⟨j,hj⟩ : Fin t)) ∧
      as (n+j+1) = .inr (e, (⟨j,hj⟩ : Fin t)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h := ar n
      rw [hb] at h
      have hh := (adj_innerR _ _ _).mp h
      exact ⟨by simpa using hb, (hh.resolve_right (by simpa [prevLeft, ha] using (ane n).symm))⟩
    | succ j ih =>
      intro hj
      obtain ⟨hB,hA⟩ := ih (by omega)
      have h := al (n+j+1)
      rw [hA] at h
      have hB' := ((adj_innerL _ _ _).mp h).resolve_left ((bne (n+j)).symm ∘ (·.trans hB.symm))
      have hnt : j+1 ≠ t := by omega
      have hB'' : bs (n+(j+1)) = .inr (e, (⟨j+1,hj⟩ : Fin t)) := by
        simpa [nextRight, hnt, Nat.add_assoc] using hB'
      have h := ar (n+(j+1))
      rw [hB''] at h
      have hA' := ((adj_innerR _ _ _).mp h).resolve_right (by
        simpa [prevLeft, ← Nat.add_assoc, ← hA] using (ane (n+j+1)).symm)
      exact ⟨hB'', hA'⟩
  refine ⟨?_, fun j => (chain j.val j.isLt).2⟩
  obtain ⟨hB,hA⟩ := chain (t-1) (by omega)
  have heq : n+(t-1)+1 = n+t := by omega
  have h := al (n+(t-1)+1)
  rw [hA] at h
  have hB' := ((adj_innerL _ _ _).mp h).resolve_left
    ((bne (n+(t-1))).symm ∘ (·.trans hB.symm))
  have hend : t-1+1 = t := by omega
  simpa [nextRight, hend, heq] using hB'

private theorem backward (n : ℕ) (e : Edge rel) (ht : 0 < t)
    (hb : bs n = .inl e.val.2) (ha : as (n+1) = .inr (e, ⟨t-1, by omega⟩)) :
    as (n+t+1) = .inl e.val.1 ∧
      ∀ j : Fin t, as (n+j.val+1) = .inr (e, ⟨t-1-j.val, by omega⟩) := by
  have chain : ∀ (j : ℕ) (hj : j < t),
      as (n+j+1) = .inr (e, (⟨t-1-j, by omega⟩ : Fin t)) ∧
      bs (n+j+1) = .inr (e, (⟨t-1-j, by omega⟩ : Fin t)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h := al (n+1)
      rw [ha] at h
      have hend : t-1+1 = t := by omega
      have hB := ((adj_innerL _ _ _).mp h).resolve_right (by
        simpa [nextRight, hend, hb] using (bne n).symm)
      exact ⟨by simpa using ha, by simpa using hB⟩
    | succ j ih =>
      intro hj
      obtain ⟨hA,hB⟩ := ih (by omega)
      have h := ar (n+j+1)
      rw [hB] at h
      have hA' := ((adj_innerR _ _ _).mp h).resolve_left
        ((ane (n+j+1)).symm ∘ (·.trans hA.symm))
      have hnz : t-1-j ≠ 0 := by omega
      have hidx : t-1-j-1 = t-1-(j+1) := by omega
      have hA'' : as (n+(j+1)+1) = .inr (e, (⟨t-1-(j+1), by omega⟩ : Fin t)) := by
        simpa [prevLeft, hnz, hidx, ← Nat.add_assoc] using hA'
      have h := al (n+(j+1)+1)
      rw [hA''] at h
      have hnt : t-1-(j+1)+1 ≠ t := by omega
      have hidx : t-1-(j+1)+1 = t-1-j := by omega
      have hnt' : t-1-j ≠ t := by omega
      have hB' := ((adj_innerL _ _ _).mp h).resolve_right (by
        simpa [nextRight, hnt, hidx, hnt', ← Nat.add_assoc, ← hB] using (bne (n+j+1)).symm)
      exact ⟨hA'', hB'⟩
  refine ⟨?_, fun j => (chain j.val j.isLt).1⟩
  obtain ⟨hA,hB⟩ := chain (t-1) (by omega)
  have h := ar (n+(t-1)+1)
  rw [hB] at h
  have hA' := ((adj_innerR _ _ _).mp h).resolve_left
    ((ane (n+(t-1)+1)).symm ∘ (·.trans hA.symm))
  have heq : n+(t-1)+1+1 = n+t+1 := by omega
  simpa [prevLeft, heq] using hA'

private theorem block (ht : 0 < t) (n : ℕ) (a : A) (ha : as n = .inl a) :
    ∃ a' b, as (n+(2*t+1)) = .inl a' ∧ bs (n+t) = .inl b ∧
      rel a b ∧ rel a' b ∧ a' ≠ a ∧
      ∀ r, 0 < r → r < 2*t+1 → ∃ p, as (n+r) = .inr p := by
  have h := al n
  rw [ha] at h
  rcases hbn : bs n with b | ⟨e,j⟩
  · rw [hbn] at h
    exact (Nat.ne_of_gt ht h.1).elim
  · rw [hbn] at h
    have ha' := ha.trans (congrArg Sum.inl h.1)
    have hj : j = (⟨0,ht⟩ : Fin t) := Fin.ext h.2
    obtain ⟨hB,hAs⟩ := forward as bs al ar ane bne n e ht ha' (by simpa [hj] using hbn)
    have h' := ar (n+t)
    rw [hB] at h'
    rcases han : as (n+t+1) with a' | ⟨f,k⟩
    · rw [han] at h'
      exact (Nat.ne_of_gt ht h'.1).elim
    · rw [han] at h'
      have hk : k = (⟨t-1, by omega⟩ : Fin t) := Fin.ext (by
        change k.val = t-1
        have := h'.2
        omega)
      obtain ⟨hA,hAs'⟩ := backward as bs al ar ane bne (n+t) f ht
        (hB.trans (congrArg Sum.inl h'.1)) (by simpa [hk] using han)
      have hne : f.val.1 ≠ a := by
        intro same
        have hef : e = f := Subtype.ext (Prod.ext ((h.1.symm).trans same.symm) h'.1)
        have lastA := hAs (⟨t-1, by omega⟩ : Fin t)
        have hin : n+(t-1)+1 = n+t := by omega
        rw [hin, hef] at lastA
        exact ane (n+t) (lastA.trans (by simpa only [hk] using han.symm))
      refine ⟨f.val.1,e.val.2,by simpa [show n+t+t+1 = n+(2*t+1) by omega] using hA,
        hB,by simpa only [h.1] using e.property,by simpa only [h'.1] using f.property,hne,?_⟩
      intro r hr hr'
      by_cases hh : r ≤ t
      · let j : Fin t := ⟨r-1, by omega⟩
        refine ⟨(e,j), ?_⟩
        simpa [show n+j.val+1 = n+r by dsimp [j]; omega] using hAs j
      · let j : Fin t := ⟨r-t-1, by omega⟩
        refine ⟨(f,⟨t-1-j.val, by have := j.isLt; omega⟩), ?_⟩
        simpa [show n+t+j.val+1 = n+r by dsimp [j]; omega] using hAs' j

private theorem has_start {N : ℕ} (hN : 0 < N) (aper : ∀ n, as (n+N) = as n) :
    ∃ n a, as n = .inl a := by
  have innerMate (n : ℕ) (e : Edge rel) (j : Fin t) (h : as n = .inr (e,j)) :
      ∃ q, bs q = .inr (e,j) := by
    let p := n+N-1
    have hA : as (p+1) = .inr (e,j) := by
      rw [show p+1 = n+N by dsimp [p]; omega, aper, h]
    have hp := ar p
    have hp' := al (p+1)
    rw [hA] at hp hp'
    rcases (has_both (bne p) ((adj_innerL _ _ _).mp hp) ((adj_innerL _ _ _).mp hp')).1 with hq | hq
    · exact ⟨p,hq⟩
    · exact ⟨p+1,hq⟩
  rcases h : as 0 with a | ⟨e,j⟩
  · exact ⟨0,a,h⟩
  · obtain ⟨q,hq⟩ := innerMate 0 e j h
    suffices descend : ∀ r : ℕ, ∀ (j : Fin t) (q : ℕ), j.val = r →
        bs q = .inr (e,j) → ∃ n a, as n = .inl a by exact descend j.val j q rfl hq
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro j q hr hq
      have hl := al q
      have hr' := ar q
      rw [hq] at hl hr'
      have hp := (has_both (ane q) ((adj_innerR _ _ _).mp hl) ((adj_innerR _ _ _).mp hr')).2
      obtain ⟨n,hn⟩ : ∃ n, as n = prevLeft e j := hp.elim (fun h => ⟨q,h⟩) (fun h => ⟨q+1,h⟩)
      by_cases hj : j.val = 0
      · exact ⟨n,e.val.1,by simpa [prevLeft, hj] using hn⟩
      · let k : Fin t := ⟨j.val-1, by omega⟩
        obtain ⟨p,hp⟩ := innerMate n e k (by simpa [prevLeft, hj, k] using hn)
        exact ih k.val (by dsimp [k]; omega) k p rfl hp

end Paths

private def unleft (rel : A → B → Prop) : U rel 0 ≃ A where
  toFun := Sum.elim id fun p => Fin.elim0 p.2
  invFun := Sum.inl
  left_inv x := by cases x with | inl a => rfl | inr p => exact Fin.elim0 p.2
  right_inv _ := rfl

private def unright (rel : A → B → Prop) : V rel 0 ≃ B where
  toFun := Sum.elim id fun p => Fin.elim0 p.2
  invFun := Sum.inl
  left_inv x := by cases x with | inl b => rfl | inr p => exact Fin.elim0 p.2
  right_inv _ := rfl

private theorem adj_zero (rel : A → B → Prop) (u : U rel 0) (v : V rel 0) :
    adj rel 0 u v ↔ rel (unleft rel u) (unright rel v) := by
  rcases u with a | p
  · rcases v with b | q
    · change (0 = 0 ∧ rel a b) ↔ rel a b
      simp
    · exact Fin.elim0 q.2
  · exact Fin.elim0 p.2

private def AtLength (rel : A → B → Prop) (k : ℕ) : Prop :=
  ∃ h : 0 < k, letI : NeZero k := ⟨Nat.ne_of_gt h⟩
    ∃ (us : Fin k ↪ A) (vs : Fin k ↪ B),
      ∀ i, rel (us i) (vs i) ∧ rel (us (i+1)) (vs i)

private theorem atLength_iff (rel : A → B → Prop) (s : ℕ) :
    AtLength rel (s+2) ↔ Cycle rel s :=
  ⟨fun ⟨_,h⟩ => h, fun h => ⟨by omega,h⟩⟩

/-- Compress a subdivision cycle by reading its old vertices in cyclic order. Between
two consecutive old left vertices it must traverse two complete edge chains. -/
theorem compress {rel : A → B → Prop} {t s : ℕ} (cycle : Cycle (adj rel t) s) :
    ∃ r, Cycle rel r ∧ (r+2)*(2*t+1) = s+2 := by
  rcases cycle with ⟨us,vs,h⟩
  by_cases ht : t = 0
  · subst t
    exact ⟨s, ⟨us.trans (unleft rel).toEmbedding, vs.trans (unright rel).toEmbedding,
      fun i => ⟨(adj_zero rel _ _).mp (h i).1, (adj_zero rel _ _).mp (h i).2⟩⟩, by simp⟩
  let N := s+2
  have hN : 0 < N := by omega
  have hN' : 1 < N := by omega
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let idx (j : ℕ) : Fin N := ⟨j%N, Nat.mod_lt _ hN⟩
  have idx_add (i j : ℕ) : idx (i+j) = idx i + idx j :=
    Fin.ext (Nat.add_mod i j N)
  have idx_nomod {i : ℕ} (hi : i < N) : idx i = ⟨i,hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
  have idx_next (j : ℕ) : idx (j+1) = idx j + 1 := by
    rw [idx_add]
    rfl
  have idx_nes (j : ℕ) : idx j ≠ idx (j+1) := by
    rw [idx_next]
    intro he
    have he' : (0:Fin N) = 1 := add_left_cancel (by simpa only [add_zero] using he)
    have hv := congrArg Fin.val he'
    simp [Nat.mod_eq_of_lt hN'] at hv
  have idx_inj (p : ℕ) {i j : ℕ} (hi : i < N) (hj : j < N)
      (he : idx (p+i) = idx (p+j)) : i = j := by
    rw [idx_add, idx_add] at he
    exact congrArg Fin.val ((idx_nomod hi).symm.trans ((add_left_cancel he).trans (idx_nomod hj)))
  let as (j : ℕ) := us (idx j)
  let bs (j : ℕ) := vs (idx j)
  have aper (j : ℕ) : as (j+N) = as j := by
    change us (idx (j+N)) = us (idx j)
    exact congrArg us (Fin.ext (Nat.add_mod_right j N))
  have al (j : ℕ) : adj rel t (as j) (bs j) := (h (idx j)).1
  have ar (j : ℕ) : adj rel t (as (j+1)) (bs j) := by simpa [as, bs, idx_next] using (h (idx j)).2
  have ane (j : ℕ) : as j ≠ as (j+1) := fun he => idx_nes j (us.injective he)
  have bne (j : ℕ) : bs j ≠ bs (j+1) := fun he => idx_nes j (vs.injective he)
  have ht' : 0 < t := Nat.pos_of_ne_zero ht
  obtain ⟨n,a,ha⟩ := has_start as bs al ar ane bne hN aper
  let d := 2*t+1
  have hd : 0 < d := by omega
  have step (p : ℕ) (a : A) (ha : as p = .inl a) :
      ∃ a' b, as (p+d) = .inl a' ∧ bs (p+t) = .inl b ∧
      rel a b ∧ rel a' b ∧ a' ≠ a ∧
      ∀ r, 0 < r → r < d → ∃ p', as (p+r) = .inr p' :=
    block as bs al ar ane bne ht' p a ha
  have shift (q : ℕ) : n+q*d+d = n+(q+1)*d := by simp [Nat.add_mul, Nat.add_assoc]
  have iter : ∀ q : ℕ, ∃ a, as (n+q*d) = .inl a := by
    intro q
    induction q with
    | zero => exact ⟨a, by simpa using ha⟩
    | succ q ih =>
      obtain ⟨a',ha'⟩ := ih
      obtain ⟨a'',_,he,_⟩ := step (n+q*d) a' ha'
      exact ⟨a'', (shift q) ▸ he⟩
  let k := N/d
  let r := N%d
  have hNkr : k*d+r=N := by simpa [k,r,Nat.mul_comm] using Nat.div_add_mod N d
  have hr : r < d := Nat.mod_lt _ hd
  have hNk : k*d=N := by
    suffices h : r=0 by simpa [h] using hNkr
    by_contra! h
    obtain ⟨a',ha'⟩ := iter k
    obtain ⟨_,_,_,_,_,_,_,hint⟩ := step (n+k*d) a' ha'
    obtain ⟨p,hp⟩ := hint r (Nat.pos_of_ne_zero h) hr
    rw [Nat.add_assoc, hNkr, aper, ha] at hp
    exact Sum.inl_ne_inr hp
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk0 : k ≠ 0 := by
      intro hz
      simp [hz] at hNk
    have hk1 : k = 1 :=
      Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hk)) (Nat.pos_of_ne_zero hk0)
    have hNd : d = N := by simpa [hk1] using hNk
    obtain ⟨a',_,he,_,_,_,hne,_⟩ := step n a ha
    rw [hNd, aper, ha] at he
    exact hne (Sum.inl.inj he.symm)
  let _ : NeZero k := ⟨by omega⟩
  choose aa haa using iter
  have bExists (q : ℕ) : ∃ b, bs (n+q*d+t) = .inl b := by
    obtain ⟨_,b,_,hb,_⟩ := step (n+q*d) (aa q) (haa q)
    exact ⟨b,hb⟩
  choose bb hbb using bExists
  have base (q : ℕ) : rel (aa q) (bb q) ∧ rel (aa (q+1)) (bb q) := by
    obtain ⟨a',b,ha',hb,hl,hr,_,_⟩ := step (n+q*d) (aa q) (haa q)
    have ea : aa (q+1) = a' := Sum.inl.inj ((haa _).symm.trans ((shift q) ▸ ha'))
    have eb : bb q = b := Sum.inl.inj ((hbb _).symm.trans hb)
    simpa only [ea,eb] using And.intro hl hr
  have wrap (i : Fin k) : aa (i+1 : Fin k).val = aa (i.val+1) := by
    have hmod : (i+1 : Fin k).val = (i.val+1)%k := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k by omega)]
    by_cases hi : i.val+1 < k
    · rw [hmod, Nat.mod_eq_of_lt hi]
    · have hei : i.val+1=k := by have := i.isLt; omega
      apply Sum.inl.inj
      rw [← haa, ← haa, hmod, hei, Nat.mod_self, zero_mul, Nat.add_zero, hNk, aper]
  have within (i : Fin k) : i.val*d < N :=
    hNk ▸ (Nat.mul_lt_mul_of_pos_right i.isLt hd)
  let u : Fin k ↪ A := ⟨fun i => aa i.val, by
    intro i j he
    apply Fin.ext
    have hh : as (n+i.val*d) = as (n+j.val*d) := (haa _).trans ((congrArg Sum.inl he).trans (haa _).symm)
    exact Nat.eq_of_mul_eq_mul_right hd (idx_inj n (within i) (within j) (us.injective hh))⟩
  let v : Fin k ↪ B := ⟨fun i => bb i.val, by
    intro i j he
    apply Fin.ext
    have hh : bs (n+i.val*d+t) = bs (n+j.val*d+t) := (hbb _).trans ((congrArg Sum.inl he).trans (hbb _).symm)
    have hi : idx (n+t+i.val*d) = idx (n+t+j.val*d) := by
      simpa only [show ∀ z, n+t+z=n+z+t by intro z; omega] using vs.injective hh
    exact Nat.eq_of_mul_eq_mul_right hd (idx_inj (n+t) (within i) (within j) hi)⟩
  have hlen : k-2+2=k := by omega
  refine ⟨k-2, ?_, by simpa only [hlen] using hNk⟩
  apply (atLength_iff rel (k-2)).mp
  rw [hlen]
  refine ⟨by omega,u,v,fun i => ⟨(base i.val).1, ?_⟩⟩
  change rel (aa (i+1 : Fin k).val) (bb i.val)
  rw [wrap]
  exact (base i.val).2

private theorem val_next {k : ℕ} [NeZero k] (i : Fin k) :
    (i+1 : Fin k).val = (i.val+1)%k := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

private theorem prod_step_inner {k d : ℕ} [NeZero (k*d)] (q : Fin k) (r : Fin d)
    (hi : r.val+1 < d) :
    finProdFinEquiv (q,r) + 1 = finProdFinEquiv (q,⟨r.val+1,hi⟩) := by
  apply Fin.ext
  rw [val_next]
  change (r.val+d*q.val+1)%(k*d) = r.val+1+d*q.val
  have hb : r.val+1+d*q.val < k*d := (finProdFinEquiv (q, (⟨r.val+1,hi⟩ : Fin d))).isLt
  rw [show r.val+d*q.val+1 = r.val+1+d*q.val by omega, Nat.mod_eq_of_lt hb]

private theorem prod_step_last {k d : ℕ} [NeZero k] [NeZero d] [NeZero (k*d)]
    (q : Fin k) (r : Fin d) (h : r.val+1 = d) :
    finProdFinEquiv (q,r) + 1 = finProdFinEquiv (q+1, (0 : Fin d)) := by
  apply Fin.ext
  rw [val_next]
  change (r.val+d*q.val+1)%(k*d) = 0+d*(q+1 : Fin k).val
  rw [Nat.zero_add, val_next, show r.val+d*q.val+1 = d*(q.val+1) by rw [Nat.mul_add]; omega]
  by_cases hq : q.val+1 < k
  · rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt]
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hq (NeZero.pos d)
  · have he : q.val+1=k := by have := q.isLt; omega
    simp [he, Nat.mul_comm]

section Lift

variable {rel : A → B → Prop} {k : ℕ} [NeZero k]
variable (u : Fin k ↪ A) (v : Fin k ↪ B)
variable (h : ∀ i, rel (u i) (v i) ∧ rel (u (i+1)) (v i))

private def first (q : Fin k) : Edge rel := ⟨(u q,v q),(h q).1⟩
private def second (q : Fin k) : Edge rel := ⟨(u (q+1),v q),(h q).2⟩

private def liftLeft (t : ℕ) (q : Fin k) (r : Fin (2*t+1)) : U rel t :=
  if h0 : r.val=0 then .inl (u q)
  else if h1 : r.val ≤ t then .inr (first u v h q,⟨r.val-1, by omega⟩)
  else .inr (second u v h q,⟨2*t-r.val, by have := r.isLt; omega⟩)

private def liftRight (t : ℕ) (q : Fin k) (r : Fin (2*t+1)) : V rel t :=
  if h1 : r.val < t then .inr (first u v h q,⟨r.val,h1⟩)
  else if h2 : r.val = t then .inl (v q)
  else .inr (second u v h q,⟨2*t-r.val, by have := r.isLt; omega⟩)

private theorem first_inj : Function.Injective (first u v h) := by
  intro i j he
  exact v.injective (congrArg (fun e : Edge rel => e.val.2) he)

private theorem second_inj : Function.Injective (second u v h) := by
  intro i j he
  exact v.injective (congrArg (fun e : Edge rel => e.val.2) he)

private theorem first_ne_second (hk : 1 < k) (i j : Fin k) :
    first u v h i ≠ second u v h j := by
  intro he
  have hq : i=j := v.injective (congrArg (fun e : Edge rel => e.val.2) he)
  have hu : i=j+1 := u.injective (congrArg (fun e : Edge rel => e.val.1) he)
  have he' : (0:Fin k) = 1 := add_left_cancel (a := j) (by simpa only [hq, add_zero] using hu)
  have hv := congrArg Fin.val he'
  simp [Nat.mod_eq_of_lt hk] at hv

private theorem liftLeft_inj (hk : 1 < k) (t : ℕ) :
    Function.Injective (fun p : Fin k × Fin (2*t+1) => liftLeft u v h t p.1 p.2) := by
  rintro ⟨i,r⟩ ⟨j,s⟩ he
  simp only [Prod.mk.injEq]
  by_cases rz : r.val=0 <;> by_cases sz : s.val=0
  · simp only [liftLeft, dite_eq_left rz, dite_eq_left sz, Sum.inl.injEq] at he
    exact ⟨u.injective he, Fin.ext (rz.trans sz.symm)⟩
  · simp only [liftLeft, dite_eq_left rz, dite_eq_right sz] at he
    split at he <;> cases he
  · simp only [liftLeft, dite_eq_right rz, dite_eq_left sz] at he
    split at he <;> cases he
  · simp only [liftLeft, dite_eq_right rz, dite_eq_right sz] at he
    by_cases hr : r.val ≤ t <;> by_cases hs : s.val ≤ t <;> simp only [hr, hs, dite_true, dite_false] at he
    · obtain ⟨he,hr⟩ := Prod.mk.inj (Sum.inr.inj he)
      have hv := congrArg (fun j : Fin t => j.val) hr
      exact ⟨first_inj u v h he, Fin.ext (by dsimp at hv; omega)⟩
    · exact (first_ne_second u v h hk i j (congrArg Prod.fst (Sum.inr.inj he))).elim
    · exact (first_ne_second u v h hk j i (congrArg Prod.fst (Sum.inr.inj he)).symm).elim
    · obtain ⟨he,hr⟩ := Prod.mk.inj (Sum.inr.inj he)
      have := r.isLt
      have := s.isLt
      have hv := congrArg (fun j : Fin t => j.val) hr
      exact ⟨second_inj u v h he, Fin.ext (by dsimp at hv; omega)⟩

private theorem liftRight_inj (hk : 1 < k) (t : ℕ) :
    Function.Injective (fun p : Fin k × Fin (2*t+1) => liftRight u v h t p.1 p.2) := by
  rintro ⟨i,r⟩ ⟨j,s⟩ he
  simp only [Prod.mk.injEq]
  by_cases hr : r.val<t <;> by_cases hs : s.val<t
  · simp only [liftRight, dite_eq_left hr, dite_eq_left hs] at he
    obtain ⟨he,hi⟩ := Prod.mk.inj (Sum.inr.inj he)
    exact ⟨first_inj u v h he, Fin.ext (congrArg (fun j : Fin t => j.val) hi)⟩
  · simp only [liftRight, dite_eq_left hr, dite_eq_right hs] at he
    split at he
    · cases he
    · exact (first_ne_second u v h hk i j (congrArg Prod.fst (Sum.inr.inj he))).elim
  · simp only [liftRight, dite_eq_right hr, dite_eq_left hs] at he
    split at he
    · cases he
    · exact (first_ne_second u v h hk j i (congrArg Prod.fst (Sum.inr.inj he)).symm).elim
  · simp only [liftRight, dite_eq_right hr, dite_eq_right hs] at he
    by_cases hre : r.val=t <;> by_cases hse : s.val=t <;> simp only [hre, hse, dite_true, dite_false] at he
    · exact ⟨v.injective (Sum.inl.inj he), Fin.ext (hre.trans hse.symm)⟩
    · cases he
    · cases he
    · obtain ⟨he,hi⟩ := Prod.mk.inj (Sum.inr.inj he)
      have := r.isLt
      have := s.isLt
      have hv := congrArg (fun j : Fin t => j.val) hi
      exact ⟨second_inj u v h he, Fin.ext (by dsimp at hv; omega)⟩

private theorem lift_same (t : ℕ) (q : Fin k) (r : Fin (2*t+1)) :
    adj rel t (liftLeft u v h t q r) (liftRight u v h t q r) := by
  by_cases ht : r.val < t
  · by_cases hz : r.val = 0
    · simp only [liftLeft, liftRight, dite_eq_left hz, dite_eq_left ht, adj, first]
      exact ⟨True.intro,hz⟩
    · have hn : r.val ≤ t := by omega
      simp [liftLeft, liftRight, ht, hz, hn, adj]
      exact Or.inr (by omega)
  · by_cases he : r.val = t
    · by_cases hz : r.val = 0
      · have ht0 : t=0 := by omega
        simp only [liftLeft, liftRight, dite_eq_left hz, dite_eq_right ht, dite_eq_left he, adj]
        exact ⟨ht0,(h q).1⟩
      · have hn : r.val ≤ t := by omega
        simp only [liftLeft, liftRight, dite_eq_right hz, dite_eq_left hn, dite_eq_right ht,
          dite_eq_left he, adj, first]
        refine ⟨True.intro, ?_⟩
        omega
    · have hz : r.val ≠ 0 := by omega
      have hn : ¬r.val ≤ t := by omega
      simp [liftLeft, liftRight, ht, he, hz, hn, adj]

private theorem lift_next_inner (t : ℕ) (q : Fin k) (r : Fin (2*t+1))
    (hi : r.val+1 < 2*t+1) :
    adj rel t (liftLeft u v h t q ⟨r.val+1,hi⟩) (liftRight u v h t q r) := by
  by_cases ht : r.val < t
  · have hle : r.val+1 ≤ t := by omega
    simp [liftLeft, liftRight, ht, hle, adj]
  · have hle : ¬r.val+1 ≤ t := by omega
    by_cases he : r.val = t
    · simp [liftLeft, liftRight, he, adj, second]
      omega
    · simp [liftLeft, liftRight, ht, he, hle, adj]
      exact Or.inr (by omega)

private theorem lift_next_last (t : ℕ) (q : Fin k) (r : Fin (2*t+1))
    (hi : r.val+1 = 2*t+1) :
    adj rel t (liftLeft u v h t (q+1) 0) (liftRight u v h t q r) := by
  have ht : ¬r.val < t := by omega
  by_cases he : r.val = t
  · have ht0 : t=0 := by omega
    simp [liftLeft, liftRight, he, adj, ht0, (h q).2]
  · simp [liftLeft, liftRight, ht, he, adj, second]
    omega

end Lift

/-- Replace each pair-step of a base cycle by a block of `2*t+1` pair-steps.
The two base edges in each block have disjoint internal vertices. -/
theorem expand {rel : A → B → Prop} {s : ℕ} (cycle : Cycle rel s) (t : ℕ) :
    ∃ j, Cycle (adj rel t) j ∧ j+2=(s+2)*(2*t+1) := by
  rcases cycle with ⟨u,v,h⟩
  let k := s+2
  let d := 2*t+1
  have hk : 1 < k := by omega
  have hd : 0 < d := by omega
  have hkd : 2 ≤ k*d := le_trans (by omega : 2 ≤ k)
    (by simpa using Nat.mul_le_mul_left k hd)
  let _ : NeZero k := ⟨by omega⟩
  let _ : NeZero d := ⟨by omega⟩
  let _ : NeZero (k*d) := ⟨by omega⟩
  let p : Fin (k*d) ≃ Fin k × Fin d := finProdFinEquiv.symm
  let u' : Fin (k*d) ↪ U rel t := ⟨fun i => liftLeft u v h t (p i).1 (p i).2,
    fun _ _ he => p.injective (liftLeft_inj u v h hk t he)⟩
  let v' : Fin (k*d) ↪ V rel t := ⟨fun i => liftRight u v h t (p i).1 (p i).2,
    fun _ _ he => p.injective (liftRight_inj u v h hk t he)⟩
  have hc : AtLength (adj rel t) (k*d) := by
    refine ⟨by omega,u',v',fun i => ⟨lift_same u v h t (p i).1 (p i).2, ?_⟩⟩
    change adj rel t (liftLeft u v h t (p (i+1)).1 (p (i+1)).2)
      (liftRight u v h t (p i).1 (p i).2)
    have eqi : finProdFinEquiv ((p i).1,(p i).2) = i :=
      finProdFinEquiv.apply_symm_apply i
    by_cases hi : (p i).2.val+1 < d
    · have hh := prod_step_inner (p i).1 (p i).2 hi
      rw [eqi] at hh
      have hp : p (i+1) = ((p i).1,⟨(p i).2.val+1,hi⟩) := by
        rw [hh]
        exact finProdFinEquiv.symm_apply_apply _
      rw [hp]
      exact lift_next_inner u v h t (p i).1 (p i).2 hi
    · have hi' : (p i).2.val+1=d := by have := (p i).2.isLt; omega
      have hh := prod_step_last (p i).1 (p i).2 hi'
      rw [eqi] at hh
      have hp : p (i+1) = ((p i).1+1, (0 : Fin d)) := by
        rw [hh]
        exact finProdFinEquiv.symm_apply_apply _
      rw [hp]
      exact lift_next_last u v h t (p i).1 (p i).2 hi'
  have hb : k*d-2+2 = k*d := by omega
  refine ⟨k*d-2, (atLength_iff _ _).mp ?_, hb⟩
  rwa [hb]

/-- A base half-girth of six becomes a half-girth of `6*(2*t+1)`. -/
theorem scale {rel : A → B → Prop} (t : ℕ) (base : Cycle rel 4)
    (lower : ∀ s, Cycle rel s → 6 ≤ s+2) :
    (∃ s, Cycle (adj rel t) s ∧ s+2=6*(2*t+1)) ∧
    (∀ s, Cycle (adj rel t) s → 6*(2*t+1) ≤ s+2) := by
  constructor
  · exact expand base t
  · intro s cycle
    obtain ⟨r,hr,hlen⟩ := compress cycle
    rw [← hlen]
    exact Nat.mul_le_mul_right _ (lower r hr)

end PEqualNP.Outside.L_pcx_341_aux.StretchGirth


namespace PEqualNP.Outside.L_pcx_341_aux.Seed

open PEqualNP.Expanders PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_207_aux

abbrev K (m n : ℕ) : BipGraph m n := fun _ => Finset.univ
abbrev X (m n : ℕ) := GEdge (K m n)

private def bit {m n : ℕ} (i : Fin m) (j : Fin n) : X m n :=
  ⟨(i, j), Finset.mem_univ _⟩

def row {m n : ℕ} (i : Fin m) : Fin n ↪ X m n :=
  ⟨bit i, fun _ _ h => congrArg (fun e : X m n => e.1.2) h⟩

def col {m n : ℕ} (j : Fin n) : Fin m ↪ X m n :=
  ⟨fun i => bit i j, fun _ _ h => congrArg (fun e : X m n => e.1.1) h⟩

def pref {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : ℕ) : Finset V :=
  (Finset.univ.filter fun i : Fin d => i.val < j).map v

theorem prefix_card {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : ℕ) :
    (pref v j).card ≤ d := by
  rw [pref, Finset.card_map]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem prefix_zero {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) :
    pref v 0 = ∅ := by simp [pref]

theorem prefix_end {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) :
    pref v d = Finset.univ.map v := by simp [pref, Fin.is_lt]

theorem prefix_miss {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d) :
    v j ∉ pref v j.val := by simp [pref]

theorem prefix_succ {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d) :
    pref v (j.val + 1) = insert (v j) (pref v j.val) := by
  have h : (Finset.univ.filter fun i : Fin d => i.val < j.val + 1) =
      insert j (Finset.univ.filter fun i : Fin d => i.val < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [pref, h, Finset.map_insert, pref]

def guard {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d) : LinKLine V :=
  Dl (v j) (pref v j.val)

def oddRow {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) : LinKLine V :=
  {{(pref v d, true)}}

theorem sat_guard {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d)
    (a : V → Bool) : LinKLineSat a (guard v j) ↔ a (v j) = false ∨ ¬ par a (pref v j.val) :=
  sat_Dl _ _ _

theorem sat_oddRow {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (a : V → Bool) :
    LinKLineSat a (oddRow v) ↔ par a (pref v d) := by
  simp [oddRow, LinKLineSat, LinTermSat, eqSat]

abbrev Der {V : Type} [DecidableEq V] (F : Set (Clause V)) :=
  IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' F)

private theorem appendDer {V : Type} [DecidableEq V] {F : Set (Clause V)} {p q : List (LinKLine V)}
    (hp : Der F p) (hq : Der F q) : Der F (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ a w ih => exact .ax ih a w
  | cut _ a b c w ih => exact .cut ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | andIntro _ a b c w ih => exact .andIntro ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | weak _ a b w ih => exact .weak ih (List.mem_append_left _ a) b w

private theorem collect {I V : Type} [DecidableEq V] {F : Set (Clause V)}
    (is : Finset I) (L : I → LinKLine V) (B : ℕ)
    (each : ∀ i ∈ is, ∃ π, Der F π ∧ L i ∈ π ∧ π.length ≤ B) :
    ∃ π, Der F π ∧ (∀ i ∈ is, L i ∈ π) ∧ π.length ≤ is.card * B := by
  classical
  induction is using Finset.induction_on with
  | empty => exact ⟨[], .nil, by simp, by simp⟩
  | @insert i is hi ih =>
    obtain ⟨p, dp, mp, lp⟩ := each i (by simp)
    obtain ⟨q, dq, mq, lq⟩ := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    refine ⟨p ++ q, appendDer dp dq, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact List.mem_append_left _ mp
      · exact List.mem_append_right _ (mq j hj)
    · rw [List.length_append, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul]
      omega

private theorem rowAxiom {m n : ℕ} (i : Fin m) :
    (Finset.univ.map (row i)).image (fun x => (x, true)) ∈ funGraphPHP (K m n) := by
  apply Or.inl
  apply Or.inl
  refine ⟨i, ?_⟩
  ext l
  rcases l with ⟨⟨⟨i', j⟩, hj⟩, b⟩
  simp only [Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, h⟩
    exact ⟨(congrArg (fun x : Literal (X m n) => x.1.1.1) h).symm,
      (congrArg Prod.snd h).symm⟩
  · rintro ⟨h, rfl⟩
    subst i'
    exact ⟨_, ⟨j, rfl⟩, rfl⟩

private theorem pairRow {m n : ℕ} (i : Fin m) (j l : Fin n) (h : j ≠ l) :
    {(row i j, false), (row i l, false)} ∈ funGraphPHP (K m n) :=
  Or.inr ⟨row i j, row i l, rfl, h, rfl⟩

private theorem pairCol {m n : ℕ} (j : Fin n) (i h : Fin m) (ne : i ≠ h) :
    {(col j i, false), (col j h, false)} ∈ funGraphPHP (K m n) :=
  Or.inl (Or.inr ⟨col j i, col j h, rfl, ne, rfl⟩)

private theorem guardOne {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (F : Set (Clause V))
    (C : Clause V) (hC : C ∈ F) (pair : ∀ i j, i ≠ j → {(v i, false), (v j, false)} ∈ F)
    (j : Fin d) : ∃ π, Der F π ∧ guard v j ∈ π ∧ π.length ≤ 5 * d + 2 := by
  let S := Finset.univ.map v
  have pairs : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ F := by
    intro x hx y hy ne
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hy
    exact pair i l (fun e => ne (congrArg v e))
  have sub : pref v j.val ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨π, len, mem, der⟩ := dchain F S pairs (v j) (by simp [S]) (pref v j.val)
    sub (prefix_miss v j) [linKOfClause C] (addAx .nil hC) (by simp)
  refine ⟨π ++ [linKOfClause C], der, mem, ?_⟩
  have h := prefix_card v j.val
  simp only [List.length_append, List.length_singleton]
  omega

private theorem oddOne {m n : ℕ} (i : Fin m) :
    ∃ π, Der (funGraphPHP (K m n)) π ∧ oddRow (row i) ∈ π ∧ π.length ≤ 4 * (n + 1) ^ 2 := by
  let S := Finset.univ.map (row (n := n) i)
  have pair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ funGraphPHP (K m n) := by
    intro x hx y hy h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hy
    exact pairRow i j l (fun e => h (congrArg (row i) e))
  obtain ⟨π, d, h, len⟩ := PEqualNP.Outside.L_pcx_207 _ S _ (rowAxiom i) pair
  exact ⟨π, d, by simpa [oddRow, prefix_end, S] using h, by simpa [S] using len⟩

theorem prelude (m n : ℕ) (hn : 2 ≤ n) (hm : n < m) :
    ∃ seed : List (LinKLine (X m n)), Der (funGraphPHP (K m n)) seed ∧
      (∀ i : Fin m, oddRow (row i) ∈ seed) ∧
      (∀ (i : Fin m) (j : Fin n), guard (row i) j ∈ seed) ∧
      (∀ (i : Fin m) (j : Fin n), guard (col j) i ∈ seed) ∧
      seed.length ≤ 16 * m * n * (m + n) := by
  let F := funGraphPHP (K m n)
  let i₀ : Fin m := ⟨0, by omega⟩
  obtain ⟨p, dp, mp, lp⟩ := collect (F := F) (Finset.univ : Finset (Fin m))
    (fun i => oddRow (row (n := n) i)) (4 * (n + 1) ^ 2)
    (fun i _ => oddOne (n := n) i)
  obtain ⟨q, dq, mq, lq⟩ := collect (Finset.univ : Finset (Fin m × Fin n))
    (fun ij => guard (row ij.1) ij.2) (5 * n + 2)
    (fun ij _ => guardOne (row ij.1) F _ (rowAxiom i₀) (pairRow ij.1) ij.2)
  obtain ⟨r, dr, mr, lr⟩ := collect (Finset.univ : Finset (Fin m × Fin n))
    (fun ij => guard (col ij.2) ij.1) (5 * m + 2)
    (fun ij _ => guardOne (col ij.2) F _ (rowAxiom i₀) (pairCol ij.2) ij.1)
  refine ⟨p ++ q ++ r, appendDer (appendDer dp dq) dr, ?_, ?_, ?_, ?_⟩
  · intro i
    exact List.mem_append_left _ (List.mem_append_left _ (mp i (Finset.mem_univ i)))
  · intro i j
    exact List.mem_append_left _ (List.mem_append_right _ (mq (i, j) (Finset.mem_univ _)))
  · intro i j
    exact List.mem_append_right _ (mr (i, j) (Finset.mem_univ _))
  · simp only [List.length_append, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at lp lq lr ⊢
    have hp : 4 * (n + 1) ^ 2 ≤ 9 * n ^ 2 := by nlinarith
    have hq : 5 * n + 2 ≤ 6 * n := by omega
    have hr : 5 * m + 2 ≤ 6 * m := by omega
    have hp' := Nat.mul_le_mul_left m hp
    have hq' := Nat.mul_le_mul_left (m*n) hq
    have hr' := Nat.mul_le_mul_left (m*n) hr
    nlinarith [Nat.zero_le (m*m*n), Nat.zero_le (m*n*n)]
end PEqualNP.Outside.L_pcx_341_aux.Seed


namespace PEqualNP.Outside.L_pcx_341_aux.Replay

open PEqualNP.ProofComplexity

/- The LinK replay and symmetric-difference parity arguments are adapted from
   lean/PEqualNP/Outside/L_pcx_209.lean at 9c8d100ad8ad29959bccaea9221609c45cb4215f.
   Here substitutions carry affine offsets, and a translated initial line may follow from the seed. -/

variable {V W : Type} [DecidableEq V] [DecidableEq W]

abbrev img (project : LinEq V → LinEq W) (L : LinKLine V) : LinKLine W :=
  L.image (fun T => T.image project)

omit [DecidableEq V] in
private theorem width_img (project : LinEq V → LinEq W) {k : ℕ} {L : LinKLine V}
    (h : ∀ T ∈ L, T.card ≤ k) : ∀ T ∈ img project L, T.card ≤ k := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
  exact Finset.card_image_le.trans (h S hS)

omit [DecidableEq W] in
private theorem weak_sub {L M : LinKLine W} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

omit [DecidableEq V] in
private theorem termSat_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) (a : W → Bool)
    (T : LinTerm V) : LinTermSat a (T.image project) ↔ LinTermSat (extend a) T := by
  constructor
  · intro h e he
    exact (hsat a e).1 (h _ (Finset.mem_image_of_mem _ he))
  · intro h q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
    exact (hsat a e).2 (h e he)

omit [DecidableEq V] in
private theorem sat_single (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

private theorem cut_img (project : LinEq V → LinEq W)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e)) {C D R : LinKLine V}
    (h : IsLinKCut C D R) :
    ∃ R', IsLinKCut (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T, hT, hD, rfl⟩ := h
  refine ⟨(img project C).erase (T.image project) ∪ (img project D \
    (T.image project).image (fun e => ({negLinEq e} : LinTerm W))),
    ⟨T.image project, Finset.mem_image_of_mem _ hT, ?_, rfl⟩, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    have h1 : ({negLinEq e0} : LinTerm V).image project = {negLinEq (project e0)} := by
      rw [Finset.image_singleton, hneg]
    rw [← h1]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) (hD e0 he0)
  · intro S hS
    rcases Finset.mem_union.1 hS with h1 | h1
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩))
    · obtain ⟨hS, hn⟩ := Finset.mem_sdiff.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      refine Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hU, ?_⟩))
      intro hU'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hU'
      apply hn
      refine Finset.mem_image.2 ⟨project e, Finset.mem_image_of_mem _ he, ?_⟩
      rw [Finset.image_singleton, hneg]

private theorem and_img (project : LinEq V → LinEq W) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) :
    ∃ R', IsLinKAndIntro (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  refine ⟨((img project C).erase (T₁.image project) ∪ (img project D).erase (T₂.image project))
    ∪ {T₁.image project ∪ T₂.image project},
    ⟨_, _, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, rfl⟩, ?_⟩
  intro S hS
  rcases Finset.mem_union.1 hS with hS | hS
  · rcases Finset.mem_union.1 hS with hS | hS
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₁ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₂ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
  · rw [Finset.mem_singleton.1 hS, ← Finset.image_union]
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

omit [DecidableEq V] in
private theorem weak_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {L M : LinKLine V}
    (h : IsLinKWeakening L M) : IsLinKWeakening (img project L) (img project M) := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
  rcases h T hT with ⟨S, hS, hTS⟩ | hq
  · exact Or.inl ⟨S.image project, Finset.mem_image_of_mem _ hS, fun a ha =>
      (termSat_img project extend hsat a S).2 (hTS _ ((termSat_img project extend hsat a T).1 ha))⟩
  · right
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hq _ ((termSat_img project extend hsat a T).1 ha)
    refine ⟨project q, ?_, (hsat a q).2 hq2⟩
    rw [show ({project q} : LinTerm W) = ({q} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) hq1

private theorem ax_weak (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {C : Clause V}
    {D : LinKLine W} (hCD : ∀ a, LinKLineSat a D → ClauseSat (extend a) C) :
    IsLinKWeakening D (img project (linKOfClause C)) := by
  intro T hT
  right
  intro a ha
  obtain ⟨l, hl, hs⟩ := hCD a ⟨T, hT, ha⟩
  refine ⟨project (({l.1} : Finset V), l.2), ?_,
    (hsat a _).2 ((sat_single (extend a) l.1 l.2).2 hs)⟩
  rw [show ({project (({l.1} : Finset V), l.2)} : LinTerm W) =
      ({(({l.1} : Finset V), l.2)} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
  refine Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) ?_
  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hl)

private theorem clause_of_line_sat (a : W → Bool) (D : Clause W)
    (h : LinKLineSat a (linKOfClause D)) : ClauseSat a D := by
  obtain ⟨T, hT, ha⟩ := h
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hT
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
  exact ⟨l, hl, (sat_single a l.1 l.2).1 (ha _ (Finset.mem_singleton_self _))⟩

private theorem width_clause {k : ℕ} (hk : 1 ≤ k) (D : Clause W) :
    ∀ T ∈ linKOfClause D, T.card ≤ k := by
  intro T hT
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hT
  rw [Finset.card_singleton]; exact hk

theorem wider {F : Set (Clause V)} {k : ℕ} (hk : 1 ≤ k) {p : List (LinKLine V)}
    (h : IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' F) p) :
    IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) p := by
  induction h with
  | nil => exact .nil
  | ax _ a w ih => exact .ax ih a (fun t ht => (w t ht).trans hk)
  | cut _ a b c w ih => exact .cut ih a b c (fun t ht => (w t ht).trans hk)
  | andIntro _ a b c w ih => exact .andIntro ih a b c (fun t ht => (w t ht).trans hk)
  | weak _ a b w ih => exact .weak ih a b (fun t ht => (w t ht).trans hk)

theorem appendDer {F : Set (Clause V)} {k : ℕ} {p q : List (LinKLine V)}
    (hp : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) p)
    (hq : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) q) :
    IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ a w ih => exact .ax ih a w
  | cut _ a b c w ih => exact .cut ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | andIntro _ a b c w ih => exact .andIntro ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | weak _ a b w ih => exact .weak ih (List.mem_append_left _ a) b w

private theorem translate (k : ℕ) (F : Set (Clause V)) (H : Set (Clause W))
    (extend : (W → Bool) → V → Bool) (project : LinEq V → LinEq W) (hk : 1 ≤ k)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e))
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e)
    (seed : List (LinKLine W))
    (dseed : IsLinKDerivation k IsLinKWeakening (linKOfClause '' H) seed)
    (hax : ∀ C ∈ F, (∃ D ∈ H, ∀ a, ClauseSat a D → ClauseSat (extend a) C) ∨
      (∃ D ∈ seed, ∀ a, LinKLineSat a D → ClauseSat (extend a) C))
    (π : List (LinKLine V))
    (h : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) π) :
    ∃ τ : List (LinKLine W),
      IsLinKDerivation k IsLinKWeakening (linKOfClause '' H) (τ ++ seed) ∧
      τ.length ≤ 2 * π.length ∧ ∀ L ∈ π, img project L ∈ τ ++ seed := by
  induction h with
  | nil => exact ⟨[], dseed, by simp, by simp⟩
  | @ax π C _ hC hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨C0, hC0, rfl⟩ := hC
    rcases hax C0 hC0 with ⟨D, hD, hCD⟩ | ⟨D, hD, hCD⟩
    · refine ⟨img project (linKOfClause C0) :: linKOfClause D :: τ,
        .weak (.ax hτ ⟨D, hD, rfl⟩ (width_clause hk D)) (List.mem_cons.2 (Or.inl rfl))
          (ax_weak project extend hsat (fun a ha => hCD a (clause_of_line_sat a D ha)))
          (width_img project hw), ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro L hL
        rcases List.mem_cons.1 hL with rfl | hL
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
    · refine ⟨img project (linKOfClause C0) :: τ,
        .weak hτ (List.mem_append_right _ hD) (ax_weak project extend hsat hCD)
          (width_img project hw), ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro L hL
        rcases List.mem_cons.1 hL with rfl | hL
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (hm L hL)
  | @cut π C D R _ hC hD hcut hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := cut_img project hneg hcut
    refine ⟨img project R :: R' :: τ,
      .weak (.cut hτ (hm _ hC) (hm _ hD) hR' (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @andIntro π C D R _ hC hD hand hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := and_img project hand
    refine ⟨img project R :: R' :: τ,
      .weak (.andIntro hτ (hm _ hC) (hm _ hD) hR'
        (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @weak π C D _ hC hW hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    refine ⟨img project D :: τ,
      .weak hτ (hm _ hC) (weak_img project extend hsat hW) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (hm L hL)

abbrev par (a : V → Bool) (f : Finset V) : Prop := Odd (f.filter (fun v => a v = true)).card

private theorem card_sd (s t : Finset V) :
    (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : V → Bool) (s t : Finset V) :
    par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

private def paritySupport {X : Type} (support : X → Finset V) : List X → Finset V
  | [] => ∅
  | x :: xs => symmDiff (support x) (paritySupport support xs)

private def parityOffset {X : Type} (const : X → Bool) : List X → Bool
  | [] => false
  | x :: xs => Bool.xor (const x) (parityOffset const xs)

def value {X : Type} (support : X → Finset V) (const : X → Bool)
    (a : V → Bool) (x : X) : Bool :=
  Bool.xor (decide (par a (support x))) (const x)

noncomputable def projection {X : Type} (support : X → Finset V) (const : X → Bool)
    (e : LinEq X) : LinEq V :=
  (paritySupport support e.1.toList, Bool.xor e.2 (parityOffset const e.1.toList))

private theorem parityList {X : Type} (support : X → Finset V) (const : X → Bool)
    (a : V → Bool) (l : List X) :
    (decide (par a (paritySupport support l))) =
      Bool.xor (decide (Odd (l.filter (value support const a)).length)) (parityOffset const l) := by
  induction l with
  | nil => simp [par, paritySupport, parityOffset]
  | cons x l ih =>
    have diff (s t : Finset V) : decide (par a (symmDiff s t)) =
        Bool.xor (decide (par a s)) (decide (par a t)) := by
      by_cases hs : par a s <;> by_cases ht : par a t <;> simp [par_sd, hs, ht]
    have step : decide (Odd ((x :: l).filter (value support const a)).length) =
        Bool.xor (value support const a x) (decide (Odd (l.filter (value support const a)).length)) := by
      have oddSucc (n : ℕ) : Odd (n + 1) ↔ ¬ Odd n := by simp only [Nat.odd_iff]; omega
      cases hx : value support const a x with
      | false => simp only [List.filter_cons_of_neg (Bool.eq_false_iff.mp hx), Bool.false_xor]
      | true => simp only [List.filter_cons_of_pos hx, List.length_cons, oddSucc, decide_not, Bool.true_xor]
    rw [paritySupport, diff, ih, parityOffset, step]
    conv_rhs => lhs; lhs; unfold value
    generalize decide (par a (support x)) = p, const x = c
    generalize decide (Odd (l.filter (value support const a)).length) = q, parityOffset const l = d
    cases p <;> cases c <;> cases q <;> cases d <;> rfl

theorem projection_sat {X : Type} (support : X → Finset V) (const : X → Bool)
    (a : V → Bool) (e : LinEq X) :
    LinEqSat a (projection support const e) ↔ LinEqSat (value support const a) e := by
  classical
  rcases e with ⟨s, b⟩
  have eq : (s.toList.filter (value support const a)).toFinset =
      s.filter (fun x => value support const a x = true) := by
    ext x
    simp
  have hlen := List.toFinset_card_of_nodup (s.nodup_toList.filter (value support const a))
  rw [eq] at hlen
  have sat {Y : Type} (a' : Y → Bool) (e' : LinEq Y) :
      LinEqSat a' e' ↔ decide (par a' e'.1) = e'.2 := by
    rcases e' with ⟨s', b'⟩
    cases b' <;> simp [LinEqSat, par]
  rw [sat, sat]
  change decide (par a (paritySupport support s.toList)) = Bool.xor b (parityOffset const s.toList) ↔
    decide (Odd (s.filter (fun x => value support const a x = true)).card) = b
  rw [parityList support const a, hlen]
  generalize decide (Odd (s.toList.filter (value support const a)).length) = q
  generalize parityOffset const s.toList = d
  cases q <;> cases b <;> cases d <;> decide

theorem singleProj {X : Type} [DecidableEq X] (support : X → Finset V) (const : X → Bool)
    (x : X) (b : Bool) : projection support const ({x}, b) = (support x, Bool.xor b (const x)) := by
  simp [projection, paritySupport, parityOffset]

private theorem projection_neg {X : Type} (support : X → Finset V) (const : X → Bool)
    (e : LinEq X) : projection support const (negLinEq e) = negLinEq (projection support const e) := by
  rcases e with ⟨s, b⟩
  simp only [projection, negLinEq]
  cases b <;> cases parityOffset const s.toList <;> rfl

/-- Replay an affine substitution with at most two new target lines per source line. -/
theorem simulate (k : ℕ) (F : Set (Clause V)) (H : Set (Clause W))
    (support : V → Finset W) (const : V → Bool) (hk : 1 ≤ k)
    (seed : List (LinKLine W))
    (dseed : IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' H) seed)
    (hax : ∀ C ∈ F, (∃ D ∈ H, ∀ a, ClauseSat a D → ClauseSat (value support const a) C) ∨
      (∃ D ∈ seed, ∀ a, LinKLineSat a D → ClauseSat (value support const a) C))
    (π : List (LinKLine V)) (h : IsLinKRefutation k F π) :
    ∃ τ, IsLinKRefutation k H τ ∧ τ.length ≤ 2 * π.length + seed.length := by
  obtain ⟨t, dt, lt, mem⟩ := translate k F H (value support const) (projection support const) hk
    (projection_neg support const) (projection_sat support const) seed (wider hk dseed) hax π h.1
  refine ⟨t ++ seed, ⟨dt, ?_⟩, ?_⟩
  · simpa [img] using mem ∅ h.2
  · simpa only [List.length_append] using Nat.add_le_add_right lt seed.length

end PEqualNP.Outside.L_pcx_341_aux.Replay

namespace PEqualNP.Outside.L_pcx_341_aux.BaseModel

open PEqualNP.Expanders PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_207_aux
open Seed GraphCounts

private abbrev Spec (V : Type) := Finset V × Bool

noncomputable def eval {V : Type} (a : V → Bool) (s : Spec V) : Bool := by
  classical
  exact decide (par a s.1) ^^ s.2

private theorem eval_flip {V : Type} (a : V → Bool) (s : Finset V) :
    eval a (s, true) = !eval a (s, false) := by
  classical
  by_cases h : par a s <;> simp [eval, h]

private theorem eval_bit {V : Type} [DecidableEq V] (a : V → Bool) (x : V) :
    eval a ({x}, false) = a x := by
  classical
  cases h : a x <;> simp [eval, par, Finset.filter_singleton, h]

private theorem eval_succ {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d)
    (a : V → Bool) : eval a (pref v (j.val + 1), false) =
      (eval a (pref v j.val, false) ^^ a (v j)) := by
  classical
  have hh := par_insert a (prefix_miss v j)
  cases h : a (v j) <;> by_cases p : par a (pref v j.val) <;>
    simp [eval, prefix_succ, hh, h, p]

private theorem eval_zero {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (a : V → Bool) :
    eval a (pref v 0, false) = false := by simp [prefix_zero, eval, par]

private abbrev Neigh (d : ℕ) := Unit ⊕ Fin (d-1)

private def valid {d : ℕ} (j : Fin d) : Neigh d → Prop :=
  Sum.elim (fun _ => True) (fun s => j.val = s.val ∨ j.val = s.val + 1)

private def port {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d) : Neigh d → Spec V :=
  Sum.elim (fun _ => ({v j}, false)) fun s => (pref v (s.val + 1), decide (j.val = s.val))

private theorem at_before {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (a : V → Bool)
    (j : Fin d) (s : Fin (d-1)) (h : j.val = s.val + 1) :
    eval a (port v j (.inr s)) = eval a (pref v j.val, false) := by
  simp [port, h]

private theorem at_after {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (a : V → Bool)
    (j : Fin d) (s : Fin (d-1)) (h : j.val = s.val) :
    eval a (port v j (.inr s)) = !(eval a (pref v j.val, false) ^^ a (v j)) := by
  simpa only [port, Sum.elim_inr, h, decide_true, eval_flip] using
    congrArg Bool.not (eval_succ v j a)

private theorem port_unique {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d)
    (a : V → Bool) (hg : LinKLineSat a (guard v j)) (q q' : Neigh d)
    (hq : valid j q) (hq' : valid j q')
    (h : eval a (port v j q) = true) (h' : eval a (port v j q') = true) : q = q' := by
  classical
  have guard' : a (v j) = false ∨ eval a (pref v j.val, false) = false := by
    rcases (sat_guard v j a).mp hg with h | h
    · exact Or.inl h
    · exact Or.inr (by simp [eval, h])
  have excl (A B : Bool) (H : B = false ∨ A = false) :
      ¬(B = true ∧ A = true) ∧ ¬(B = true ∧ !(A ^^ B) = true) ∧
        ¬(A = true ∧ !(A ^^ B) = true) := by
    cases A <;> cases B <;> simp_all
  obtain ⟨hba, hbc, hac⟩ := excl _ _ guard'
  cases q with
  | inl u =>
    change eval a ({v j}, false) = true at h
    rw [eval_bit] at h
    cases q' with
    | inl u' => cases u; cases u'; rfl
    | inr s =>
      rcases hq' with hs | hs
      · exact (hbc ⟨h, (at_after v a j s hs).symm ▸ h'⟩).elim
      · exact (hba ⟨h, (at_before v a j s hs).symm ▸ h'⟩).elim
  | inr s =>
    cases q' with
    | inl _ =>
      change eval a ({v j}, false) = true at h'
      rw [eval_bit] at h'
      rcases hq with hs | hs
      · exact (hbc ⟨h', (at_after v a j s hs).symm ▸ h⟩).elim
      · exact (hba ⟨h', (at_before v a j s hs).symm ▸ h⟩).elim
    | inr s' =>
      rcases hq with hs | hs <;> rcases hq' with hs' | hs'
      · exact congrArg Sum.inr (Fin.ext (by omega))
      · exact (hac ⟨(at_before v a j s' hs').symm ▸ h', (at_after v a j s hs).symm ▸ h⟩).elim
      · exact (hac ⟨(at_before v a j s hs).symm ▸ h, (at_after v a j s' hs').symm ▸ h'⟩).elim
      · exact congrArg Sum.inr (Fin.ext (by omega))

private theorem port_positive {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (j : Fin d)
    (a : V → Bool) (hodd : LinKLineSat a (oddRow v)) :
    ∃ q : Neigh d, valid j q ∧ eval a (port v j q) = true := by
  cases hb : a (v j)
  case true => exact ⟨.inl (), trivial, (eval_bit a (v j)).trans hb⟩
  case false =>
    cases ha : eval a (pref v j.val, false)
    case true =>
      have hj : 0 < j.val := by
        by_contra! he
        have hz : j.val = 0 := by omega
        rw [hz, eval_zero] at ha
        contradiction
      let s : Fin (d-1) := ⟨j.val-1, by have := j.isLt; omega⟩
      have hjs : j.val = s.val + 1 := by dsimp [s]; omega
      exact ⟨.inr s, Or.inr hjs, (at_before v a j s hjs).trans ha⟩
    case false =>
      have hj : j.val < d-1 := by
        by_contra! he
        have hd : j.val + 1 = d := by have := j.isLt; omega
        have htrue : eval a (pref v d, false) = true := by
          classical
          simp [eval, (sat_oddRow v a).mp hodd]
        have heq := congrArg (pref v) hd
        rw [← heq, eval_succ, ha, hb] at htrue
        contradiction
      let s : Fin (d-1) := ⟨j.val, hj⟩
      exact ⟨.inr s, Or.inl rfl, by rw [at_after v a j s rfl, ha, hb]; rfl⟩

private theorem opposite {V : Type} [DecidableEq V] {d : ℕ} (v : Fin d ↪ V) (a : V → Bool)
    (s : Fin (d-1)) (j j' : Fin d)
    (hj : j.val = s.val ∨ j.val = s.val + 1) (hj' : j'.val = s.val ∨ j'.val = s.val + 1)
    (hne : j ≠ j') : eval a (port v j (.inr s)) = !(eval a (port v j' (.inr s))) := by
  rcases hj with h | h <;> rcases hj' with h' | h'
  · exact (hne (Fin.ext (h.trans h'.symm))).elim
  · have ne' : j'.val ≠ s.val := by omega
    simp [port, h, ne', eval_flip]
  · have ne : j.val ≠ s.val := by omega
    simp [port, h', ne, eval_flip]
  · exact (hne (Fin.ext (h.trans h'.symm))).elim

private noncomputable def left {m n : ℕ} (e : E m n) : L m n := (Fintype.equivFin _).symm e.1.1
private noncomputable def right {m n : ℕ} (e : E m n) : R m n := (Fintype.equivFin _).symm e.1.2

private theorem edge {m n : ℕ} (e : E m n) : baseAdj m n (left e) (right e) = true := by
  simpa only [H, left, right, Finset.mem_filter, Finset.mem_univ, true_and] using e.2

private noncomputable def mkEdge {m n : ℕ} (l : L m n) (r : R m n) (h : baseAdj m n l r = true) : E m n :=
  ⟨(Fintype.equivFin _ l, Fintype.equivFin _ r), by simpa [H] using h⟩

private theorem mkLeft {m n : ℕ} (l : L m n) (r : R m n) (h : baseAdj m n l r = true) :
    left (mkEdge l r h) = l := Equiv.symm_apply_apply _ _

private theorem mkRight {m n : ℕ} (l : L m n) (r : R m n) (h : baseAdj m n l r = true) :
    right (mkEdge l r h) = r := Equiv.symm_apply_apply _ _

noncomputable def spec {m n : ℕ} (e : E m n) : Spec (X m n) :=
  match left e, right e with
  | .inl p, .inl _ => port (row p.1) p.2 (.inl ())
  | .inl p, .inr s => port (row p.1) p.2 (.inr s.2)
  | .inr s, .inl p => port (col p.2) p.1 (.inr s.1)
  | .inr _, .inr _ => (∅, false)

private def leftNbr {m n : ℕ} (p : Cell m n) : Neigh n → R m n :=
  Sum.elim (fun _ => .inl p) (fun s => .inr (p.1, s))

private theorem leftNbr_valid {m n : ℕ} (p : Cell m n) (q : Neigh n) (hq : valid p.2 q) :
    baseAdj m n (.inl p) (leftNbr p q) = true := by
  cases q with
  | inl u => simp [leftNbr, baseAdj]
  | inr s => simpa [leftNbr, baseAdj, valid] using hq

private theorem left_case {m n : ℕ} (e : E m n) (p : Cell m n) (hl : left e = .inl p) :
    ∃ q : Neigh n, valid p.2 q ∧ right e = leftNbr p q ∧ spec e = port (row p.1) p.2 q := by
  have he := edge e
  rw [hl] at he
  cases hr : right e with
  | inl p' =>
    have eq : p = p' := by simpa [baseAdj, hr] using he
    subst p'
    exact ⟨.inl (), trivial, rfl, by simp [spec, hl, hr]⟩
  | inr s =>
    obtain ⟨i, j⟩ := s
    have he' : p.1 = i ∧ valid p.2 (.inr j) := by simpa [baseAdj, valid, hr] using he
    rcases he' with ⟨hi, hj⟩
    subst i
    exact ⟨.inr j, hj, rfl, by simp [spec, hl, hr]⟩

private def rightNbr {m n : ℕ} (p : Cell m n) : Neigh m → L m n :=
  Sum.elim (fun _ => .inl p) (fun s => .inr (s, p.2))

private theorem right_case {m n : ℕ} (e : E m n) (p : Cell m n) (hr : right e = .inl p) :
    ∃ q : Neigh m, valid p.1 q ∧ left e = rightNbr p q ∧ spec e = port (col p.2) p.1 q := by
  have he := edge e
  rw [hr] at he
  cases hl : left e with
  | inl p' =>
    have eq : p' = p := by simpa [baseAdj, hl] using he
    subst p'
    refine ⟨.inl (), trivial, rfl, ?_⟩
    rw [spec, hl, hr]
    rfl
  | inr s =>
    obtain ⟨i, j⟩ := s
    have he' : j = p.2 ∧ valid p.1 (.inr i) := by simpa [baseAdj, valid, hl] using he
    rcases he' with ⟨hj, hi⟩
    subst j
    exact ⟨.inr i, hi, rfl, by simp [spec, hl, hr]⟩

private theorem left_spacer {m n : ℕ} (e : E m n) (s : Fin (m-1) × Fin n) (hl : left e = .inr s) :
    ∃ i : Fin m, right e = .inl (i,s.2) ∧ (i.val = s.1.val ∨ i.val = s.1.val + 1) ∧
      spec e = port (col s.2) i (.inr s.1) := by
  have he := edge e
  rw [hl] at he
  cases hr : right e with
  | inl p =>
    obtain ⟨i,j⟩ := p
    have he' : s.2 = j ∧ (i.val = s.1.val ∨ i.val = s.1.val + 1) := by
      simpa [baseAdj, hr] using he
    rcases he' with ⟨hj, hi⟩
    subst j
    exact ⟨i, rfl, hi, by simp [spec, hl, hr]⟩
  | inr _ => simp [baseAdj, hr] at he

private theorem right_spacer {m n : ℕ} (e : E m n) (s : Fin m × Fin (n-1)) (hr : right e = .inr s) :
    ∃ j : Fin n, left e = .inl (s.1,j) ∧ (j.val = s.2.val ∨ j.val = s.2.val + 1) ∧
      spec e = port (row s.1) j (.inr s.2) := by
  have he := edge e
  rw [hr] at he
  cases hl : left e with
  | inl p =>
    obtain ⟨i,j⟩ := p
    have he' : i = s.1 ∧ (j.val = s.2.val ∨ j.val = s.2.val + 1) := by
      simpa [baseAdj, hl] using he
    rcases he' with ⟨hi, hj⟩
    subst i
    exact ⟨j, rfl, hj, by simp [spec, hl, hr]⟩
  | inr _ => simp [baseAdj, hl] at he

private theorem pair_sat {V : Type} [DecidableEq V] (a : V → Bool) (e e' : V)
    (h : a e = true → a e' = true → False) : ClauseSat a {(e,false),(e',false)} := by
  cases he : a e
  · exact ⟨(e,false), by simp, he⟩
  · cases he' : a e'
    · exact ⟨(e',false), by simp, he'⟩
    · exact (h he he').elim

theorem transfer {m n : ℕ} (hm : 0 < m) (seed : List (LinKLine (X m n)))
    (odd : ∀ i : Fin m, oddRow (row i) ∈ seed)
    (rows : ∀ (i : Fin m) (j : Fin n), guard (row i) j ∈ seed)
    (cols : ∀ (i : Fin m) (j : Fin n), guard (col j) i ∈ seed)
    (C : Clause (E m n)) (hC : C ∈ funGraphPHP (H m n)) :
    ∃ B ∈ seed, ∀ a, LinKLineSat a B → ClauseSat (fun e => eval a (spec e)) C := by
  let i₀ : Fin m := ⟨0, hm⟩
  rcases hC with (⟨u, rfl⟩ | ⟨e,e',he,hne,rfl⟩) | ⟨e,e',he,hne,rfl⟩
  · cases hl : (Fintype.equivFin (L m n)).symm u with
    | inl p =>
      refine ⟨oddRow (row p.1), odd p.1, ?_⟩
      intro a ho
      obtain ⟨q, hq, hv⟩ := port_positive (row p.1) p.2 a ho
      let f := mkEdge (.inl p) (leftNbr p q) (leftNbr_valid p q hq)
      have hf : left f = .inl p := mkLeft _ _ _
      have hR : right f = leftNbr p q := mkRight _ _ _
      have hh : f.1.1 = u := (Fintype.equivFin _).symm.injective (hf.trans hl.symm)
      refine ⟨(f,true), by simp [hh], ?_⟩
      change eval a (spec f) = true
      cases q with
      | inl x => cases x; simpa [spec, hf, hR, leftNbr] using hv
      | inr s => simpa [spec, hf, hR, leftNbr] using hv
    | inr s =>
      refine ⟨oddRow (row i₀), odd i₀, ?_⟩
      intro a _
      have hs := s.1.isLt
      let i : Fin m := ⟨s.1.val, by omega⟩
      let i' : Fin m := ⟨s.1.val+1, by omega⟩
      have takeEdge (j : Fin m) (hj : j.val = s.1.val ∨ j.val = s.1.val+1)
          (hv : eval a (port (col s.2) j (.inr s.1)) = true) :
          ClauseSat (fun f => eval a (spec f)) (Finset.univ.filter
            (fun l : Literal (E m n) => l.1.1.1 = u ∧ l.2 = true)) := by
        have h : baseAdj m n (.inr s) (.inl (j,s.2)) = true := by simp [baseAdj, hj]
        have hh : (mkEdge _ _ h).1.1 = u := (Fintype.equivFin _).symm.injective ((mkLeft _ _ h).trans hl.symm)
        exact ⟨(mkEdge _ _ h,true), by simp [hh], by simpa [spec, mkLeft, mkRight] using hv⟩
      have ne : i ≠ i' := by intro h; have := congrArg Fin.val h; dsimp [i,i'] at this; omega
      have hop := opposite (col s.2) a s.1 i i' (Or.inl rfl) (Or.inr rfl) ne
      cases hh : eval a (port (col s.2) i' (.inr s.1))
      · exact takeEdge i (Or.inl rfl) (by simp [hop, hh])
      · exact takeEdge i' (Or.inr rfl) hh
  · have hr : right e = right e' := congrArg (Fintype.equivFin _).symm he
    cases h : right e with
    | inl p =>
      refine ⟨guard (col p.2) p.1, cols p.1 p.2, fun a ha => pair_sat _ _ _ ?_⟩
      obtain ⟨q,hq,eq,hsp⟩ := right_case e p h
      obtain ⟨q',hq',eq',hsp'⟩ := right_case e' p (hr.symm.trans h)
      intro hv hv'
      rw [hsp] at hv
      rw [hsp'] at hv'
      have eqQ := port_unique (col p.2) p.1 a ha q q' hq hq' hv hv'
      exact hne ((Fintype.equivFin _).symm.injective (eq.trans ((congrArg (rightNbr p) eqQ).trans eq'.symm)))
    | inr s =>
      refine ⟨oddRow (row i₀), odd i₀, fun a _ => pair_sat _ _ _ ?_⟩
      obtain ⟨j,hj,hi,hs⟩ := right_spacer e s h
      obtain ⟨j',hj',hi',hs'⟩ := right_spacer e' s (hr.symm.trans h)
      have ne : j ≠ j' := by intro hn; exact hne ((Fintype.equivFin _).symm.injective (hj.trans (hn ▸ hj'.symm)))
      intro hv hv'
      rw [hs, opposite (row s.1) a s.2 j j' hi hi' ne, ← hs', hv'] at hv
      contradiction
  · have hl : left e = left e' := congrArg (Fintype.equivFin _).symm he
    cases h : left e with
    | inl p =>
      refine ⟨guard (row p.1) p.2, rows p.1 p.2, fun a ha => pair_sat _ _ _ ?_⟩
      obtain ⟨q,hq,eq,hsp⟩ := left_case e p h
      obtain ⟨q',hq',eq',hsp'⟩ := left_case e' p (hl.symm.trans h)
      intro hv hv'
      rw [hsp] at hv
      rw [hsp'] at hv'
      have eqQ := port_unique (row p.1) p.2 a ha q q' hq hq' hv hv'
      exact hne ((Fintype.equivFin _).symm.injective (eq.trans ((congrArg (leftNbr p) eqQ).trans eq'.symm)))
    | inr s =>
      refine ⟨oddRow (row i₀), odd i₀, fun a _ => pair_sat _ _ _ ?_⟩
      obtain ⟨i,hi,hj,hs⟩ := left_spacer e s h
      obtain ⟨i',hi',hj',hs'⟩ := left_spacer e' s (hl.symm.trans h)
      have ne : i ≠ i' := by intro hn; exact hne ((Fintype.equivFin _).symm.injective (hi.trans (hn ▸ hi'.symm)))
      intro hv hv'
      rw [hs, opposite (col s.2) a s.1 i i' hj hj' ne, ← hs', hv'] at hv
      contradiction

end PEqualNP.Outside.L_pcx_341_aux.BaseModel

namespace PEqualNP.Outside.L_pcx_341_aux.StretchModel

open PEqualNP.Expanders PEqualNP.ProofComplexity GraphCounts

private abbrev A (m n : ℕ) := Fin (Fintype.card (L m n))
private abbrev B (m n : ℕ) := Fin (Fintype.card (R m n))
private abbrev Raw (m n t : ℕ) := {p : U m n t × V m n t // adj m n t p.1 p.2 = true}
private abbrev Actual (m n t : ℕ) := GEdge (G m n t)

private noncomputable def raw {m n t : ℕ} (e : Actual m n t) : Raw m n t :=
  ⟨((Fintype.equivFin _).symm e.1.1, (Fintype.equivFin _).symm e.1.2), by
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using e.2⟩

private noncomputable def enc {m n t : ℕ} (e : Raw m n t) : Actual m n t :=
  ⟨(Fintype.equivFin (U m n t) e.1.1, Fintype.equivFin (V m n t) e.1.2), by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.symm_apply_apply] using e.2⟩

private theorem raw_enc {m n t : ℕ} (e : Raw m n t) : raw (enc e) = e := by
  apply Subtype.ext
  exact Prod.ext (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)

private theorem raw_inj {m n t : ℕ} : Function.Injective (raw (m := m) (n := n) (t := t)) := by
  intro e e' h
  exact Subtype.ext (Prod.ext ((Fintype.equivFin _).symm.injective (congrArg (fun f => f.1.1) h))
    ((Fintype.equivFin _).symm.injective (congrArg (fun f => f.1.2) h)))

private def lower {m n t : ℕ} : Raw m n t → E m n
  | ⟨(.inl u,.inl v),h⟩ => ⟨(u,v), (of_decide_eq_true h).2⟩
  | ⟨(.inl _,.inr s),_⟩ => s.1
  | ⟨(.inr s,.inl _),_⟩ => s.1
  | ⟨(.inr s,.inr _),_⟩ => s.1

private def flip {m n t : ℕ} (e : Raw m n t) : Bool :=
  match e.1.1, e.1.2 with
  | .inr s,.inr z => decide (s.2 = z.2)
  | _,_ => false

private noncomputable def lift {m n t : ℕ} (b : E m n → Bool) (e : Actual m n t) : Bool :=
  b (lower (raw e)) ^^ flip (raw e)

private noncomputable def first {m n t : ℕ} (f : E m n) : Raw m n t :=
  if ht : t = 0 then ⟨(.inl f.1.1,.inl f.1.2), decide_eq_true ⟨ht,f.2⟩⟩
  else ⟨(.inl f.1.1,.inr (f,⟨0, Nat.pos_of_ne_zero ht⟩)), by simp [adj]⟩

private noncomputable def last {m n t : ℕ} (f : E m n) : Raw m n t :=
  if ht : t = 0 then ⟨(.inl f.1.1,.inl f.1.2), decide_eq_true ⟨ht,f.2⟩⟩
  else ⟨(.inr (f,⟨t - 1, by omega⟩),.inl f.1.2), by simp [adj]; omega⟩

private theorem first_facts {m n t : ℕ} (f : E m n) :
    (first (t := t) f).1.1 = .inl f.1.1 ∧ lower (first (t := t) f) = f ∧ flip (first (t := t) f) = false := by
  by_cases ht : t = 0 <;> simp [first, ht, lower, flip]

private theorem old_left {m n t : ℕ} (e : Raw m n t) (u : A m n) (he : e.1.1 = .inl u) :
    (lower e).1.1 = u ∧ flip e = false ∧ e = first (lower e) := by
  rcases e with ⟨⟨a|s,b|z⟩,h⟩ <;> simp only [Sum.inl.injEq, Sum.inr_ne_inl] at he
  · subst a
    have ht := (of_decide_eq_true h).1
    simp [first, ht, lower, flip]
  · subst a
    obtain ⟨f,i⟩ := z
    have h' : u = f.1.1 ∧ i.val = 0 := of_decide_eq_true h
    rcases h' with ⟨rfl,hi⟩
    have ht : t ≠ 0 := by have := i.isLt; omega
    simp only [lower, flip, first, dite_eq_right ht, true_and]
    exact Subtype.ext (Prod.ext rfl (congrArg Sum.inr (Prod.ext rfl (Fin.ext hi))))

private theorem old_right {m n t : ℕ} (e : Raw m n t) (v : B m n) (he : e.1.2 = .inl v) :
    (lower e).1.2 = v ∧ flip e = false ∧ e = last (lower e) := by
  rcases e with ⟨⟨a|s,b|z⟩,h⟩ <;> simp only [Sum.inl.injEq, Sum.inr_ne_inl] at he
  · subst b
    have ht := (of_decide_eq_true h).1
    simp [last, ht, lower, flip]
  · subst b
    obtain ⟨f,i⟩ := s
    have h' : v = f.1.2 ∧ i.val + 1 = t := of_decide_eq_true h
    rcases h' with ⟨rfl,hi⟩
    have ht : t ≠ 0 := by omega
    have hi' : i.val = t - 1 := by omega
    simp only [lower, flip, last, dite_eq_right ht, true_and]
    exact Subtype.ext (Prod.ext (congrArg Sum.inr (Prod.ext rfl (Fin.ext hi'))) rfl)

private theorem inner_left {m n t : ℕ} (e : Raw m n t) (s : E m n × Fin t)
    (he : e.1.1 = .inr s) : lower e = s.1 := by
  rcases e with ⟨⟨u|z,v⟩,h⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he
  subst z
  cases v <;> rfl

private theorem inner_right {m n t : ℕ} (e : Raw m n t) (s : E m n × Fin t)
    (he : e.1.2 = .inr s) : lower e = s.1 := by
  rcases e with ⟨⟨u,v|z⟩,h⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he
  subst z
  cases u with
  | inl _ => rfl
  | inr x => exact (of_decide_eq_true h).1

private theorem inner_left_inj {m n t : ℕ} (e e' : Raw m n t) (s : E m n × Fin t)
    (he : e.1.1 = .inr s) (he' : e'.1.1 = .inr s) (hf : flip e = flip e') : e = e' := by
  rcases e with ⟨⟨u|z,v|w⟩,h⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he <;> subst z
  all_goals rcases e' with ⟨⟨u'|z',v'|w'⟩,h'⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he' <;> subst z'
  all_goals simp only [flip] at hf
  · exact Subtype.ext (Prod.ext rfl (congrArg Sum.inl ((of_decide_eq_true h).1.trans (of_decide_eq_true h').1.symm)))
  · have hv : v = s.1.val.2 ∧ s.2.val+1 = t := of_decide_eq_true h
    have hw : s.1 = w'.1 ∧ (s.2 = w'.2 ∨ w'.2.val = s.2.val+1) := of_decide_eq_true h'
    have hn : s.2 ≠ w'.2 := by simpa [eq_comm] using hf
    have := hw.2.resolve_left hn
    have := w'.2.isLt
    omega
  · have hv : v' = s.1.val.2 ∧ s.2.val+1 = t := of_decide_eq_true h'
    have hw : s.1 = w.1 ∧ (s.2 = w.2 ∨ w.2.val = s.2.val+1) := of_decide_eq_true h
    have hn : s.2 ≠ w.2 := by simpa using hf
    have := hw.2.resolve_left hn
    have := w.2.isLt
    omega
  · have hw : s.1 = w.1 ∧ (s.2 = w.2 ∨ w.2.val = s.2.val+1) := of_decide_eq_true h
    have hw' : s.1 = w'.1 ∧ (s.2 = w'.2 ∨ w'.2.val = s.2.val+1) := of_decide_eq_true h'
    have hi : w.2 = w'.2 := by
      by_cases hz : s.2 = w.2
      · have hz' : s.2 = w'.2 := by simpa [hz, eq_comm] using hf
        exact hz.symm.trans hz'
      · have hz' : s.2 ≠ w'.2 := by simpa [hz, eq_comm] using hf
        exact Fin.ext ((hw.2.resolve_left hz).trans (hw'.2.resolve_left hz').symm)
    exact Subtype.ext (Prod.ext rfl (congrArg Sum.inr (Prod.ext (hw.1.symm.trans hw'.1) hi)))

private theorem inner_right_inj {m n t : ℕ} (e e' : Raw m n t) (s : E m n × Fin t)
    (he : e.1.2 = .inr s) (he' : e'.1.2 = .inr s) (hf : flip e = flip e') : e = e' := by
  rcases e with ⟨⟨u|w,v|z⟩,h⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he <;> subst z
  all_goals rcases e' with ⟨⟨u'|w',v'|z'⟩,h'⟩ <;> simp only [Sum.inl_ne_inr, Sum.inr.injEq] at he' <;> subst z'
  all_goals simp only [flip] at hf
  · exact Subtype.ext (Prod.ext (congrArg Sum.inl ((of_decide_eq_true h).1.trans (of_decide_eq_true h').1.symm)) rfl)
  · have hu : u = s.1.val.1 ∧ s.2.val = 0 := of_decide_eq_true h
    have hw : w'.1 = s.1 ∧ (w'.2 = s.2 ∨ s.2.val = w'.2.val+1) := of_decide_eq_true h'
    have hn : w'.2 ≠ s.2 := by simpa [eq_comm] using hf
    have := hw.2.resolve_left hn
    omega
  · have hu : u' = s.1.val.1 ∧ s.2.val = 0 := of_decide_eq_true h'
    have hw : w.1 = s.1 ∧ (w.2 = s.2 ∨ s.2.val = w.2.val+1) := of_decide_eq_true h
    have hn : w.2 ≠ s.2 := by simpa using hf
    have := hw.2.resolve_left hn
    omega
  · have hw : w.1 = s.1 ∧ (w.2 = s.2 ∨ s.2.val = w.2.val+1) := of_decide_eq_true h
    have hw' : w'.1 = s.1 ∧ (w'.2 = s.2 ∨ s.2.val = w'.2.val+1) := of_decide_eq_true h'
    have hi : w.2 = w'.2 := by
      by_cases hz : w.2 = s.2
      · have hz' : w'.2 = s.2 := by simpa [hz, eq_comm] using hf
        exact hz.trans hz'.symm
      · have hz' : w'.2 ≠ s.2 := by simpa [hz, eq_comm] using hf
        have h₁ := hw.2.resolve_left hz
        have h₂ := hw'.2.resolve_left hz'
        exact Fin.ext (by omega)
    exact Subtype.ext (Prod.ext (congrArg Sum.inr (Prod.ext (hw.1.trans hw'.1.symm) hi)) rfl)

private theorem raw_positive {m n t : ℕ} (s : E m n × Fin t) (b : E m n → Bool) :
    ∃ e : Raw m n t, e.1.1 = .inr s ∧ (b (lower e) ^^ flip e) = true := by
  cases h : b s.1
  case false =>
    let e : Raw m n t := ⟨(.inr s,.inr s), by simp [adj]⟩
    exact ⟨e, rfl, by simp [e, lower, flip, h]⟩
  case true =>
    by_cases ht : s.2.val + 1 < t
    · let i : Fin t := ⟨s.2.val+1,ht⟩
      let e : Raw m n t := ⟨(.inr s,.inr (s.1,i)), by simp [adj, i]⟩
      have ne : s.2 ≠ i := by intro eq; have := congrArg Fin.val eq; dsimp [i] at this; omega
      exact ⟨e, rfl, by simp [e, lower, flip, h, ne]⟩
    · have ht' : s.2.val + 1 = t := by have := s.2.isLt; omega
      let e : Raw m n t := ⟨(.inr s,.inl s.1.1.2), by simp [adj, ht']⟩
      exact ⟨e, rfl, by simp [e, lower, flip, h]⟩

private theorem pair_sat {T : Type} [DecidableEq T] (a : T → Bool) (e e' : T)
    (h : a e = true → a e' = true → False) : ClauseSat a {(e,false),(e',false)} := by
  cases he : a e
  · exact ⟨(e,false), by simp, he⟩
  · cases he' : a e'
    · exact ⟨(e',false), by simp, he'⟩
    · exact (h he he').elim

private theorem pair_map {T W : Type} [DecidableEq T] [DecidableEq W] (a : T → Bool) (b : W → Bool)
    (e e' : T) (f f' : W) (he : a e = b f) (he' : a e' = b f')
    (h : ClauseSat b {(f,false),(f',false)}) : ClauseSat a {(e,false),(e',false)} := by
  rcases h with ⟨l,hl,hs⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact ⟨(e,false), by simp, he.trans hs⟩
  · exact ⟨(e',false), by simp, he'.trans hs⟩

private theorem opposite_false (b p q : Bool) (ne : p ≠ q) :
    b ^^ p = true → b ^^ q = true → False := by
  cases b <;> cases p <;> cases q <;> simp_all

private theorem stretch_axiom {m n t : ℕ} (C : Clause (Actual m n t)) (hC : C ∈ funGraphPHP (G m n t)) :
    (∀ b, ClauseSat (lift b) C) ∨
      ∃ D ∈ funGraphPHP (H m n), ∀ b, ClauseSat b D → ClauseSat (lift b) C := by
  rcases hC with (⟨u,rfl⟩ | ⟨e,e',he,hne,rfl⟩) | ⟨e,e',he,hne,rfl⟩
  · cases hu : (Fintype.equivFin (U m n t)).symm u with
    | inl x =>
      right
      refine ⟨_, Or.inl (Or.inl ⟨x,rfl⟩), ?_⟩
      intro b h
      obtain ⟨⟨f,p⟩,hf,hv⟩ := h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨rfl,rfl⟩ := hf
      have ⟨hl,hs,ht⟩ := first_facts (t := t) f
      have eq : (enc (first (t := t) f)).1.1 = u := (Fintype.equivFin _).symm.injective
        (by change (raw (enc (first f))).1.1 = _; rw [raw_enc, hl, hu])
      exact ⟨(enc (first f),true), by simp [eq], by simpa [lift,raw_enc,hs,ht] using hv⟩
    | inr s =>
      left
      intro b
      obtain ⟨f,hl,hv⟩ := raw_positive s b
      have eq : (enc f).1.1 = u := (Fintype.equivFin _).symm.injective
        (by change (raw (enc f)).1.1 = _; rw [raw_enc,hl,hu])
      exact ⟨(enc f,true), by simp [eq], by simpa [lift,raw_enc] using hv⟩
  · have hr : (raw e).1.2 = (raw e').1.2 := congrArg (Fintype.equivFin _).symm he
    have distinct : raw e ≠ raw e' := fun h => hne (congrArg (fun z : Actual m n t => z.1.1) (raw_inj h))
    cases hv : (raw e).1.2 with
    | inl v =>
      right
      obtain ⟨h,hf,eq⟩ := old_right (raw e) v hv
      obtain ⟨h',hf',eq'⟩ := old_right (raw e') v (hr.symm.trans hv)
      have hn : lower (raw e) ≠ lower (raw e') := fun hn => distinct (eq.trans ((congrArg last hn).trans eq'.symm))
      have hn' : (lower (raw e)).1.1 ≠ (lower (raw e')).1.1 := fun hh => hn (Subtype.ext (Prod.ext hh (h.trans h'.symm)))
      exact ⟨_, Or.inl (Or.inr ⟨lower (raw e), lower (raw e'), h.trans h'.symm, hn', rfl⟩),
        fun b => pair_map _ _ _ _ _ _ (by simp [lift,hf]) (by simp [lift,hf'])⟩
    | inr s =>
      left
      have h := inner_right (raw e) s hv
      have h' := inner_right (raw e') s (hr.symm.trans hv)
      have hn : flip (raw e) ≠ flip (raw e') := fun hh => distinct (inner_right_inj (raw e) (raw e') s hv (hr.symm.trans hv) hh)
      exact fun b => pair_sat _ _ _ (by simpa [lift,h,h'] using opposite_false (b s.1) _ _ hn)
  · have hl : (raw e).1.1 = (raw e').1.1 := congrArg (Fintype.equivFin _).symm he
    have distinct : raw e ≠ raw e' := fun h => hne (congrArg (fun z : Actual m n t => z.1.2) (raw_inj h))
    cases hu : (raw e).1.1 with
    | inl u =>
      right
      obtain ⟨h,hf,eq⟩ := old_left (raw e) u hu
      obtain ⟨h',hf',eq'⟩ := old_left (raw e') u (hl.symm.trans hu)
      have hn : lower (raw e) ≠ lower (raw e') := fun hn => distinct (eq.trans ((congrArg first hn).trans eq'.symm))
      have hn' : (lower (raw e)).1.2 ≠ (lower (raw e')).1.2 := fun hh => hn (Subtype.ext (Prod.ext (h.trans h'.symm) hh))
      exact ⟨_, Or.inr ⟨lower (raw e), lower (raw e'), h.trans h'.symm, hn', rfl⟩,
        fun b => pair_map _ _ _ _ _ _ (by simp [lift,hf]) (by simp [lift,hf'])⟩
    | inr s =>
      left
      have h := inner_left (raw e) s hu
      have h' := inner_left (raw e') s (hl.symm.trans hu)
      have hn : flip (raw e) ≠ flip (raw e') := fun hh => distinct (inner_left_inj (raw e) (raw e') s hu (hl.symm.trans hu) hh)
      exact fun b => pair_sat _ _ _ (by simpa [lift,h,h'] using opposite_false (b s.1) _ _ hn)

open Seed BaseModel in
noncomputable def support {m n t : ℕ} (e : Actual m n t) : Finset (X m n) :=
  (spec (lower (raw e))).1

open BaseModel in
noncomputable def offset {m n t : ℕ} (e : Actual m n t) : Bool :=
  (spec (lower (raw e))).2 ^^ flip (raw e)

open Seed BaseModel in
theorem axiom_step {m n t : ℕ} (hm : 0 < m) (seed : List (LinKLine (X m n)))
    (odd : ∀ i : Fin m, oddRow (row i) ∈ seed)
    (rows : ∀ (i : Fin m) (j : Fin n), guard (row i) j ∈ seed)
    (cols : ∀ (i : Fin m) (j : Fin n), guard (col j) i ∈ seed)
    (C : Clause (Actual m n t)) (hC : C ∈ funGraphPHP (G m n t)) :
    ∃ D ∈ seed, ∀ a, LinKLineSat a D → ClauseSat (Replay.value support offset a) C := by
  have hv (a : X m n → Bool) : Replay.value (support (t := t)) offset a = lift (fun f => eval a (spec f)) := by
    funext e
    classical
    simp only [Replay.value, support, offset, lift, eval, Bool.xor_assoc]
    by_cases h : Replay.par a (spec (lower (raw e))).1
    · have h' : PEqualNP.Outside.L_pcx_207_aux.par a (spec (lower (raw e))).1 := h
      simp [h, h']
    · have h' : ¬ PEqualNP.Outside.L_pcx_207_aux.par a (spec (lower (raw e))).1 := h
      simp [h, h']
  rcases stretch_axiom C hC with h | ⟨D,hD,h⟩
  · let i : Fin m := ⟨0,hm⟩
    exact ⟨oddRow (row i), odd i, fun a _ => (hv a).symm ▸ h _⟩
  · obtain ⟨L,hL,hs⟩ := BaseModel.transfer hm seed odd rows cols D hD
    exact ⟨L,hL,fun a ha => (hv a).symm ▸ h _ (hs a ha)⟩

end PEqualNP.Outside.L_pcx_341_aux.StretchModel

namespace PEqualNP.Outside.L_pcx_341_aux

open PEqualNP.Expanders PEqualNP.ProofComplexity

private theorem cycle_equiv {A B C D : Type} (e : A ≃ C) (f : B ≃ D) (p : A → B → Prop)
    (q : C → D → Prop) (h : ∀ a b, p a b ↔ q (e a) (f b)) (s : ℕ) :
    StretchGirth.Cycle p s ↔ StretchGirth.Cycle q s := by
  constructor
  · rintro ⟨u,v,huv⟩
    refine ⟨u.trans e.toEmbedding, v.trans f.toEmbedding, fun i => ⟨?_, ?_⟩⟩
    · exact (h _ _).mp (huv i).1
    · exact (h _ _).mp (huv i).2
  · rintro ⟨u,v,huv⟩
    refine ⟨u.trans e.symm.toEmbedding, v.trans f.symm.toEmbedding, fun i => ⟨?_, ?_⟩⟩
    · apply (h _ _).mpr
      simpa using (huv i).1
    · apply (h _ _).mpr
      simpa using (huv i).2

open GraphCounts in
private theorem girth (m n t : ℕ) (hn : 2 ≤ n) (hm : n < m) :
    IsLeast {z : ℕ | ∃ s : ℕ, z = 2*(s+2) ∧
      StretchGirth.Cycle (fun u v => v ∈ G m n t u) s} (12*(2*t+1)) := by
  let rel := fun u v => v ∈ H m n u
  have congrBase (u : L m n) (v : R m n) : baseAdj m n u v = BaseGirth.adjBool u v := by
    cases u <;> cases v <;> rfl
  have base (s : ℕ) : StretchGirth.Cycle rel s ↔ StretchGirth.Cycle (@BaseGirth.Adj m n) s := by
    apply cycle_equiv (Fintype.equivFin (L m n)).symm (Fintype.equivFin (R m n)).symm
    intro u v
    simpa only [rel, H, Finset.mem_filter, Finset.mem_univ, true_and, congrBase] using BaseGirth.adjBool_eq_true
      ((Fintype.equivFin (L m n)).symm u) ((Fintype.equivFin (R m n)).symm v)
  have congrAdj (u : U m n t) (v : V m n t) :
      adj m n t u v = true ↔ StretchGirth.adj rel t u v := by
    rcases u with u|⟨e,i⟩ <;> rcases v with v|⟨f,j⟩ <;>
      simp only [adj, Sum.elim_inl, Sum.elim_inr, StretchGirth.adj, rel, decide_eq_true_eq]
  have stretched (s : ℕ) : StretchGirth.Cycle (fun u v => v ∈ G m n t u) s ↔
      StretchGirth.Cycle (StretchGirth.adj rel t) s := by
    apply cycle_equiv (Fintype.equivFin (U m n t)).symm (Fintype.equivFin (V m n t)).symm
    intro u v
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using congrAdj
      ((Fintype.equivFin (U m n t)).symm u) ((Fintype.equivFin (V m n t)).symm v)
  obtain ⟨⟨s, hs, hlen⟩, lb⟩ := StretchGirth.scale t
    ((base 4).mpr (BaseGirth.exists_cycle hn hm)) (fun z h => by
      obtain ⟨u,v,huv⟩ := (base z).mp h
      exact BaseGirth.lower u v huv)
  constructor
  · exact ⟨s, by omega, (stretched s).mpr hs⟩
  · rintro z ⟨r,rfl,hr⟩
    have h := lb r ((stretched r).mp hr)
    omega

open GraphCounts in
private theorem simulate (m n t k : ℕ) (hn : 2 ≤ n) (hm : n < m) (hk : 1 ≤ k)
    (π : List (LinKLine (GEdge (G m n t)))) (hπ : IsLinKRefutation k (funGraphPHP (G m n t)) π) :
    ∃ τ, IsLinKRefutation k (funGraphPHP (Seed.K m n)) τ ∧
      τ.length ≤ 2 * π.length + 16 * m * n * (m + n) := by
  obtain ⟨seed, hd, odd, rows, cols, len⟩ := Seed.prelude m n hn hm
  obtain ⟨τ, hτ, ht⟩ := Replay.simulate k (funGraphPHP (G m n t)) (funGraphPHP (Seed.K m n))
    StretchModel.support StretchModel.offset hk seed hd
    (fun C hC => Or.inr (StretchModel.axiom_step (by omega) seed odd rows cols C hC)) π hπ
  exact ⟨τ, hτ, ht.trans (Nat.add_le_add_left len _)⟩

end PEqualNP.Outside.L_pcx_341_aux

open PEqualNP.Outside.L_pcx_341_aux in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.L_pcx_341 :
∃ C : ℕ, 0 < C ∧ ∀ (m n t : ℕ), 2 ≤ n → n < m →
  let Cell := Fin m × Fin n
  let L := Cell ⊕ (Fin (m-1) × Fin n)
  let R := Cell ⊕ (Fin m × Fin (n-1))
  let baseAdj : L → R → Bool := Sum.elim
    (fun p => Sum.elim (fun h => decide (p = h))
      (fun s => decide (p.1 = s.1 ∧ (p.2.val = s.2.val ∨ p.2.val = s.2.val+1))))
    (fun s => Sum.elim (fun h => decide (s.2 = h.2 ∧ (h.1.val = s.1.val ∨ h.1.val = s.1.val+1)))
      (fun _ => false))
  let H : PEqualNP.Expanders.BipGraph (Fintype.card L) (Fintype.card R) :=
    fun u => Finset.univ.filter (fun v => baseAdj ((Fintype.equivFin L).symm u)
      ((Fintype.equivFin R).symm v) = true)
  let E := PEqualNP.Expanders.GEdge H
  let U := Fin (Fintype.card L) ⊕ (E × Fin t)
  let V := Fin (Fintype.card R) ⊕ (E × Fin t)
  let adj : U → V → Bool := Sum.elim
    (fun u => Sum.elim (fun v => decide (t = 0 ∧ v ∈ H u))
      (fun s => decide (u = s.1.val.1 ∧ s.2.val = 0)))
    (fun s => Sum.elim (fun v => decide (v = s.1.val.2 ∧ s.2.val+1 = t))
      (fun z => decide (s.1 = z.1 ∧ (s.2 = z.2 ∨ z.2.val = s.2.val+1))))
  let G : PEqualNP.Expanders.BipGraph (Fintype.card U) (Fintype.card V) :=
    fun u => Finset.univ.filter (fun v => adj ((Fintype.equivFin U).symm u)
      ((Fintype.equivFin V).symm v) = true)
  let cycles : Set ℕ := {z | ∃ s : ℕ, z = 2*(s+2) ∧
    ∃ (us : Fin (s+2) ↪ Fin (Fintype.card U)) (vs : Fin (s+2) ↪ Fin (Fintype.card V)),
      ∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i+1))}
  let K : PEqualNP.Expanders.BipGraph m n := fun _ => Finset.univ
  PEqualNP.Expanders.LeftDegLe G 3 ∧ PEqualNP.Expanders.RightDegLe G 3 ∧
    Fintype.card U + n = Fintype.card V + m ∧
    Fintype.card (PEqualNP.Expanders.GEdge G) =
      (2*t+1)*(m*n + 2*m*(n-1) + 2*n*(m-1)) ∧
    IsLeast cycles (12*(2*t+1)) ∧
    ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G))),
      1 ≤ k → PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π →
      ∃ τ : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge K)),
        PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP K) τ ∧
        τ.length ≤ 2*π.length + C*m*n*(m+n) := by
  refine ⟨16, by decide, ?_⟩
  intro m n t hn hm
  obtain ⟨hl, hr, hd, he⟩ := GraphCounts.counts m n t hn hm
  exact ⟨hl, hr, hd, he, girth m n t hn hm, fun k π hk hπ => simulate m n t k hn hm hk π hπ⟩
