import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1298

def cnd : Bool → Prop → Prop → Prop
  | true, P, _ => P
  | false, _, Q => Q

theorem ite_cnd (c : Bool) (P Q : Prop) [Decidable (c = true)] :
    (if c = true then P else Q) ↔ cnd c P Q := by
  cases c <;> simp [cnd]

def Ins (s : Option (Nat × Nat)) (z : Nat) : Prop :=
  ∃ l u, s = some (l,u) ∧ l ≤ z ∧ z ≤ u

def Nrm (D : Nat) (s : Option (Nat × Nat)) : Prop :=
  ∀ l u, s = some (l,u) → l ≤ u ∧ u ≤ D

theorem repr_exists (D : Nat) (S : Nat → Prop) (hb : ∀ z, S z → z ≤ D)
    (hc : ∀ z1 z z2, S z1 → S z2 → z1 ≤ z → z ≤ z2 → S z) :
    ∃ s, Nrm D s ∧ ∀ z, Ins s z ↔ S z := by
  classical
  by_cases h : ∃ z, S z
  · refine ⟨some (Nat.find h, Nat.findGreatest S D), ?_, ?_⟩
    · intro l u he
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨Nat.le_findGreatest (hb _ (Nat.find_spec h)) (Nat.find_spec h),
        Nat.findGreatest_le D⟩
    · intro z
      constructor
      · rintro ⟨l, u, he, h1, h2⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hc _ z _ (Nat.find_spec h)
          (Nat.findGreatest_spec (hb _ (Nat.find_spec h)) (Nat.find_spec h)) h1 h2
      · intro hz
        exact ⟨_, _, rfl, Nat.find_min' h hz, Nat.le_findGreatest (hb _ hz) hz⟩
  · refine ⟨none, ?_, ?_⟩
    · intro l u he; cases he
    · intro z
      constructor
      · rintro ⟨l, u, he, _⟩; cases he
      · intro hz; exact absurd ⟨z, hz⟩ h

theorem repr_unique (D : Nat) (s s' : Option (Nat × Nat)) (h1 : Nrm D s) (h2 : Nrm D s')
    (h : ∀ z, Ins s z ↔ Ins s' z) : s = s' := by
  rcases s with _ | ⟨l, u⟩ <;> rcases s' with _ | ⟨l', u'⟩
  · rfl
  · obtain ⟨a, b⟩ := h2 l' u' rfl
    obtain ⟨_, _, he, _⟩ := (h l').2 ⟨l', u', rfl, le_refl _, a⟩
    cases he
  · obtain ⟨a, b⟩ := h1 l u rfl
    obtain ⟨_, _, he, _⟩ := (h l).1 ⟨l, u, rfl, le_refl _, a⟩
    cases he
  · obtain ⟨a, b⟩ := h1 l u rfl
    obtain ⟨a', b'⟩ := h2 l' u' rfl
    have e1 := h l; have e2 := h u; have e3 := h l'; have e4 := h u'
    simp [Ins] at e1 e2 e3 e4
    have : l = l' := by omega
    have : u = u' := by omega
    subst_vars
    rfl

section
variable {m k : Nat} (D : Nat) (parent : Fin m → Option (Fin m)) (up : Fin m → Bool)
  (loss : Fin k → Fin k → Nat) (low high : Fin m → Fin k → Nat)

def Pred (T : Fin m → Fin k → Option (Nat × Nat)) (i : Fin m) (a : Fin k) (z : Nat) : Prop :=
  low i a ≤ z ∧ z ≤ min D (high i a) ∧ ∀ j, parent j = some i → ∃ b l u, T j b = some (l,u) ∧
    cnd (up j) (z + loss a b ≤ u) (l + loss b a ≤ z)

def Rec (T : Fin m → Fin k → Option (Nat × Nat)) : Prop :=
  (∀ i a, Nrm D (T i a)) ∧ ∀ i a z, Ins (T i a) z ↔ Pred D parent up loss low high T i a z

def Good (v : Fin m → Fin k) (s : Fin m → Nat) : Prop :=
  (∀ i, low i (v i) ≤ s i ∧ s i ≤ min D (high i (v i))) ∧
    ∀ i j, parent j = some i → cnd (up j) (s i + loss (v i) (v j) ≤ s j)
      (s j + loss (v j) (v i) ≤ s i)

theorem pred_congr (T T' : Fin m → Fin k → Option (Nat × Nat)) (i : Fin m) (a : Fin k) (z : Nat)
    (h : ∀ j, parent j = some i → T j = T' j) :
    Pred D parent up loss low high T i a z ↔ Pred D parent up loss low high T' i a z := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j hj => (h j hj) ▸ h3 j hj⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j hj => (h j hj).symm ▸ h3 j hj⟩

theorem pred_repr (T : Fin m → Fin k → Option (Nat × Nat)) (i : Fin m) (a : Fin k) :
    ∃ s, Nrm D s ∧ ∀ z, Ins s z ↔ Pred D parent up loss low high T i a z := by
  apply repr_exists
  · rintro z ⟨_, h, _⟩
    exact le_trans h (min_le_left _ _)
  · rintro z1 z z2 ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h1 h2
    refine ⟨by omega, by omega, fun j hj => ?_⟩
    cases hu : up j
    · obtain ⟨b, l, u, he, hc⟩ := c1 j hj
      refine ⟨b, l, u, he, ?_⟩
      simp only [hu, cnd] at hc ⊢; omega
    · obtain ⟨b, l, u, he, hc⟩ := c2 j hj
      refine ⟨b, l, u, he, ?_⟩
      simp only [hu, cnd] at hc ⊢; omega

variable {parent}

theorem exists_aux (hp : ∀ i j, parent j = some i → i.val < j.val) (n : Nat) :
    ∃ T : Fin m → Fin k → Option (Nat × Nat), ∀ i : Fin m, m ≤ i.val + n →
      ∀ a, Nrm D (T i a) ∧ ∀ z, Ins (T i a) z ↔ Pred D parent up loss low high T i a z := by
  induction n with
  | zero => exact ⟨fun _ _ => none, fun i hi => absurd i.isLt (by omega)⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    by_cases hn : n < m
    · let i0 : Fin m := ⟨m - 1 - n, by omega⟩
      choose sf hsf using fun a => pred_repr D parent up loss low high T i0 a
      refine ⟨Function.update T i0 sf, fun i hi a => ?_⟩
      have hch : ∀ j, parent j = some i → Function.update T i0 sf j = T j := by
        intro j hj
        apply Function.update_of_ne
        intro he
        have := hp i j hj
        by_cases hii : i = i0
        · subst hii; rw [he] at this; simp at this
        · have : i.val ≠ m - 1 - n := fun h => hii (Fin.ext h)
          have := congrArg Fin.val he
          simp [i0] at this; omega
      by_cases hii : i = i0
      · subst hii
        rw [Function.update_self]
        refine ⟨(hsf a).1, fun z => ?_⟩
        rw [(hsf a).2 z]
        exact (pred_congr D parent up loss low high _ _ _ a z (fun j hj => (hch j hj).symm))
      · have hne : i.val ≠ m - 1 - n := fun h => hii (Fin.ext h)
        rw [Function.update_of_ne hii]
        refine ⟨(hT i (by omega) a).1, fun z => ?_⟩
        rw [(hT i (by omega) a).2 z]
        exact (pred_congr D parent up loss low high _ _ _ a z (fun j hj => (hch j hj).symm))
    · exact ⟨T, fun i hi => hT i (by omega)⟩

theorem rec_exists (hp : ∀ i j, parent j = some i → i.val < j.val) :
    ∃ T, Rec D parent up loss low high T := by
  obtain ⟨T, hT⟩ := exists_aux D up loss low high hp m
  exact ⟨T, fun i a => (hT i (by omega) a).1, fun i a z => (hT i (by omega) a).2 z⟩

theorem rec_unique (hp : ∀ i j, parent j = some i → i.val < j.val)
    (T T' : Fin m → Fin k → Option (Nat × Nat))
    (hT : Rec D parent up loss low high T) (hT' : Rec D parent up loss low high T') : T = T' := by
  funext i
  induction h : m - i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    funext a
    apply repr_unique D _ _ (hT.1 i a) (hT'.1 i a)
    intro z
    rw [hT.2 i a z, hT'.2 i a z]
    apply pred_congr
    intro j hj
    have := hp i j hj
    exact ih (m - j.val) (by omega) j rfl

theorem good_inside (hp : ∀ i j, parent j = some i → i.val < j.val)
    (T : Fin m → Fin k → Option (Nat × Nat))
    (hT : Rec D parent up loss low high T) (v : Fin m → Fin k) (s : Fin m → Nat)
    (hg : Good D parent up loss low high v s) : ∀ i, Ins (T i (v i)) (s i) := by
  intro i
  induction h : m - i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    rw [hT.2 i (v i) (s i)]
    refine ⟨(hg.1 i).1, (hg.1 i).2, fun j hj => ?_⟩
    have := hp i j hj
    obtain ⟨l, u, he, hl, hu⟩ := ih (m - j.val) (by omega) j rfl
    refine ⟨v j, l, u, he, ?_⟩
    have hc := hg.2 i j hj
    cases hup : up j <;> simp only [hup, cnd] at hc ⊢ <;> omega

theorem inside_good (hp : ∀ i j, parent j = some i → i.val < j.val)
    (T : Fin m → Fin k → Option (Nat × Nat))
    (hT : Rec D parent up loss low high T)
    (hr : ∀ i, parent i = none → ∃ a z, Ins (T i a) z) :
    ∃ v s, Good D parent up loss low high v s := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have h0 : parent ⟨0, hm⟩ = none := by
    cases h : parent ⟨0, hm⟩ with
    | none => rfl
    | some i => have := hp i _ h; simp at this
  obtain ⟨a0, _, _⟩ := hr _ h0
  have aux : ∀ n, ∃ f : Fin m → Fin k × Nat, ∀ x : Fin m, x.val < n →
      Ins (T x (f x).1) (f x).2 ∧ ∀ y, parent x = some y →
        cnd (up x) ((f y).2 + loss (f y).1 (f x).1 ≤ (f x).2)
          ((f x).2 + loss (f x).1 (f y).1 ≤ (f y).2) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => (a0, 0), fun x hx => absurd hx (by omega)⟩
    | succ n ih =>
      obtain ⟨f, hf⟩ := ih
      by_cases hn : n < m
      · let x0 : Fin m := ⟨n, hn⟩
        have hch : ∃ b z, Ins (T x0 b) z ∧ ∀ y, parent x0 = some y →
            cnd (up x0) ((f y).2 + loss (f y).1 b ≤ z) (z + loss b (f y).1 ≤ (f y).2) := by
          cases hpx : parent x0 with
          | none =>
            obtain ⟨b, z, hz⟩ := hr x0 hpx
            exact ⟨b, z, hz, fun y hy => by cases hy⟩
          | some y =>
            have hyx := hp y x0 hpx
            have hy := (hf y (by simpa [x0] using hyx)).1
            rw [hT.2] at hy
            obtain ⟨b, l, u, he, hc⟩ := hy.2.2 x0 hpx
            obtain ⟨hlu, _⟩ := hT.1 x0 b l u he
            cases hup : up x0
            · refine ⟨b, l, ⟨l, u, he, le_refl _, hlu⟩, fun y' hy' => ?_⟩
              cases hy'
              simp only [hup, cnd] at hc ⊢; exact hc
            · refine ⟨b, u, ⟨l, u, he, hlu, le_refl _⟩, fun y' hy' => ?_⟩
              cases hy'
              simp only [hup, cnd] at hc ⊢; exact hc
        obtain ⟨b, z, hz, hc⟩ := hch
        refine ⟨Function.update f x0 (b, z), fun x hx => ?_⟩
        have hpar : ∀ y, parent x = some y → Function.update f x0 (b, z) y = f y := by
          intro y hy
          apply Function.update_of_ne
          intro he
          have := hp y x hy
          rw [he] at this
          simp [x0] at this; omega
        by_cases hxx : x = x0
        · subst hxx
          rw [Function.update_self]
          refine ⟨hz, fun y hy => ?_⟩
          rw [hpar y hy]
          exact hc y hy
        · have hne : x.val ≠ n := fun h => hxx (Fin.ext h)
          rw [Function.update_of_ne hxx]
          refine ⟨(hf x (by omega)).1, fun y hy => ?_⟩
          rw [hpar y hy]
          exact (hf x (by omega)).2 y hy
      · exact ⟨f, fun x hx => hf x (by omega)⟩
  obtain ⟨f, hf⟩ := aux m
  refine ⟨fun x => (f x).1, fun x => (f x).2, fun x => ?_, fun i j hj => (hf j j.isLt).2 i hj⟩
  have := (hf x x.isLt).1
  rw [hT.2] at this
  exact ⟨this.1, this.2.1⟩

variable (parent)

def Anc (x w : Fin m) : Prop := Relation.ReflTransGen (fun a b => parent a = some b) x w

theorem anc_le (hp : ∀ i j, parent j = some i → i.val < j.val) {x w : Fin m}
    (h : Anc parent x w) : w.val ≤ x.val := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => have := hp _ _ hbc; omega

theorem anc_step {x y w : Fin m} (hxy : parent x = some y) :
    Anc parent x w ↔ x = w ∨ Anc parent y w := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, hcw⟩
    · exact Or.inl h
    · rw [hxy] at hc; cases hc; exact Or.inr hcw
  · rintro (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hxy h

theorem convex (hp : ∀ i j, parent j = some i → i.val < j.val) (i : Fin m) (a : Fin k)
    (v1 : Fin m → Fin k) (p1 : Fin m → Nat) (g1 : Good D parent up loss low high v1 p1)
    (hv1 : v1 i = a)
    (v2 : Fin m → Fin k) (p2 : Fin m → Nat) (g2 : Good D parent up loss low high v2 p2)
    (hv2 : v2 i = a) (z : Nat) (h1 : p1 i ≤ z) (h2 : z ≤ p2 i) :
    ∃ v p, Good D parent up loss low high v p ∧ v i = a ∧ p i = z := by
  classical
  let B : Fin m → Prop := fun x =>
    (∃ j, parent j = some i ∧ Anc parent x j ∧ up j = true) ∨
      (¬ Anc parent x i ∧ ∃ y, parent i = some y ∧ up i = false)
  let v : Fin m → Fin k := fun x => if x = i then a else if B x then v2 x else v1 x
  let p : Fin m → Nat := fun x => if x = i then z else if B x then p2 x else p1 x
  have vi : v i = a := by simp [v]
  have pi : p i = z := by simp [p]
  have vB : ∀ x, x ≠ i → B x → v x = v2 x ∧ p x = p2 x := by
    intro x hx hb; simp [v, p, hx, hb]
  have vA : ∀ x, x ≠ i → ¬ B x → v x = v1 x ∧ p x = p1 x := by
    intro x hx hb; simp [v, p, hx, hb]
  refine ⟨v, p, ⟨fun x => ?_, fun y x hxy => ?_⟩, vi, pi⟩
  · by_cases hx : x = i
    · subst hx
      rw [vi, pi]
      have a1 := g1.1 x
      have a2 := g2.1 x
      rw [hv1] at a1; rw [hv2] at a2
      constructor <;> omega
    · by_cases hb : B x
      · obtain ⟨e1, e2⟩ := vB x hx hb; rw [e1, e2]; exact g2.1 x
      · obtain ⟨e1, e2⟩ := vA x hx hb; rw [e1, e2]; exact g1.1 x
  · have hlt := hp y x hxy
    by_cases hx : x = i
    · subst hx
      have hy : y ≠ x := fun h => by subst h; omega
      have hB : B y ↔ up x = false := by
        constructor
        · rintro (⟨j, hj, ha, _⟩ | ⟨_, y', _, hu⟩)
          · have := anc_le parent hp ha
            have := hp _ _ hj
            omega
          · exact hu
        · intro hu
          exact Or.inr ⟨fun ha => by have := anc_le parent hp ha; omega, y, hxy, hu⟩
      rw [vi, pi]
      cases hup : up x
      · obtain ⟨e1, e2⟩ := vB y hy (hB.2 hup); rw [e1, e2]
        have c := g2.2 y x hxy
        rw [hv2, hup] at c
        simp only [cnd] at c ⊢; omega
      · obtain ⟨e1, e2⟩ := vA y hy (fun h => by rw [hB.1 h] at hup; cases hup); rw [e1, e2]
        have c := g1.2 y x hxy
        rw [hv1, hup] at c
        simp only [cnd] at c ⊢; omega
    · by_cases hy : y = i
      · subst hy
        have hB : B x ↔ up x = true := by
          constructor
          · rintro (⟨j, hj, ha, hu⟩ | ⟨hn, _⟩)
            · rcases (anc_step parent hxy).1 ha with rfl | ha'
              · exact hu
              · have := anc_le parent hp ha'
                have := hp _ _ hj
                omega
            · exact absurd ((anc_step parent hxy).2 (Or.inr Relation.ReflTransGen.refl)) hn
          · intro hu
            exact Or.inl ⟨x, hxy, Relation.ReflTransGen.refl, hu⟩
        rw [vi, pi]
        cases hup : up x
        · obtain ⟨e1, e2⟩ := vA x hx (fun h => by rw [hB.1 h] at hup; cases hup); rw [e1, e2]
          have c := g1.2 y x hxy
          rw [hv1, hup] at c
          simp only [cnd] at c ⊢; omega
        · obtain ⟨e1, e2⟩ := vB x hx (hB.2 hup); rw [e1, e2]
          have c := g2.2 y x hxy
          rw [hv2, hup] at c
          simp only [cnd] at c ⊢; omega
      · have hj : ∀ j, parent j = some i → (Anc parent x j ↔ Anc parent y j) := by
          intro j hj
          rw [anc_step parent hxy]
          constructor
          · rintro (rfl | h)
            · rw [hxy] at hj; cases hj; exact absurd rfl hy
            · exact h
          · exact Or.inr
        have hi : Anc parent x i ↔ Anc parent y i := by
          rw [anc_step parent hxy]
          constructor
          · rintro (h | h)
            · exact absurd h hx
            · exact h
          · exact Or.inr
        have hB : B x ↔ B y := by
          constructor
          · rintro (⟨j, h1, h2, h3⟩ | ⟨h1, h2⟩)
            · exact Or.inl ⟨j, h1, (hj j h1).1 h2, h3⟩
            · exact Or.inr ⟨fun h => h1 (hi.2 h), h2⟩
          · rintro (⟨j, h1, h2, h3⟩ | ⟨h1, h2⟩)
            · exact Or.inl ⟨j, h1, (hj j h1).2 h2, h3⟩
            · exact Or.inr ⟨fun h => h1 (hi.1 h), h2⟩
        by_cases hb : B y
        · obtain ⟨e1, e2⟩ := vB x hx (hB.2 hb)
          obtain ⟨e3, e4⟩ := vB y hy hb
          rw [e1, e2, e3, e4]; exact g2.2 y x hxy
        · obtain ⟨e1, e2⟩ := vA x hx (fun h => hb (hB.1 h))
          obtain ⟨e3, e4⟩ := vA y hy hb
          rw [e1, e2, e3, e4]; exact g1.2 y x hxy

theorem proj (hp : ∀ i j, parent j = some i → i.val < j.val) (i : Fin m) (a : Fin k) :
    ∃ s, Nrm D s ∧ ∀ z, Ins s z ↔
      ∃ v p, Good D parent up loss low high v p ∧ v i = a ∧ p i = z := by
  apply repr_exists
  · rintro z ⟨v, p, g, _, rfl⟩
    exact le_trans (g.1 i).2 (min_le_left _ _)
  · rintro z1 z z2 ⟨v1, p1, g1, hv1, rfl⟩ ⟨v2, p2, g2, hv2, rfl⟩ h1 h2
    exact convex D parent up loss low high hp i a v1 p1 g1 hv1 v2 p2 g2 hv2 z h1 h2

theorem main (hp : ∀ i j, parent j = some i → i.val < j.val) :
    (∃! T, Rec D parent up loss low high T) ∧
    (∀ T, Rec D parent up loss low high T → ((∃ v s, Good D parent up loss low high v s) ↔
      ∀ i, parent i = none → ∃ a z, Ins (T i a) z)) ∧
    (∀ i a, ∃ s, Nrm D s ∧ ∀ z, Ins s z ↔
      ∃ v p, Good D parent up loss low high v p ∧ v i = a ∧ p i = z) := by
  refine ⟨?_, fun T hT => ⟨?_, inside_good D up loss low high hp T hT⟩,
    proj D parent up loss low high hp⟩
  · obtain ⟨T, hT⟩ := rec_exists D up loss low high hp
    exact ⟨T, hT, fun T' hT' => rec_unique D up loss low high hp T' T hT' hT⟩
  · rintro ⟨v, s, hg⟩ i _
    exact ⟨v i, s i, good_inside D up loss low high hp T hT v s hg i⟩

end

end PEqualNP.Outside.L_lib_1298

theorem PEqualNP.Outside.L_lib_1298 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (m k t D : Nat) (parent : Fin m → Option (Fin m)) (up : Fin m → Bool)
  (word : Fin k → Fin t → Bool) (low high : Fin m → Fin k → Nat),
  (∀ i j, parent j = some i → i.val < j.val) →
  let loss := fun (a b : Fin k) => if ∃ q, word a q = true ∧ word b q = false then 1 else 0
  let inside := fun (s : Option (Nat × Nat)) (z : Nat) =>
    ∃ l u, s = some (l,u) ∧ l ≤ z ∧ z ≤ u
  let norm := fun (s : Option (Nat × Nat)) =>
    ∀ l u, s = some (l,u) → l ≤ u ∧ u ≤ D
  let recur := fun (T : Fin m → Fin k → Option (Nat × Nat)) =>
    (∀ i a, norm (T i a)) ∧
    ∀ i a z, inside (T i a) z ↔ low i a ≤ z ∧ z ≤ min D (high i a) ∧
      ∀ j, parent j = some i → ∃ b l u, T j b = some (l,u) ∧
        (if up j then z + loss a b ≤ u else l + loss b a ≤ z)
  let good := fun (v : Fin m → Fin k) (s : Fin m → Nat) =>
    (∀ i, low i (v i) ≤ s i ∧ s i ≤ min D (high i (v i))) ∧
    ∀ i j, parent j = some i →
      (if up j then s i + loss (v i) (v j) ≤ s j else s j + loss (v j) (v i) ≤ s i)
  (∃! T, recur T) ∧
    (∀ T, recur T → ((∃ v s, good v s) ↔ ∀ i, parent i = none → ∃ a z, inside (T i a) z)) ∧
    (∀ i a, ∃ s, norm s ∧ ∀ z, inside s z ↔
      ∃ v p, good v p ∧ v i = a ∧ p i = z) := by
  intro m k t D parent up word low high hp
  simp only [PEqualNP.Outside.L_lib_1298.ite_cnd]
  exact PEqualNP.Outside.L_lib_1298.main D parent up
    (fun a b => @ite Nat (∃ q, word a q = true ∧ word b q = false) (Classical.propDecidable _) 1 0)
    low high hp
