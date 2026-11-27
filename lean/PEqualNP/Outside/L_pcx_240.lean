import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_240_aux

open PEqualNP.ProofComplexity

section Fixed

variable (n w p : ℕ) (hn : 0 < n) (owner : Fin n → Fin p)

abbrev Win (w : ℕ) := Fin (w + 1) → Bool

def atSite (n w : ℕ) (hn : 0 < n) (i : Fin n) (j : Fin (w + 1)) : Fin n :=
  ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

theorem atSite_zero (i : Fin n) : atSite n w hn i ⟨0, Nat.succ_pos w⟩ = i := by
  ext
  simp [atSite, Nat.mod_eq_of_lt i.isLt]

def readers (z : Fin n) : Finset (Fin p) :=
  Finset.univ.filter fun o : Fin p =>
    ∃ i : Fin n, owner i = o ∧ ∃ j : Fin (w + 1), atSite n w hn i j = z

theorem owner_mem_readers (z : Fin n) : owner z ∈ readers n w p hn owner z := by
  simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨z, rfl, ⟨0, Nat.succ_pos w⟩, atSite_zero n w hn z⟩

def boundary : Finset (Fin n) :=
  Finset.univ.filter fun site : Fin n => 1 < (readers n w p hn owner site).card

abbrev Var (k q : ℕ) (o : Fin p) (view : Fin p → Finset (Fin k)) :=
  Sum ({i : Fin n // owner i = o} × Win w) (Sum {t : Fin k // t ∈ view o} (Fin q))

def assign (k : ℕ) (view : Fin p → Finset (Fin k)) (q : ℕ) (o : Fin p)
    (tab : Fin n → Win w → Bool) (y : Fin k → Bool) (localBits : Fin q → Bool) :
    Var n w p owner k q o view → Bool :=
  Sum.elim (fun r : {row : Fin n // owner row = o} × Win w => tab r.1.val r.2)
    (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) localBits)

def Represents (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool) : Prop :=
  ∃ (priv : Fin p → ℕ) (F : (o : Fin p) →
      Finset (Clause (Var n w p owner k (priv o) o view))),
    (ternary = true → ∀ o, ∀ C ∈ F o, C.card ≤ 3) ∧
    ∀ tab : Fin n → Win w → Bool,
      (∃ x : Fin n → Bool, ∀ i, tab i (fun off => x (atSite n w hn i off)) = true) ↔
      ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
        Satisfies (assign n w p owner k view (priv o) o tab y localBits) (↑(F o) : Set _)

def tabOf (x : Fin n → Bool) : Fin n → Win w → Bool :=
  fun i u => decide (u = fun off => x (atSite n w hn i off))

theorem tabOf_sat (x : Fin n → Bool) :
    ∃ x' : Fin n → Bool, ∀ i, tabOf n w hn x i (fun off => x' (atSite n w hn i off)) = true :=
  ⟨x, fun i => by simp [tabOf]⟩

theorem tabOf_eq_at {x x' : Fin n → Bool} {i : Fin n}
    (h : tabOf n w hn x i (fun off => x' (atSite n w hn i off)) = true)
    (j : Fin (w + 1)) : x' (atSite n w hn i j) = x (atSite n w hn i j) := by
  simp only [tabOf, decide_eq_true_eq] at h
  exact congrFun h j

def extendWord (M : Finset (Fin n)) (a : {z : Fin n // z ∈ M} → Bool) : Fin n → Bool :=
  fun z => if h : z ∈ M then a ⟨z, h⟩ else false

theorem extendWord_mem (M : Finset (Fin n)) (a : {z : Fin n // z ∈ M} → Bool)
    (z : Fin n) (hz : z ∈ M) : extendWord n M a z = a ⟨z, hz⟩ := by
  simp [extendWord, hz]

theorem satisfies_congr {V : Type} {a b : V → Bool} {F : Set (Clause V)}
    (hab : ∀ v, a v = b v) (ha : Satisfies a F) : Satisfies b F := by
  intro C hC
  obtain ⟨l, hl, hval⟩ := ha C hC
  exact ⟨l, hl, (hab l.1).symm.trans hval⟩

theorem part1 (k : ℕ) (view : Fin p → Finset (Fin k))
    (hrep : Represents n w p hn owner k view false) (group : Fin p → Fin p) :
    (Finset.univ.filter fun mark : Fin n =>
      1 < ((readers n w p hn owner mark).image group).card).card ≤
    (Finset.univ.filter fun t : Fin k =>
      1 < ((Finset.univ.filter fun party : Fin p => t ∈ view party).image group).card).card := by
  classical
  obtain ⟨priv, F, _, hiff⟩ := hrep
  set M : Finset (Fin n) := Finset.univ.filter fun mark : Fin n =>
    1 < ((readers n w p hn owner mark).image group).card
  set T : Finset (Fin k) := Finset.univ.filter fun t : Fin k =>
    1 < ((Finset.univ.filter fun party : Fin p => t ∈ view party).image group).card
  have hex : ∀ a : {z : Fin n // z ∈ M} → Bool,
      ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ loc : Fin (priv o) → Bool,
        Satisfies (assign n w p owner k view (priv o) o (tabOf n w hn (extendWord n M a)) y loc)
          (↑(F o) : Set _) := fun a =>
    (hiff (tabOf n w hn (extendWord n M a))).mp (tabOf_sat n w hn (extendWord n M a))
  let Y : ({z : Fin n // z ∈ M} → Bool) → (Fin k → Bool) := fun a => Classical.choose (hex a)
  have hY : ∀ a o, ∃ loc : Fin (priv o) → Bool,
      Satisfies (assign n w p owner k view (priv o) o (tabOf n w hn (extendWord n M a)) (Y a) loc)
        (↑(F o) : Set _) := fun a => Classical.choose_spec (hex a)
  let phi : ({z : Fin n // z ∈ M} → Bool) → ({t : Fin k // t ∈ T} → Bool) :=
    fun a t => Y a t.val
  have hinj : Function.Injective phi := by
    intro a b hab
    by_contra hne
    have hexz : ∃ z : {z : Fin n // z ∈ M}, a z ≠ b z := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨⟨z0, hz0M⟩, hdiff⟩ := hexz
    have hcard : 1 < ((readers n w p hn owner z0).image group).card :=
      (Finset.mem_filter.mp hz0M).2
    obtain ⟨g1, hg1, g2, hg2, hgne⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨o1, ho1, rfl⟩ := Finset.mem_image.mp hg1
    obtain ⟨o2, ho2, rfl⟩ := Finset.mem_image.mp hg2
    let tab' : Fin n → Win w → Bool := fun i =>
      if group (owner i) = group o1 then tabOf n w hn (extendWord n M a) i
      else tabOf n w hn (extendWord n M b) i
    let y' : Fin k → Bool := fun t =>
      if ∃ party : Fin p, group party = group o1 ∧ t ∈ view party then Y a t else Y b t
    have hsat' : ∀ o : Fin p, ∃ loc : Fin (priv o) → Bool,
        Satisfies (assign n w p owner k view (priv o) o tab' y' loc) (↑(F o) : Set _) := by
      intro o
      by_cases hgo : group o = group o1
      · obtain ⟨loc, hloc⟩ := hY a o
        refine ⟨loc, satisfies_congr ?_ hloc⟩
        intro v
        rcases v with ⟨⟨row, hrow⟩, u⟩ | ⟨⟨t, ht⟩ | q⟩
        · simp [assign, tab', hrow, hgo]
        · have hexp : ∃ party : Fin p, group party = group o1 ∧ t ∈ view party := ⟨o, hgo, ht⟩
          simp [assign, y', hexp]
        · rfl
      · obtain ⟨loc, hloc⟩ := hY b o
        refine ⟨loc, satisfies_congr ?_ hloc⟩
        intro v
        rcases v with ⟨⟨row, hrow⟩, u⟩ | ⟨⟨t, ht⟩ | q⟩
        · simp [assign, tab', hrow, hgo]
        · simp only [assign, Sum.elim_inr, Sum.elim_inl, y']
          split_ifs with hexp
          · obtain ⟨party, hgp, htp⟩ := hexp
            have htT : t ∈ T := by
              simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
              refine Finset.one_lt_card.mpr ⟨group party, ?_, group o, ?_, ?_⟩
              · exact Finset.mem_image.mpr ⟨party, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htp⟩, rfl⟩
              · exact Finset.mem_image.mpr ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
              · exact fun heq => hgo (heq.symm.trans hgp)
            exact (congrFun hab ⟨t, htT⟩).symm
          · rfl
        · rfl
    obtain ⟨x', hx'⟩ := (hiff tab').mpr ⟨y', hsat'⟩
    obtain ⟨i1, hi1, j1, hj1⟩ := (Finset.mem_filter.mp ho1).2
    obtain ⟨i2, hi2, j2, hj2⟩ := (Finset.mem_filter.mp ho2).2
    have h1 := hx' i1
    simp only [tab', hi1, ↓reduceIte] at h1
    have hval1 := tabOf_eq_at n w hn h1 j1
    rw [hj1, extendWord_mem n M a z0 hz0M] at hval1
    have h2 := hx' i2
    have hne2 : group (owner i2) ≠ group o1 := by rw [hi2]; exact hgne.symm
    simp only [tab', hne2, ↓reduceIte] at h2
    have hval2 := tabOf_eq_at n w hn h2 j2
    rw [hj2, extendWord_mem n M b z0 hz0M] at hval2
    exact hdiff (hval1.symm.trans hval2)
  have hle : Fintype.card ({z : Fin n // z ∈ M} → Bool) ≤
      Fintype.card ({t : Fin k // t ∈ T} → Bool) := Fintype.card_le_of_injective phi hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hle
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle

theorem dep_inter {k : ℕ} {g : (Fin k → Bool) → Bool} {A B : Finset (Fin k)}
    (hA : ∀ y1 y2, (∀ t ∈ A, y1 t = y2 t) → g y1 = g y2)
    (hB : ∀ y1 y2, (∀ t ∈ B, y1 t = y2 t) → g y1 = g y2) :
    ∀ y1 y2, (∀ t ∈ A ∩ B, y1 t = y2 t) → g y1 = g y2 := by
  classical
  intro y1 y2 hAB
  let ym : Fin k → Bool := fun t => if t ∈ A then y1 t else y2 t
  have h1 : g y1 = g ym := hA y1 ym (fun t ht => by simp [ym, ht])
  have h2 : g ym = g y2 := hB ym y2 (fun t ht => by
    by_cases htA : t ∈ A
    · simp only [ym, htA, ↓reduceIte]
      exact hAB t (Finset.mem_inter.mpr ⟨htA, ht⟩)
    · simp [ym, htA])
  exact h1.trans h2

theorem dep_biInter {k : ℕ} {α : Type} [DecidableEq α]
    {g : (Fin k → Bool) → Bool} {S : Finset α} {V : α → Finset (Fin k)}
    (hS : S.Nonempty)
    (hdep : ∀ o ∈ S, ∀ y1 y2, (∀ t ∈ V o, y1 t = y2 t) → g y1 = g y2) :
    ∀ y1 y2, (∀ t, (∀ o ∈ S, t ∈ V o) → y1 t = y2 t) → g y1 = g y2 := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton o =>
    intro y1 y2 hy
    exact hdep o (Finset.mem_singleton_self o) y1 y2 (fun t ht => hy t (fun o' ho' => by
      rw [Finset.mem_singleton.mp ho']; exact ht))
  | cons a s has hs ih =>
    intro y1 y2 hy
    let A : Finset (Fin k) := V a
    let B : Finset (Fin k) := Finset.univ.filter fun t => ∀ o ∈ s, t ∈ V o
    have hA : ∀ u1 u2, (∀ t ∈ A, u1 t = u2 t) → g u1 = g u2 :=
      hdep a (Finset.mem_cons_self a s)
    have hB : ∀ u1 u2, (∀ t ∈ B, u1 t = u2 t) → g u1 = g u2 := by
      intro u1 u2 hu
      exact ih (fun o ho => hdep o (Finset.mem_cons_of_mem ho)) u1 u2
        (fun t ht => hu t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
    exact dep_inter hA hB y1 y2 (fun t ht => by
      obtain ⟨htA, htB⟩ := Finset.mem_inter.mp ht
      have htB' : ∀ o ∈ s, t ∈ V o := (Finset.mem_filter.mp htB).2
      exact hy t (fun o ho => by
        rcases Finset.mem_cons.mp ho with rfl | hos
        · exact htA
        · exact htB' o hos))

theorem part2_mp (view : Fin p → Finset (Fin (boundary n w p hn owner).card)) (ternary : Bool)
    (hrep : Represents n w p hn owner (boundary n w p hn owner).card view ternary) :
    ∃ f : {z : Fin n // z ∈ boundary n w p hn owner} ↪ Fin (boundary n w p hn owner).card,
      ∀ z, ∀ o ∈ readers n w p hn owner z.val, f z ∈ view o := by
  classical
  let B := boundary n w p hn owner
  let k := B.card
  obtain ⟨priv, F, _, hiff⟩ := hrep
  have hex : ∀ a : {z : Fin n // z ∈ B} → Bool,
      ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ loc : Fin (priv o) → Bool,
        Satisfies (assign n w p owner k view (priv o) o (tabOf n w hn (extendWord n B a)) y loc)
          (↑(F o) : Set _) := fun a =>
    (hiff (tabOf n w hn (extendWord n B a))).mp (tabOf_sat n w hn (extendWord n B a))
  let Y : ({z : Fin n // z ∈ B} → Bool) → (Fin k → Bool) := fun a => Classical.choose (hex a)
  have hY : ∀ a o, ∃ loc : Fin (priv o) → Bool,
      Satisfies (assign n w p owner k view (priv o) o (tabOf n w hn (extendWord n B a)) (Y a) loc)
        (↑(F o) : Set _) := fun a => Classical.choose_spec (hex a)
  have hsplice : ∀ (a b : {z : Fin n // z ∈ B} → Bool) (o : Fin p),
      (∀ t ∈ view o, Y a t = Y b t) →
      ∀ z : {z : Fin n // z ∈ B}, o ∈ readers n w p hn owner z.val → a z = b z := by
    intro a b o hagree z hoz
    let tab' : Fin n → Win w → Bool := fun i =>
      if owner i = o then tabOf n w hn (extendWord n B a) i
      else tabOf n w hn (extendWord n B b) i
    have hsat' : ∀ o' : Fin p, ∃ loc : Fin (priv o') → Bool,
        Satisfies (assign n w p owner k view (priv o') o' tab' (Y b) loc) (↑(F o') : Set _) := by
      intro o'
      by_cases hoo' : o' = o
      · subst hoo'
        obtain ⟨loc, hloc⟩ := hY a o'
        refine ⟨loc, satisfies_congr ?_ hloc⟩
        intro v
        rcases v with ⟨⟨row, hrow⟩, u⟩ | ⟨⟨t, ht⟩ | q⟩
        · simp [assign, tab', hrow]
        · exact hagree t ht
        · rfl
      · obtain ⟨loc, hloc⟩ := hY b o'
        refine ⟨loc, satisfies_congr ?_ hloc⟩
        intro v
        rcases v with ⟨⟨row, hrow⟩, u⟩ | ⟨⟨t, ht⟩ | q⟩
        · simp [assign, tab', hrow, hoo']
        · rfl
        · rfl
    obtain ⟨x', hx'⟩ := (hiff tab').mpr ⟨Y b, hsat'⟩
    obtain ⟨i1, hi1, j1, hj1⟩ := (Finset.mem_filter.mp hoz).2
    have h1 := hx' i1
    simp only [tab', hi1, ↓reduceIte] at h1
    have hval1 := tabOf_eq_at n w hn h1 j1
    rw [hj1, extendWord_mem n B a z.val z.property] at hval1
    have hcard : 1 < (readers n w p hn owner z.val).card := (Finset.mem_filter.mp z.property).2
    obtain ⟨o2, ho2, ho2ne⟩ := Finset.exists_mem_ne hcard o
    obtain ⟨i2, hi2, j2, hj2⟩ := (Finset.mem_filter.mp ho2).2
    have h2 := hx' i2
    have hne2 : owner i2 ≠ o := by rw [hi2]; exact ho2ne
    simp only [tab', hne2, ↓reduceIte] at h2
    have hval2 := tabOf_eq_at n w hn h2 j2
    rw [hj2, extendWord_mem n B b z.val z.property] at hval2
    exact hval1.symm.trans hval2
  have hY_inj : Function.Injective Y := by
    intro a b hab
    funext z
    have hcard : 1 < (readers n w p hn owner z.val).card := (Finset.mem_filter.mp z.property).2
    obtain ⟨o, ho⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hcard)
    exact hsplice a b o (fun t _ => congrFun hab t) z ho
  have hcard_eq : Fintype.card ({z : Fin n // z ∈ B} → Bool) = Fintype.card (Fin k → Bool) := by
    simp [k]
  have hY_bij : Function.Bijective Y :=
    (Fintype.bijective_iff_injective_and_card Y).mpr ⟨hY_inj, hcard_eq⟩
  let e : ({z : Fin n // z ∈ B} → Bool) ≃ (Fin k → Bool) := Equiv.ofBijective Y hY_bij
  let psi : (Fin k → Bool) → ({z : Fin n // z ∈ B} → Bool) := e.symm
  have hpsi_Y : ∀ a, psi (Y a) = a := fun a => e.symm_apply_apply a
  have hY_psi : ∀ y, Y (psi y) = y := fun y => e.apply_symm_apply y
  have hpsi_surj : Function.Surjective psi := e.symm.surjective
  let N : {z : Fin n // z ∈ B} → Finset (Fin k) :=
    fun z => Finset.univ.filter fun t => ∀ o ∈ readers n w p hn owner z.val, t ∈ view o
  have hpsi_dep : ∀ (z : {z : Fin n // z ∈ B}) (y1 y2 : Fin k → Bool),
      (∀ t ∈ N z, y1 t = y2 t) → psi y1 z = psi y2 z := by
    intro z y1 y2 hy
    have hne : (readers n w p hn owner z.val).Nonempty :=
      Finset.card_pos.mp (Nat.zero_lt_of_lt (Finset.mem_filter.mp z.property).2)
    have hdep_each : ∀ o ∈ readers n w p hn owner z.val, ∀ u1 u2 : Fin k → Bool,
        (∀ t ∈ view o, u1 t = u2 t) → psi u1 z = psi u2 z := by
      intro o ho u1 u2 hu
      have h1 : ∀ t ∈ view o, Y (psi u1) t = Y (psi u2) t := by
        intro t ht; rw [hY_psi, hY_psi]; exact hu t ht
      exact hsplice (psi u1) (psi u2) o h1 z ho
    exact dep_biInter hne hdep_each y1 y2 (fun t ht => hy t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
  have hHall : ∀ s : Finset {z : Fin n // z ∈ B}, s.card ≤ (s.biUnion N).card := by
    intro s
    set U : Finset (Fin k) := s.biUnion N
    let lift : ({t : Fin k // t ∈ U} → Bool) → (Fin k → Bool) :=
      fun u t => if h : t ∈ U then u ⟨t, h⟩ else false
    let G : ({t : Fin k // t ∈ U} → Bool) → ({z : {z : Fin n // z ∈ B} // z ∈ s} → Bool) :=
      fun u z => psi (lift u) z.val
    have hG_surj : Function.Surjective G := by
      intro f
      let a : {z : Fin n // z ∈ B} → Bool := fun z => if h : z ∈ s then f ⟨z, h⟩ else false
      obtain ⟨y, hy⟩ := hpsi_surj a
      refine ⟨fun t => y t.val, ?_⟩
      funext ⟨z, hzs⟩
      have hsub : N z ⊆ U := Finset.subset_biUnion_of_mem N hzs
      have hagree : ∀ t ∈ N z, lift (fun t => y t.val) t = y t := by
        intro t ht
        simp [lift, hsub ht]
      change psi (lift (fun t => y t.val)) z = f ⟨z, hzs⟩
      rw [hpsi_dep z _ y hagree, hy]
      simp [a, hzs]
    have hle : Fintype.card ({z : {z : Fin n // z ∈ B} // z ∈ s} → Bool) ≤
        Fintype.card ({t : Fin k // t ∈ U} → Bool) := Fintype.card_le_of_surjective G hG_surj
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hle
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  exact ⟨⟨f, hfinj⟩, fun z o ho => (Finset.mem_filter.mp (hfmem z)).2 o ho⟩

theorem clause_card_le3_of_pair {V : Type} [DecidableEq V] (a b : Literal V) :
    ({a, b} : Clause V).card ≤ 3 := by
  calc ({a, b} : Finset (Literal V)).card ≤ 2 := Finset.card_le_two
    _ ≤ 3 := by decide

theorem clause_card_le3_of_triple {V : Type} [DecidableEq V] (a b c : Literal V) :
    ({a, b, c} : Clause V).card ≤ 3 :=
  Finset.card_le_three

theorem part2_mpr (view : Fin p → Finset (Fin (boundary n w p hn owner).card)) (ternary : Bool)
    (hmatch : ∃ f : {z : Fin n // z ∈ boundary n w p hn owner} ↪ Fin (boundary n w p hn owner).card,
      ∀ z, ∀ o ∈ readers n w p hn owner z.val, f z ∈ view o) :
    Represents n w p hn owner (boundary n w p hn owner).card view ternary := by
  classical
  let B := boundary n w p hn owner
  let k := B.card
  obtain ⟨f, hf⟩ := hmatch
  let PrivType : Fin p → Type := fun o =>
    Sum (Fin n) ({row : Fin n // owner row = o} × Win w × Fin (w + 2))
  let priv : Fin p → ℕ := fun o => Fintype.card (PrivType o)
  let eqv : (o : Fin p) → PrivType o ≃ Fin (priv o) := fun o => Fintype.equivFin (PrivType o)
  let vX : (o : Fin p) → Fin n → Var n w p owner k (priv o) o view :=
    fun o z => Sum.inr (Sum.inr (eqv o (Sum.inl z)))
  let vEq : (o : Fin p) → {row : Fin n // owner row = o} → Win w → Fin (w + 2) →
      Var n w p owner k (priv o) o view :=
    fun o row u m => Sum.inr (Sum.inr (eqv o (Sum.inr (row, u, m))))
  let vTab : (o : Fin p) → {row : Fin n // owner row = o} → Win w →
      Var n w p owner k (priv o) o view :=
    fun o row u => Sum.inl (row, u)
  let agreeClauses : (o : Fin p) → Finset (Clause (Var n w p owner k (priv o) o view)) := fun o =>
    (Finset.univ.filter fun z : {z : Fin n // z ∈ B} => o ∈ readers n w p hn owner z.val).attach.biUnion
      fun z =>
        let hz : o ∈ readers n w p hn owner z.val.val := (Finset.mem_filter.mp z.property).2
        let vS : Var n w p owner k (priv o) o view := Sum.inr (Sum.inl ⟨f z.val, hf z.val o hz⟩)
        ({({(vX o z.val.val, true), (vS, false)} : Clause _),
          ({(vX o z.val.val, false), (vS, true)} : Clause _)} : Finset _)
  let baseClauses : (o : Fin p) → Finset (Clause (Var n w p owner k (priv o) o view)) := fun o =>
    Finset.univ.image fun r : {row : Fin n // owner row = o} × Win w =>
      ({(vEq o r.1 r.2 ⟨0, Nat.succ_pos (w + 1)⟩, true)} : Clause _)
  let stepClauses : (o : Fin p) → Finset (Clause (Var n w p owner k (priv o) o view)) := fun o =>
    Finset.univ.image fun r : {row : Fin n // owner row = o} × Win w × Fin (w + 1) =>
      ({(vEq o r.1 r.2.1 ⟨r.2.2.val, Nat.lt_succ_of_lt r.2.2.isLt⟩, false),
        (vX o (atSite n w hn r.1.val r.2.2), !(r.2.1 r.2.2)),
        (vEq o r.1 r.2.1 ⟨r.2.2.val + 1, Nat.succ_lt_succ r.2.2.isLt⟩, true)} : Clause _)
  let finalClauses : (o : Fin p) → Finset (Clause (Var n w p owner k (priv o) o view)) := fun o =>
    Finset.univ.image fun r : {row : Fin n // owner row = o} × Win w =>
      ({(vEq o r.1 r.2 ⟨w + 1, Nat.lt_succ_self (w + 1)⟩, false), (vTab o r.1 r.2, true)} : Clause _)
  let F : (o : Fin p) → Finset (Clause (Var n w p owner k (priv o) o view)) :=
    fun o => agreeClauses o ∪ baseClauses o ∪ stepClauses o ∪ finalClauses o
  refine ⟨priv, F, ?_, ?_⟩
  · intro _ o C hC
    simp only [F, Finset.mem_union] at hC
    rcases hC with ((hC | hC) | hC) | hC
    · obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> exact clause_card_le3_of_pair _ _
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
      simp
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
      exact clause_card_le3_of_triple _ _ _
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
      exact clause_card_le3_of_pair _ _
  · intro tab
    constructor
    · rintro ⟨x, hx⟩
      let y : Fin k → Bool := fun t =>
        if h : ∃ z : {z : Fin n // z ∈ B}, f z = t then x (Classical.choose h).val else false
      have hy_f : ∀ z : {z : Fin n // z ∈ B}, y (f z) = x z.val := by
        intro z
        have hex : ∃ z' : {z : Fin n // z ∈ B}, f z' = f z := ⟨z, rfl⟩
        simp only [y, hex, ↓reduceDIte]
        have hch : f (Classical.choose hex) = f z := Classical.choose_spec hex
        rw [f.injective hch]
      refine ⟨y, fun o => ?_⟩
      let locVal : PrivType o → Bool := fun v =>
        match v with
        | Sum.inl z => x z
        | Sum.inr (row, u, m) =>
            decide (∀ off : Fin (w + 1), off.val < m.val → x (atSite n w hn row.val off) = u off)
      let loc : Fin (priv o) → Bool := fun q => locVal ((eqv o).symm q)
      refine ⟨loc, fun C hC => ?_⟩
      change C ∈ F o at hC
      simp only [F, Finset.mem_union] at hC
      rcases hC with ((hC | hC) | hC) | hC
      · obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        have hzo : o ∈ readers n w p hn owner z.val.val := (Finset.mem_filter.mp z.property).2
        rcases hz with rfl | rfl
        · cases hxz : x z.val.val
          · refine ⟨(Sum.inr (Sum.inl ⟨f z.val, hf z.val o hzo⟩), false), by simp, ?_⟩
            simp [assign, hy_f, hxz]
          · refine ⟨(vX o z.val.val, true), by simp, ?_⟩
            simp [assign, vX, loc, locVal, hxz]
        · cases hxz : x z.val.val
          · refine ⟨(vX o z.val.val, false), by simp, ?_⟩
            simp [assign, vX, loc, locVal, hxz]
          · refine ⟨(Sum.inr (Sum.inl ⟨f z.val, hf z.val o hzo⟩), true), by simp, ?_⟩
            simp [assign, hy_f, hxz]
      · obtain ⟨⟨row, u⟩, _, rfl⟩ := Finset.mem_image.mp hC
        refine ⟨(vEq o row u ⟨0, Nat.succ_pos (w + 1)⟩, true), by simp, ?_⟩
        simp [assign, vEq, loc, locVal]
      · obtain ⟨⟨row, u, off⟩, _, rfl⟩ := Finset.mem_image.mp hC
        by_cases hprev : ∀ off' : Fin (w + 1), off'.val < off.val → x (atSite n w hn row.val off') = u off'
        · by_cases hcur : x (atSite n w hn row.val off) = u off
          · refine ⟨(vEq o row u ⟨off.val + 1, Nat.succ_lt_succ off.isLt⟩, true), by simp, ?_⟩
            simp only [assign, vEq, Sum.elim_inr, loc, Equiv.symm_apply_apply, locVal, decide_eq_true_eq]
            intro off' hoff'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hoff' with hlt | heq
            · exact hprev off' hlt
            · have : off' = off := Fin.ext heq
              rw [this]; exact hcur
          · refine ⟨(vX o (atSite n w hn row.val off), !(u off)), by simp, ?_⟩
            simp only [assign, vX, Sum.elim_inr, loc, Equiv.symm_apply_apply, locVal]
            cases h1 : x (atSite n w hn row.val off) <;> cases h2 : u off <;> simp_all
        · refine ⟨(vEq o row u ⟨off.val, Nat.lt_succ_of_lt off.isLt⟩, false), by simp, ?_⟩
          simp only [assign, vEq, Sum.elim_inr, loc, Equiv.symm_apply_apply, locVal, decide_eq_false_iff_not]
          exact hprev
      · obtain ⟨⟨row, u⟩, _, rfl⟩ := Finset.mem_image.mp hC
        by_cases hall : ∀ off : Fin (w + 1), off.val < w + 1 → x (atSite n w hn row.val off) = u off
        · refine ⟨(vTab o row u, true), by simp, ?_⟩
          have hu : u = fun off => x (atSite n w hn row.val off) := by
            funext off
            exact (hall off off.isLt).symm
          simp only [assign, vTab, Sum.elim_inl, hu]
          exact hx row.val
        · refine ⟨(vEq o row u ⟨w + 1, Nat.lt_succ_self (w + 1)⟩, false), by simp, ?_⟩
          simp only [assign, vEq, Sum.elim_inr, loc, Equiv.symm_apply_apply, locVal, decide_eq_false_iff_not]
          exact hall
    · rintro ⟨y, hsat⟩
      let loc : (o : Fin p) → Fin (priv o) → Bool := fun o => Classical.choose (hsat o)
      have hloc : ∀ o : Fin p,
          Satisfies (assign n w p owner k view (priv o) o tab y (loc o)) (↑(F o) : Set _) :=
        fun o => Classical.choose_spec (hsat o)
      let xLoc : Fin p → Fin n → Bool := fun o z => loc o (eqv o (Sum.inl z))
      let eqLoc : (o : Fin p) → {row : Fin n // owner row = o} → Win w → Fin (w + 2) → Bool :=
        fun o row u m => loc o (eqv o (Sum.inr (row, u, m)))
      have hagree_shared : ∀ (o : Fin p) (z : {z : Fin n // z ∈ B}),
          o ∈ readers n w p hn owner z.val → xLoc o z.val = y (f z) := by
        intro o z hoz
        have hmem_filt : z ∈ Finset.univ.filter (fun z : {z : Fin n // z ∈ B} => o ∈ readers n w p hn owner z.val) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoz⟩
        have hC1 : ({(vX o z.val, true), (Sum.inr (Sum.inl ⟨f z, hf z o hoz⟩), false)} : Clause _) ∈ F o := by
          simp only [F, Finset.mem_union]
          left; left; left
          refine Finset.mem_biUnion.mpr ⟨⟨z, hmem_filt⟩, Finset.mem_attach _ _, ?_⟩
          simp
        have hC2 : ({(vX o z.val, false), (Sum.inr (Sum.inl ⟨f z, hf z o hoz⟩), true)} : Clause _) ∈ F o := by
          simp only [F, Finset.mem_union]
          left; left; left
          refine Finset.mem_biUnion.mpr ⟨⟨z, hmem_filt⟩, Finset.mem_attach _ _, ?_⟩
          simp
        have hs1 := hloc o _ hC1
        have hs2 := hloc o _ hC2
        simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
          exists_eq_left, assign, vX, Sum.elim_inr, Sum.elim_inl] at hs1 hs2
        change (xLoc o z.val = true ∨ y (f z) = false) at hs1
        change (xLoc o z.val = false ∨ y (f z) = true) at hs2
        cases h1 : xLoc o z.val <;> cases h2 : y (f z) <;> simp_all
      let x : Fin n → Bool := fun z => xLoc (owner z) z
      have hxLoc_eq : ∀ (o : Fin p) (z : Fin n), o ∈ readers n w p hn owner z → xLoc o z = x z := by
        intro o z hoz
        by_cases hoo : o = owner z
        · subst hoo; rfl
        · have hzB : z ∈ B := by
            simp only [B, boundary, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Finset.one_lt_card.mpr ⟨o, hoz, owner z, owner_mem_readers n w p hn owner z, hoo⟩
          have h1 := hagree_shared o ⟨z, hzB⟩ hoz
          have h2 := hagree_shared (owner z) ⟨z, hzB⟩ (owner_mem_readers n w p hn owner z)
          exact h1.trans h2.symm
      refine ⟨x, fun i => ?_⟩
      let o := owner i
      let row : {r : Fin n // owner r = o} := ⟨i, rfl⟩
      let u : Win w := fun off => x (atSite n w hn i off)
      have heq_ind : ∀ m : ℕ, (hm : m < w + 2) → eqLoc o row u ⟨m, hm⟩ = true := by
        intro m
        induction m with
        | zero =>
          intro hm
          have hC : ({(vEq o row u ⟨0, Nat.succ_pos (w + 1)⟩, true)} : Clause _) ∈ F o := by
            simp only [F, Finset.mem_union]
            left; left; right
            exact Finset.mem_image.mpr ⟨(row, u), Finset.mem_univ _, rfl⟩
          have hs := hloc o _ hC
          simp only [ClauseSat, Finset.mem_singleton, exists_eq_left, assign, vEq, Sum.elim_inr] at hs
          exact hs
        | succ m ih =>
          intro hm
          have hm1 : m < w + 1 := Nat.lt_of_succ_lt_succ hm
          let off : Fin (w + 1) := ⟨m, hm1⟩
          have hprev : eqLoc o row u ⟨m, Nat.lt_succ_of_lt hm1⟩ = true := ih (Nat.lt_succ_of_lt hm1)
          have horead : o ∈ readers n w p hn owner (atSite n w hn i off) := by
            simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨i, rfl, off, rfl⟩
          have hbit : xLoc o (atSite n w hn i off) = u off := hxLoc_eq o (atSite n w hn i off) horead
          have hC : ({(vEq o row u ⟨off.val, Nat.lt_succ_of_lt off.isLt⟩, false),
              (vX o (atSite n w hn row.val off), !(u off)),
              (vEq o row u ⟨off.val + 1, Nat.succ_lt_succ off.isLt⟩, true)} : Clause _) ∈ F o := by
            simp only [F, Finset.mem_union]
            left; right
            exact Finset.mem_image.mpr ⟨(row, u, off), Finset.mem_univ _, rfl⟩
          have hs := hloc o _ hC
          simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
            exists_eq_left, assign, vEq, vX, Sum.elim_inr] at hs
          change (eqLoc o row u ⟨m, Nat.lt_succ_of_lt hm1⟩ = false ∨
              xLoc o (atSite n w hn i off) = !(u off) ∨
              eqLoc o row u ⟨m + 1, hm⟩ = true) at hs
          rcases hs with h1 | h2 | h3
          · rw [hprev] at h1; cases h1
          · rw [hbit] at h2; cases hu : u off <;> simp [hu] at h2
          · exact h3
      have hlast : eqLoc o row u ⟨w + 1, Nat.lt_succ_self (w + 1)⟩ = true :=
        heq_ind (w + 1) (Nat.lt_succ_self (w + 1))
      have hCf : ({(vEq o row u ⟨w + 1, Nat.lt_succ_self (w + 1)⟩, false),
          (vTab o row u, true)} : Clause _) ∈ F o := by
        simp only [F, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨(row, u), Finset.mem_univ _, rfl⟩
      have hs := hloc o _ hCf
      simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
        exists_eq_left, assign, vEq, vTab, Sum.elim_inr, Sum.elim_inl] at hs
      change (eqLoc o row u ⟨w + 1, Nat.lt_succ_self (w + 1)⟩ = false ∨ tab i u = true) at hs
      rcases hs with h1 | h2
      · rw [hlast] at h1; cases h1
      · exact h2

end Fixed

end PEqualNP.Outside.L_pcx_240_aux

theorem PEqualNP.Outside.L_pcx_240 : (∀ (n w p : ℕ) (hn : 0 < n) (owner : Fin n → Fin p),
  let W := Fin (w + 1) → Bool
  let atSite := fun (i : Fin n) (j : Fin (w+1)) =>
    (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let readers := fun z : Fin n => Finset.univ.filter (fun o : Fin p =>
    ∃ i : Fin n, owner i = o ∧ ∃ j : Fin (w+1), atSite i j = z)
  let boundary := Finset.univ.filter (fun site : Fin n => 1 < (readers site).card)
  let V := fun (k q : ℕ) (o : Fin p) (view : Fin p → Finset (Fin k)) =>
    Sum ({i : Fin n // owner i = o} × W) (Sum {t : Fin k // t ∈ view o} (Fin q))
  let represents := fun (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool) =>
    ∃ (priv : Fin p → ℕ) (F : (o : Fin p) →
        Finset (PEqualNP.ProofComplexity.Clause (V k (priv o) o view))),
      (ternary = true → ∀ o, ∀ C ∈ F o, C.card ≤ 3) ∧
      ∀ tab : Fin n → W → Bool,
        (∃ x : Fin n → Bool, ∀ i, tab i (fun off => x (atSite i off)) = true) ↔
        ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
          PEqualNP.ProofComplexity.Satisfies
            (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab r.1.val r.2)
              (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) localBits)) (↑(F o) : Set _)
  (∀ (k : ℕ) (view : Fin p → Finset (Fin k)), represents k view false →
    ∀ group : Fin p → Fin p,
      (Finset.univ.filter (fun mark : Fin n => 1 < ((readers mark).image group).card)).card ≤
      (Finset.univ.filter (fun t : Fin k =>
        1 < ((Finset.univ.filter (fun party : Fin p => t ∈ view party)).image group).card)).card) ∧
  ∀ (view : Fin p → Finset (Fin boundary.card)) (ternary : Bool),
    represents boundary.card view ternary ↔
      ∃ f : {z : Fin n // z ∈ boundary} ↪ Fin boundary.card,
        ∀ z, ∀ o ∈ readers z.val, f z ∈ view o) := by
  intro n w p hn owner
  refine ⟨?_, ?_⟩
  · intro k view hrep group
    exact PEqualNP.Outside.L_pcx_240_aux.part1 n w p hn owner k view hrep group
  · intro view ternary
    exact ⟨PEqualNP.Outside.L_pcx_240_aux.part2_mp n w p hn owner view ternary,
      PEqualNP.Outside.L_pcx_240_aux.part2_mpr n w p hn owner view ternary⟩
