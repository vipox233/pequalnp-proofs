import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_702

private abbrev Half (s : ℕ) := Fin s → ZMod 2
private abbrev Names (s : ℕ) := Half s × Half s
private abbrev Aug (s : ℕ) := Names s × ZMod 2

private def quad {s : ℕ} (v : Names s) : ZMod 2 := ∑ i, v.1 i * v.2 i

private def unit {s : ℕ} (i : Fin s) : Half s := fun j => if i = j then 1 else 0

private def basis {s : ℕ} (i : Fin (2*s+1)) : Aug s :=
  ((fun j => if i.val = j.val then 1 else 0, fun j => if i.val = s + j.val then 1 else 0),
    if i.val = 2*s then 1 else 0)

private def coordLeft {s : ℕ} (i : Fin s) : Fin (2*s+1) := ⟨i.val, by omega⟩

private def coordRight {s : ℕ} (i : Fin s) : Fin (2*s+1) := ⟨s + i.val, by omega⟩

private def coordCheck (s : ℕ) : Fin (2*s+1) := ⟨2*s, by omega⟩

private def coordRead {s : ℕ} (w : Fin (2*s+1) → ZMod 2) : Aug s :=
  ((fun i => w (coordLeft i), fun i => w (coordRight i)), w (coordCheck s))

private theorem coordRead_injective (s : ℕ) : Function.Injective (@coordRead s) := by
  intro x y h
  funext j
  by_cases h₀ : j.val < s
  · let i : Fin s := ⟨j.val, h₀⟩
    have hj : coordLeft i = j := Fin.ext rfl
    simpa only [coordRead, hj] using congrArg (fun z : Aug s => z.1.1 i) h
  by_cases h₁ : j.val < 2*s
  · let i : Fin s := ⟨j.val - s, by omega⟩
    have hj : coordRight i = j := Fin.ext (show s + (j.val - s) = j.val by omega)
    simpa only [coordRead, hj] using congrArg (fun z : Aug s => z.1.2 i) h
  · have hj : coordCheck s = j := Fin.ext (show 2*s = j.val by omega)
    simpa only [coordRead, hj] using congrArg (fun z : Aug s => z.2) h

private theorem coordRead_bijective (s : ℕ) : Function.Bijective (@coordRead s) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨coordRead_injective s, ?_⟩
  simp [pow_succ, two_mul, pow_add]

private theorem coordRead_basis {s : ℕ} (i : Fin (2*s+1)) :
    coordRead (fun j => if i = j then 1 else 0) = basis i := by
  simp [coordRead, coordLeft, coordRight, coordCheck, basis, Fin.ext_iff]

private def coordBit (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem coordBit_injective : Function.Injective coordBit := by
  intro x y h
  cases x <;> cases y <;> simp_all [coordBit]

private def coordName {s : ℕ} (u : Fin (4^s)) : Names s :=
  (fun i => coordBit (u.val.testBit i.val), fun i => coordBit (u.val.testBit (s+i.val)))

private theorem coordBound (s : ℕ) : 4^s = 2^(2*s) := by
  rw [pow_mul]
  rfl

private theorem coordName_bijective (s : ℕ) : Function.Bijective (@coordName s) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · intro x y h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases h₀ : j < s
    · let i : Fin s := ⟨j, h₀⟩
      exact coordBit_injective (congrArg (fun z : Names s => z.1 i) h)
    by_cases h₁ : j < 2*s
    · let i : Fin s := ⟨j - s, by omega⟩
      have hj : s + i.val = j := by change s + (j - s) = j; omega
      simpa only [coordName, hj] using
        coordBit_injective (congrArg (fun z : Names s => z.2 i) h)
    · have hpow : 4^s ≤ 2^j :=
        (coordBound s).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hpow),
        Nat.testBit_eq_false_of_lt (y.isLt.trans_le hpow)]
  · simpa [two_mul, pow_add] using coordBound s

private theorem coordName_ne_zero {s : ℕ} (u : Fin (4^s)) :
    coordName u ≠ 0 ↔ u.val ≠ 0 := by
  have hp : 0 < 4^s := by positivity
  let o : Fin (4^s) := ⟨0, hp⟩
  have ho : coordName o = 0 := by ext i <;> simp [coordName, o, coordBit]
  rw [← ho, (coordName_bijective s).1.ne_iff]
  exact not_congr (Fin.ext_iff (a := u) (b := o))

private def coordParity {s : ℕ} (u : Fin (4^s)) :=
  ((Finset.univ : Finset (Fin s)).filter (fun i =>
    u.val.testBit i.val && u.val.testBit (s+i.val))).card % 2 == 1

private def coordGraph {s : ℕ} (u : Fin (4^s)) (j : Fin (2*s+1)) : ZMod 2 :=
  if (if j.val < 2*s then u.val.testBit j.val else coordParity u) then 1 else 0

private theorem coordParity_correct {s : ℕ} (u : Fin (4^s)) :
    coordBit (coordParity u) = quad (coordName u) := by
  let p (i : Fin s) := u.val.testBit i.val && u.val.testBit (s+i.val)
  let n := ((Finset.univ : Finset (Fin s)).filter fun i => p i).card
  have hquad : quad (coordName u) = (n : ZMod 2) := by
    rw [quad, show (n : ZMod 2) = ∑ i : Fin s, if p i then 1 else 0 from
      Finset.natCast_card_filter (fun i => p i) Finset.univ]
    apply Finset.sum_congr rfl
    intro i _
    change coordBit (u.val.testBit i.val) * coordBit (u.val.testBit (s+i.val)) =
      if p i then 1 else 0
    cases hx : u.val.testBit i.val <;> cases hy : u.val.testBit (s+i.val) <;>
      simp [coordBit, p, hx, hy]
  rw [hquad]
  change (if (n % 2 == 1) then 1 else 0) = (n : ZMod 2)
  rw [← ZMod.natCast_mod n 2]
  have ht : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases ht with h | h <;> simp [h]

private theorem coordRead_graph {s : ℕ} (u : Fin (4^s)) :
    coordRead (coordGraph u) = (coordName u, quad (coordName u)) := by
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) ?_
  · have hi : i.val < 2*s := by omega
    simp [coordRead, coordLeft, coordGraph, coordName, coordBit, hi]
  · have hi : s + i.val < 2*s := by omega
    simp [coordRead, coordRight, coordGraph, coordName, coordBit, hi]
  · simpa [coordRead, coordCheck, coordGraph, coordBit] using coordParity_correct u

private theorem coordinates (s g : ℕ) :
    (∃ w : ℕ → Fin (2*s+1) → ZMod 2,
      (∀ i j : Fin (2*s+1), w i.val j = if i = j then 1 else 0) ∧
      (∀ v : Fin g, ∃ a b : ℕ, a < 2*s+1+v.val ∧ b < 2*s+1+v.val ∧
        w (2*s+1+v.val) = w a + w b) ∧
      (∀ u : Fin (4^s), u.val ≠ 0 → ∃ a : ℕ, a < 2*s+1+g ∧
        w a = fun j =>
          if (if j.val < 2*s then u.val.testBit j.val else
            ((Finset.univ : Finset (Fin s)).filter (fun i =>
              u.val.testBit i.val && u.val.testBit (s+i.val))).card % 2 == 1) then
            (1 : ZMod 2) else 0)) ↔
    (∃ w : ℕ → Aug s,
      (∀ i : Fin (2*s+1), w i.val = basis i) ∧
      (∀ v : Fin g, ∃ a b : ℕ, a < 2*s+1+v.val ∧ b < 2*s+1+v.val ∧
        w (2*s+1+v.val) = w a + w b) ∧
      (∀ z : Names s, z ≠ 0 → ∃ a : ℕ, a < 2*s+1+g ∧ w a = (z, quad z))) := by
  constructor
  · rintro ⟨w, hinput, hgate, hout⟩
    refine ⟨fun a => coordRead (w a), ?_, ?_, ?_⟩
    · intro i
      change coordRead (w i.val) = basis i
      rw [show w i.val = fun j => if i = j then 1 else 0 from funext (hinput i)]
      exact coordRead_basis i
    · intro v
      obtain ⟨a, b, ha, hb, heq⟩ := hgate v
      exact ⟨a, b, ha, hb, congrArg coordRead heq⟩
    · intro z hz
      obtain ⟨u, rfl⟩ := (coordName_bijective s).2 z
      obtain ⟨a, ha, heq⟩ := hout u ((coordName_ne_zero u).1 hz)
      exact ⟨a, ha, (congrArg coordRead heq).trans (coordRead_graph u)⟩
  · rintro ⟨w, hinput, hgate, hout⟩
    let e := Equiv.ofBijective (@coordRead s) (coordRead_bijective s)
    have he (a : ℕ) : coordRead (e.symm (w a)) = w a := e.apply_symm_apply _
    refine ⟨fun a => e.symm (w a), ?_, ?_, ?_⟩
    · intro i j
      have h := coordRead_injective s ((he i.val).trans ((hinput i).trans (coordRead_basis i).symm))
      exact congrFun h j
    · intro v
      obtain ⟨a, b, ha, hb, heq⟩ := hgate v
      refine ⟨a, b, ha, hb, coordRead_injective s ?_⟩
      change coordRead (e.symm (w (2*s+1+v.val))) =
        coordRead (e.symm (w a)) + coordRead (e.symm (w b))
      rw [he, he, he, heq]
    · intro u hu
      obtain ⟨a, ha, heq⟩ := hout (coordName u) ((coordName_ne_zero u).2 hu)
      exact ⟨a, ha, coordRead_injective s ((he a).trans (heq.trans (coordRead_graph u).symm))⟩

private theorem graph_lower {V : Type*} [AddGroup V] [Fintype V]
    (tag : V → ZMod 2) (h0 : tag 0 = 0) (h1 : ∃ z, tag z = 1)
    (k g : ℕ) (w : ℕ → V × ZMod 2) (hc : w k = (0, 1))
    (hb : ∀ i < k, (w i).2 = 0)
    (hg : ∀ v : Fin g, ∃ a b : ℕ, a < k + 1 + v.val ∧ b < k + 1 + v.val ∧
      w (k + 1 + v.val) = w a + w b)
    (ho : ∀ z : V, z ≠ 0 → ∃ a : ℕ, a < k + 1 + g ∧ w a = (z, tag z)) :
    Fintype.card V ≤ g + k := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hbit (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  classical
  obtain ⟨z, hz⟩ := h1
  have hzn : z ≠ 0 := by
    intro h
    simp [h, h0] at hz
  obtain ⟨r, hr, hwr⟩ := ho z hzn
  have hex : ∃ j, j < k + 1 + g ∧ (w j).2 = 1 ∧ w j ≠ (0, 1) := by
    refine ⟨r, hr, by simpa [hwr] using hz, ?_⟩
    intro heq
    exact hzn (by simpa [hwr] using congrArg Prod.fst heq)
  let j := Nat.find hex
  obtain ⟨hj, hj1, hjn⟩ := Nat.find_spec hex
  have unit_of_earlier {i : ℕ} (hi : i < j) (hi1 : (w i).2 = 1) : w i = (0, 1) := by
    by_contra h
    exact Nat.find_min hex hi ⟨hi.trans hj, hi1, h⟩
  have hjk : k < j := by
    apply lt_of_not_ge
    intro h
    rcases lt_or_eq_of_le h with hjlt | hjeq
    · exact h01 ((hb j hjlt).symm.trans hj1)
    · exact hjn ((congrArg w hjeq).trans hc)
  let v : Fin g := ⟨j - (k + 1), by omega⟩
  have hv : k + 1 + v.val = j := by dsimp [v]; omega
  obtain ⟨a, b, ha, hb', hab⟩ := hg v
  rw [hv] at ha hb' hab
  have hab1 : (w a).2 + (w b).2 = 1 := by
    change (w a + w b).2 = 1
    rw [← hab, hj1]
  have hother : ∃ i < j, (w i).2 = 0 ∧ (w i).1 = (w j).1 := by
    rcases hbit (w a).2 with ha0 | ha1
    · have hb1 : (w b).2 = 1 := by simpa [ha0] using hab1
      refine ⟨a, ha, ha0, ?_⟩
      rw [hab, unit_of_earlier hb' hb1]
      change (w a).1 = (w a).1 + 0
      rw [add_zero]
    · have hb0 : (w b).2 = 0 := by
        rcases hbit (w b).2 with hb0 | hb1
        · exact hb0
        · rw [ha1, hb1, h11] at hab1
          exact (h01 hab1).elim
      refine ⟨b, hb', hb0, ?_⟩
      rw [hab, unit_of_earlier ha ha1]
      change (w b).1 = 0 + (w b).1
      rw [zero_add]
  obtain ⟨e, he, hek, hebad⟩ : ∃ e < k + 1 + g, e ≠ k ∧ (w e).2 ≠ tag (w e).1 := by
    by_cases hjgood : (w j).2 = tag (w j).1
    · obtain ⟨i, hi, hi0, hisame⟩ := hother
      refine ⟨i, hi.trans hj, ?_, ?_⟩
      · intro h
        exact h01 (by simpa [h, hc] using hi0.symm)
      · rw [hi0, hisame, ← hjgood, hj1]
        exact h01
    · exact ⟨j, hj, ne_of_gt hjk, hjgood⟩
  let c : Fin (k + 1 + g) := ⟨k, by omega⟩
  let S := Finset.univ.erase c
  have mem_slots {a : ℕ} (ha : a < k + 1 + g) (hak : a ≠ k) :
      (⟨a, ha⟩ : Fin (k + 1 + g)) ∈ S := by
    simp only [S, Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    exact hak (congrArg Fin.val h)
  -- Decode graph slots by their names and use the extra slot to decode zero.
  let value (i : S) : V :=
    if (w i.val.val).2 = tag (w i.val.val).1 then (w i.val.val).1 else 0
  have hsurj : Function.Surjective value := by
    intro x
    by_cases hx : x = 0
    · refine ⟨⟨⟨e, he⟩, mem_slots he hek⟩, ?_⟩
      change (if (w e).2 = tag (w e).1 then (w e).1 else 0) = x
      simp [hebad, hx]
    · obtain ⟨a, ha, hwa⟩ := ho x hx
      have hak : a ≠ k := by
        intro h
        exact hx (by simpa [h, hc] using (congrArg Prod.fst hwa).symm)
      refine ⟨⟨⟨a, ha⟩, mem_slots ha hak⟩, ?_⟩
      change (if (w a).2 = tag (w a).1 then (w a).1 else 0) = x
      simp [hwa]
  calc
    Fintype.card V ≤ Fintype.card S := Fintype.card_le_of_surjective value hsurj
    _ = S.card := Fintype.card_coe S
    _ = g + k := by
      change (Finset.univ.erase c).card = g + k
      rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      omega

private theorem names_card (s : ℕ) : Fintype.card (Names s) = 4^s := by
  simp [Fintype.card_prod, ZMod.card, ← mul_pow]

-- Append a fresh permitted sum unless the target set has already been covered.
private theorem finite_schedule {A : Type*} [Add A] [DecidableEq A]
    (S : Finset A) {b : ℕ} (hb : 0 < b) (init : Fin b → A)
    (hinj : Function.Injective init) (hinit : ∀ i, init i ∈ S)
    (hclose : ∀ T : Finset A, (∀ i, init i ∈ T) →
      (∀ x ∈ T, ∀ y ∈ T, x + y ∈ S → x + y ∈ T) → S ⊆ T)
    (g : ℕ) (hg : S.card ≤ b + g) :
    ∃ w : ℕ → A, (∀ i : Fin b, w i.val = init i) ∧
      (∀ n < g, ∃ a c : ℕ, a < b+n ∧ c < b+n ∧ w (b+n) = w a + w c) ∧
      (∀ x ∈ S, ∃ a < b+g, w a = x) := by
  classical
  let avail (w : ℕ → A) (n : ℕ) := (Finset.range (b+n)).image w
  have ha (w : ℕ → A) (n : ℕ) (x : A) : x ∈ avail w n ↔ ∃ a < b+n, w a = x := by
    simp [avail]
  suffices ∀ n : ℕ, ∃ w : ℕ → A, (∀ i : Fin b, w i.val = init i) ∧
      (∀ j < n, ∃ a c : ℕ, a < b+j ∧ c < b+j ∧ w (b+j) = w a + w c) ∧
      (S ⊆ avail w n ∨ (avail w n ⊆ S ∧ b+n ≤ (avail w n).card)) by
    obtain ⟨w, hw, hstep, h⟩ := this g
    refine ⟨w, hw, hstep, fun x hx => (ha w g x).mp (?_ : x ∈ avail w g)⟩
    rcases h with h | ⟨h, hcard⟩
    · exact h hx
    · rwa [Finset.eq_of_subset_of_card_le h (hg.trans hcard)]
  intro n
  induction n with
  | zero =>
    let w (i : ℕ) := if hi : i < b then init ⟨i, hi⟩ else init ⟨0, hb⟩
    have hw (i : Fin b) : w i.val = init i := by simp [w, i.isLt]
    have heq : avail w 0 = Finset.univ.image init := by
      ext x
      simp only [ha, Nat.add_zero, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨⟨i, hi⟩, (hw ⟨i, hi⟩).symm.trans h⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, hw i⟩
    refine ⟨w, hw, by simp, Or.inr ⟨?_, ?_⟩⟩
    · rw [heq]
      exact fun x hx => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hinit i
    · rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      omega
  | succ n ih =>
    obtain ⟨w, hw, hstep, h⟩ := ih
    have happend (a c : ℕ) (ha' : a < b+n) (hc' : c < b+n) :
        ∃ w' : ℕ → A, (∀ i : Fin b, w' i.val = init i) ∧
          (∀ j < n+1, ∃ u v : ℕ, u < b+j ∧ v < b+j ∧ w' (b+j) = w' u + w' v) ∧
          avail w' (n+1) = insert (w a + w c) (avail w n) := by
      let w' := Function.update w (b+n) (w a + w c)
      have hprefix (i : ℕ) (hi : i < b+n) : w' i = w i :=
        Function.update_of_ne hi.ne _ _
      refine ⟨w', fun i => (hprefix i.val (by omega)).trans (hw i), ?_, ?_⟩
      · intro j hj
        rcases (show j < n ∨ j = n by omega) with hlt | rfl
        · obtain ⟨u, v, hu, hv, huv⟩ := hstep j hlt
          exact ⟨u, v, hu, hv, by rw [hprefix _ (by omega), hprefix _ (by omega),
            hprefix _ (by omega), huv]⟩
        · refine ⟨a, c, ha', hc', ?_⟩
          rw [hprefix _ ha', hprefix _ hc']
          exact Function.update_self _ _ _
      · ext x
        simp only [ha, Finset.mem_insert]
        constructor
        · rintro ⟨i, hi, rfl⟩
          rcases (show i < b+n ∨ i = b+n by omega) with hlt | rfl
          · exact Or.inr ⟨i, hlt, (hprefix i hlt).symm⟩
          · exact Or.inl (Function.update_self _ _ _)
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨b+n, by omega, Function.update_self _ _ _⟩
          · exact ⟨i, by omega, hprefix i hi⟩
    by_cases hfull : S ⊆ avail w n
    · obtain ⟨w', hw', hstep', hnew⟩ := happend 0 0 (by omega) (by omega)
      exact ⟨w', hw', hstep', Or.inl (hnew ▸ hfull.trans (Finset.subset_insert _ _))⟩
    · have hb' (i : Fin b) : init i ∈ avail w n :=
        (ha w n _).mpr ⟨i.val, by omega, hw i⟩
      have hadd : ∃ x ∈ avail w n, ∃ y ∈ avail w n, x+y ∈ S ∧ x+y ∉ avail w n := by
        by_contra hnot
        push Not at hnot
        exact hfull (hclose _ hb' hnot)
      obtain ⟨x, hx, y, hy, hxy, hfresh⟩ := hadd
      obtain ⟨a, ha', rfl⟩ := (ha w n x).mp hx
      obtain ⟨c, hc', rfl⟩ := (ha w n y).mp hy
      obtain ⟨w', hw', hstep', hnew⟩ := happend a c ha' hc'
      obtain ⟨hsub, hcard⟩ := h.resolve_left hfull
      refine ⟨w', hw', hstep', Or.inr ⟨?_, ?_⟩⟩
      · rw [hnew]
        exact Finset.insert_subset hxy hsub
      · rw [hnew, Finset.card_insert_of_notMem hfresh]
        omega

private theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x

private theorem bit_self_add (x : ZMod 2) : x + x = 0 := by
  exact (by decide : ∀ x : ZMod 2, x + x = 0) x

private def left {s : ℕ} : Half s →+ Aug s where
  toFun x := ((x, 0), 0)
  map_zero' := rfl
  map_add' x y := by simp

private def right {s : ℕ} : Half s →+ Aug s where
  toFun x := ((0, x), 0)
  map_zero' := rfl
  map_add' x y := by simp

private def check {s : ℕ} : Aug s := (0, 1)

private def seed {s : ℕ} (i : Fin s) : Names s := (unit i, unit i)

private theorem quad_zero {s : ℕ} : quad (0 : Names s) = 0 := by simp [quad]

private theorem quad_pure_left {s : ℕ} (x : Half s) : quad (x, 0) = 0 := by simp [quad]

private theorem quad_pure_right {s : ℕ} (x : Half s) : quad (0, x) = 0 := by simp [quad]

private theorem quad_seed {s : ℕ} (i : Fin s) : quad (seed i) = 1 := by
  calc
    quad (seed i) = ∑ j : Fin s, (if i = j then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [seed, unit, h]
    _ = 1 := by simp

private theorem quad_add_seed {s : ℕ} (z : Names s) (i : Fin s) :
    quad (z + seed i) = quad z + (z.1 i + z.2 i + 1) := by
  unfold quad
  calc
    _ = ∑ j, (z.1 j * z.2 j + (if i = j then z.1 i + z.2 i + 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      change (z.1 j + unit i j) * (z.2 j + unit i j) = _
      by_cases h : i = j
      · subst j
        simp [unit]
        ring
      · simp [unit, h]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private theorem cancel_name {s : ℕ} (x y : Names s) : x + (y + x) = y := by
  have hx : x + x = 0 := by
    apply Prod.ext
    · funext i; exact bit_self_add (x.1 i)
    · funext i; exact bit_self_add (x.2 i)
  rw [add_comm y x, ← add_assoc, hx, zero_add]

private theorem basis_left {s : ℕ} (i : Fin s) :
    basis (⟨i.val, by omega⟩ : Fin (2*s+1)) = left (unit i) := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      simp [basis, left, unit, Fin.ext_iff]
    · funext j
      have h : i.val ≠ s+j.val := by omega
      simp [basis, left, h]
  · have h : i.val ≠ 2*s := by omega
    simp [basis, left, h]

private theorem basis_right {s : ℕ} (i : Fin s) :
    basis (⟨s+i.val, by omega⟩ : Fin (2*s+1)) = right (unit i) := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      have h : s+i.val ≠ j.val := by omega
      simp [basis, right, h]
    · funext j
      simp [basis, right, unit, Fin.ext_iff]
  · have h : s+i.val ≠ 2*s := by omega
    simp [basis, right, h]

private theorem basis_check (s : ℕ) :
    basis (⟨2*s, by omega⟩ : Fin (2*s+1)) = check := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      have h : 2*s ≠ j.val := by omega
      simp [basis, check, h]
    · funext j
      have h : 2*s ≠ s+j.val := by omega
      simp [basis, check, h]
  · simp [basis, check]

private theorem basis_injective (s : ℕ) : Function.Injective (@basis s) := by
  intro i j h
  have hvec := coordRead_injective s
    ((coordRead_basis i).trans (h.trans (coordRead_basis j).symm))
  have hk := congrFun hvec j
  by_contra hne
  simp [hne] at hk

private theorem unit_ne_zero {s : ℕ} (i : Fin s) : unit i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [unit] at hi

private def allowed {s : ℕ} (i₀ : Fin s) : Finset (Aug s) :=
  insert check (insert (seed i₀, 0)
    ((Finset.univ.erase (0 : Names s)).image (fun z => (z, quad z))))

private theorem graph_allowed {s : ℕ} (i₀ : Fin s) {z : Names s} (hz : z ≠ 0) :
    (z, quad z) ∈ allowed i₀ := by
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ?_))
  exact ⟨z, by simp [hz], rfl⟩

private theorem allowed_card {s : ℕ} (i₀ : Fin s) : (allowed i₀).card ≤ 4^s+1 := by
  classical
  unfold allowed
  refine (Finset.card_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_insert_le _ _) 1).trans ?_
  have h := Finset.card_image_le (s := Finset.univ.erase (0 : Names s))
    (f := fun z => (z, quad z))
  have he : (Finset.univ.erase (0 : Names s)).card = 4^s-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, names_card]
  rw [he] at h
  have hp : 0 < 4^s := by positivity
  omega

private theorem basis_allowed {s : ℕ} (i₀ : Fin s) (i : Fin (2*s+1)) :
    basis i ∈ allowed i₀ := by
  by_cases hi : i.val < s
  · let j : Fin s := ⟨i.val, hi⟩
    have e : i = ⟨j.val, by omega⟩ := Fin.ext rfl
    rw [e, basis_left]
    have hm : (unit j, (0 : Half s)) ≠ (0 : Names s) :=
      fun h => unit_ne_zero j (congrArg Prod.fst h)
    simpa [quad_pure_left, left] using graph_allowed i₀ hm
  · by_cases hj : i.val < 2*s
    · let j : Fin s := ⟨i.val-s, by omega⟩
      have e : i = ⟨s+j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      rw [e, basis_right]
      have hm : ((0 : Half s), unit j) ≠ (0 : Names s) :=
        fun h => unit_ne_zero j (congrArg Prod.snd h)
      simpa [quad_pure_right, right] using graph_allowed i₀ hm
    · have e : i = ⟨2*s, by omega⟩ := Fin.ext (show i.val = 2*s by omega)
      rw [e, basis_check]
      exact Finset.mem_insert_self _ _

private theorem pure_words {s : ℕ} (S T : Finset (Aug s))
    (hclose : ∀ x ∈ T, ∀ y ∈ T, x+y ∈ S → x+y ∈ T)
    (f : Half s →+ Aug s) (hS : ∀ x ≠ 0, f x ∈ S)
    (hb : ∀ i, f (unit i) ∈ T) (x : Half s) : x = 0 ∨ f x ∈ T := by
  classical
  have hrep : ∑ i : Fin s, (fun j => if i = j then x i else 0) = x := by
    funext j
    simp [Finset.sum_apply]
  rw [← hrep]
  generalize (Finset.univ : Finset (Fin s)) = I
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    rcases bit_cases (x i) with h | h
    · have hz : (fun j : Fin s => if i = j then x i else 0) = (0 : Half s) := by
        funext j
        simp [h]
      rwa [hz, zero_add]
    · simp only [h]
      change unit i + (∑ j ∈ I, (fun k => if j = k then x j else 0)) = 0 ∨ _
      rcases ih with hh | hh
      · have he : (∑ j ∈ I, (fun k => if j = k then x j else 0)) = 0 := hh
        simp only [he, add_zero]
        exact Or.inr (hb i)
      · by_cases hn : unit i + (∑ j ∈ I, (fun k => if j = k then x j else 0)) = 0
        · exact Or.inl hn
        · exact Or.inr (by rw [map_add]; exact hclose _ (hb i) _ hh (map_add f _ _ ▸ hS _ hn))

private theorem complete_pair {s : ℕ} (z : Names s) (h : quad z = 1) :
    ∃ i : Fin s, z.1 i = 1 ∧ z.2 i = 1 := by
  by_contra hn
  push Not at hn
  have hz (i : Fin s) : z.1 i * z.2 i = 0 := by
    rcases bit_cases (z.1 i) with h₁ | h₁
    · simp [h₁]
    · rcases bit_cases (z.2 i) with h₂ | h₂
      · simp [h₂]
      · exact (hn i h₁ h₂).elim
  simp [quad, hz] at h

private theorem allowed_closed {s : ℕ} (i₀ : Fin s) (T : Finset (Aug s))
    (hb : ∀ i, basis i ∈ T)
    (hclose : ∀ x ∈ T, ∀ y ∈ T, x+y ∈ allowed i₀ → x+y ∈ T) : allowed i₀ ⊆ T := by
  have hcheck : check ∈ T := basis_check s ▸ hb ⟨2*s, by omega⟩
  have hleft (x : Half s) : x = 0 ∨ left x ∈ T := by
    refine pure_words _ _ hclose left (fun y hy => ?_) (fun i => ?_) x
    · have hm : (y, (0 : Half s)) ≠ (0 : Names s) :=
        fun h => hy (congrArg Prod.fst h)
      simpa [quad_pure_left, left] using graph_allowed i₀ hm
    · exact basis_left i ▸ hb ⟨i.val, by omega⟩
  have hright (x : Half s) : x = 0 ∨ right x ∈ T := by
    refine pure_words _ _ hclose right (fun y hy => ?_) (fun i => ?_) x
    · have hm : ((0 : Half s), y) ≠ (0 : Names s) :=
        fun h => hy (congrArg Prod.snd h)
      simpa [quad_pure_right, right] using graph_allowed i₀ hm
    · exact basis_right i ▸ hb ⟨s+i.val, by omega⟩
  have hpure_add (x y : Half s) : left x + right y = ((x,y),0) := by
    simp [left, right]
  have hzmem (z : Names s) (hn : z ≠ 0) (hz : quad z = 0) : (z, 0) ∈ T := by
    rcases z with ⟨x,y⟩
    rcases hleft x with rfl | hx
    · rcases hright y with rfl | hy
      · exact (hn rfl).elim
      · exact hy
    · rcases hright y with rfl | hy
      · exact hx
      · have ha : ((x,y),0) ∈ allowed i₀ := by simpa [hz] using graph_allowed i₀ hn
        rw [← hpure_add] at ha ⊢
        exact hclose _ hx _ hy ha
  -- This mixed check-zero word is the only temporary word in the allowed set.
  have htemp : (seed i₀, 0) ∈ T := by
    have hx := (hleft (unit i₀)).resolve_left (unit_ne_zero i₀)
    have hy := (hright (unit i₀)).resolve_left (unit_ne_zero i₀)
    have ha : (seed i₀, 0) ∈ allowed i₀ :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    change ((unit i₀, unit i₀), 0) ∈ T
    rw [← hpure_add]
    exact hclose _ hx _ hy (hpure_add _ _ ▸ ha)
  have hseed₀ : (seed i₀, 1) ∈ T := by
    have hn : seed i₀ ≠ 0 := fun h => unit_ne_zero i₀ (congrArg Prod.fst h)
    have ha : (seed i₀, 1) ∈ allowed i₀ := by simpa [quad_seed] using graph_allowed i₀ hn
    have e : (seed i₀, (0 : ZMod 2)) + check = (seed i₀, 1) := by simp [check]
    rw [← e] at ha ⊢
    exact hclose _ htemp _ hcheck ha
  -- A check-one seed reaches another check-one word by a zero-check difference.
  have add_zero_word (z y : Names s) (hz : (z, 1) ∈ T) (hy : y ≠ 0) (hyq : quad y = 1)
      (hzero : quad (y+z) = 0) : (y, 1) ∈ T := by
    have e : (z, (1 : ZMod 2)) + (y+z, 0) = (y, 1) := by simp [cancel_name]
    by_cases h : y+z = 0
    · simp [h] at e
      rwa [← e]
    · have ha : (y, 1) ∈ allowed i₀ := by simpa [hyq] using graph_allowed i₀ hy
      rw [← e] at ha ⊢
      exact hclose _ hz _ (hzmem _ h hzero) ha
  have hseed (i : Fin s) : (seed i, 1) ∈ T := by
    by_cases h : i = i₀
    · rwa [h]
    · have hn : seed i ≠ 0 := fun h => unit_ne_zero i (congrArg Prod.fst h)
      apply add_zero_word _ _ hseed₀ hn (quad_seed i)
      rw [quad_add_seed, quad_seed]
      simp only [seed, unit, ite_eq_right h]
      decide
  intro a ha
  simp only [allowed, Finset.mem_insert, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true] at ha
  rcases ha with rfl | rfl | ⟨z, hz, rfl⟩
  · exact hcheck
  · exact htemp
  · rcases bit_cases (quad z) with h | h
    · rw [h]; exact hzmem z hz h
    · obtain ⟨i, h₁, h₂⟩ := complete_pair z h
      rw [h]
      apply add_zero_word _ _ (hseed i) hz h
      rw [quad_add_seed, h, h₁, h₂]
      decide

private theorem graph_upper (s : ℕ) (hs : 1 ≤ s) (g : ℕ) (hg : 4^s ≤ g + 2*s) :
    ∃ w : ℕ → Aug s, (∀ i : Fin (2*s+1), w i.val = basis i) ∧
      (∀ v : Fin g, ∃ a b : ℕ, a < 2*s+1+v.val ∧ b < 2*s+1+v.val ∧
        w (2*s+1+v.val) = w a + w b) ∧
      (∀ z : Names s, z ≠ 0 → ∃ a : ℕ, a < 2*s+1+g ∧ w a = (z, quad z)) := by
  classical
  let i₀ : Fin s := ⟨0, by omega⟩
  have hc : (allowed i₀).card ≤ 2*s+1+g := (allowed_card i₀).trans (by omega)
  obtain ⟨w, hw, hstep, hout⟩ := finite_schedule (allowed i₀) (by omega)
    (@basis s) (basis_injective s) (basis_allowed i₀) (allowed_closed i₀) g hc
  exact ⟨w, hw, fun v => hstep v.val v.isLt, fun z hz => hout _ (graph_allowed i₀ hz)⟩

private theorem graph_exact (s : ℕ) (hs : 1 ≤ s) (g : ℕ) :
    (∃ w : ℕ → Aug s, (∀ i : Fin (2*s+1), w i.val = basis i) ∧
      (∀ v : Fin g, ∃ a b : ℕ, a < 2*s+1+v.val ∧ b < 2*s+1+v.val ∧
        w (2*s+1+v.val) = w a + w b) ∧
      (∀ z : Names s, z ≠ 0 → ∃ a : ℕ, a < 2*s+1+g ∧ w a = (z, quad z))) ↔
    4^s ≤ g + 2*s := by
  constructor
  · rintro ⟨w, hinit, hgate, hout⟩
    let i₀ : Fin s := ⟨0, by omega⟩
    have hc : w (2*s) = (0, 1) := (hinit ⟨2*s, by omega⟩).trans (basis_check s)
    have hb : ∀ i < 2*s, (w i).2 = 0 := by
      intro i hi
      rw [show w i = basis ⟨i, by omega⟩ from hinit ⟨i, by omega⟩]
      simp [basis, hi.ne]
    have h := graph_lower (@quad s) quad_zero ⟨seed i₀, quad_seed i₀⟩
      (2*s) g w hc hb hgate hout
    exact names_card s ▸ h
  · exact graph_upper s hs g

end PEqualNP.Outside.L_lib_702

theorem PEqualNP.Outside.L_lib_702 :
    ∀ s : ℕ, 1 ≤ s →
      let k := 2*s
      let N := 4^s
      let W := Fin (k+1) → ZMod 2
      let q := fun (u : Fin N) =>
        ((Finset.univ : Finset (Fin s)).filter (fun i =>
          u.val.testBit i.val && u.val.testBit (s+i.val))).card % 2 == 1
      let graph := fun (u : Fin N) (j : Fin (k+1)) =>
        if (if j.val < k then u.val.testBit j.val else q u) then (1 : ZMod 2) else 0
      ∀ g : ℕ,
        (∃ w : ℕ → W,
          (∀ i j : Fin (k+1), w i.val j = if i = j then 1 else 0) ∧
          (∀ v : Fin g, ∃ a b : ℕ, a < k+1+v.val ∧ b < k+1+v.val ∧
            w (k+1+v.val) = w a + w b) ∧
          (∀ u : Fin N, u.val ≠ 0 → ∃ a : ℕ, a < k+1+g ∧ w a = graph u)) ↔
        4^s ≤ g + k := by
  intro s hs
  dsimp only
  intro g
  exact (PEqualNP.Outside.L_lib_702.coordinates s g).trans
    (PEqualNP.Outside.L_lib_702.graph_exact s hs g)
