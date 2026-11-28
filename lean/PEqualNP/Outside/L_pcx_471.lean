import PEqualNP.Defs
import Mathlib.LinearAlgebra.BilinearForm.Basic

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_471

namespace Plane470

abbrev F := ZMod 2
abbrev X (m : ℕ) := (Fin m → F) × (Fin m → F)

def form {m : ℕ} (x y : X m) : F := dotProduct x.1 y.2 + dotProduct x.2 y.1

def turn {m : ℕ} (x : X m) : X m := (x.2, x.1+x.2)

theorem bit_double : ∀ b : F, b+b = 0 := by decide +kernel

theorem vec_double {m : ℕ} (x : Fin m → F) : x+x = 0 := by
  funext i
  exact bit_double (x i)

theorem pair_double {m : ℕ} (x : X m) : x+x = 0 :=
  Prod.ext (vec_double x.1) (vec_double x.2)

private theorem commute_cancel {m : ℕ} (x y : Fin m → F) : x+(y+x) = y := by
  calc
    _ = y+(x+x) := by abel
    _ = _ := by rw [vec_double, add_zero]

private def turnBack {m : ℕ} (x : X m) : X m := (x.1+x.2, x.1)

private theorem turnBack_turn {m : ℕ} (x : X m) : turnBack (turn x) = x := by
  exact Prod.ext (commute_cancel x.2 x.1) rfl

private theorem turn_turnBack {m : ℕ} (x : X m) : turn (turnBack x) = x := by
  apply Prod.ext
  · rfl
  · change (x.1+x.2)+x.1 = x.2
    rw [add_assoc, commute_cancel]

theorem turn_bijective (m : ℕ) : Function.Bijective (@turn m) :=
  ⟨(show Function.LeftInverse (@turnBack m) (@turn m) from turnBack_turn).injective,
   (show Function.RightInverse (@turnBack m) (@turn m) from turn_turnBack).surjective⟩

theorem sum_turn_bijective (m : ℕ) : Function.Bijective (fun x : X m => x + turn x) := by
  have he (x : X m) : x + turn x = turnBack x := Prod.ext rfl (commute_cancel x.2 x.1)
  simp only [he]
  exact ⟨(show Function.LeftInverse (@turn m) (@turnBack m) from turn_turnBack).injective,
    (show Function.RightInverse (@turn m) (@turnBack m) from turnBack_turn).surjective⟩

theorem turn_add {m : ℕ} (x y : X m) : turn (x+y) = turn x + turn y := by
  apply Prod.ext
  · rfl
  · change (x.1+y.1)+(x.2+y.2) = (x.1+x.2)+(y.1+y.2)
    abel

theorem form_add_left {m : ℕ} (x y z : X m) : form (x+y) z = form x z + form y z := by
  simp only [form, Prod.fst_add, Prod.snd_add, add_dotProduct]
  abel

theorem form_add_right {m : ℕ} (x y z : X m) : form x (y+z) = form x y + form x z := by
  simp only [form, Prod.fst_add, Prod.snd_add, dotProduct_add]
  abel

theorem form_self {m : ℕ} (x : X m) : form x x = 0 := by
  unfold form
  rw [dotProduct_comm x.2 x.1, bit_double]

def q {m : ℕ} (x : X m) : F := form x (turn x)

private theorem cross {m : ℕ} (x y : X m) : form x (turn y) + form y (turn x) = form x y := by
  simp only [form, turn, dotProduct_add]
  rw [dotProduct_comm y.1 x.1, dotProduct_comm y.1 x.2, dotProduct_comm y.2 x.2]
  calc
    _ = (dotProduct x.1 y.1 + dotProduct x.1 y.1) +
        (dotProduct x.2 y.2 + dotProduct x.2 y.2) +
        (dotProduct x.1 y.2 + dotProduct x.2 y.1) := by abel
    _ = _ := by rw [bit_double, bit_double, zero_add, zero_add]

theorem q_polar {m : ℕ} (x y : X m) : q (x+y) = q x + q y + form x y := by
  unfold q
  rw [turn_add, form_add_left, form_add_right, form_add_right, ← cross x y]
  abel

theorem q_translate {m : ℕ} (x t : X m) : q (x+t)+form (x+t) t = q x+q t := by
  rw [q_polar, form_add_left, form_self, add_zero, add_assoc, bit_double, add_zero]

def one_vector (m : ℕ) (hm : 0 < m) : X m := (Pi.single ⟨0,hm⟩ 1, 0)

theorem q_one_vector (m : ℕ) (hm : 0 < m) : q (one_vector m hm) = 1 := by
  simp [one_vector, q, form, turn, dotProduct, Pi.single_apply]

def newForm {m : ℕ} (t : X m) (b : Bool) (x : X m) : F :=
  form x (turn x + if b then t else 0) + 1

theorem newForm_flip {m : ℕ} (t : X m) (ht : q t = 1) (b : Bool) (x : X m) :
    newForm t (!b) (x+t) = newForm t b x + 1 := by
  have hf (y : X m) : newForm t true (y+t) = newForm t false y + 1 := by
    simp only [newForm, ite_true, Bool.false_eq_true, ite_false, add_zero,
      form_add_right]
    change q (y+t)+form (y+t) t+1 = q y+1+1
    rw [q_translate, ht]
  cases b
  · exact hf x
  · have e := hf (x+t)
    rw [add_assoc, pair_double, add_zero] at e
    change newForm t false (x+t) = newForm t true x + 1
    rw [e, add_assoc, bit_double, add_zero]

theorem new_count_eq {m : ℕ} (t : X m) (ht : q t = 1) :
    Nat.card {p : Bool × X m // newForm t p.1 p.2 = 1} =
      Nat.card {p : Bool × X m // newForm t p.1 p.2 = 0} := by
  let flip (p : Bool × X m) : Bool × X m := (!p.1, p.2+t)
  have inv : Function.Involutive flip := by
    intro p
    apply Prod.ext
    · simp [flip]
    · simp [flip, add_assoc, pair_double]
  have flip_form (p : Bool × X m) : newForm t (flip p).1 (flip p).2 = newForm t p.1 p.2+1 :=
    newForm_flip t ht p.1 p.2
  exact Nat.card_congr
    { toFun := fun p => ⟨flip p.val, by rw [flip_form, p.property, bit_double]⟩
      invFun := fun p => ⟨flip p.val, by rw [flip_form, p.property, zero_add]⟩
      left_inv := fun p => Subtype.ext (inv p.val)
      right_inv := fun p => Subtype.ext (inv p.val) }

end Plane470

namespace Counts470

theorem sum_restrict {α β : Type} [Finite α] [Finite β] (P : α → Prop) (Q : β → Prop) :
    Nat.card {i : α ⊕ β // Sum.elim P Q i} =
      Nat.card {i : α // P i} + Nat.card {i : β // Q i} := by
  let e : {i : α ⊕ β // Sum.elim P Q i} ≃ ({i : α // P i} ⊕ {i : β // Q i}) :=
    { toFun := fun i =>
        match i with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun i =>
        match i with
        | Sum.inl a => ⟨Sum.inl a.val, a.property⟩
        | Sum.inr b => ⟨Sum.inr b.val, b.property⟩
      left_inv := by rintro ⟨a | b, h⟩ <;> rfl
      right_inv := by rintro (⟨a, h⟩ | ⟨b, h⟩) <;> rfl }
  exact (Nat.card_congr e).trans Nat.card_sum

theorem bool_restrict {α : Type} [Finite α] (P : Bool → α → Prop) :
    Nat.card {i : Bool × α // P i.1 i.2} =
      Nat.card {i : α // P false i} + Nat.card {i : α // P true i} := by
  let e := Equiv.boolProdEquivSum α
  have hp (i : Bool × α) : P i.1 i.2 ↔ Sum.elim (P false) (P true) (e i) := by
    rcases i with ⟨b, a⟩
    cases b <;> rfl
  exact (Nat.card_congr (e.subtypeEquiv hp)).trans (sum_restrict _ _)

theorem pointwise {α : Type} {P Q : α → Prop} (h : ∀ i, P i ↔ Q i) :
    Nat.card {i : α // P i} = Nat.card {i : α // Q i} :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

theorem all {α : Type} {P : α → Prop} (h : ∀ i, P i) :
    Nat.card {i : α // P i} = Nat.card α := by
  let e : {i : α // P i} ≃ α :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, h i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

theorem none {α : Type} {P : α → Prop} (h : ∀ i, ¬ P i) :
    Nat.card {i : α // P i} = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun i => h i.val i.property⟩)

def size (m : ℕ) : ℕ := 2 * ((4^m - 1) / 3)

theorem size_succ (m : ℕ) : size (m+1) = size m + 2 * 4^m := by
  have h : 1 ≤ 4^m := Nat.one_le_pow _ _ (by decide)
  have ha : 4^m * 4 - 1 = 4^m - 1 + 3 * 4^m := by omega
  unfold size
  rw [pow_succ, ha, Nat.add_mul_div_left _ _ (by decide), Nat.mul_add]

theorem card_index (m : ℕ) :
    Nat.card (Fin (size m) ⊕ (Bool × ((Fin m → ZMod 2) × (Fin m → ZMod 2)))) =
      size (m+1) := by
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_eq_fintype_card.trans (ZMod.card 2)
  rw [Nat.card_sum, Nat.card_fin, Nat.card_prod, Nat.card_prod,
    Nat.card_pi, hF, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, size_succ]
  have hB : Nat.card Bool = 2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
  rw [hB, ← mul_pow]
  rfl

end Counts470

namespace Plane470

def Good {m : ℕ} {ι : Type} (u v : ι → X m) : Prop :=
  (∀ i, u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i) ∧
    (∀ a : X m, a ≠ 0 → Nat.card {i : ι // a = u i ∨ a = v i ∨ a = u i + v i} = 2) ∧
    Nat.card {i : ι // form (u i) (v i) = 1} = Nat.card {i : ι // form (u i) (v i) = 0} + 2

private def e : X 1 := (fun _ => 1, 0)

private def h : X 1 := (0, fun _ => 1)

private theorem base_nonzero : e ≠ 0 ∧ h ≠ 0 ∧ e ≠ h := by decide +kernel

private theorem base_cover : ∀ a : X 1, a ≠ 0 → a = e ∨ a = h ∨ a = e+h := by decide +kernel

private theorem base_form : form e h = 1 := by decide +kernel

theorem base : ∃ (u v : Fin (Counts470.size 1) → X 1), Good u v := by
  refine ⟨fun _ => e, fun _ => h, fun _ => base_nonzero, ?_, ?_⟩
  · intro a ha
    have hall : ∀ _ : Fin (Counts470.size 1), a = e ∨ a = h ∨ a = e+h :=
      fun _ => base_cover a ha
    rw [Counts470.all hall, Nat.card_fin]
    rfl
  · have hall : ∀ _ : Fin (Counts470.size 1), form e h = 1 := fun _ => base_form
    have hn : ∀ _ : Fin (Counts470.size 1), ¬form e h = 0 := by
      intro _
      rw [base_form]
      decide +kernel
    rw [Counts470.all hall, Counts470.none hn, Nat.card_fin]
    rfl

end Plane470

namespace Lift470

open Plane470

def extend {m : ℕ} (x : X m) (a b : F) : X (m+1) :=
  (Fin.cons a x.1, Fin.cons b x.2)

def head {m : ℕ} (x : X (m+1)) : F × F := (x.1 0, x.2 0)

def tail {m : ℕ} (x : X (m+1)) : X m :=
  (fun i => x.1 i.succ, fun i => x.2 i.succ)

@[simp] theorem head_extend {m : ℕ} (x : X m) (a b : F) :
    head (extend x a b) = (a,b) := by simp [head, extend]

@[simp] theorem tail_extend {m : ℕ} (x : X m) (a b : F) :
    tail (extend x a b) = x := by
  rcases x with ⟨p,q⟩
  simp [tail, extend]

@[simp] theorem head_zero {m : ℕ} : head (0 : X (m+1)) = 0 := rfl

@[simp] theorem tail_zero {m : ℕ} : tail (0 : X (m+1)) = 0 := rfl

theorem head_add {m : ℕ} (x y : X (m+1)) : head (x+y) = head x + head y := rfl

theorem extend_head_tail {m : ℕ} (x : X (m+1)) :
    extend (tail x) (head x).1 (head x).2 = x := by
  apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [extend, tail, head]

theorem extend_injective {m : ℕ} (a b : F) :
    Function.Injective (fun x : X m => extend x a b) := by
  intro x y h
  simpa only [tail_extend] using congrArg tail h

@[simp] theorem extend_zero {m : ℕ} : extend (0 : X m) 0 0 = 0 := by
  exact extend_head_tail (0 : X (m+1))

theorem extend_add {m : ℕ} (x y : X m) (a b c d : F) :
    extend x a b + extend y c d = extend (x+y) (a+c) (b+d) := by
  apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [extend]

theorem form_extend {m : ℕ} (x y : X m) (a b c d : F) :
    form (extend x a b) (extend y c d) = form x y + a*d + b*c := by
  simp only [form, extend, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  abel

def u {m : ℕ} (x : X m) : X (m+1) := extend x 1 0

def v {m : ℕ} (c x : X m) : X (m+1) := extend (turn x+c) 0 1

@[simp] theorem head_u {m : ℕ} (x : X m) : head (u x) = (1,0) := head_extend _ _ _

@[simp] theorem head_v {m : ℕ} (c x : X m) : head (v c x) = (0,1) := head_extend _ _ _

theorem u_ne_zero {m : ℕ} (x : X m) : u x ≠ 0 := by
  intro h
  have h' := congrArg head h
  simp at h'

theorem v_ne_zero {m : ℕ} (c x : X m) : v c x ≠ 0 := by
  intro h
  have h' := congrArg head h
  simp at h'

theorem u_ne_v {m : ℕ} (c x : X m) : u x ≠ v c x := by
  intro h
  have h' := congrArg head h
  simp at h'

theorem form_new {m : ℕ} (c x : X m) :
    form (u x) (v c x) = form x (turn x+c) + 1 := by
  rw [u, v, form_extend]
  simp

theorem hit_old {m : ℕ} (a x : X m) :
    extend a 0 0 = extend x 0 0 ↔ a = x :=
  ⟨fun h => (extend_injective 0 0) h, congrArg (fun z => extend z 0 0)⟩

theorem extend_eq_iff {m : ℕ} (y : X (m+1)) (x : X m) (a b : F) :
    y = extend x a b ↔ head y = (a,b) ∧ tail y = x := by
  constructor
  · intro h
    subst y
    simp
  · rintro ⟨hh,ht⟩
    conv_lhs => rw [← extend_head_tail y]
    rw [hh, ht]

theorem old_hits {m : ℕ} (a : X (m+1)) (x y : X m) :
    (a = extend x 0 0 ∨ a = extend y 0 0 ∨ a = extend x 0 0 + extend y 0 0) ↔
      head a = 0 ∧ (tail a = x ∨ tail a = y ∨ tail a = x+y) := by
  simp only [extend_add, zero_add, extend_eq_iff]
  change (_ ∧ _ ∨ _ ∧ _ ∨ _ ∧ _) ↔ (head a = (0,0) ∧ _)
  tauto

theorem hit_iff {m : ℕ} (c x : X m) (y : X (m+1)) :
    (y = u x ∨ y = v c x ∨ y = u x + v c x) ↔
      (head y = (1,0) ∧ tail y = x) ∨
      (head y = (0,1) ∧ tail y = turn x+c) ∨
      (head y = (1,1) ∧ tail y = x+turn x+c) := by
  simp only [u, v, extend_add, add_zero, zero_add, extend_eq_iff, add_assoc]

theorem family_none {m : ℕ} (c : X m) (y : X (m+1)) (hy : head y = 0) (x : X m) :
    ¬ (y = u x ∨ y = v c x ∨ y = u x + v c x) := by
  have hy0 : head y = (0,0) := hy
  rw [hit_iff, hy0]
  simp

theorem family_zero {m : ℕ} (c : X m) (y : X (m+1)) (hy : head y = 0) :
    Nat.card {x : X m // y = u x ∨ y = v c x ∨ y = u x + v c x} = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun x => family_none c y hy x.val x.property⟩)

private theorem translated_bijective {m : ℕ} (f : X m → X m) (hf : Function.Bijective f)
    (c : X m) : Function.Bijective (fun x => f x+c) := by
  constructor
  · intro a b hab
    exact hf.1 (add_right_cancel hab)
  · intro y
    obtain ⟨x,hx⟩ := hf.2 (y-c)
    exact ⟨x, by change f x+c=y; rw [hx, sub_add_cancel]⟩

theorem family_card {m : ℕ} (c : X m) (y : X (m+1)) (hy : head y ≠ 0) :
    Nat.card {x : X m // y = u x ∨ y = v c x ∨ y = u x + v c x} = 1 := by
  have heads : ∀ h : F×F, h = 0 ∨ h = (1,0) ∨ h = (0,1) ∨ h = (1,1) := by decide +kernel
  have forms : ∃ (f : X m → X m), Function.Bijective f ∧
      ∀ x, (y = u x ∨ y = v c x ∨ y = u x + v c x) ↔ tail y = f x := by
    rcases (heads (head y)).resolve_left hy with h | h | h
    · refine ⟨id,Function.bijective_id,fun x => ?_⟩
      simp [hit_iff, h]
    · refine ⟨fun x => turn x+c,translated_bijective turn (turn_bijective m) c,fun x => ?_⟩
      simp [hit_iff, h]
    · refine ⟨fun x => x+turn x+c,
        translated_bijective (fun x => x+turn x) (sum_turn_bijective m) c,fun x => ?_⟩
      simp [hit_iff, h]
  obtain ⟨f,hf,he⟩ := forms
  obtain ⟨x,hx⟩ := hf.2 (tail y)
  let _ : Unique {x : X m // y = u x ∨ y = v c x ∨ y = u x + v c x} :=
    { default := ⟨x,(he x).mpr hx.symm⟩
      uniq := fun z => Subtype.ext (hf.1 (((he z.val).mp z.property).symm.trans hx.symm)) }
  exact Nat.card_unique

end Lift470

namespace Plane470

theorem good_reindex {m : ℕ} {I J : Type} (u v : I → X m) (e : J ≃ I)
    (h : Good u v) : Good (u ∘ e) (v ∘ e) := by
  obtain ⟨hn, hh, hb⟩ := h
  have card (P : I → Prop) :
      Nat.card {j : J // P (e j)} = Nat.card {i : I // P i} :=
    Nat.card_congr (Equiv.subtypeEquivOfSubtype e)
  refine ⟨fun j => hn (e j), ?_, ?_⟩
  · intro a ha
    exact (card (fun i => a = u i ∨ a = v i ∨ a = u i + v i)).trans (hh a ha)
  · dsimp only [Function.comp_apply]
    rw [card (fun i => form (u i) (v i) = 1), card (fun i => form (u i) (v i) = 0)]
    exact hb

theorem next {m : ℕ} (hm : 0 < m) (u v : Fin (Counts470.size m) → X m) (h : Good u v) :
    ∃ U V : Fin (Counts470.size (m+1)) → X (m+1), Good U V := by
  let t := one_vector m hm
  let offset (b : Bool) : X m := if b then t else 0
  let I := Fin (Counts470.size m) ⊕ (Bool × X m)
  let U : I → X (m+1) :=
    Sum.elim (fun i => Lift470.extend (u i) 0 0) (fun p => Lift470.u p.2)
  let V : I → X (m+1) :=
    Sum.elim (fun i => Lift470.extend (v i) 0 0) (fun p => Lift470.v (offset p.1) p.2)
  obtain ⟨hn, hh, hb⟩ := h
  have newGood : Good U V := by
    constructor
    · intro i
      cases i with
      | inl j =>
        obtain ⟨hu, hv, huv⟩ := hn j
        exact ⟨fun he => hu (Lift470.extend_injective 0 0 (he.trans Lift470.extend_zero.symm)),
          fun he => hv (Lift470.extend_injective 0 0 (he.trans Lift470.extend_zero.symm)),
          fun he => huv (Lift470.extend_injective 0 0 he)⟩
      | inr p =>
        exact ⟨Lift470.u_ne_zero p.2, Lift470.v_ne_zero (offset p.1) p.2,
          Lift470.u_ne_v (offset p.1) p.2⟩
    constructor
    · intro a ha
      let P (i : Fin (Counts470.size m)) :=
        a = Lift470.extend (u i) 0 0 ∨ a = Lift470.extend (v i) 0 0 ∨
          a = Lift470.extend (u i) 0 0 + Lift470.extend (v i) 0 0
      let Q (b : Bool) (x : X m) :=
        a = Lift470.u x ∨ a = Lift470.v (offset b) x ∨
          a = Lift470.u x + Lift470.v (offset b) x
      have split :
          Nat.card {i : I // a = U i ∨ a = V i ∨ a = U i + V i} =
            Nat.card {i // P i} + (Nat.card {x // Q false x} + Nat.card {x // Q true x}) := by
        have hsplit := Counts470.pointwise (P := fun i : I => a = U i ∨ a = V i ∨ a = U i + V i)
          (Q := Sum.elim P (fun p : Bool × X m => Q p.1 p.2)) (by rintro (i | p) <;> rfl)
        rw [hsplit, Counts470.sum_restrict, Counts470.bool_restrict Q]
      rw [split]
      by_cases hhead : Lift470.head a = 0
      · have htail : Lift470.tail a ≠ 0 := by
          intro he
          apply ha
          have hrec := Lift470.extend_head_tail a
          rw [hhead, he] at hrec
          exact hrec.symm.trans Lift470.extend_zero
        have hold := Counts470.pointwise (P := P)
          (Q := fun i => Lift470.tail a = u i ∨ Lift470.tail a = v i ∨ Lift470.tail a = u i + v i)
          (fun i => (Lift470.old_hits a (u i) (v i)).trans (and_iff_right hhead))
        have hf : Nat.card {x // Q false x} = 0 := Lift470.family_zero (offset false) a hhead
        have ht : Nat.card {x // Q true x} = 0 := Lift470.family_zero (offset true) a hhead
        rw [hold, hh _ htail, hf, ht]
      · have hold : Nat.card {i // P i} = 0 := Counts470.none fun i hi =>
          hhead ((Lift470.old_hits a (u i) (v i)).mp hi).1
        have hf : Nat.card {x // Q false x} = 1 := Lift470.family_card (offset false) a hhead
        have ht : Nat.card {x // Q true x} = 1 := Lift470.family_card (offset true) a hhead
        rw [hold, hf, ht]
    · have split (b : F) :
          Nat.card {i : I // form (U i) (V i) = b} =
            Nat.card {i : Fin (Counts470.size m) // form (u i) (v i) = b} +
            Nat.card {p : Bool × X m // newForm t p.1 p.2 = b} := by
        let P (i : Fin (Counts470.size m)) := form (u i) (v i) = b
        let Q (p : Bool × X m) := newForm t p.1 p.2 = b
        refine (Counts470.pointwise (Q := Sum.elim P Q) ?_).trans
          (Counts470.sum_restrict P Q)
        intro i
        cases i with
        | inl j =>
          change form (Lift470.extend (u j) 0 0) (Lift470.extend (v j) 0 0) = b ↔ P j
          simp [Lift470.form_extend, P]
        | inr p =>
          change form (Lift470.u p.2) (Lift470.v (offset p.1) p.2) = b ↔ Q p
          rw [Lift470.form_new]
          rfl
      rw [split 1, split 0, hb, new_count_eq t (q_one_vector m hm)]
      omega
  have hc : Fintype.card I = Counts470.size (m+1) :=
    Nat.card_eq_fintype_card.symm.trans (Counts470.card_index m)
  let e : Fin (Counts470.size (m+1)) ≃ I := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨U ∘ e, V ∘ e, good_reindex U V e newGood⟩

theorem realize (m : ℕ) (hm : 0 < m) :
    ∃ (u v : Fin (Counts470.size m) → X m), Good u v := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      exact base
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      obtain ⟨u, v, h⟩ := ih hp
      exact next hp u v h

end Plane470

namespace Model471

abbrev F := ZMod 2
abbrev W (m : ℕ) := Fin m → F
abbrev X (m : ℕ) := W m × W m

def quad {m : ℕ} (x : X m) : F := dotProduct x.1 x.2

def form {m : ℕ} (x y : X m) : F := dotProduct x.1 y.2 + dotProduct x.2 y.1

def sign (b : F) : ℚ := if b = 0 then 1 else -1

theorem bit_cases : ∀ b : F, b = 0 ∨ b = 1 := by decide +kernel

theorem bit_add_self : ∀ b : F, b+b = 0 := by decide +kernel

theorem sign_add : ∀ a b : F, sign (a+b) = sign a * sign b := by decide +kernel

theorem sign_mul_self : ∀ b : F, sign b * sign b = 1 := by decide +kernel

theorem form_symm {m : ℕ} (u v : X m) : form u v = form v u := by
  unfold form
  rw [dotProduct_comm u.1 v.2, dotProduct_comm u.2 v.1, add_comm]

theorem quad_add {m : ℕ} (u v : X m) : quad (u+v) = quad u + quad v + form u v := by
  simp only [quad, form, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm v.1 u.2]
  abel

def dotLinear {m : ℕ} (u : W m) : W m →ₗ[F] F where
  toFun := dotProduct u
  map_add' v w := dotProduct_add u v w
  map_smul' c v := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def formLinear {m : ℕ} (u : X m) : X m →ₗ[F] F :=
  (dotLinear u.1).comp (LinearMap.snd F _ _) + (dotLinear u.2).comp (LinearMap.fst F _ _)

theorem formLinear_apply {m : ℕ} (u v : X m) : formLinear u v = form u v := rfl

theorem dot_single {m : ℕ} (u : W m) (i : Fin m) :
    dotProduct u (Pi.single i 1) = u i := by
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [Pi.single_apply, h, Ne.symm h]
  · simp

private theorem basis_eval {m : ℕ} (l : W m →ₗ[F] F) (x : W m) :
    l x = dotProduct (fun i => l (Pi.single i 1)) x := by
  have h : (∑ i : Fin m, x i • Pi.single i (1 : F)) = x := by
    calc
      _ = ∑ i : Fin m, Pi.single i (x i) := by
        apply Finset.sum_congr rfl
        intro i _
        funext j
        by_cases h : j = i <;> simp [h]
      _ = x := LinearMap.sum_single_apply (fun _ : Fin m => F) x
  conv_lhs => rw [← h]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem probe_repr {m : ℕ} (l : X m →ₗ[F] F) : ∃ u : X m, ∀ x, l x = form u x := by
  let l₁ := l.comp (LinearMap.inl F (W m) (W m))
  let l₂ := l.comp (LinearMap.inr F (W m) (W m))
  refine ⟨(fun i => l₂ (Pi.single i 1), fun i => l₁ (Pi.single i 1)), fun x => ?_⟩
  have hsum : (x.1, 0) + (0, x.2) = x := by ext <;> simp
  calc
    l x = l (x.1, 0) + l (0, x.2) := by rw [← map_add, hsum]
    _ = l₁ x.1 + l₂ x.2 := rfl
    _ = _ := by rw [basis_eval l₁, basis_eval l₂]; exact add_comm _ _

theorem sum_sign_linear {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
    (l : V →ₗ[F] F) (hl : l ≠ 0) : (∑ x, sign (l x)) = 0 := by
  have h : ∃ a : V, l a ≠ 0 := by
    by_contra! h
    exact hl (LinearMap.ext h)
  obtain ⟨a, ha⟩ := h
  have ha' : l a = 1 := (bit_cases _).resolve_left ha
  have hshift : (∑ x, sign (l (x+a))) = ∑ x, sign (l x) :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
  simp only [map_add, sign_add, ha', show sign 1 = -1 by rfl, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hshift
  linarith

theorem card_W (m : ℕ) : Fintype.card (W m) = 2^m := by
  simp [W, Fintype.card_fun, ZMod.card]

theorem card_X (m : ℕ) : Fintype.card (X m) = 4^m := by
  change Fintype.card (W m × W m) = _
  rw [Fintype.card_prod, card_W, ← mul_pow]
  rfl

private theorem sum_sign_dot {m : ℕ} (u : W m) :
    (∑ v : W m, sign (dotProduct u v)) = if u = 0 then (2:ℚ)^m else 0 := by
  by_cases h : u = 0
  · subst u
    simp [sign, card_W]
  · rw [if_neg h]
    change (∑ v : W m, sign (dotLinear u v)) = _
    apply sum_sign_linear (dotLinear u)
    intro hzero
    apply h
    funext i
    have he := LinearMap.congr_fun hzero (Pi.single i 1)
    change dotProduct u (Pi.single i 1) = 0 at he
    exact (dot_single u i).symm.trans he

theorem sum_quad (m : ℕ) : (∑ x : X m, sign (quad x)) = (2:ℚ)^m := by
  rw [Fintype.sum_prod_type]
  simp only [quad, sum_sign_dot, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_corr {m : ℕ} (x : X m) :
    (∑ u : X m, sign (quad u) * sign (form u x)) = (2:ℚ)^m * sign (quad x) := by
  have hpt (u : X m) : sign (quad u)*sign (form u x) = sign (quad (u+x))*sign (quad x) := by
    rw [quad_add, sign_add, sign_add]
    calc
      _ = (sign (quad u)*sign (form u x)) * (sign (quad x)*sign (quad x)) := by rw [sign_mul_self, mul_one]
      _ = _ := by ring
  simp_rw [hpt]
  rw [← Finset.sum_mul]
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight x) _ _ (fun _ => rfl)).trans (sum_quad m)

def average {V : Type} [Fintype V] (f : V → ℚ) : ℚ := (∑ x, f x)/(Fintype.card V : ℚ)

theorem mean_quad (m : ℕ) : average (fun x : X m => sign (quad x)) = 1/(2:ℚ)^m := by
  unfold average
  rw [sum_quad, card_X, Nat.cast_pow]
  norm_num
  have h : (4:ℚ)^m = ((2:ℚ)^m)^2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h]
  field_simp

theorem mean_corr {m : ℕ} (u : X m) :
    average (fun x => sign (quad x)*sign (form u x)) = sign (quad u)/(2:ℚ)^m := by
  unfold average
  simp_rw [form_symm u]
  rw [sum_corr, card_X, Nat.cast_pow]
  norm_num
  have h : (4:ℚ)^m = ((2:ℚ)^m)^2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h]
  field_simp

end Model471

namespace Normal471

abbrev F := ZMod 2
abbrev Word (n : ℕ) := Fin n → F
abbrev Pair (n : ℕ) := Word n × Word n

def form {n : ℕ} (x y : Pair n) : F := dotProduct x.1 y.2 + dotProduct x.2 y.1

private theorem bit_cases (b : F) : b=0 ∨ b=1 :=
  (show ∀ b : F, b=0 ∨ b=1 by decide +kernel) b

private theorem eq_of_add_zero {a b : F} (h : a+b=0) : a=b :=
  (show ∀ a b : F, a+b=0 → a=b by decide +kernel) a b h

private theorem symm_form {V : Type} [AddCommGroup V] [Module F V]
    (B : V →ₗ[F] V →ₗ[F] F) (hAlt : ∀ x, B x x=0) (x y : V) :
    B x y=B y x := by
  have h := hAlt (x+y)
  rw [LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right x x y, LinearMap.BilinForm.add_right y x y,
    hAlt x, hAlt y, zero_add, add_zero] at h
  exact eq_of_add_zero h

private theorem split {V : Type} [AddCommGroup V] [Module F V]
    (B : V →ₗ[F] V →ₗ[F] F) (hAlt : ∀ x, B x x=0) (u v : V) (huv : B u v=1) :
    ∃ (W : Submodule F V) (E : V ≃ₗ[F] (F×F)×W), ∀ x y,
      B x y = (E x).1.1*(E y).1.2 + (E x).1.2*(E y).1.1 +
        B (E x).2.val (E y).2.val := by
  have hvu : B v u=1 := (symm_form B hAlt v u).trans huv
  let W := (B u).ker ⊓ (B v).ker
  have wu (w : W) : B u w.val=0 := w.property.1
  have wv (w : W) : B v w.val=0 := w.property.2
  let A : (F×F)×W →ₗ[F] V :=
    { toFun := fun p => p.1.1 • u + p.1.2 • v + p.2.val
      map_add' := by
        intro p q
        change (p.1.1+q.1.1) • u + (p.1.2+q.1.2) • v + (p.2.val+q.2.val) =
          _ + _
        simp only [add_smul]
        abel
      map_smul' := by
        intro a p
        change (a*p.1.1) • u + (a*p.1.2) • v + a • p.2.val =
          a • (p.1.1 • u + p.1.2 • v + p.2.val)
        simp [smul_add, mul_smul] }
  have first (p : (F×F)×W) : B v (A p) = p.1.1 := by
    change B v (p.1.1 • u + p.1.2 • v + p.2.val) = _
    simp [LinearMap.BilinForm.add_right, hvu, hAlt, wv]
  have second (p : (F×F)×W) : B u (A p) = p.1.2 := by
    change B u (p.1.1 • u + p.1.2 • v + p.2.val) = _
    simp [LinearMap.BilinForm.add_right, huv, hAlt, wu]
  have ha : Function.Bijective A := by
    constructor
    · intro p q hp
      have h1 : p.1.1=q.1.1 := by rw [← first p, hp, first]
      have h2 : p.1.2=q.1.2 := by rw [← second p, hp, second]
      refine Prod.ext (Prod.ext h1 h2) (Subtype.ext ?_)
      change p.1.1 • u + p.1.2 • v + p.2.val = q.1.1 • u + q.1.2 • v + q.2.val at hp
      rw [h1,h2] at hp
      exact add_left_cancel hp
    · intro x
      let p := (B v x, B u x)
      let z := p.1 • u + p.2 • v
      have hW : x-z ∈ W := by
        constructor
        · change B u (x-z)=0
          simp [z,p, map_sub, LinearMap.BilinForm.add_right, huv, hAlt]
        · change B v (x-z)=0
          simp [z,p, map_sub, LinearMap.BilinForm.add_right, hvu, hAlt]
      exact ⟨(p,⟨x-z,hW⟩), by change z+(x-z)=x; abel⟩
  let E := (LinearEquiv.ofBijective A ha).symm
  refine ⟨W,E,?_⟩
  have he (x : V) : A (E x) = x := (LinearEquiv.ofBijective A ha).apply_symm_apply x
  intro x y
  have move (p q : (F×F)×W) :
      B (A p) (A q) = p.1.1*q.1.2 + p.1.2*q.1.1 + B p.2.val q.2.val := by
    change B (p.1.1 • u + p.1.2 • v + p.2.val) (q.1.1 • u + q.1.2 • v + q.2.val) = _
    have uw (w : W) : B w.val u=0 := (symm_form B hAlt _ _).trans (wu w)
    have vw (w : W) : B w.val v=0 := (symm_form B hAlt _ _).trans (wv w)
    simp [LinearMap.BilinForm.add_right, hAlt, huv, hvu, wu, wv, uw, vw]
  simpa only [he] using move (E x) (E y)

private def grow (m r : ℕ) : ((F×F)×(Pair m × Word r)) ≃ₗ[F] (Pair (m+1) × Word r) :=
  { toFun := fun x => ((Fin.cons x.1.1 x.2.1.1,Fin.cons x.1.2 x.2.1.2), x.2.2)
    invFun := fun x => ((x.1.1 0,x.1.2 0),((fun i => x.1.1 i.succ,fun i => x.1.2 i.succ),x.2))
    left_inv := by
      intro x
      rcases x with ⟨⟨a,b⟩,⟨⟨u,v⟩,w⟩⟩
      simp
    right_inv := by
      intro x
      apply Prod.ext
      · apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp
      · rfl
    map_add' := by
      intro x y
      apply Prod.ext
      · apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp
      · rfl
    map_smul' := by
      intro a x
      apply Prod.ext
      · apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp
      · rfl }

private theorem grow_form (m r : ℕ) (x y : (F×F)×(Pair m × Word r)) :
    form (grow m r x).1 (grow m r y).1 =
      x.1.1*y.1.2 + x.1.2*y.1.1 + form x.2.1 y.2.1 := by
  change dotProduct (Fin.cons _ _) (Fin.cons _ _) + dotProduct (Fin.cons _ _) (Fin.cons _ _) = _
  simp only [form, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  abel

private theorem normalFinrank (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [Finite V]
      (B : V →ₗ[F] V →ₗ[F] F), (∀ x, B x x=0) → Module.finrank F V=n →
      ∃ m r, ∃ E : V ≃ₗ[F] (Pair m × Word r), ∀ x y, B x y = form (E x).1 (E y).1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro V _ _ _ B hAlt hn
    by_cases hz : ∀ x y, B x y=0
    · let E : V ≃ₗ[F] Word n := (Module.finBasis F V).equivFun.trans
        (LinearEquiv.funCongrLeft F F (finCongr hn).symm)
      let I : V ≃ₗ[F] Pair 0 × Word n :=
        { toFun := fun x => (0,E x)
          invFun := fun y => E.symm y.2
          left_inv := fun x => E.symm_apply_apply x
          right_inv := fun y => Prod.ext (Subsingleton.elim _ _) (E.apply_symm_apply _)
          map_add' := by intro x y; simp
          map_smul' := by intro a x; simp }
      exact ⟨0,n,I,fun x y => by simp [hz, I, form]⟩
    · push Not at hz
      obtain ⟨u,v,huv⟩ := hz
      obtain ⟨W,E,hE⟩ := split B hAlt u v ((bit_cases (B u v)).resolve_left huv)
      have hdim : Module.finrank F V = 2 + Module.finrank F W := by
        simpa [Module.finrank_prod] using E.finrank_eq
      have hr : Module.finrank F W < n := by omega
      let B' : W →ₗ[F] W →ₗ[F] F := LinearMap.BilinForm.restrict B W
      obtain ⟨m,r,E',hE'⟩ := ih _ hr W B' (fun x => hAlt x.val) rfl
      let Q := (LinearEquiv.refl F (F×F)).prodCongr E'
      refine ⟨m+1,r,(E.trans Q).trans (grow m r),?_⟩
      intro x y
      change B x y = form (grow m r (Q (E x))).1 (grow m r (Q (E y))).1
      rw [grow_form, hE x y]
      exact congrArg (fun z => (E x).1.1 * (E y).1.2 + (E x).1.2 * (E y).1.1 + z)
        (hE' (E x).2 (E y).2)

private theorem form_non_deg {m : ℕ} (x : Pair m) (hx : ∀ y, form x y=0) : x=0 := by
  apply Prod.ext <;> funext i
  · have h := hx (0,Pi.single i 1)
    simpa [form, dotProduct, Pi.single_apply, mul_ite] using h
  · have h := hx (Pi.single i 1,0)
    simpa [form, dotProduct, Pi.single_apply, mul_ite] using h

theorem normal (V : Type) [AddCommGroup V] [Module F V] [Finite V]
    (B : V →ₗ[F] V →ₗ[F] F) (hAlt : ∀ x, B x x=0) :
    ∃ m r, ∃ E : V ≃ₗ[F] (Pair m × Word r),
      (∀ x y, B x y = form (E x).1 (E y).1) ∧
      m = (Module.finrank F V - (Nat.card {u : V // ∀ v, B u v=0}).log2)/2 := by
  classical
  obtain ⟨m,r,E,he⟩ := normalFinrank _ V B hAlt rfl
  have eq (x : V) : (∀ y, B x y=0) ↔ (E x).1=0 := by
    constructor
    · intro h
      refine form_non_deg _ (fun y => ?_)
      simpa only [he, LinearEquiv.apply_symm_apply] using h (E.symm (y,0))
    · intro h y
      rw [he,h]
      simp [form]
  let R : {u : V // ∀ v, B u v=0} ≃ Word r :=
    { toFun := fun x => (E x.val).2
      invFun := fun y => ⟨E.symm (0,y),(eq _).mpr (by simp)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply E.injective
        simp only [LinearEquiv.apply_symm_apply]
        exact Prod.ext ((eq x.val).mp x.property).symm rfl
      right_inv := fun y => by simp }
  have hcard : Nat.card {u : V // ∀ v, B u v=0} = 2^r := by
    rw [Nat.card_congr R, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hdim : Module.finrank F V = 2*m+r := by
    have h := E.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at h
    omega
  refine ⟨m,r,E,he,?_⟩
  rw [hcard, Nat.log2_two_pow, hdim]
  omega

end Normal471

namespace Center471

open Model471

section Polar

variable {V : Type} [AddCommGroup V] [Module F V]

def polar (f : V → F) (u v : V) : F := f (u+v)+f u+f v+f 0

theorem polar_symm (f : V → F) (u v : V) : polar f u v = polar f v u := by
  unfold polar
  rw [add_comm u v]
  abel

theorem add_cancel_three (a b c : F) : a+b+c+a+b = c := by
  calc
    _ = (a+a)+(b+b)+c := by abel
    _ = _ := by rw [bit_add_self, bit_add_self, zero_add, zero_add]

private theorem bit_zero_iff : ∀ (a b : F), a+b=0 ↔ a=b := by decide +kernel

theorem polar_zero (f : V → F) (u : V) : polar f u 0 = 0 := by
  simp only [polar, add_zero]
  calc
    _ = (f u+f u)+(f 0+f 0) := by abel
    _ = _ := by rw [bit_add_self, bit_add_self, add_zero]

theorem vec_self (u : V) : u+u=0 := by
  rw [← two_smul F, show (2 : F) = 0 by decide, zero_smul]

theorem polar_self (f : V → F) (u : V) : polar f u u = 0 := by
  rw [polar, vec_self]
  calc
    _ = (f u+f u)+(f 0+f 0) := by abel
    _ = _ := by rw [bit_add_self, bit_add_self, add_zero]

private theorem polar_add_right (f : V → F)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = polar f u v)
    (u v w : V) : polar f u (v+w) = polar f u v + polar f u w := by
  have he := h v u w
  rw [add_comm v u, add_assoc u v w] at he
  rw [← he]
  unfold polar
  calc
    _ = (f (u+(v+w))+f u+f (v+w)+f 0)+
      (f (u+v)+f (u+v))+(f v+f v) := by rw [bit_add_self, bit_add_self, add_zero, add_zero]
    _ = _ := by abel

def bilin (f : V → F)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = polar f u v) :
    V →ₗ[F] V →ₗ[F] F where
  toFun u :=
    { toFun := polar f u
      map_add' := polar_add_right f h u
      map_smul' := by
        intro a v
        rcases bit_cases a with rfl | rfl
        · simp [polar_zero]
        · simp }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change polar f (u+v) w = polar f u w+polar f v w
    rw [polar_symm f (u+v), polar_add_right f h, polar_symm f w u, polar_symm f w v]
  map_smul' := by
    intro a u
    apply LinearMap.ext
    intro v
    change polar f (a • u) v = a * polar f u v
    rcases bit_cases a with rfl | rfl
    · simp [polar_symm f 0 v, polar_zero]
    · simp

theorem bilin_apply (f : V → F)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = polar f u v) (u v : V) :
    bilin f h u v = polar f u v := rfl

def linearPart (g : V → F) (hg : ∀ u v, polar g u v = 0) : V →ₗ[F] F where
  toFun u := g u + g 0
  map_add' u v := by
    have he : g (u+v) = g u+g v+g 0 := (bit_zero_iff _ _).mp (by
      simpa only [polar, add_assoc] using hg u v)
    rw [he]
    abel
  map_smul' := by
    intro a u
    rcases bit_cases a with rfl | rfl
    · simp [bit_add_self]
    · simp

theorem polar_compAdd (f g : V → F) (u v : V) :
    polar (fun x => f x+g x) u v = polar f u v+polar g u v := by
  simp only [polar]
  abel

end Polar

theorem polar_quad {m r : ℕ} (u v : X m × W r) :
    polar (fun x : X m × W r => quad x.1) u v = form u.1 v.1 := by
  simp only [polar, Prod.fst_add, quad_add, show quad (0 : X m) = 0 by simp [quad],
    Prod.fst_zero, add_zero]
  apply add_cancel_three

theorem center {n m r : ℕ} (f : W n → F)
    (e : W n ≃ₗ[F] (X m × W r))
    (hf : ∀ u v, polar f u v = form (e u).1 (e v).1)
    (hunb : Nat.card {x : W n // f x=0} ≠ Nat.card {x : W n // f x=1}) :
    ∃ (t : X m) (c : F), ∀ x : W n, f x = quad ((e x).1+t)+c := by
  let g (y : X m × W r) : F := f (e.symm y)
  let Q (y : X m × W r) : F := quad y.1
  let d (y : X m × W r) : F := g y+Q y
  have hg (u v : X m × W r) : polar g u v = form u.1 v.1 := by
    simpa only [polar, g, map_add, map_zero, LinearEquiv.apply_symm_apply] using hf (e.symm u) (e.symm v)
  have hd (u v : X m × W r) : polar d u v = 0 := by
    change polar (fun y => g y+Q y) u v = 0
    rw [polar_compAdd, hg, show polar Q u v = _ from polar_quad u v, bit_add_self]
  let L := linearPart d hd
  have eqG (y : X m × W r) : g y = Q y + L y + g 0 := by
    change g y = Q y + (g y+Q y+(g 0+Q 0)) + g 0
    rw [show Q 0 = 0 by simp [Q, quad], add_zero]
    calc
      _ = g y + (Q y+Q y)+(g 0+g 0) := by rw [bit_add_self, bit_add_self, add_zero, add_zero]
      _ = _ := by abel
  have radical (z : W r) : L (0,z) = 0 := by
    by_contra hz
    have hL := (bit_cases (L (0,z))).resolve_left hz
    have shift (y : X m × W r) : g (y+(0,z)) = g y+1 := by
      rw [eqG (y+(0,z)), eqG y, map_add, hL]
      have hQ : Q (y+(0,z)) = Q y := by simp [Q]
      rw [hQ]
      abel
    have hcongr (a : F) : Nat.card {x : W n // f x=a} = Nat.card {y : X m × W r // g y=a} :=
      Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by simp [g])
    have hcard : Nat.card {y : X m × W r // g y=0} = Nat.card {y : X m × W r // g y=1} := by
      apply Nat.card_congr ((Equiv.addRight (0,z)).subtypeEquiv _)
      intro y
      change g y=0 ↔ g (y+(0,z))=1
      rw [shift]
      simpa only [zero_add] using (add_right_cancel_iff (a := (1:F)) (b := g y) (c := 0)).symm
    exact hunb ((hcongr 0).trans (hcard.trans (hcongr 1).symm))
  let l := L.comp (LinearMap.inl F (X m) (W r))
  obtain ⟨t, ht⟩ := probe_repr l
  have Lval (y : X m × W r) : L y = form y.1 t := by
    have hy : (y.1,0)+(0,y.2) = y := by ext <;> simp
    rw [← hy, map_add, radical, add_zero]
    change l y.1 = _
    rw [ht, form_symm]
    simp
  refine ⟨t, g 0 + quad t, fun x => ?_⟩
  have hx := eqG (e x)
  rw [Lval] at hx
  simp only [g, LinearEquiv.symm_apply_apply] at hx
  rw [hx, quad_add]
  change quad (e x).1 + form (e x).1 t + g 0 =
    quad (e x).1 + quad t + form (e x).1 t + (g 0 + quad t)
  calc
    _ = (quad (e x).1 + form (e x).1 t + g 0) + (quad t+quad t) := by rw [bit_add_self, add_zero]
    _ = _ := by abel

end Center471

namespace Lower471

abbrev F := ZMod 2

def sign (b : F) : ℚ := if b = 0 then 1 else -1

def average {V : Type} [Fintype V] (g : V → ℚ) : ℚ :=
  (∑ x : V, g x) / (Fintype.card V : ℚ)

theorem average_one {V : Type} [Fintype V] [Nonempty V] :
    average (fun _ : V => 1) = 1 := by
  have hc : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, nsmul_eq_mul, hc]

theorem average_sub {V : Type} [Fintype V] (g h : V → ℚ) :
    average (fun x => g x - h x) = average g - average h := by
  simp [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul_left {V : Type} [Fintype V] (c : ℚ) (g : V → ℚ) :
    average (fun x => c * g x) = c * average g := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem average_sum {I V : Type} [Fintype I] [Fintype V] (g : I → V → ℚ) :
    average (fun x => ∑ i : I, g i x) = ∑ i : I, average (g i) := by
  unfold average
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem average_mono {V : Type} [Fintype V] (g h : V → ℚ) (hgh : ∀ x, g x ≤ h x) :
    average g ≤ average h := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x) (by positivity)

private theorem sign_sq : ∀ b : F, sign b * sign b = 1 := by decide +kernel

private theorem sign_zero : sign (0 : F) = 1 := by decide +kernel

private theorem sign_bounds : ∀ b : F, -1 ≤ sign b ∧ sign b ≤ 1 := by decide +kernel

def prior {V : Type} (f : V → F) (μ : ℚ) (x : V) : ℚ := 1 - μ * sign (f x)

theorem prior_pos {V : Type} (f : V → F) (μ : ℚ) (h₀ : 0 ≤ μ) (h₁ : μ < 1) (x : V) :
    0 < prior f μ x := by
  have h : μ * sign (f x) ≤ μ := by simpa using mul_le_mul_of_nonneg_left (sign_bounds (f x)).2 h₀
  unfold prior
  linarith

theorem average_prior {V : Type} [Fintype V] [Nonempty V] (f : V → F) (μ : ℚ)
    (h : average (fun x => sign (f x)) = μ) : average (prior f μ) = 1-μ*μ := by
  unfold prior
  rw [average_sub, average_mul_left, average_one, h]

def correlation {V : Type} [Fintype V] (f g : V → F) (μ : ℚ) : ℚ :=
  average (fun x => prior f μ x * sign (f x) * sign (g x))

theorem correlation_eq {V : Type} [Fintype V] (f g : V → F) (μ : ℚ) :
    correlation f g μ = average (fun x => sign (f x) * sign (g x)) -
      μ * average (fun x => sign (g x)) := by
  unfold correlation
  rw [← average_mul_left, ← average_sub]
  congr 1
  funext x
  unfold prior
  calc
    _ = sign (f x) * sign (g x) - μ * (sign (f x) * sign (f x)) * sign (g x) := by ring
    _ = _ := by rw [sign_sq, mul_one]

private abbrev Bits := Fin 2 → F

private def char (s y : Bits) : ℚ := sign (dotProduct s y)

private def coeff (g : Bits → F) (s : Bits) : ℚ :=
  (∑ y : Bits, sign (g y) * char s y) / 4

private theorem finite_expansion : ∀ (g : Bits → F) (y : Bits),
    sign (g y) = ∑ s : Bits, coeff g s * char s y := by decide +kernel

private theorem finite_mass : ∀ g : Bits → F,
    (∑ s : Bits, if s = 0 then 0 else |coeff g s|) ≤ (3:ℚ)/2 := by decide +kernel

private def dotLin (s : Bits) : Bits →ₗ[F] F where
  toFun := dotProduct s
  map_add' x y := dotProduct_add _ _ _
  map_smul' c x := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem per_probe {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
    (f : V → F) (μ : ℚ) (hμ : 0 ≤ μ) (c0 : average (fun x => sign (f x)) = μ)
    (cN : ∀ a : V →ₗ[F] F, a ≠ 0 → average (fun x => sign (a x)) = 0 ∧
      |average (fun x => sign (f x) * sign (a x))| ≤ μ)
    (A : V →ₗ[F] (Fin 2 → F)) (out : (Fin 2 → F) → F) :
    correlation f (fun x => out (A x)) μ ≤ 3*μ/2 := by
  classical
  let L (s : Bits) : V →ₗ[F] F := (dotLin s).comp A
  have c_zero (s : Bits) (h : L s = 0) : correlation f (L s) μ = 0 := by
    rw [h, correlation_eq]
    simp only [LinearMap.zero_apply, sign_zero, mul_one, c0, average_one, sub_self]
  have c_small (s : Bits) (h : L s ≠ 0) : |correlation f (L s) μ| ≤ μ := by
    obtain ⟨hz, hb⟩ := cN (L s) h
    simpa only [correlation_eq, hz, mul_zero, sub_zero] using hb
  have exp : correlation f (fun x => out (A x)) μ =
      ∑ s : Bits, coeff out s * correlation f (L s) μ := by
    have hx (x : V) : prior f μ x * sign (f x) * sign (out (A x)) =
        ∑ s : Bits, coeff out s * (prior f μ x * sign (f x) * sign (L s x)) := by
      rw [finite_expansion out (A x), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change _ * (coeff out s * sign (L s x)) = _
      ring
    unfold correlation
    simp_rw [hx]
    rw [average_sum]
    simp_rw [average_mul_left]
  rw [exp]
  calc
    _ ≤ ∑ s : Bits, if s = 0 then 0 else μ * |coeff out s| := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = 0
      · subst s
        have h0 : L 0 = 0 := by
          ext x
          change dotProduct (0 : Bits) (A x) = 0
          exact zero_dotProduct _
        simp [c_zero 0 h0]
      · rw [ite_eq_right hs]
        by_cases hz : L s = 0
        · rw [c_zero s hz, mul_zero]
          positivity
        · calc
            _ ≤ |coeff out s * correlation f (L s) μ| := le_abs_self _
            _ = |coeff out s| * |correlation f (L s) μ| := abs_mul _ _
            _ ≤ _ := by rw [mul_comm μ]; exact mul_le_mul_of_nonneg_left (c_small s hz) (abs_nonneg _)
    _ = μ * (∑ s : Bits, if s = 0 then 0 else |coeff out s|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : s = 0 <;> simp [h]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (finite_mass out) hμ]

def blocks (m : ℕ) : ℕ := (4^m-1)/3

def mu (m : ℕ) : ℚ := 1/(2:ℚ)^m

private def peak (m : ℕ) : ℚ := (2:ℚ)^(m-1)/(blocks m : ℚ)

private theorem blocks_succ (m : ℕ) : blocks (m+1) = blocks m + 4^m := by
  have h : 1 ≤ 4^m := Nat.one_le_pow _ _ (by decide)
  have he : 4^m*4-1 = (4^m-1) + 3*4^m := by omega
  unfold blocks
  rw [pow_succ, he, Nat.add_mul_div_left _ _ (by decide)]

private theorem blocks_eq (m : ℕ) : 3*blocks m+1 = 4^m := by
  induction m with
  | zero => decide +kernel
  | succ m ih =>
    rw [blocks_succ, pow_succ, Nat.mul_add]
    omega

private theorem blocks_odd (m : ℕ) (hm : 0 < m) : Odd (blocks m) := by
  have hz := (show Even (4 : ℕ) by decide).pow_of_ne_zero hm.ne'
  have h := blocks_eq m
  rw [Nat.even_iff] at hz
  exact Nat.odd_iff.mpr (by omega)

private theorem numerator_coprime (m : ℕ) (hm : 2 ≤ m) :
    (blocks m + 2^(m-1)).Coprime (2*blocks m) := by
  have ho := blocks_odd m (by omega)
  have he := (show Even (2 : ℕ) by decide).pow_of_ne_zero (show m-1 ≠ 0 by omega)
  have hn : Odd (blocks m + 2^(m-1)) := ho.add_even he
  have hb : (2^(m-1)).Coprime (blocks m) := ho.coprime_two_left.pow_left _
  have hc : (blocks m + 2^(m-1)).Coprime (blocks m) := by
    simpa [Nat.Coprime, Nat.add_comm (blocks m)] using hb
  exact hn.coprime_two_right.mul_right hc

private theorem peak_normalization (m : ℕ) (hm : 0 < m) :
    peak m * (1-mu m*mu m) = 3*mu m/2 := by
  let u : ℚ := 2^m
  let p : ℚ := 2^(m-1)
  have hu : 1 < u := one_lt_pow₀ (by norm_num) hm.ne'
  have hu0 : u ≠ 0 := by linarith
  have hp : u = 2*p := by
    dsimp [u, p]
    conv_lhs => rw [show m = m-1+1 by omega, pow_succ]
    ring
  have h₁ : (4:ℚ)^m = u^2 := by
    unfold u
    rw [pow_two, ← mul_pow]
    norm_num
  have h₂ : 3 * (blocks m : ℚ) + 1 = (4:ℚ)^m := by exact_mod_cast blocks_eq m
  have hM : 0 < (blocks m : ℚ) := by
    rw [h₁] at h₂
    nlinarith
  have hform : u^2-1 = 3 * (blocks m : ℚ) := by linarith
  change p/(blocks m : ℚ) * (1-1/u*(1/u)) = 3*(1/u)/2
  calc
    _ = p/(blocks m : ℚ) * ((u^2-1)/u^2) := by field_simp [hu0]
    _ = p/(blocks m : ℚ) * (3*(blocks m : ℚ)/u^2) := by rw [hform]
    _ = _ := by field_simp [hu0, hM.ne']; nlinarith [congrArg (fun x : ℚ => u*x) hp]

private theorem sign_agree : ∀ a b : F, sign a * sign b = (if b = a then (2 : ℚ) else 0) - 1 := by
  decide +kernel

private theorem correlations_count {V : Type} (f : V → F) (g : Fin T → V → F) (x : V) :
    (∑ i : Fin T, sign (f x) * sign (g i x)) =
      2*(Nat.card {i : Fin T // g i x = f x} : ℚ) - T := by
  simp_rw [sign_agree]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [nsmul_eq_mul, mul_comm]

private theorem vanishes_of_average {V : Type} [Fintype V] [Nonempty V] (g : V → ℚ)
    (hg : ∀ x, 0 ≤ g x) (ha : average g ≤ 0) : ∀ x, g x = 0 := by
  have hc : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos
  have hs : (∑ x, g x) ≤ 0 := by
    simpa only [zero_mul] using (div_le_iff₀ hc).mp ha
  intro x
  have hx : g x ≤ ∑ y, g y := Finset.single_le_sum (fun i _ => hg i) (Finset.mem_univ x)
  exact (hx.trans hs).antisymm (hg x)

theorem necessity {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
    (m : ℕ) (hm : 2 ≤ m) (f : V → F) (c0 : average (fun x => sign (f x)) = mu m)
    (cN : ∀ a : V →ₗ[F] F, a ≠ 0 → average (fun x => sign (a x)) = 0 ∧
      |average (fun x => sign (f x) * sign (a x))| ≤ mu m)
    (T : ℕ) (A : Fin T → V →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F)
    (h : ∀ x, (blocks m+2^(m-1))*T ≤ (2*blocks m)*Nat.card {i : Fin T // out i (A i x)=f x}) :
    2*blocks m ∣ T := by
  classical
  let hit (x : V) := Nat.card {i : Fin T // out i (A i x)=f x}
  let corr (i : Fin T) (x : V) := sign (f x)*sign (out i (A i x))
  let w := prior f (mu m)
  have hμ : 0 ≤ mu m := by unfold mu; positivity
  have hμ₁ : mu m < 1 := by
    unfold mu
    exact (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hM : 0 < (blocks m : ℚ) := by
    have hn : 0 < blocks m := by
      have he := Nat.odd_iff.mp (blocks_odd m (by omega))
      omega
    exact_mod_cast hn
  have hcnt (x : V) : (∑ i, corr i x) = 2*(hit x : ℚ)-T :=
    correlations_count f (fun i y => out i (A i y)) x
  have hpoint (x : V) : (T : ℚ)*peak m ≤ ∑ i, corr i x := by
    have hx : ((blocks m : ℚ)+(2:ℚ)^(m-1))*T ≤ 2*(blocks m : ℚ)*(hit x : ℚ) := by
      exact_mod_cast h x
    rw [hcnt, peak, ← mul_div_assoc, div_le_iff₀ hM]
    nlinarith
  have upper : average (fun x => w x * ∑ i, corr i x) ≤ (T : ℚ)*(3*mu m/2) := by
    simp_rw [Finset.mul_sum, average_sum]
    calc
      _ ≤ ∑ _ : Fin T, 3*mu m/2 := Finset.sum_le_sum fun i _ => by
        simpa only [w, corr, correlation, mul_assoc] using per_probe f (mu m) hμ c0 cN (A i) (out i)
      _ = _ := by simp [nsmul_eq_mul]
  let excess (x : V) := w x * ((∑ i, corr i x)-(T : ℚ)*peak m)
  have nonneg (x : V) : 0 ≤ excess x :=
    mul_nonneg (prior_pos f (mu m) hμ hμ₁ x).le (sub_nonneg.mpr (hpoint x))
  have mean_excess : average excess ≤ 0 := by
    unfold excess
    simp_rw [mul_sub]
    rw [average_sub]
    have hshift : average (fun x => w x * (↑T * peak m)) = (T : ℚ) * (3*mu m/2) := by
      simp_rw [mul_comm (w _), average_mul_left, w, average_prior f (mu m) c0,
        mul_assoc, peak_normalization m (by omega)]
    rw [hshift]
    linarith
  have hz := vanishes_of_average excess nonneg mean_excess (0 : V)
  have hzero : (∑ i, corr i (0 : V)) - (T : ℚ)*peak m = 0 :=
    (mul_eq_zero.mp hz).resolve_left (prior_pos f (mu m) hμ hμ₁ _).ne'
  rw [hcnt, peak, ← mul_div_assoc] at hzero
  have hEq := (eq_div_iff hM.ne').mp (sub_eq_zero.mp hzero)
  have hInt : (blocks m + 2^(m-1))*T = (2*blocks m)*hit (0 : V) := by
    exact_mod_cast (show ((blocks m : ℚ)+(2:ℚ)^(m-1))*T = 2*(blocks m : ℚ)*(hit (0 : V) : ℚ) by nlinarith)
  exact (numerator_coprime m hm).symm.dvd_of_dvd_mul_left ⟨hit (0 : V), hInt⟩

end Lower471

namespace Transport471

open Model471

def possible {V : Type} [AddCommMonoid V] [Module F V]
    (f : V → F) (T P D : ℕ) : Prop :=
  ∃ (A : Fin T → V →ₗ[F] W 2) (out : Fin T → W 2 → F), ∀ x,
    P ≤ D * Nat.card {i : Fin T // out i (A i x) = f x}

theorem transport {n m r T P D : ℕ} (f : W n → F)
    (E : W n ≃ₗ[F] (X m × W r)) (t : X m) (c : F)
    (hf : ∀ x, f x = quad ((E x).1+t)+c) :
    possible f T P D ↔ possible (@quad m) T P D := by
  constructor
  · rintro ⟨A,out,h⟩
    let S : X m →ₗ[F] W n :=
      E.symm.toLinearMap.comp (LinearMap.inl F (X m) (W r))
    have hs (y : X m) : (E (S y)).1 = y := by
      change (E (E.symm (y,0))).1 = y
      rw [E.apply_symm_apply]
    let As (i : Fin T) := (A i).comp S
    let os (i : Fin T) (z : W 2) := out i (z - As i t) - c
    refine ⟨As,os,fun y => ?_⟩
    have hval : f (S (y-t)) = quad y+c := by
      rw [hf, hs, sub_add_cancel]
    have hcard : Nat.card {i : Fin T // os i (As i y) = quad y} =
        Nat.card {i : Fin T // out i (A i (S (y-t))) = f (S (y-t))} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      change out i (As i y - As i t) - c = quad y ↔ out i (As i (y-t)) = f (S (y-t))
      rw [map_sub, hval, sub_eq_iff_eq_add]
    rw [hcard]
    exact h (S (y-t))
  · rintro ⟨A,out,h⟩
    let Q : W n →ₗ[F] X m :=
      (LinearMap.fst F (X m) (W r)).comp E.toLinearMap
    let As (i : Fin T) := (A i).comp Q
    let os (i : Fin T) (z : W 2) := out i (z + A i t) + c
    refine ⟨As,os,fun x => ?_⟩
    have hcard : Nat.card {i : Fin T // os i (As i x) = f x} =
        Nat.card {i : Fin T // out i (A i ((E x).1+t)) = quad ((E x).1+t)} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      change out i (A i (E x).1 + A i t)+c = f x ↔
        out i (A i ((E x).1+t)) = quad ((E x).1+t)
      rw [map_add, hf, add_right_cancel_iff]
    rw [hcard]
    exact h ((E x).1+t)

end Transport471

namespace Upper471

open Plane470
open scoped BigOperators

def q {m : ℕ} (x : X m) : F := dotProduct x.1 x.2

def sign (a : F) : ℚ := if a = 0 then 1 else -1

private theorem q_polar {m : ℕ} (u v : X m) :
    q (u+v) = q u+q v+form u v := by
  simp only [q, form, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm v.1 u.2]
  abel

private theorem polar_sign : ∀ a b c : F, sign a*sign b*sign (a+b+c) = sign c := by
  decide +kernel

private theorem bit_sign : ∀ a : F, -sign a =
    (if a=1 then (1:ℚ) else 0) - (if a=0 then 1 else 0) := by decide +kernel

private theorem match_sign : ∀ a b : F, sign a*sign b =
    (if a=b then (2:ℚ) else 0)-1 := by decide +kernel

private theorem sign_square : ∀ a : F, sign a * sign a = 1 := by decide +kernel

private def value (a b c p r : F) : ℚ :=
  (-sign a*sign b*sign c + sign a*sign p + sign b*sign r + sign c*sign (p+r))/2

private def pick (a b c p r : F) : F := if value a b c p r = 1 then 0 else 1

private theorem pick_sign : ∀ a b c p r : F, sign (pick a b c p r) = value a b c p r := by
  decide +kernel

private def measure {m : ℕ} (u : X m) : X m →ₗ[F] F where
  toFun := form u
  map_add' := form_add_right u
  map_smul' := by
    intro a x
    simp [form, dotProduct_smul, smul_eq_mul, mul_add]

private def queries {m : ℕ} (u v : X m) : X m →ₗ[F] (Fin 2 → F) :=
  LinearMap.pi (fun j : Fin 2 => if j=0 then measure u else measure v)

private def decoder {m : ℕ} (u v : X m) (p : Fin 2 → F) : F :=
  pick (q u) (q v) (q (u+v)) (p 0) (p 1)

private theorem decoder_sign {m : ℕ} (u v x : X m) :
    sign (decoder u v (queries u v x)) =
      (-sign (form u v) + (sign (q u)*sign (form u x) + sign (q v)*sign (form v x) +
        sign (q (u+v))*sign (form (u+v) x)))/2 := by
  have hc : sign (q u)*sign (q v)*sign (q (u+v)) = sign (form u v) := by
    rw [q_polar, polar_sign]
  have hl : queries u v x 0 = form u x := by simp [queries, measure]
  have hr : queries u v x 1 = form v x := by simp [queries, measure]
  simp only [decoder, hl, hr, pick_sign, value, form_add_left]
  rw [neg_mul, neg_mul, hc]
  ring

private theorem count_sum {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (c : ℚ) :
    (∑ i, if P i then c else 0) = (Nat.card {i // P i}:ℚ)*c := by
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem constant_total {m : ℕ} (u v : Fin (Counts470.size m) → X m) (good : Good u v) :
    (∑ i, -sign (form (u i) (v i))) = 2 := by
  simp_rw [bit_sign]
  rw [Finset.sum_sub_distrib, count_sum, count_sum, mul_one, mul_one]
  have h := good.2.2
  rw [h, Nat.cast_add]
  ring

private theorem sum_three {m : ℕ} {u v : X m} (hu : u ≠ 0) (hv : v ≠ 0) (hd : u ≠ v)
    (f : X m → ℚ) :
    f u + f v + f (u+v) = ∑ a : X m, if a=u ∨ a=v ∨ a=u+v then f a else 0 := by
  classical
  have hu' : u ≠ u+v := by
    intro e
    exact hv (add_left_cancel (e.symm.trans (add_zero u).symm))
  have hv' : v ≠ u+v := by
    intro e
    exact hu (add_right_cancel (e.symm.trans (zero_add v).symm))
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter (fun a : X m => a=u ∨ a=v ∨ a=u+v)) = {u,v,u+v} := by
    ext a; simp
  rw [hs, Finset.sum_insert (by simp [hd, hu']), Finset.sum_pair hv']
  ring

private theorem nonconstant_total {m : ℕ} (u v : Fin (Counts470.size m) → X m)
    (good : Good u v) (f : X m → ℚ) (hf : f 0 = 1) :
    (∑ i, (f (u i)+f (v i)+f (u i+v i))) = 2*(∑ a, f a)-2 := by
  classical
  have hcard (a : X m) : Nat.card {i : Fin (Counts470.size m) // a=u i ∨ a=v i ∨ a=u i+v i} =
      if a=0 then 0 else 2 := by
    by_cases ha : a=0
    · rw [ite_eq_left ha, ha]
      apply Counts470.none
      intro i h
      obtain ⟨hu,hv,hd⟩ := good.1 i
      rcases h with h | h | h
      · exact hu h.symm
      · exact hv h.symm
      · apply hd
        apply add_left_cancel (a := u i)
        rw [Plane470.pair_double, ← h]
    · rw [ite_eq_right ha]
      exact good.2.1 a ha
  calc
    _ = ∑ i, ∑ a : X m, if a=u i ∨ a=v i ∨ a=u i+v i then f a else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_three (good.1 i).1 (good.1 i).2.1 (good.1 i).2.2 f
    _ = ∑ a : X m, ∑ i, if a=u i ∨ a=v i ∨ a=u i+v i then f a else 0 := Finset.sum_comm
    _ = ∑ a : X m, (2*f a - (if a=0 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [count_sum, hcard]
      by_cases ha : a=0
      · simp [ha, hf]
      · simp [ha]
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']; simp

private theorem decoder_total {m : ℕ} (u v : Fin (Counts470.size m) → X m)
    (good : Good u v) (x : X m)
    (corr : (∑ a : X m, sign (q a)*sign (form a x)) = (2:ℚ)^m*sign (q x)) :
    (∑ i, sign (decoder (u i) (v i) (queries (u i) (v i) x))) = (2:ℚ)^m*sign (q x) := by
  let f (a : X m) := sign (q a)*sign (form a x)
  have hf : f 0 = 1 := by simp [f, q, form, sign]
  simp_rw [decoder_sign]
  change (∑ i, (-sign (form (u i) (v i)) + (f (u i)+f (v i)+f (u i+v i)))/2) = _
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_add_distrib, constant_total u v good,
    nonconstant_total u v good f hf]
  change (∑ a, f a) = _ at corr
  rw [corr]
  ring

private theorem hit_exact {m : ℕ} (hm : 0 < m) (u v : Fin (Counts470.size m) → X m)
    (good : Good u v) (x : X m)
    (corr : (∑ a : X m, sign (q a)*sign (form a x)) = (2:ℚ)^m*sign (q x)) :
    Nat.card {i : Fin (Counts470.size m) // decoder (u i) (v i) (queries (u i) (v i) x) = q x} =
      (4^m-1)/3+2^(m-1) := by
  classical
  let N := Counts470.size m
  let H (i : Fin N) := decoder (u i) (v i) (queries (u i) (v i) x)
  let A := Nat.card {i : Fin N // H i = q x}
  have hs : (∑ i : Fin N, sign (H i)*sign (q x)) = (2:ℚ)^m := by
    rw [← Finset.sum_mul]
    change (∑ i, sign (decoder (u i) (v i) (queries (u i) (v i) x)))*sign (q x) = _
    rw [decoder_total u v good x corr, mul_assoc, sign_square, mul_one]
  simp_rw [match_sign] at hs
  rw [Finset.sum_sub_distrib, count_sum] at hs
  have hN : (∑ _i : Fin N, (1:ℚ)) = (N:ℚ) := by simp
  rw [hN] at hs
  change (A:ℚ)*2 - (N:ℚ) = (2:ℚ)^m at hs
  have hc : A*2 = N + 2^m := by exact_mod_cast (show (A:ℚ)*2 = (N:ℚ)+(2:ℚ)^m by linarith)
  have hp : (2:ℕ)^m=2*2^(m-1) := by obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm); simp [pow_succ, mul_comm]
  change A = _
  simp only [N, Counts470.size, hp] at hc
  omega

private theorem repeats {n k : ℕ} (P : Fin n → Prop) :
    Nat.card {i : Fin (n*k) // P (finProdFinEquiv.symm i).1} = Nat.card {i // P i} * k := by
  let e : {i : Fin (n*k) // P (finProdFinEquiv.symm i).1} ≃ ({i : Fin n // P i} × Fin k) :=
    { toFun := fun i => (⟨(finProdFinEquiv.symm i.val).1,i.property⟩,(finProdFinEquiv.symm i.val).2)
      invFun := fun i => ⟨finProdFinEquiv (i.1.val,i.2), by simpa using i.1.property⟩
      left_inv := by intro i; apply Subtype.ext; exact finProdFinEquiv.apply_symm_apply i.val
      right_inv := by intro i; apply Prod.ext <;> simp }
  exact (Nat.card_congr e).trans (by rw [Nat.card_prod, Nat.card_fin])

theorem upper (m T : ℕ) (hm : 2 ≤ m) (hT : Counts470.size m ∣ T)
    (sum_corr : ∀ x : X m, (∑ a : X m, sign (q a)*sign (form a x)) = (2:ℚ)^m*sign (q x)) :
    ∃ (A : Fin T → X m →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F),
      ∀ x, ((4^m-1)/3+2^(m-1))*T ≤ Counts470.size m*Nat.card {i : Fin T // out i (A i x)=q x} := by
  have hm' : 0 < m := by omega
  obtain ⟨u,v,hgood⟩ := Plane470.realize m hm'
  obtain ⟨k,rfl⟩ := hT
  refine ⟨fun i => queries (u (finProdFinEquiv.symm i).1) (v (finProdFinEquiv.symm i).1),
    fun i => decoder (u (finProdFinEquiv.symm i).1) (v (finProdFinEquiv.symm i).1), ?_⟩
  intro x
  let P (i : Fin (Counts470.size m)) : Prop := decoder (u i) (v i) (queries (u i) (v i) x) = q x
  change _ ≤ Counts470.size m*Nat.card {i : Fin (Counts470.size m*k) // P (finProdFinEquiv.symm i).1}
  have hH : Nat.card {i // P i} = (4^m-1)/3+2^(m-1) := hit_exact hm' u v hgood x (sum_corr x)
  rw [repeats P, hH]
  exact le_of_eq (by ac_rfl)

end Upper471

end PEqualNP.Outside.L_pcx_471

open PEqualNP.Outside.L_pcx_471

theorem PEqualNP.Outside.L_pcx_471 :
    ∀ (n : ℕ),
      let F := ZMod 2
      let X := Fin n → F
      ∀ f : X → F,
        let B := fun u v : X => f (u+v)+f u+f v+f 0
        (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
        let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
        Nat.card {x : X // f x=0} ≠ Nat.card {x : X // f x=1} →
        2 ≤ m →
        let M := (4^m-1)/3
        ∀ T : ℕ, 0 < T →
          ((∃ (A : Fin T → X →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F),
             ∀ x : X, (M+2^(m-1))*T ≤
               (2*M)*Nat.card {i : Fin T // out i (A i x) = f x}) ↔ 2*M ∣ T) := by
  intro n
  dsimp only
  intro f hquad hunb hm T _hT
  let B := Center471.bilin f hquad
  obtain ⟨m, r, e, he, hrank⟩ :=
    Normal471.normal (Model471.W n) B (Center471.polar_self f)
  let rankHalf := (n-(Nat.card {u : Model471.W n // ∀ v, Center471.polar f u v=0}).log2)/2
  have hdim : Module.finrank (ZMod 2) (Model471.W n) = n := by
    simp [Model471.W, Module.finrank_pi_fintype, Module.finrank_self]
  rw [hdim] at hrank
  have hr : m = rankHalf := hrank
  have hm' : 2 ≤ m := by rw [hr]; exact hm
  obtain ⟨t, c, hf⟩ := Center471.center f e he hunb
  change (Transport471.possible f T
    (((4^rankHalf-1)/3+2^(rankHalf-1))*T) (2*((4^rankHalf-1)/3))) ↔
      2*((4^rankHalf-1)/3) ∣ T
  rw [← hr, Transport471.transport f e t c hf]
  have hmean :
      Lower471.average (fun x : Model471.X m => Lower471.sign (Model471.quad x)) =
        Lower471.mu m :=
    Model471.mean_quad m
  have hc (l : Model471.X m →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) :
      Lower471.average (fun x => Lower471.sign (l x)) = 0 ∧
      |Lower471.average (fun x => Lower471.sign (Model471.quad x)*Lower471.sign (l x))| ≤
        Lower471.mu m := by
    constructor
    · change (∑ x, Model471.sign (l x))/(Fintype.card (Model471.X m) : ℚ) = 0
      rw [Model471.sum_sign_linear l hl, zero_div]
    · obtain ⟨u, hu⟩ := Model471.probe_repr l
      have h :
          Lower471.average (fun x => Lower471.sign (Model471.quad x)*Lower471.sign (l x)) =
            Model471.sign (Model471.quad u)/(2:ℚ)^m := by
        change Model471.average (fun x => Model471.sign (Model471.quad x)*Model471.sign (l x)) = _
        simp_rw [hu]
        exact Model471.mean_corr u
      rw [h, abs_div, abs_of_nonneg (by positivity : 0 ≤ (2:ℚ)^m)]
      by_cases hz : Model471.quad u=0 <;> simp [Model471.sign, hz, Lower471.mu]
  constructor
  · rintro ⟨A, out, h⟩
    exact Lower471.necessity m hm' Model471.quad hmean hc T A out h
  · intro hd
    exact Upper471.upper m T hm' hd (fun x => Model471.sum_corr x)
