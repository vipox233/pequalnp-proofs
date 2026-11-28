import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_946_aux

abbrev dotY {m : ℕ} (u v : Fin m → ZMod 2) : ZMod 2 := ∑ j : Fin m, u j * v j

abbrev earlier {k p : ℕ} (slot : Fin p → Option (Fin k)) (i : Fin k) (a : Fin p) : Prop :=
  slot a = none ∨ ∃ j : Fin k, slot a = some j ∧ j < i

abbrev exposes {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (i : Fin k) (l : Fin m → ZMod 2) : Prop :=
  (∀ a : Fin p, earlier slot i a → dotY l (col a) = 0) ∧
    (∑ a : Fin p, if slot a = some i then dotY l (col a) else 0) = 1

abbrev piv {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter (fun i => ∃ l : Fin m → ZMod 2, exposes slot col i l)

abbrev valid {k p : ℕ} (slot : Fin p → Option (Fin k)) (T : Fin p → (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∀ (a : Fin p) (i : Fin k), slot a = some i → ∀ x z : Fin k → ZMod 2,
    (∀ j : Fin k, i < j → x j = z j) → T a x = T a z

abbrev output {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (T : Fin p → (Fin k → ZMod 2) → ZMod 2) (x : Fin k → ZMod 2) (j : Fin m) : ZMod 2 :=
  ∑ a : Fin p, (((slot a).elim 0 (fun i => x i)) + T a x) * col a j

noncomputable def ab_l {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (i : Fin k) : Fin m → ZMod 2 :=
  Classical.epsilon (fun l => exposes slot col i l)

theorem ab_exp {k m p : ℕ} {slot : Fin p → Option (Fin k)} {col : Fin p → Fin m → ZMod 2}
    {i : Fin k} (hi : i ∈ piv slot col) : exposes slot col i (ab_l slot col i) :=
  Classical.epsilon_spec (Finset.mem_filter.mp hi).2

theorem ab_dot {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (T : Fin p → (Fin k → ZMod 2) → ZMod 2) (l : Fin m → ZMod 2) (x : Fin k → ZMod 2) :
    dotY l (output slot col T x) =
      ∑ a : Fin p, (((slot a).elim 0 (fun i => x i)) + T a x) * dotY l (col a) := by
  simp only [dotY, output, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

theorem ab_key {k m p : ℕ} {slot : Fin p → Option (Fin k)} {col : Fin p → Fin m → ZMod 2}
    {T : Fin p → (Fin k → ZMod 2) → ZMod 2} {i : Fin k} {l : Fin m → ZMod 2}
    (h : exposes slot col i l) (hT : valid slot T) (w w' : Fin k → ZMod 2)
    (hw : ∀ j : Fin k, i < j → w j = w' j) :
    dotY l (output slot col T w) + w i = dotY l (output slot col T w') + w' i := by
  have e : ∀ x : Fin k → ZMod 2, dotY l (output slot col T x) + x i =
      ∑ a : Fin p, ((((slot a).elim 0 (fun j => x j)) + T a x) * dotY l (col a) +
        if slot a = some i then dotY l (col a) * x i else 0) := by
    intro x
    have h3 : ∀ a : Fin p, (if slot a = some i then dotY l (col a) * x i else 0) =
        (if slot a = some i then dotY l (col a) else 0) * x i := fun a => by
      split_ifs <;> simp
    rw [ab_dot, Finset.sum_add_distrib, Finset.sum_congr rfl (fun a _ => h3 a),
      ← Finset.sum_mul, h.2, one_mul]
  rw [e w, e w']
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases hs : slot a with _ | j
  · have h0 := h.1 a (Or.inl hs)
    simp [h0]
  · rcases lt_trichotomy j i with hj | rfl | hj
    · have h0 := h.1 a (Or.inr ⟨j, hs, hj⟩)
      simp [h0]
    · have hTa := hT a j hs w w' hw
      simp only [Option.elim]
      rw [hTa]
      generalize T a w' = t
      generalize dotY l (col a) = d
      generalize w j = u
      generalize w' j = u'
      revert t d u u'
      decide
    · have hTa := hT a j hs w w' (fun j' hj' => hw j' (hj.trans hj'))
      have hne : j ≠ i := hj.ne'
      simp [hTa, hw j hj, hne]

theorem ab_inj {k m p : ℕ} {slot : Fin p → Option (Fin k)} {col : Fin p → Fin m → ZMod 2}
    {T : Fin p → (Fin k → ZMod 2) → ZMod 2} (hT : valid slot T) {w w' : Fin k → ZMod 2}
    (hoff : ∀ i : Fin k, i ∉ piv slot col → w i = w' i)
    (hon : ∀ i ∈ piv slot col, dotY (ab_l slot col i) (output slot col T w) =
      dotY (ab_l slot col i) (output slot col T w')) : w = w' := by
  have H : ∀ n : ℕ, ∀ i : Fin k, k - i.val = n → w i = w' i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hab : ∀ j : Fin k, i < j → w j = w' j := fun j hj => by
        have h1 := Fin.lt_def.mp hj
        have h2 := j.isLt
        exact ih (k - j.val) (by omega) j rfl
      by_cases hp : i ∈ piv slot col
      · have h3 := ab_key (ab_exp hp) hT w w' hab
        rw [hon i hp] at h3
        exact add_left_cancel h3
      · exact hoff i hp
  funext i
  exact H _ i rfl

noncomputable def ab_Phi {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (T : Fin p → (Fin k → ZMod 2) → ZMod 2) (w : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  if i ∈ piv slot col then dotY (ab_l slot col i) (output slot col T w) else w i

theorem partA {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2) :
    ∃ l : Fin k → Fin m → ZMod 2, (∀ i ∈ piv slot col, exposes slot col i (l i)) ∧
      ∀ (T : Fin p → (Fin k → ZMod 2) → ZMod 2), valid slot T → ∀ (seed y : Fin k → ZMod 2),
        ∃! w : Fin k → ZMod 2, (∀ i : Fin k, i ∉ piv slot col → w i = seed i) ∧
          ∀ i ∈ piv slot col, dotY (l i) (output slot col T w) = y i := by
  refine ⟨ab_l slot col, fun i hi => ab_exp hi, fun T hT seed y => ?_⟩
  have hinj : Function.Injective (ab_Phi slot col T) := by
    intro w w' h
    apply ab_inj hT
    · intro i hi
      have h1 := congrFun h i
      rwa [ab_Phi, ab_Phi, if_neg hi, if_neg hi] at h1
    · intro i hi
      have h1 := congrFun h i
      rwa [ab_Phi, ab_Phi, if_pos hi, if_pos hi] at h1
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj)
    (fun i => if i ∈ piv slot col then y i else seed i)
  refine ⟨w, ⟨fun i hi => ?_, fun i hi => ?_⟩, fun w' hw' => ?_⟩
  · have h1 := congrFun hw i
    rwa [ab_Phi, if_neg hi, if_neg hi] at h1
  · have h1 := congrFun hw i
    rwa [ab_Phi, if_pos hi, if_pos hi] at h1
  · apply hinj
    rw [hw]
    funext i
    by_cases hi : i ∈ piv slot col
    · rw [ab_Phi, if_pos hi, if_pos hi]
      exact hw'.2 i hi
    · rw [ab_Phi, if_neg hi, if_neg hi]
      exact hw'.1 i hi

theorem partB {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (T : Fin p → (Fin k → ZMod 2) → ZMod 2) (hT : valid slot T) (y : Fin m → ZMod 2) :
    Nat.card {w : Fin k → ZMod 2 // output slot col T w = y} ≤ 2^(k - (piv slot col).card) := by
  classical
  let f : {w : Fin k → ZMod 2 // output slot col T w = y} →
      ({i : Fin k // i ∉ piv slot col} → ZMod 2) := fun w i => w.1 i.1
  have hf : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    apply ab_inj hT
    · intro i hi
      exact congrFun h ⟨i, hi⟩
    · intro i _
      rw [w.2, w'.2]
  rw [Nat.card_eq_fintype_card]
  refine (Fintype.card_le_of_injective f hf).trans (le_of_eq ?_)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

def cc_dl {m : ℕ} (l : Fin m → ZMod 2) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := dotY l v
  map_add' x y := by simp [dotY, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [dotY, Finset.mul_sum, mul_left_comm]

@[simp] theorem cc_dl_apply {m : ℕ} (l v : Fin m → ZMod 2) : cc_dl l v = dotY l v := rfl

theorem cc_dual {m : ℕ} (f : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    cc_dl (fun j => f (Pi.single j 1)) = f := by
  ext j
  simp [dotY, Pi.single_apply]

theorem cc_two : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem cc_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem cc_ite {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (F : M →ₗ[ZMod 2] ZMod 2)
    (P : Prop) [Decidable P] (x : M) : F (if P then x else 0) = if P then F x else 0 := by
  split_ifs <;> simp

theorem cc_mu {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2) (i : Fin k)
    (hi : i ∉ piv slot col) : ∃ μ : Fin p → ZMod 2, (∀ a, μ a ≠ 0 → earlier slot i a) ∧
      ∑ a, μ a • col a = ∑ a, if slot a = some i then col a else 0 := by
  classical
  have hc : (∑ a, if slot a = some i then col a else 0) ∈
      Submodule.span (ZMod 2) (Set.range (fun a => if earlier slot i a then col a else 0)) := by
    by_contra hn
    obtain ⟨f, hf2, hf1⟩ := Submodule.exists_le_ker_of_notMem hn
    have hd : ∀ v, dotY (fun j => f (Pi.single j 1)) v = f v := fun v => by
      rw [← cc_dl_apply, cc_dual]
    apply hi
    simp only [piv, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
    · intro a ha
      have hm : (if earlier slot i a then col a else 0) ∈
          Submodule.span (ZMod 2) (Set.range (fun a => if earlier slot i a then col a else 0)) :=
        Submodule.subset_span ⟨a, rfl⟩
      rw [ite_eq_left ha] at hm
      rw [hd]
      exact LinearMap.mem_ker.mp (hf1 hm)
    · simp only [hd]
      rw [← cc_two _ hf2, map_sum]
      exact Finset.sum_congr rfl fun a _ => (cc_ite f _ _).symm
  rw [Submodule.mem_span_range_iff_exists_fun] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨fun a => if earlier slot i a then g a else 0, ?_, ?_⟩
  · intro a ha
    by_contra h
    exact ha (ite_eq_right h)
  · rw [← hg]
    exact Finset.sum_congr rfl fun a _ => by
      by_cases h : earlier slot i a <;> simp only [h, ite_true, ite_false, smul_zero, zero_smul]

theorem cc_card {k : ℕ} (s : Finset (Fin k)) :
    Nat.card {w : Fin k → ZMod 2 // ∀ i ∈ s, w i = 0} = 2 ^ (k - s.card) := by
  classical
  have e : {w : Fin k → ZMod 2 // ∀ i ∈ s, w i = 0} ≃ ({i : Fin k // i ∉ s} → ZMod 2) :=
    { toFun := fun w i => w.1 i.1
      invFun := fun v => ⟨fun i => if h : i ∈ s then 0 else v ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun w => Subtype.ext (funext fun i => by
        by_cases h : i ∈ s
        · simp [h, w.2 i h]
        · simp [h])
      right_inv := fun v => funext fun i => by simp [i.2] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

theorem cc_out {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (S : Finset (Fin k)) (μ : Fin k → Fin p → ZMod 2)
    (hμ : ∀ i, i ∉ S → ∑ a, μ i a • col a = ∑ a, if slot a = some i then col a else 0)
    (w : Fin k → ZMod 2) (jj : Fin m) :
    output slot col (fun a x => cc_dl (fun i => if i ∈ S then 0 else μ i a) x) w jj =
      ∑ i, if i ∈ S then w i * ∑ a, (if slot a = some i then col a jj else 0) else 0 := by
  have h1 : ∀ a, (slot a).elim 0 (fun i => w i) * col a jj =
      ∑ i, w i * (if slot a = some i then col a jj else 0) := by
    intro a
    cases slot a <;> simp
  have h2 : ∀ a, cc_dl (fun i => if i ∈ S then 0 else μ i a) w * col a jj =
      ∑ i, (if i ∈ S then 0 else w i * (μ i a * col a jj)) := by
    intro a
    simp only [cc_dl_apply, dotY, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have h3 : ∀ i, i ∉ S → ∑ a, μ i a * col a jj = ∑ a, if slot a = some i then col a jj else 0 := by
    intro i hi
    have := congrFun (hμ i hi) jj
    simpa [Finset.sum_apply, ite_apply] using this
  calc output slot col (fun a x => cc_dl (fun i => if i ∈ S then 0 else μ i a) x) w jj
      = ∑ a, ∑ i, (w i * (if slot a = some i then col a jj else 0) +
          (if i ∈ S then 0 else w i * (μ i a * col a jj))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [add_mul, h1, h2, Finset.sum_add_distrib]
    _ = ∑ i, ∑ a, (w i * (if slot a = some i then col a jj else 0) +
          (if i ∈ S then 0 else w i * (μ i a * col a jj))) := Finset.sum_comm
    _ = ∑ i, (w i * ∑ a, (if slot a = some i then col a jj else 0) +
          (if i ∈ S then 0 else w i * ∑ a, μ i a * col a jj)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        split_ifs <;> simp [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with h
        · simp
        · rw [h3 i h, cc_add_self]

theorem cc_indep {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2)
    (w : Fin k → ZMod 2)
    (h : ∀ jj, ∑ i, (if i ∈ piv slot col then w i * ∑ a, (if slot a = some i then col a jj else 0)
      else 0) = 0) :
    ∀ i ∈ piv slot col, w i = 0 := by
  by_contra hne
  push Not at hne
  have hs : ((piv slot col).filter (fun i => w i ≠ 0)).Nonempty := by
    obtain ⟨i, hi, hw⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hw⟩⟩
  have htm := Finset.max'_mem _ hs
  set t := ((piv slot col).filter (fun i => w i ≠ 0)).max' hs with ht
  obtain ⟨htp, htw⟩ := Finset.mem_filter.mp htm
  obtain ⟨l, hl1, hl2⟩ := (Finset.mem_filter.mp htp).2
  have hV : (∑ i, if i ∈ piv slot col then
      w i • ∑ a, (if slot a = some i then col a else 0) else 0) = 0 := by
    funext jj
    simpa [Finset.sum_apply, ite_apply] using h jj
  have key := congrArg (cc_dl l) hV
  simp only [map_sum, cc_ite, map_smul, map_zero, smul_eq_mul, cc_dl_apply] at key
  rw [Finset.sum_eq_single t] at key
  · rw [ite_eq_left htp, hl2, cc_two _ htw] at key
    exact one_ne_zero key
  · intro i _ hit
    split_ifs with hip
    · rcases lt_or_gt_of_ne hit with hlt | hlt
      · rw [Finset.sum_eq_zero, mul_zero]
        intro a _
        split_ifs with ha
        · exact hl1 a (Or.inr ⟨i, ha, hlt⟩)
        · rfl
      · have hw : w i = 0 := by
          by_contra hw
          have := Finset.le_max' ((piv slot col).filter (fun i => w i ≠ 0)) i (Finset.mem_filter.mpr ⟨hip, hw⟩)
          rw [← ht] at this
          exact absurd hlt (not_lt.mpr this)
        rw [hw, zero_mul]
    · rfl
  · intro hn
    exact absurd (Finset.mem_univ t) hn

theorem partC {k m p : ℕ} (slot : Fin p → Option (Fin k)) (col : Fin p → Fin m → ZMod 2) :
    ∃ L : Fin p → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2), valid slot (fun a x => L a x) ∧
      Nat.card {w : Fin k → ZMod 2 // output slot col (fun a x => L a x) w = 0} = 2^(k - (piv slot col).card) := by
  have hμ0 : ∀ i, ∃ μ : Fin p → ZMod 2, i ∉ piv slot col → ((∀ a, μ a ≠ 0 → earlier slot i a) ∧
      ∑ a, μ a • col a = ∑ a, if slot a = some i then col a else 0) := by
    intro i
    by_cases hi : i ∉ piv slot col
    · obtain ⟨μ, h⟩ := cc_mu slot col i hi
      exact ⟨μ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose μ hμ using hμ0
  refine ⟨fun a => cc_dl (fun i => if i ∈ piv slot col then 0 else μ i a), ?_, ?_⟩
  · intro a j hj x z hxz
    simp only [cc_dl_apply, dotY]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ piv slot col
    · simp [hi]
    · by_cases hne : μ i a = 0
      · simp [hne]
      · rcases (hμ i hi).1 a hne with h | ⟨j', hj', hlt⟩
        · rw [hj] at h
          exact absurd h (Option.some_ne_none _)
        · rw [hj] at hj'
          obtain rfl := Option.some.inj hj'
          rw [hxz i hlt]
  · rw [← cc_card (piv slot col)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
    · refine cc_indep slot col w fun jj => ?_
      rw [← cc_out slot col (piv slot col) μ (fun i hi => (hμ i hi).2) w jj]
      exact congrFun hw jj
    · funext jj
      rw [cc_out slot col (piv slot col) μ (fun i hi => (hμ i hi).2) w jj]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with h
      · rw [hw i h, zero_mul]
      · rfl

end PEqualNP.Outside.L_lib_946_aux

theorem PEqualNP.Outside.L_lib_946 : (∀ (k m p : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Y := Fin m → F
  let dot := fun (u v : Y) => ∑ j : Fin m, u j * v j
  ∀ (slot : Fin p → Option (Fin k)) (col : Fin p → Y),
    let earlier := fun (i : Fin k) (a : Fin p) =>
      slot a = none ∨ ∃ j : Fin k, slot a = some j ∧ j < i
    let exposes := fun (i : Fin k) (l : Y) =>
      (∀ a : Fin p, earlier i a → dot l (col a) = 0) ∧
      (∑ a : Fin p, if slot a = some i then dot l (col a) else 0) = 1
    let piv := (Finset.univ : Finset (Fin k)).filter (fun i => ∃ l : Y, exposes i l)
    let valid := fun (T : Fin p → X → F) => ∀ (a : Fin p) (i : Fin k),
      slot a = some i → ∀ x z : X, (∀ j : Fin k, i < j → x j = z j) → T a x = T a z
    let output := fun (T : Fin p → X → F) (x : X) (j : Fin m) =>
      ∑ a : Fin p, (((slot a).elim 0 (fun i => x i)) + T a x) * col a j
    (∃ l : Fin k → Y, (∀ i ∈ piv, exposes i (l i)) ∧
      ∀ (T : Fin p → X → F), valid T → ∀ (seed y : X),
        ∃! w : X, (∀ i : Fin k, i ∉ piv → w i = seed i) ∧
          ∀ i ∈ piv, dot (l i) (output T w) = y i) ∧
    (∀ (T : Fin p → X → F), valid T → ∀ y : Y,
      Nat.card {w : X // output T w = y} ≤ 2^(k-piv.card)) ∧
    ∃ L : Fin p → (X →ₗ[F] F), valid (fun a x => L a x) ∧
      Nat.card {w : X // output (fun a x => L a x) w = 0} = 2^(k-piv.card)) := by
  intro k m p
  dsimp only
  intro slot col
  exact ⟨PEqualNP.Outside.L_lib_946_aux.partA slot col,
    fun T hT y => PEqualNP.Outside.L_lib_946_aux.partB slot col T hT y,
    PEqualNP.Outside.L_lib_946_aux.partC slot col⟩
