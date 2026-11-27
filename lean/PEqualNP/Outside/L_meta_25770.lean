import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25770_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private abbrev W := ℕ → Bool
private abbrev F := W → Bool

private def Tracks (f : F) (S : Finset ℕ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

private def Apart (i : ℕ) (x y : W) : Prop := ∀ j, j ≠ i → x j = y j

private theorem Apart.symm {i x y} (h : Apart i x y) : Apart i y x :=
  fun j hj => (h j hj).symm

private def Essential (f : F) (i : ℕ) : Prop :=
  ∃ x y, Apart i x y ∧ f x ≠ f y

private def Dir (p : Bool) (a b : Bool) : Prop := if p then a ≤ b else b ≤ a

private def Signed (f : F) (i : ℕ) (p : Bool) : Prop :=
  ∀ x y, Apart i x y → Dir p (x i) (y i) → f x ≤ f y

private def Unate (f : F) (i : ℕ) : Prop := ∃ p, Signed f i p

private def AllUnate (f : F) : Prop := ∀ i, Unate f i

private def Good (f : F) : Prop := AllUnate f ∨ ∃ i, Unate f i ∧ Essential f i

private theorem Tracks.eq_of_off {f : F} {S : Finset ℕ} (h : Tracks f S) {i x y}
    (hi : i ∉ S) (ha : Apart i x y) : f x = f y :=
  h x y fun j hj => ha j (fun e => hi (e ▸ hj))

private theorem Tracks.unate_off {f : F} {S : Finset ℕ} (h : Tracks f S) {i}
    (hi : i ∉ S) : Unate f i :=
  ⟨true, fun _ _ ha _ => le_of_eq (h.eq_of_off hi ha)⟩

private theorem Tracks.essential_mem {f : F} {S : Finset ℕ} (h : Tracks f S) {i}
    (hi : Essential f i) : i ∈ S := by
  by_contra hnot
  obtain ⟨x, y, ha, hne⟩ := hi
  exact hne (h.eq_of_off hnot ha)

private theorem Tracks.insert_irrel {f : F} {S : Finset ℕ} {i : ℕ}
    (h : Tracks f (insert i S)) (hi : ¬ Essential f i) : Tracks f S := by
  intro x y he
  let z := Function.update x i (y i)
  have h₁ : f x = f z := by
    by_contra hn
    exact hi ⟨x, z, fun j hj => by simp [z, Function.update_of_ne hj], hn⟩
  refine h₁.trans (h z y fun j hj => ?_)
  by_cases hj' : j = i
  · subst j; simp [z]
  · exact (Function.update_of_ne hj' _ _).trans (he j (by simpa [hj'] using hj))

private theorem Tracks.restrict {f : F} {S T : Finset ℕ} (h : Tracks f S)
    (hi : ∀ i ∈ S, i ∉ T → ¬ Essential f i) : Tracks f T := by
  have aux : ∀ U : Finset ℕ, Tracks f (U ∪ T) →
      (∀ i ∈ U, i ∉ T → ¬ Essential f i) → Tracks f T := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U _ ih =>
      intro hut hu
      rw [Finset.insert_union] at hut
      apply ih _ (fun i hiU => hu i (Finset.mem_insert_of_mem hiU))
      by_cases ha : a ∈ T
      · rwa [Finset.insert_eq_of_mem (Finset.mem_union_right U ha)] at hut
      · exact hut.insert_irrel (hu a (Finset.mem_insert_self _ _) ha)
  exact aux S (fun x y he => h x y fun i hiS => he i (Finset.mem_union_left T hiS)) hi

private theorem singleton_unate {f : F} {k : ℕ} (h : Tracks f {k}) : AllUnate f := by
  intro i
  by_cases hi : i = k
  · subst i
    let z : W := fun _ => false
    let o : W := fun _ => true
    have hz (x : W) (hx : x k = false) : f x = f z := h x z (by simpa [z])
    have ho (x : W) (hx : x k = true) : f x = f o := h x o (by simpa [o])
    by_cases hp : f z ≤ f o
    · refine ⟨true, fun x y _ hxy => ?_⟩
      rcases hxb : x k <;> rcases hyb : y k <;> simp_all [Dir]
      exact False.elim ((by decide : ¬ true ≤ false) hxy)
    · refine ⟨false, fun x y _ hxy => ?_⟩
      have hp' : f o ≤ f z := le_of_not_ge hp
      rcases hxb : x k <;> rcases hyb : y k <;> simp_all [Dir]
      exact False.elim ((by decide : ¬ true ≤ false) hxy)
  · exact h.unate_off (by simpa using hi)

private theorem one_exception_good {f : F} {S : Finset ℕ} {k : ℕ} (h : Tracks f S)
    (hu : ∀ i, i ≠ k → Unate f i) : Good f := by
  by_cases he : ∃ i, i ≠ k ∧ Essential f i
  · obtain ⟨i, hi, he⟩ := he
    exact Or.inr ⟨i, hu i hi, he⟩
  · exact Or.inl (singleton_unate (h.restrict fun i _ hi hess =>
      he ⟨i, fun e => hi (Finset.mem_singleton.mpr e), hess⟩))

private def subst (f q : F) (t : ℕ) (x : W) : Bool := f (Function.update x t (q x))

private theorem subst_tracks {f q : F} {R S : Finset ℕ} (hf : Tracks f R)
    (hq : Tracks q S) (t : ℕ) : Tracks (subst f q t) (R.erase t ∪ S) := by
  intro x y hxy
  have hq' := hq x y (fun i hi => hxy i (Finset.mem_union_right _ hi))
  apply hf
  intro i hi
  by_cases hit : i = t
  · subst i; simpa using hq'
  · simpa [Function.update_of_ne hit] using
      hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hit, hi⟩))

private theorem subst_unate_off {f q : F} {S : Finset ℕ} {t i : ℕ}
    (hq : Tracks q S) (hi : i ∉ S) (hu : Unate f i) :
    Unate (subst f q t) i := by
  obtain ⟨p, hp⟩ := hu
  refine ⟨p, fun x y ha hd => ?_⟩
  have hqq := hq.eq_of_off hi ha
  apply hp
  · intro j hj
    by_cases hjt : j = t
    · subst j; simpa using hqq
    · simp [Function.update_of_ne hjt, ha j hj]
  · by_cases hit : i = t
    · subst i; simp [hqq, Dir]
    · simpa [Function.update_of_ne hit] using hd

private theorem subst_unate_fresh {f q : F} {R : Finset ℕ} {t i : ℕ}
    (hf : Tracks f R) (hi : i ∉ R.erase t) (hut : Unate f t) (huq : Unate q i) :
    Unate (subst f q t) i := by
  obtain ⟨p, hp⟩ := hut
  obtain ⟨r, hr⟩ := huq
  let z (x : W) : W := Function.update (Function.update x i false) t (q x)
  have hz (x : W) : subst f q t x = f (z x) := by
    apply hf
    intro j hj
    by_cases hjt : j = t
    · subst j; simp [z]
    · have hji : j ≠ i := fun e => hi (e ▸ Finset.mem_erase.mpr ⟨hjt, hj⟩)
      simp [z, Function.update_of_ne hjt, Function.update_of_ne hji]
  refine ⟨!(p ^^ r), fun x y ha hd => ?_⟩
  rw [hz, hz]
  apply hp
  · intro j hj
    by_cases hji : j = i
    · subst j; simp [z, Function.update_of_ne hj]
    · simp [z, Function.update_of_ne hj, Function.update_of_ne hji, ha j hji]
  · have e₁ : z x t = q x := by simp [z]
    have e₂ : z y t = q y := by simp [z]
    rw [e₁, e₂]
    cases p <;> cases r <;> simp [Dir] at hd ⊢
    · exact hr y x ha.symm hd
    · exact hr y x ha.symm hd
    · exact hr x y ha hd
    · exact hr x y ha hd

private theorem subst_unate_except_overlap {f q : F} {R S : Finset ℕ} {t i : ℕ}
    (hf : Tracks f R) (hq : Tracks q S) (hu : Unate f t) (hi : Unate f i)
    (huq : Unate q i) (hn : i ∉ R.erase t ∩ S) : Unate (subst f q t) i := by
  by_cases hs : i ∈ S
  · exact subst_unate_fresh hf (fun h => hn (Finset.mem_inter.mpr ⟨h, hs⟩)) hu huq
  · exact subst_unate_off hq hs hi

private theorem subst_all_unate {f q : F} {R S : Finset ℕ} {t : ℕ}
    (hf : Tracks f R) (hq : Tracks q S) (hu : AllUnate f) (huq : AllUnate q)
    (hd : Disjoint (R.erase t) S) : AllUnate (subst f q t) := by
  intro i
  exact subst_unate_except_overlap hf hq (hu t) (hu i) (huq i)
    (by rw [Finset.disjoint_iff_inter_eq_empty.mp hd]; simp)

private def overlay (S : Finset ℕ) (x u : W) : W := fun i => if i ∈ S then u i else x i

private theorem subst_overlay {f q : F} {R S : Finset ℕ} {t : ℕ}
    (hf : Tracks f R) (hq : Tracks q S) (hd : Disjoint (R.erase t) S)
    {x u y : W} (hxy : ∀ i ∈ R.erase t, x i = y i) (hu : q u = y t) :
    subst f q t (overlay S x u) = f y := by
  have hqu : q (overlay S x u) = q u := hq _ _ (fun i hi => by simp [overlay, hi])
  apply hf
  intro i hi
  by_cases hit : i = t
  · subst i; simpa using hqu.trans hu
  · have he := Finset.mem_erase.mpr ⟨hit, hi⟩
    have hs : i ∉ S := fun h => Finset.disjoint_left.mp hd he h
    simpa [Function.update_of_ne hit, overlay, hs] using hxy i he

private theorem bool_swap {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem subst_good_fresh {f q : F} {R S : Finset ℕ} {t : ℕ}
    (hf : Tracks f R) (hq : Tracks q S) (huq : AllUnate q)
    (hd : Disjoint (R.erase t) S) (hne : S.Nonempty)
    (hess : ∀ i ∈ S, Essential q i) (hg : Good f) : Good (subst f q t) := by
  rcases hg with hu | ⟨i, hi, he⟩
  · exact Or.inl (subst_all_unate hf hq hu huq hd)
  obtain ⟨x, y, ha, hxy⟩ := he
  obtain ⟨j, hj⟩ := hne
  obtain ⟨u, v, huv, hquv⟩ := hess j hj
  have ha' (k : ℕ) (hk : k ∈ R.erase t) (h : i = t) : x k = y k :=
    ha k (by simpa [h] using (Finset.mem_erase.mp hk).1)
  have eq_sub (a b : W) (ha : ∀ k ∈ R.erase t, a k = b k)
      (w : W) (hw : q w = b t) : subst f q t (overlay S a w) = f b :=
    subst_overlay hf hq hd ha hw
  by_cases hit : i = t
  · have hn : x t ≠ y t := by
      intro ht
      apply hxy
      congr 1
      funext k
      by_cases hk : k = t
      · simpa [hk] using ht
      · exact ha k (by simpa [hit] using hk)
    have out (a b : W) (hab : Apart j a b) (haq : q a = x t) (hbq : q b = y t) :
        Good (subst f q t) := by
      right
      refine ⟨j, subst_unate_fresh hf (fun h => Finset.disjoint_left.mp hd h hj)
        (hit ▸ hi) (huq j), overlay S x a, overlay S x b, ?_, ?_⟩
      · intro k hk; simp [overlay, hab k hk]
      · rwa [eq_sub x x (fun _ _ => rfl) a haq, eq_sub x y (fun k hk => ha' k hk hit) b hbq]
    rcases bool_swap hquv hn with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact out u v huv hu hv
    · exact out v u huv.symm hv hu
  · have hir : i ∈ R.erase t :=
      Finset.mem_erase.mpr ⟨hit, hf.essential_mem ⟨x, y, ha, hxy⟩⟩
    have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hd hir h
    have hty : x t = y t := ha t (Ne.symm hit)
    obtain ⟨a, haq⟩ : ∃ a, q a = x t := by
      cases hx : x t <;> cases hu : q u <;> cases hv : q v <;>
        simp_all <;> first | exact ⟨u, hu⟩ | exact ⟨v, hv⟩
    right
    refine ⟨i, subst_unate_off hq hiS hi, overlay S x a, overlay S y a, ?_, ?_⟩
    · intro k hk; simp [overlay, ha k hk]
    · rwa [eq_sub x x (fun _ _ => rfl) a haq, eq_sub y y (fun _ _ => rfl) a (haq.trans hty)]

private def isNot : GateOp → Bool
  | .not => true
  | _ => false

private def loss (g : Gate) : ℕ := if isNot g.op then 1 else 0

private def readWire (t a : ℕ) (x : W) : Bool := if a < t then x a else false

private def readSet (t a : ℕ) : Finset ℕ := if a < t then {a} else ∅

private def gateFun (t : ℕ) (g : Gate) (x : W) : Bool :=
  g.op.eval (g.inputs.map (fun a => readWire t a x))

private def Profile (t c : ℕ) (q : F) (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, i < t) ∧ S.card ≤ c ∧ Tracks q S ∧ AllUnate q ∧
    (S.card = c → S.Nonempty ∧ ∀ i ∈ S, Essential q i)

private theorem readSet_lt {t a i : ℕ} (hi : i ∈ readSet t a) : i < t := by
  by_cases h : a < t <;> simp [readSet, h] at hi
  simpa [hi] using h

private theorem readSet_card (t a : ℕ) : (readSet t a).card ≤ 1 := by
  by_cases h : a < t <;> simp [readSet, h]

private theorem read_tracks (t a : ℕ) : Tracks (readWire t a) (readSet t a) := by
  intro x y hxy
  by_cases h : a < t
  · simpa [readWire, h] using hxy a (by simp [readSet, h])
  · simp [readWire, h]

private theorem read_signed (t a i : ℕ) : Signed (readWire t a) i true := by
  intro x y ha hd
  by_cases h : a < t
  · by_cases hai : a = i
    · subst a; simpa [readWire, h, Dir] using hd
    · simp [readWire, h, ha a hai]
  · simp [readWire, h]

private theorem constant_profile (t c : ℕ) (b : Bool) (hc : 0 < c) :
    Profile t c (fun _ => b) ∅ := by
  refine ⟨by simp, by simp, fun _ _ _ => rfl, fun _ => ⟨true, fun _ _ _ _ => le_rfl⟩, ?_⟩
  simpa using hc.ne

private theorem read_profile (t a : ℕ) : Profile t 2 (readWire t a) (readSet t a) :=
  ⟨fun _ => readSet_lt, (readSet_card t a).trans (by decide), read_tracks t a,
    fun i => ⟨true, read_signed t a i⟩, fun e => by have := readSet_card t a; omega⟩

private theorem not_le_not' : ∀ a b : Bool, a ≤ b → (!b) ≤ (!a) := by decide

private theorem not_profile (t a : ℕ) : Profile t 1 (fun x => !(readWire t a x)) (readSet t a) := by
  refine ⟨fun _ => readSet_lt, readSet_card t a, ?_, ?_, ?_⟩
  · intro x y h; exact congrArg Bool.not (read_tracks t a x y h)
  · intro i
    exact ⟨false, fun x y ha hd => not_le_not' _ _ (read_signed t a i y x ha.symm hd)⟩
  · intro hs
    have ht : a < t := by by_contra h; simp [readSet, h] at hs
    simp only [readSet, ht, ite_true]
    refine ⟨Finset.singleton_nonempty _, fun i hi => ?_⟩
    have e : i = a := Finset.mem_singleton.mp hi
    subst i
    refine ⟨fun _ => false, fun j => decide (j = a), ?_, by simp [readWire, ht]⟩
    intro j hj
    simp [hj]

private def bop (p a b : Bool) : Bool := if p then a && b else a || b

private theorem bop_mono : ∀ p a b a' b' : Bool, a ≤ a' → b ≤ b' →
    bop p a b ≤ bop p a' b' := by decide

private theorem bop_comm : ∀ p a b : Bool, bop p a b = bop p b a := by decide

private theorem bop_essential {t a b : ℕ} (ha : a < t) (hb : b < t) (hab : a ≠ b) (p : Bool) :
    Essential (fun x => bop p (readWire t a x) (readWire t b x)) a := by
  refine ⟨fun _ => p, fun j => if j = a then !p else p, ?_, ?_⟩
  · intro j hj; simp [hj]
  · cases p <;> simp [bop, readWire, ha, hb, Ne.symm hab]

private theorem bop_profile (p : Bool) (t a b : ℕ) :
    Profile t 2 (fun x => bop p (readWire t a x) (readWire t b x))
      (readSet t a ∪ readSet t b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rcases Finset.mem_union.mp hi with h | h <;> exact readSet_lt h
  · have hc := Finset.card_union_le (readSet t a) (readSet t b)
    have ha := readSet_card t a
    have hb := readSet_card t b
    omega
  · intro x y h
    dsimp only
    rw [read_tracks t a x y (fun i hi => h i (Finset.mem_union_left _ hi)),
        read_tracks t b x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · intro i
    exact ⟨true, fun x y ha hd => bop_mono _ _ _ _ _
      (read_signed t a i x y ha hd) (read_signed t b i x y ha hd)⟩
  · intro h
    have ha : a < t := by
      by_contra hn
      have hc := readSet_card t b
      rw [show readSet t a = ∅ by simp [readSet, hn], Finset.empty_union] at h
      omega
    have hb : b < t := by
      by_contra hn
      have hc := readSet_card t a
      rw [show readSet t b = ∅ by simp [readSet, hn], Finset.union_empty] at h
      omega
    have hab : a ≠ b := by
      rintro rfl
      simp [readSet, ha] at h
    simp only [readSet, ha, hb, ite_true]
    refine ⟨⟨a, by simp⟩, fun i hi => ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact bop_essential ha hb hab p
    · have e : (fun x => bop p (readWire t a x) (readWire t i x)) =
          (fun x => bop p (readWire t i x) (readWire t a x)) := funext (fun _ => bop_comm _ _ _)
      rw [e]
      exact bop_essential hb ha (Ne.symm hab) p

private theorem gate_profile (t : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h2 : g.inputs.length ≤ 2) :
    ∃ S, Profile t (2 - loss g) (gateFun t g) S := by
  rcases g with ⟨o, l⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exact ⟨∅, constant_profile t 2 true (by decide)⟩
    · have e : gateFun t ⟨GateOp.and, [a]⟩ = readWire t a := by
        funext x; simp [gateFun, GateOp.eval]
      exact ⟨_, by rw [e]; exact read_profile t a⟩
    · have e : gateFun t ⟨GateOp.and, [a, b]⟩ =
          (fun x => bop true (readWire t a x) (readWire t b x)) := by
        funext x; simp [gateFun, GateOp.eval, bop]
      exact ⟨_, by rw [e]; exact bop_profile true t a b⟩
    · simp at h2
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exact ⟨∅, constant_profile t 2 false (by decide)⟩
    · have e : gateFun t ⟨GateOp.or, [a]⟩ = readWire t a := by
        funext x; simp [gateFun, GateOp.eval]
      exact ⟨_, by rw [e]; exact read_profile t a⟩
    · have e : gateFun t ⟨GateOp.or, [a, b]⟩ =
          (fun x => bop false (readWire t a x) (readWire t b x)) := by
        funext x; simp [gateFun, GateOp.eval, bop]
      exact ⟨_, by rw [e]; exact bop_profile false t a b⟩
    · simp at h2
  · rcases l with _ | ⟨a, l⟩
    · exact ⟨∅, constant_profile t 1 true (by decide)⟩
    · exact ⟨_, not_profile t a⟩

private def Budget (used limit : ℕ) (f f' : F) : Prop :=
  used ≤ limit ∧
    (used = limit → AllUnate f → AllUnate f') ∧
    (used = limit → Good f → Good f') ∧
    (limit ≤ used + 1 → AllUnate f → Good f')

private theorem Budget.combine {a b c k l z : ℕ} {f f₁ f₂ : F}
    (h : Budget (b + k) (a + 1) f f₁) (h' : Budget (c + l) (b + z) f₁ f₂) :
    Budget (c + (l + k)) (a + (z + 1)) f f₂ := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  obtain ⟨h₀', h₁', h₂', h₃'⟩ := h'
  refine ⟨by omega, fun he hu => h₁' (by omega) (h₁ (by omega) hu),
    fun he hu => h₂' (by omega) (h₂ (by omega) hu), fun he hu => ?_⟩
  by_cases ht : b + k = a + 1
  · exact h₃' (by omega) (h₁ ht hu)
  · exact h₂' (by omega) (h₃ (by omega) hu)

-- A full step has no overlap. One unit of spare budget allows at most one overlapping wire.
private theorem eliminate_gate (t : ℕ) (g : Gate) (f : F) (R : Finset ℕ)
    (hR : ∀ i ∈ R, i < t + 1) (hf : Tracks f R)
    (hgate : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h2 : g.inputs.length ≤ 2) :
    ∃ R₀ f₀, (∀ i ∈ R₀, i < t) ∧ Tracks f₀ R₀ ∧
      Budget (R₀.card + loss g) (R.card + 1) f f₀ ∧
      ∀ x, f (Function.update x t (gateFun t g x)) = f₀ x := by
  have hl : loss g ≤ 1 := by unfold loss; split <;> decide
  by_cases ht : t ∈ R
  · obtain ⟨S, hb, hc, hq, huq, hs⟩ := gate_profile t g hgate h2
    let T := R.erase t ∪ S
    let D := R.erase t ∩ S
    have he := Finset.card_erase_of_mem ht
    have hpos : 0 < R.card := Finset.card_pos.mpr ⟨t, ht⟩
    have hcards : T.card + D.card = (R.erase t).card + S.card :=
      Finset.card_union_add_card_inter _ _
    have hd0 (h : T.card + loss g = R.card + 1) : Disjoint (R.erase t) S :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (show D.card = 0 by omega))
    have hT := subst_tracks hf hq t
    refine ⟨T, subst f (gateFun t g) t, ?_, hT, ?_, fun _ => rfl⟩
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
        have := hR i hmem
        omega
      · exact hb i h
    · refine ⟨by omega, ?_, ?_, ?_⟩
      · exact fun h hu => subst_all_unate hf hq hu huq (hd0 h)
      · intro h hu
        obtain ⟨hne, hess⟩ := hs (by omega)
        exact subst_good_fresh hf hq huq (hd0 h) hne hess hu
      · intro h hu
        have hD : D.card ≤ 1 := by omega
        by_cases hz : D.Nonempty
        · obtain ⟨k, hk⟩ := hz
          exact one_exception_good hT fun i hik =>
            subst_unate_except_overlap hf hq (hu t) (hu i) (huq i)
              (fun hi => hik (Finset.card_le_one.mp hD i hi k hk))
        · have hd : Disjoint (R.erase t) S :=
            Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hz)
          exact Or.inl (subst_all_unate hf hq hu huq hd)
  · refine ⟨R, f, ?_, hf, ⟨by omega, fun _ h => h, fun _ h => h, fun _ h => Or.inl h⟩, ?_⟩
    · intro i hi
      have := hR i hi
      have : i ≠ t := fun e => ht (e ▸ hi)
      omega
    · intro x
      apply hf
      intro i hi
      have hne : i ≠ t := fun e => ht (e ▸ hi)
      exact Function.update_of_ne hne _ _

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def vals (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

private def env (x : List Bool) : W := fun i => x.getD i false

private theorem vals_length (gs : List Gate) (x : List Bool) :
    (vals gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [vals]
  | append_singleton gs g ih =>
    simp only [vals, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (step (vals gs x) g).length = x.length + (gs ++ [g]).length
    simp [step, ih, Nat.add_assoc]

private theorem env_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : env w i = false := by
  simp [env, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem env_append (w : List Bool) (b : Bool) :
    env (w ++ [b]) = Function.update (env w) w.length b := by
  funext i
  by_cases hi : i < w.length
  · have hne := hi.ne
    simp [env, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, Function.update_of_ne hne]
  · by_cases he : i = w.length
    · subst i; simp [env]
    · rw [env_ge _ _ (by simp; omega), Function.update_of_ne he, env_ge _ _ (by omega)]

private theorem env_vals_append (N : ℕ) (gs : List Gate) (g : Gate) (x : List Bool)
    (hx : x.length = N) :
    env (vals (gs ++ [g]) x) = Function.update (env (vals gs x)) (N + gs.length)
      (gateFun (N + gs.length) g (env (vals gs x))) := by
  have hlen : (vals gs x).length = N + gs.length := (vals_length gs x).trans (by rw [hx])
  have he : gateFun (N + gs.length) g (env (vals gs x)) =
      g.op.eval (g.inputs.map fun i => (vals gs x).getD i false) := by
    unfold gateFun
    congr 1
    apply List.map_congr_left
    intro i _
    rw [← hlen]
    by_cases hi : i < (vals gs x).length
    · simp [readWire, env, hi]
    · change readWire (vals gs x).length i (env (vals gs x)) = env (vals gs x) i
      rw [env_ge _ _ (by omega)]
      simp [readWire, hi]
  conv_lhs => simp only [vals, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  change env (vals gs x ++ _) = _
  rw [env_append, hlen]
  exact congrArg (Function.update (env (vals gs x)) (N + gs.length)) he.symm

private def nots (gs : List Gate) : ℕ := (gs.map loss).sum

private theorem loss_le_nots {gs : List Gate} {g : Gate} (h : g ∈ gs) : loss g ≤ nots gs := by
  induction gs with
  | nil => simp at h
  | cons d ds ih =>
    simp only [nots, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | e
    · subst d; omega
    · have := ih e
      unfold nots at this
      omega

private theorem reduce_gates (N : ℕ) (gs : List Gate) (fg : FanInTwo ⟨gs, 0⟩)
    (R : Finset ℕ) (f : F) (hR : ∀ i ∈ R, i < N + gs.length) (hf : Tracks f R) :
    ∃ S q, (∀ i ∈ S, i < N) ∧ Tracks q S ∧
      Budget (S.card + nots gs) (R.card + gs.length) f q ∧
      ∀ x : List Bool, x.length = N → f (env (vals gs x)) = q (env x) := by
  induction gs using List.reverseRecOn generalizing R f with
  | nil =>
    exact ⟨R, f, by simpa using hR, hf,
      ⟨by simp [nots], fun _ h => h, fun _ h => h, fun _ h => Or.inl h⟩, fun _ _ => rfl⟩
  | append_singleton gs g ih =>
    have hgate := fg g (by simp)
    have hf' : FanInTwo ⟨gs, 0⟩ := fun d hd => fg d (by simp [hd])
    have hR' : ∀ i ∈ R, i < (N + gs.length) + 1 := by
      intro i hi
      have hh := hR i hi
      simp only [List.length_append, List.length_singleton] at hh
      omega
    obtain ⟨R₀, f₀, hb, ht, hc, he⟩ :=
      eliminate_gate (N + gs.length) g f R hR' hf hgate.1 hgate.2
    obtain ⟨S, q, hbs, hts, hcs, hes⟩ := ih hf' R₀ f₀ hb ht
    refine ⟨S, q, hbs, hts, ?_, ?_⟩
    · simpa [nots, List.map_append, List.sum_append] using hc.combine hcs
    · intro x hx
      rw [env_vals_append N gs g x hx, he, hes x hx]

private def pick (a b : ℕ) : W := fun i => decide (i = a ∨ i = b)

private theorem oneEach_true {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = true ↔ (i = u.val ∨ i = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

private theorem env_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    env (oneEach u v) = pick u.val (n + v.val) := by
  funext i
  exact Bool.eq_iff_iff.mpr ((oneEach_true u v i).trans (by simp [pick]))

-- If a wire is omitted, changing from that vertex to another vertex flips just one
-- tracked bit. The two directions of separation rule out both signs on that bit.
private theorem missing_nonunate {n m : ℕ} (p : Fin n → ℕ) (r : Fin m → ℕ)
    (hpr : ∀ u v, p u ≠ r v)
    (A : Fin n → Fin m → Bool)
    (hsep : ∀ u u', u ≠ u' → ∃ v, A u v = true ∧ A u' v = false)
    {f : F} {S : Finset ℕ} (ht : Tracks f S)
    (hrep : ∀ u v, f (pick (p u) (r v)) = A u v)
    {u₀ u : Fin n} (hmiss : p u₀ ∉ S) (hu : u ≠ u₀) : ¬ Unate f (p u) := by
  let z (v : Fin m) : W := fun i => decide (i = r v)
  have hz (v : Fin m) : f (z v) = A u₀ v := by
    rw [← hrep u₀ v]
    apply ht
    intro i hi
    have hne : i ≠ p u₀ := fun e => hmiss (e ▸ hi)
    simp [z, pick, hne]
  have ha (v : Fin m) : Apart (p u) (z v) (pick (p u) (r v)) := by
    intro i hi; simp [z, pick, hi]
  intro ⟨sgn, h⟩
  apply (by decide : ¬ (true : Bool) ≤ false)
  cases sgn
  · obtain ⟨v, hv, hv₀⟩ := hsep u u₀ hu
    have hh := h (pick (p u) (r v)) (z v) (ha v).symm
      (by simp [Dir, z, pick, hpr])
    rwa [hrep u v, hz v, hv, hv₀] at hh
  · obtain ⟨v, hv₀, hv⟩ := hsep u₀ u (Ne.symm hu)
    have hh := h (z v) (pick (p u) (r v)) (ha v)
      (by simp [Dir, z, pick, hpr])
    rwa [hrep u v, hz v, hv, hv₀] at hh

private theorem other {n : ℕ} (hn : 2 ≤ n) (u : Fin n) : ∃ v : Fin n, v ≠ u := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  by_cases h : a = u
  · exact ⟨b, fun e => by have he := congrArg Fin.val (e.trans h.symm); simp [a, b] at he⟩
  · exact ⟨a, h⟩

private theorem missing_card {n : ℕ} {p : Fin n → ℕ} {S : Finset ℕ} {f : F}
    (ht : Tracks f S)
    (h : ∀ {u₀ u : Fin n}, p u₀ ∉ S → u ≠ u₀ → ¬ Unate f (p u)) :
    (Finset.univ.filter (fun u => p u ∉ S)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun u hu v hv => ?_
  by_contra hne
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  exact h hv' hne (ht.unate_off hu')

private theorem support_count (n m : ℕ) (S : Finset ℕ) :
    n + m ≤ S.card + (Finset.univ.filter (fun u : Fin n => u.val ∉ S)).card +
      (Finset.univ.filter (fun v : Fin m => n + v.val ∉ S)).card := by
  have h₁ := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => u.val ∈ S)
  have h₂ := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun v : Fin m => n + v.val ∈ S)
  rw [Finset.card_univ, Fintype.card_fin] at h₁ h₂
  have h₃ : (Finset.univ.filter (fun u : Fin n => u.val ∈ S)).card ≤ (S.filter (· < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    refine Finset.card_le_card fun i hi => ?_
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, u.isLt⟩
  have h₄ : (Finset.univ.filter (fun v : Fin m => n + v.val ∈ S)).card ≤
      (S.filter (¬ · < n)).card := by
    have hinj : Function.Injective (fun v : Fin m => n + v.val) :=
      fun _ _ e => Fin.ext (Nat.add_left_cancel e)
    rw [← Finset.card_image_of_injective _ hinj]
    refine Finset.card_le_card fun i hi => ?_
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by omega⟩
  have h₅ := Finset.card_filter_add_card_filter_not (s := S) (· < n)
  omega

private theorem prove (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hrow : ∀ u u' : Fin n, u ≠ u' → ∃ v, A u v = true ∧ A u' v = false)
    (hcol : ∀ v v' : Fin m, v ≠ v' → ∃ u, A u v = true ∧ A u v' = false)
    (hfan : FanInTwo C) (hrep : Represents A C)
    (hno : ¬ RepSizeAtMost A (n + m - 1)) : n + m ≤ C.size := by
  by_contra hsmall
  change ¬ n + m ≤ C.gates.length at hsmall
  have hsize : C.gates.length ≤ n + m - 1 := by omega
  have hpos : 0 < nots C.gates := by
    by_contra hnp
    have hz : nots C.gates = 0 := by omega
    apply hno
    refine ⟨C, ?_, hsize, hrep⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hl := loss_le_nots hg
      simp [loss, h, isNot, hz] at hl
  have hout : C.output < n + m + C.gates.length := by
    by_contra hb
    let u : Fin n := ⟨0, by omega⟩
    obtain ⟨u', hu'⟩ := other hn u
    obtain ⟨v, hv, _⟩ := hrow u u' (Ne.symm hu')
    have he : C.eval (oneEach u v) = false := by
      apply env_ge
      change (vals C.gates (oneEach u v)).length ≤ C.output
      simpa [vals_length, oneEach] using Nat.le_of_not_gt hb
    rw [hrep u v, hv] at he
    contradiction
  let f : F := fun x => x C.output
  have hfu : AllUnate f := by
    intro i
    refine ⟨true, fun x y ha hd => ?_⟩
    by_cases hi : C.output = i
    · simpa [f, Dir, hi] using hd
    · exact le_of_eq (ha _ hi)
  obtain ⟨S, q, hS, htrack, hBudget, hq⟩ := reduce_gates (n + m) C.gates
    (fun g hg => hfan g hg) {C.output} f (by simpa) (by intro x y h; exact h _ (by simp))
  have hrepr (u : Fin n) (v : Fin m) : q (pick u.val (n + v.val)) = A u v := by
    rw [← env_oneEach u v, ← hq _ (by simp [oneEach])]
    exact hrep u v
  have hdisj (u : Fin n) (v : Fin m) : u.val ≠ n + v.val := by
    have := u.isLt
    omega
  let Mr := Finset.univ.filter (fun u : Fin n => u.val ∉ S)
  let Mc := Finset.univ.filter (fun v : Fin m => n + v.val ∉ S)
  have hru {u₀ u : Fin n} (hmiss : u₀.val ∉ S) (hu : u ≠ u₀) : ¬ Unate q u.val :=
    missing_nonunate Fin.val (fun v => n + v.val) hdisj A hrow
      htrack hrepr hmiss hu
  have hcu {v₀ v : Fin m} (hmiss : n + v₀.val ∉ S) (hv : v ≠ v₀) :
      ¬ Unate q (n + v.val) :=
    missing_nonunate (fun v => n + v.val) Fin.val
      (fun v u => Ne.symm (hdisj u v)) (fun v u => A u v) hcol htrack
      (fun v u => by
        have he : pick (n + v.val) u.val = pick u.val (n + v.val) := by
          funext i; simp only [pick, or_comm]
        rw [he]
        exact hrepr u v)
      hmiss hv
  have hr₁ : Mr.card ≤ 1 := missing_card htrack (fun hm hu => hru hm hu)
  have hc₁ : Mc.card ≤ 1 := missing_card htrack (fun hm hv => hcu hm hv)
  have hcount : n + m ≤ S.card + Mr.card + Mc.card := support_count n m S
  rw [Finset.card_singleton] at hBudget
  obtain ⟨hb, hall, _, hnear⟩ := hBudget
  have hun : ¬ AllUnate q := by
    intro h
    have hp : 0 < Mr.card ∨ 0 < Mc.card := by omega
    rcases hp with hp | hp
    · obtain ⟨r, hr⟩ := Finset.card_pos.mp hp
      obtain ⟨u, hu⟩ := other hn r
      exact hru (Finset.mem_filter.mp hr).2 hu (h u.val)
    · obtain ⟨c, hc⟩ := Finset.card_pos.mp hp
      obtain ⟨v, hv⟩ := other hm c
      exact hcu (Finset.mem_filter.mp hc).2 hv (h (n + v.val))
  have htight : S.card + nots C.gates ≠ 1 + C.gates.length := fun h => hun (hall h hfu)
  have hgood := hnear (by omega) hfu
  have hboth : Mr.card = 1 ∧ Mc.card = 1 := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < Mr.card)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < Mc.card)
  rcases hgood with h | ⟨i, hi, hei⟩
  · exact hun h
  · have him : i ∈ S := htrack.essential_mem hei
    have hib := hS i him
    by_cases hin : i < n
    · let u : Fin n := ⟨i, hin⟩
      have hne : u ≠ r := by
        intro e
        apply (Finset.mem_filter.mp hr).2
        exact (congrArg Fin.val e) ▸ him
      exact hru (Finset.mem_filter.mp hr).2 hne hi
    · let v : Fin m := ⟨i - n, by omega⟩
      have heq : n + v.val = i := by change n + (i - n) = i; omega
      have hne : v ≠ c := by
        intro e
        apply (Finset.mem_filter.mp hc).2
        rw [← e, heq]
        exact him
      exact hcu (Finset.mem_filter.mp hc).2 hne (heq.symm ▸ hi)

end PEqualNP.Outside.L_meta_25770_aux

theorem PEqualNP.Outside.L_meta_25770 :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v = true ∧ A u' v = false) → (∀ v v' : Fin m, v ≠ v' → ∃ u, A u v = true ∧ A u v' = false) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ¬ PEqualNP.Represents.RepSizeAtMost A (n + m - 1) → n + m ≤ C.size := by
  exact PEqualNP.Outside.L_meta_25770_aux.prove
